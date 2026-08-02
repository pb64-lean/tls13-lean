module

public import HaclStar.Sha256
public import TLS13.X509.Certificate

public section

/-!
RFC 5929 `tls-server-end-point` channel-binding data.

The input is the exact DER `Certificate` TLV retained by the X.509 parser,
never a re-encoding.  SHA-384 and SHA-512 certificate signatures select their
matching digest.  SHA-256 signatures, MD5/SHA-1 signatures, and signature
algorithms whose digest cannot be determined select SHA-256.

PostgreSQL asks OpenSSL's `X509_get_signature_info` for this digest, including
the hash embedded in RSASSA-PSS parameters.  Ed25519 has no separately exposed
digest and OpenSSL reports `NID_undef`; current upstream PostgreSQL consequently
cannot obtain an EVP digest for such a certificate.  This implementation uses
the requested unknown-algorithm SHA-256 fallback so Ed25519 certificates still
produce deterministic channel-binding data.
-/

namespace TLS13
namespace X509
namespace ChannelBinding

/-- Digest algorithms used by `tls-server-end-point` in this stack. -/
inductive HashAlgorithm where
  | sha256
  | sha384
  | sha512
  deriving Repr, BEq, DecidableEq, Inhabited

namespace SignatureOID

private def sha384WithRSAEncryption : OID :=
  { arcs := #[1, 2, 840, 113549, 1, 1, 12] }

private def sha512WithRSAEncryption : OID :=
  { arcs := #[1, 2, 840, 113549, 1, 1, 13] }

private def ecdsaWithSha384 : OID :=
  { arcs := #[1, 2, 840, 10045, 4, 3, 3] }

private def ecdsaWithSha512 : OID :=
  { arcs := #[1, 2, 840, 10045, 4, 3, 4] }

private def dsaWithSha384 : OID :=
  { arcs := #[2, 16, 840, 1, 101, 3, 4, 3, 3] }

private def dsaWithSha512 : OID :=
  { arcs := #[2, 16, 840, 1, 101, 3, 4, 3, 4] }

private def sha384 : OID :=
  { arcs := #[2, 16, 840, 1, 101, 3, 4, 2, 2] }

private def sha512 : OID :=
  { arcs := #[2, 16, 840, 1, 101, 3, 4, 2, 3] }

end SignatureOID

private def unwrapExplicit
    (value : DER.TLV) (number : Nat) : Except String DER.TLV := do
  value.requireTag {
    tagClass := .contextSpecific
    constructed := true
    number
  } "RSASSA-PSS parameter"
  let (inner, reader) ← value.reader.readTLV
  reader.requireEnd "RSASSA-PSS parameter"
  pure inner

private def parseAlgorithmIdentifier
    (value : DER.TLV) : Except String (OID × Option DER.TLV) := do
  value.requireTag DER.Tag.sequence "AlgorithmIdentifier"
  let (oidValue, reader) ← value.reader.readTLV
  let oid ← oidValue.asOID
  let (parameters, reader) ←
    if reader.atEnd then
      pure (none, reader)
    else
      let (parameters, reader) ← reader.readTLV
      pure (some parameters, reader)
  reader.requireEnd "AlgorithmIdentifier"
  pure (oid, parameters)

private def nullOrAbsent (parameters : Option DER.TLV) : Bool :=
  match parameters with
  | none => true
  | some value => value.tag == DER.Tag.null && value.contents.isEmpty

private def parametersAbsent (parameters : Option DER.TLV) : Bool :=
  parameters.isNone

private def parseNonnegativeInteger (value : DER.TLV) : Except String Nat := do
  value.requireTag DER.Tag.integer "RSASSA-PSS integer parameter"
  if value.contents.isEmpty then
    throw "RSASSA-PSS integer parameter is empty"
  if value.contents.size > 8 then
    throw "RSASSA-PSS integer parameter exceeds 8 octets"
  let first := value.contents.get! 0
  if first ≥ 0x80 then
    throw "RSASSA-PSS integer parameter is negative"
  if value.contents.size > 1 &&
      first == 0x00 && value.contents.get! 1 < 0x80 then
    throw "RSASSA-PSS integer parameter has redundant sign padding"
  pure (value.contents.foldl
    (fun result octet => result * 256 + octet.toNat) 0)

private def pssHashAlgorithm
    (parameters : Option DER.TLV) : Except String HashAlgorithm := do
  -- The absent/default hashAlgorithm is SHA-1, which RFC 5929 upgrades to
  -- SHA-256. Certificate parsing normally supplies the mandatory parameters,
  -- but treating absence as the ASN.1 default keeps this selector total.
  let some parameters := parameters
    | return .sha256
  parameters.requireTag DER.Tag.sequence "RSASSA-PSS-params"
  let mut reader := parameters.reader
  let mut previousTag : Option Nat := none
  let mut result := HashAlgorithm.sha256
  while !reader.atEnd do
    let (field, next) ← reader.readTLV
    unless field.tag.tagClass == .contextSpecific &&
        field.tag.constructed && field.tag.number ≤ 3 do
      throw "RSASSA-PSS-params contains an unexpected field"
    match previousTag with
    | some previous =>
      if field.tag.number ≤ previous then
        throw "RSASSA-PSS-params fields are duplicated or out of order"
    | none => pure ()
    let inner ← unwrapExplicit field field.tag.number
    if field.tag.number == 0 then
      let (oid, hashParameters) ← parseAlgorithmIdentifier inner
      unless nullOrAbsent hashParameters do
        throw "RSASSA-PSS hash AlgorithmIdentifier has invalid parameters"
      if oid == SignatureOID.sha384 then
        result := .sha384
      else if oid == SignatureOID.sha512 then
        result := .sha512
      else
        result := .sha256
    else if field.tag.number == 1 then
      let (oid, maskParameters) ← parseAlgorithmIdentifier inner
      unless oid == OID.mgf1 do
        throw "RSASSA-PSS mask generation algorithm is not MGF1"
      let some maskHash := maskParameters
        | throw "RSASSA-PSS MGF1 parameters are absent"
      let (_, maskHashParameters) ← parseAlgorithmIdentifier maskHash
      unless nullOrAbsent maskHashParameters do
        throw "RSASSA-PSS MGF1 hash has invalid parameters"
    else if field.tag.number == 2 then
      let _ ← parseNonnegativeInteger inner
    else
      let trailer ← parseNonnegativeInteger inner
      unless trailer == 1 do
        throw "RSASSA-PSS trailerField is not 1"
    previousTag := some field.tag.number
    reader := next
  pure result

/-- Select the RFC 5929 digest from a certificate signature AlgorithmIdentifier.

RSASSA-PSS reads the explicit `[0] hashAlgorithm`; its default SHA-1 and
malformed or unknown parameter sets use SHA-256. -/
def signatureHashAlgorithm (algorithm : AlgorithmIdentifier) : HashAlgorithm :=
  if algorithm.oid == SignatureOID.sha384WithRSAEncryption &&
      nullOrAbsent algorithm.parameters then
    .sha384
  else if (algorithm.oid == SignatureOID.ecdsaWithSha384 ||
      algorithm.oid == SignatureOID.dsaWithSha384) &&
      parametersAbsent algorithm.parameters then
    .sha384
  else if algorithm.oid == SignatureOID.sha512WithRSAEncryption &&
      nullOrAbsent algorithm.parameters then
    .sha512
  else if (algorithm.oid == SignatureOID.ecdsaWithSha512 ||
      algorithm.oid == SignatureOID.dsaWithSha512) &&
      parametersAbsent algorithm.parameters then
    .sha512
  else if algorithm.oid == OID.rsassaPss then
    match pssHashAlgorithm algorithm.parameters with
    | .ok hash => hash
    | .error _ => .sha256
  else
    .sha256

/-- Hash `data` with a selected channel-binding digest. -/
def hash (algorithm : HashAlgorithm) (data : ByteArray) : ByteArray :=
  match algorithm with
  | .sha256 => HaclStar.sha256 data
  | .sha384 => HaclStar.sha384 data
  | .sha512 => HaclStar.sha512 data

/-- RFC 5929 `tls-server-end-point` data for the exact leaf certificate DER. -/
def tlsServerEndPoint (certificate : Certificate) : ByteArray :=
  hash (signatureHashAlgorithm certificate.signatureAlgorithm)
    certificate.encoded

end ChannelBinding
end X509
end TLS13
