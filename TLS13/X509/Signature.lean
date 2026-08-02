module

public import HaclStar.Signature
public import TLS13.X509.RSA

public section

/-!
Signature verification over the public-key model parsed from X.509.

ECDSA signature framing and RSASSA-PSS AlgorithmIdentifier parameters are
validated in Lean. The elliptic-curve equations are delegated to HACL*;
RSA verification, whose inputs are entirely public, is implemented with Lean
`Nat` arithmetic in `TLS13.X509.RSA`.
-/

namespace TLS13
namespace X509
namespace Signature

inductive Scheme where
  | ecdsaP256Sha256
  | ed25519
  | rsaPKCS1v15Sha256
  | rsaPSSSha256 (saltLength : Nat)
  deriving Repr, BEq, DecidableEq

/-- TLS 1.3 signature schemes accepted for a server CertificateVerify.
PKCS#1 v1.5 is intentionally absent: TLS 1.3 permits it for certificate-chain
signatures, but not for CertificateVerify. -/
inductive CertificateVerifyScheme where
  | ecdsaSecp256r1Sha256
  | ed25519
  | rsaPssRsaeSha256
  | rsaPssPssSha256
  deriving Repr, BEq, DecidableEq

structure PSSParameters where
  saltLength : Nat
  deriving Repr, BEq, Inhabited

/-- P-256's prime subgroup order. -/
def p256Order : Nat :=
  0xffffffff00000000ffffffffffffffffbce6faada7179e84f3b9cac2fc632551

private def parsePositiveInteger
    (value : DER.TLV) (context : String) (maxOctets : Nat) :
    Except String Nat := do
  value.requireTag DER.Tag.integer context
  if value.contents.isEmpty then
    throw s!"{context} INTEGER is empty"
  if value.contents.size > maxOctets then
    throw s!"{context} INTEGER exceeds {maxOctets} octets"
  let first := value.contents.get! 0
  if first ≥ 0x80 then
    throw s!"{context} INTEGER is negative"
  if value.contents.size > 1 &&
      first == 0x00 && value.contents.get! 1 < 0x80 then
    throw s!"{context} INTEGER has redundant sign padding"
  let value :=
    value.contents.foldl
      (fun result octet => result * 256 + octet.toNat) 0
  if value == 0 then
    throw s!"{context} INTEGER must be positive"
  pure value

private def parseNonnegativeInteger
    (value : DER.TLV) (context : String) (maxOctets : Nat) :
    Except String Nat := do
  value.requireTag DER.Tag.integer context
  if value.contents.isEmpty then
    throw s!"{context} INTEGER is empty"
  if value.contents.size > maxOctets then
    throw s!"{context} INTEGER exceeds {maxOctets} octets"
  let first := value.contents.get! 0
  if first ≥ 0x80 then
    throw s!"{context} INTEGER is negative"
  if value.contents.size > 1 &&
      first == 0x00 && value.contents.get! 1 < 0x80 then
    throw s!"{context} INTEGER has redundant sign padding"
  pure (value.contents.foldl
    (fun result octet => result * 256 + octet.toNat) 0)

/-- Decode a DER ECDSA-Sig-Value and return fixed-width P-256 scalars. -/
def parseECDSAP256Signature (signature : ByteArray) :
    Except String (ByteArray × ByteArray) := do
  let sequence ← DER.decode signature
  sequence.requireTag DER.Tag.sequence "ECDSA-Sig-Value"
  let (rValue, reader) ← sequence.reader.readTLV
  let (sValue, reader) ← reader.readTLV
  reader.requireEnd "ECDSA-Sig-Value"
  let r ← parsePositiveInteger rValue "ECDSA r" 33
  let s ← parsePositiveInteger sValue "ECDSA s" 33
  if r ≥ p256Order then
    throw "ECDSA r is outside the P-256 scalar range"
  if s ≥ p256Order then
    throw "ECDSA s is outside the P-256 scalar range"
  pure (← RSA.i2osp r 32, ← RSA.i2osp s 32)

private def parseAlgorithmIdentifierTLV (value : DER.TLV) :
    Except String AlgorithmIdentifier := do
  value.requireTag DER.Tag.sequence "AlgorithmIdentifier"
  let (oidValue, reader) ← value.reader.readTLV
  let oid ← oidValue.asOID
  let (parameters, reader) ←
    if reader.atEnd then
      pure (none, reader)
    else
      let (parameter, reader) ← reader.readTLV
      pure (some parameter, reader)
  reader.requireEnd "AlgorithmIdentifier"
  pure { oid, parameters, encoded := value.encoded }

private def requireNull (value : DER.TLV) (context : String) :
    Except String Unit := do
  value.requireTag DER.Tag.null context
  unless value.contents.isEmpty do
    throw s!"{context} NULL must be empty"

private def requireSha256 (algorithm : AlgorithmIdentifier) :
    Except String Unit := do
  unless algorithm.oid == OID.sha256 do
    throw s!"unsupported PSS hash algorithm {algorithm.oid}"
  match algorithm.parameters with
  | none => pure ()
  | some parameters => requireNull parameters "SHA-256 parameters"

private def unwrapExplicit
    (value : DER.TLV) (number : Nat) (context : String) :
    Except String DER.TLV := do
  value.requireTag
    { tagClass := .contextSpecific, constructed := true, number } context
  let (inner, reader) ← value.reader.readTLV
  reader.requireEnd context
  pure inner

/-- Parse the RFC 4055 RSASSA-PSS parameters accepted by the SHA-256 verifier.
The hash and MGF fields must explicitly select SHA-256 because their ASN.1
defaults select SHA-1. Salt length defaults to 20. RFC 4055 specifically
requires validators to accept trailer field 1 both absent and explicitly
present. -/
def parsePSSSha256Parameters (algorithm : AlgorithmIdentifier) :
    Except String PSSParameters := do
  unless algorithm.oid == OID.rsassaPss do
    throw s!"expected id-RSASSA-PSS, got {algorithm.oid}"
  let some parameters := algorithm.parameters
    | throw "RSASSA-PSS signature parameters must be present"
  parameters.requireTag DER.Tag.sequence "RSASSA-PSS-params"
  let mut reader := parameters.reader
  let mut previousTag : Option Nat := none
  let mut sawHash := false
  let mut sawMask := false
  let mut saltLength := 20
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
    let inner ← unwrapExplicit field field.tag.number "RSASSA-PSS parameter"
    match field.tag.number with
    | 0 =>
      requireSha256 (← parseAlgorithmIdentifierTLV inner)
      sawHash := true
    | 1 =>
      let maskAlgorithm ← parseAlgorithmIdentifierTLV inner
      unless maskAlgorithm.oid == OID.mgf1 do
        throw s!"unsupported PSS mask generation algorithm {maskAlgorithm.oid}"
      let some maskHashValue := maskAlgorithm.parameters
        | throw "MGF1 parameters must contain a hash AlgorithmIdentifier"
      requireSha256 (← parseAlgorithmIdentifierTLV maskHashValue)
      sawMask := true
    | 2 =>
      let parsed ←
        parseNonnegativeInteger inner "RSASSA-PSS saltLength" 8
      if parsed == 20 then
        throw "RSASSA-PSS saltLength DEFAULT 20 must be omitted in DER"
      saltLength := parsed
    | 3 =>
      let trailer ←
        parseNonnegativeInteger inner "RSASSA-PSS trailerField" 8
      unless trailer == 1 do
        throw s!"unsupported RSASSA-PSS trailerField {trailer}"
    | _ => throw "unreachable RSASSA-PSS parameter"
    previousTag := some field.tag.number
    reader := next
  unless sawHash do
    throw "RSASSA-PSS default SHA-1 hash is unsupported"
  unless sawMask do
    throw "RSASSA-PSS default MGF1-SHA1 is unsupported"
  pure { saltLength }

private def parametersAbsent (algorithm : AlgorithmIdentifier) : Bool :=
  algorithm.parameters.isNone

private def rsaPkcs1ParametersValid (algorithm : AlgorithmIdentifier) : Bool :=
  match algorithm.parameters with
  | none => true
  | some parameters =>
    parameters.tag == DER.Tag.null && parameters.contents.isEmpty

/-- Check the RFC 4055 restrictions carried by a PSS-only RSA public key.
Absent SPKI parameters impose no restriction. Present SHA-256 parameters fix
the hash/MGF/trailer and establish a minimum salt length. -/
private def pssKeyAllows
    (spki : SubjectPublicKeyInfo) (signatureParameters : PSSParameters) : Bool :=
  if spki.algorithm.oid == OID.rsaEncryption then
    true
  else if spki.algorithm.oid == OID.rsassaPss then
    match spki.algorithm.parameters with
    | none => true
    | some _ =>
      match parsePSSSha256Parameters spki.algorithm with
      | .ok keyParameters =>
        signatureParameters.saltLength ≥ keyParameters.saltLength
      | .error _ => false
  else
    false

/-- Verify one supported signature scheme against a parsed public key. -/
def verify
    (scheme : Scheme) (publicKey : PublicKey)
    (message signature : ByteArray) : Bool :=
  match scheme, publicKey with
  | .ecdsaP256Sha256, .p256 point =>
    match parseECDSAP256Signature signature with
    | .ok (r, s) =>
      HaclStar.Signature.ecdsaP256Sha256 point message r s
    | .error _ => false
  | .ed25519, .ed25519 key =>
    HaclStar.Signature.ed25519 key message signature
  | .rsaPKCS1v15Sha256, .rsa key =>
    RSA.verify key .pkcs1v15Sha256 message signature
  | .rsaPSSSha256 saltLength, .rsa key =>
    RSA.verify key (.pssSha256 saltLength) message signature
  | _, _ => false

/-- Whether a leaf SPKI is permitted for the selected TLS 1.3
CertificateVerify scheme. RSA-PSS uses a 32-byte salt for SHA-256; RSAE and
PSS-OID schemes remain distinct as required by TLS 1.3. -/
def certificateVerifySchemeCompatible
    (scheme : CertificateVerifyScheme) (spki : SubjectPublicKeyInfo) : Bool :=
  match scheme with
  | .ecdsaSecp256r1Sha256 =>
    spki.algorithm.oid == OID.ecPublicKey &&
      (spki.key matches .p256 _)
  | .ed25519 =>
    spki.algorithm.oid == OID.ed25519 &&
      (spki.key matches .ed25519 _)
  | .rsaPssRsaeSha256 =>
    spki.algorithm.oid == OID.rsaEncryption &&
      (spki.key matches .rsa _)
  | .rsaPssPssSha256 =>
    spki.algorithm.oid == OID.rsassaPss &&
      (spki.key matches .rsa _) &&
      pssKeyAllows spki { saltLength := HaclStar.sha256DigestLen }

/-- RFC 8446 server CertificateVerify input:
64 spaces, the server context string, one zero separator, and the negotiated
transcript hash. This stack currently negotiates SHA-256 only. -/
def serverCertificateVerifyContent (transcriptHash : ByteArray) :
    Except String ByteArray := do
  unless transcriptHash.size == HaclStar.sha256DigestLen do
    throw s!"CertificateVerify transcript hash must contain exactly \
      {HaclStar.sha256DigestLen} bytes"
  let spaces := ByteArray.mk (Array.replicate 64 0x20)
  let context := "TLS 1.3, server CertificateVerify".toUTF8
  pure (((spaces ++ context).push 0x00) ++ transcriptHash)

/-- Verify a TLS 1.3 server CertificateVerify against the leaf SPKI and the
SHA-256 transcript hash through Certificate, inclusive. ECDSA and RSA hash
the constructed content with SHA-256; Ed25519 receives the whole content and
performs PureEdDSA hashing internally. -/
def verifyServerCertificateVerify
    (scheme : CertificateVerifyScheme) (spki : SubjectPublicKeyInfo)
    (transcriptHash signature : ByteArray) : Bool :=
  if !certificateVerifySchemeCompatible scheme spki then
    false
  else
    match serverCertificateVerifyContent transcriptHash with
    | .error _ => false
    | .ok content =>
      match scheme with
      | .ecdsaSecp256r1Sha256 =>
        verify .ecdsaP256Sha256 spki.key content signature
      | .ed25519 =>
        verify .ed25519 spki.key content signature
      | .rsaPssRsaeSha256
      | .rsaPssPssSha256 =>
        verify (.rsaPSSSha256 HaclStar.sha256DigestLen)
          spki.key content signature

/-- Dispatch an X.509 signature AlgorithmIdentifier. This checks the signature
algorithm parameters and the issuer SPKI algorithm restrictions in addition
to the cryptographic signature. -/
def verifyX509
    (algorithm : AlgorithmIdentifier) (spki : SubjectPublicKeyInfo)
    (message signature : ByteArray) : Bool :=
  if algorithm.oid == OID.ecdsaWithSha256 then
    spki.algorithm.oid == OID.ecPublicKey &&
      parametersAbsent algorithm &&
      verify .ecdsaP256Sha256 spki.key message signature
  else if algorithm.oid == OID.ed25519 then
    spki.algorithm.oid == OID.ed25519 &&
      parametersAbsent algorithm &&
      verify .ed25519 spki.key message signature
  else if algorithm.oid == OID.sha256WithRSAEncryption then
    spki.algorithm.oid == OID.rsaEncryption &&
      rsaPkcs1ParametersValid algorithm &&
      verify .rsaPKCS1v15Sha256 spki.key message signature
  else if algorithm.oid == OID.rsassaPss then
    match parsePSSSha256Parameters algorithm with
    | .ok parameters =>
      pssKeyAllows spki parameters &&
        verify (.rsaPSSSha256 parameters.saltLength)
          spki.key message signature
    | .error _ => false
  else
    false

end Signature
end X509
end TLS13
