module

public import TLS13.X509.DER
public import TLS13.X509.PEM
public import TLS13.X509.Time

public section

/-!
Schema-directed X.509 certificate parsing for the TLS verifier.

Every signed or identity-bearing structure retains its exact input encoding:
`Certificate.encoded`, `TBSCertificate.encoded`, and `Name.encoded` are slices
of the original DER, never reconstructions.
-/

namespace TLS13
namespace X509

namespace OID

def commonName : OID := { arcs := #[2, 5, 4, 3] }
def subjectKeyIdentifier : OID := { arcs := #[2, 5, 29, 14] }
def keyUsage : OID := { arcs := #[2, 5, 29, 15] }
def subjectAltName : OID := { arcs := #[2, 5, 29, 17] }
def basicConstraints : OID := { arcs := #[2, 5, 29, 19] }
def authorityKeyIdentifier : OID := { arcs := #[2, 5, 29, 35] }

def rsaEncryption : OID := { arcs := #[1, 2, 840, 113549, 1, 1, 1] }
def mgf1 : OID := { arcs := #[1, 2, 840, 113549, 1, 1, 8] }
def rsassaPss : OID := { arcs := #[1, 2, 840, 113549, 1, 1, 10] }
def sha256WithRSAEncryption : OID := { arcs := #[1, 2, 840, 113549, 1, 1, 11] }
def sha256 : OID := { arcs := #[2, 16, 840, 1, 101, 3, 4, 2, 1] }
def ecPublicKey : OID := { arcs := #[1, 2, 840, 10045, 2, 1] }
def prime256v1 : OID := { arcs := #[1, 2, 840, 10045, 3, 1, 7] }
def ecdsaWithSha256 : OID := { arcs := #[1, 2, 840, 10045, 4, 3, 2] }
def ed25519 : OID := { arcs := #[1, 3, 101, 112] }

end OID

/-- X.509's zero-based encoded versions, presented by their conventional
names. -/
inductive Version where
  | v1
  | v2
  | v3
  deriving Repr, BEq, DecidableEq, Inhabited

/-- An AlgorithmIdentifier with its exact SEQUENCE retained. -/
structure AlgorithmIdentifier where
  oid : OID
  parameters : Option DER.TLV
  encoded : ByteArray
  deriving BEq, Inhabited

/-- One decoded ASN.1 BIT STRING. -/
structure BitString where
  bytes : ByteArray
  unusedBits : Nat
  deriving BEq, Inhabited

/-- One AttributeTypeAndValue from an X.500 Name. `value` retains the exact
typed DER value; `text` is populated for supported string encodings. -/
structure NameAttribute where
  oid : OID
  value : DER.TLV
  text : Option String
  deriving BEq, Inhabited

structure RelativeDistinguishedName where
  attributes : Array NameAttribute
  deriving BEq, Inhabited

/-- Parsed Name plus the load-bearing byte-exact Name SEQUENCE. -/
structure Name where
  encoded : ByteArray
  rdns : Array RelativeDistinguishedName
  commonNames : Array String
  deriving BEq, Inhabited

structure Validity where
  notBefore : Timestamp
  notAfter : Timestamp
  deriving Repr, BEq, Inhabited

structure RSAPublicKey where
  modulus : Nat
  exponent : Nat
  deriving Repr, BEq, Inhabited

/-- Public-key algorithms supported by the TLS certificate verifier. -/
inductive PublicKey where
  | rsa (key : RSAPublicKey)
  | p256 (point : ByteArray)
  | ed25519 (key : ByteArray)
  deriving BEq, Inhabited

structure SubjectPublicKeyInfo where
  encoded : ByteArray
  algorithm : AlgorithmIdentifier
  key : PublicKey
  deriving BEq, Inhabited

structure SubjectAltName where
  dnsNames : Array String
  ipAddresses : Array ByteArray
  deriving BEq, Inhabited

structure BasicConstraints where
  ca : Bool
  pathLenConstraint : Option Nat
  deriving Repr, BEq, Inhabited

structure KeyUsage where
  digitalSignature : Bool := false
  contentCommitment : Bool := false
  keyEncipherment : Bool := false
  dataEncipherment : Bool := false
  keyAgreement : Bool := false
  keyCertSign : Bool := false
  cRLSign : Bool := false
  encipherOnly : Bool := false
  decipherOnly : Bool := false
  deriving Repr, BEq, Inhabited

/-- A parsed extension with its critical bit and exact Extension SEQUENCE. -/
structure ParsedExtension (α : Type) where
  critical : Bool
  value : α
  encoded : ByteArray
  deriving BEq, Inhabited

/-- An extension not interpreted by M2. M5 can reject an unhandled critical
extension during path validation. -/
structure RawExtension where
  oid : OID
  critical : Bool
  valueDER : ByteArray
  encoded : ByteArray
  deriving BEq, Inhabited

structure Extensions where
  subjectAltName : Option (ParsedExtension SubjectAltName) := none
  basicConstraints : Option (ParsedExtension BasicConstraints) := none
  keyUsage : Option (ParsedExtension KeyUsage) := none
  unhandled : Array RawExtension := #[]
  deriving BEq, Inhabited

structure TBSCertificate where
  /-- Exact DER TLV signed by the certificate signature. -/
  encoded : ByteArray
  version : Version
  serialNumber : Nat
  signatureAlgorithm : AlgorithmIdentifier
  issuer : Name
  validity : Validity
  subject : Name
  subjectPublicKeyInfo : SubjectPublicKeyInfo
  issuerUniqueID : Option BitString
  subjectUniqueID : Option BitString
  extensions : Extensions
  deriving BEq, Inhabited

structure Certificate where
  encoded : ByteArray
  tbsCertificate : TBSCertificate
  signatureAlgorithm : AlgorithmIdentifier
  signature : ByteArray
  deriving BEq, Inhabited

namespace Certificate

/-- Generous RSA input bound: up to an 8192-bit modulus plus a sign octet. -/
def maxRsaModulusOctets : Nat := 1025

/-- Certificates in practice contain a few dozen extensions. This generous
bound also keeps duplicate-OID detection from becoming attacker-controlled
quadratic work on a maximum-sized TLS Certificate message. -/
def maxExtensions : Nat := 256

private def contextTag (number : Nat) (constructed : Bool) : DER.Tag :=
  { tagClass := .contextSpecific, constructed, number }

private def parseBoolean (value : DER.TLV) (context : String) : Except String Bool := do
  value.requireTag DER.Tag.boolean context
  if value.contents.size != 1 then
    throw s!"{context} BOOLEAN must contain exactly one octet"
  match value.contents.get! 0 with
  | 0x00 => pure false
  | 0xff => pure true
  | _ => throw s!"{context} BOOLEAN is not canonical DER"

private def checkIntegerEncoding (value : DER.TLV) (context : String) :
    Except String Unit := do
  value.requireTag DER.Tag.integer context
  if value.contents.isEmpty then
    throw s!"{context} INTEGER is empty"
  if value.contents.size > 1 then
    let first := value.contents.get! 0
    let second := value.contents.get! 1
    if first == 0x00 && second < 0x80 then
      throw s!"{context} INTEGER has redundant positive sign padding"
    if first == 0xff && second ≥ 0x80 then
      throw s!"{context} INTEGER has redundant negative sign padding"

private def parseNonnegativeInteger (value : DER.TLV) (context : String)
    (maxOctets : Nat) : Except String Nat := do
  checkIntegerEncoding value context
  if value.contents.size > maxOctets then
    throw s!"{context} INTEGER exceeds {maxOctets} octets"
  if value.contents.get! 0 ≥ 0x80 then
    throw s!"{context} INTEGER is negative"
  let mut result := 0
  for octet in value.contents do
    result := (result <<< 8) ||| octet.toNat
  pure result

private def parseBitStringContents (contents : ByteArray) (context : String) :
    Except String BitString := do
  if contents.isEmpty then
    throw s!"{context} BIT STRING has no unused-bit count"
  let unusedBits := (contents.get! 0).toNat
  if unusedBits > 7 then
    throw s!"{context} BIT STRING has invalid unused-bit count {unusedBits}"
  let bytes := contents.extract 1 contents.size
  if bytes.isEmpty then
    if unusedBits != 0 then
      throw s!"{context} empty BIT STRING has nonzero unused-bit count"
  else if unusedBits > 0 then
    let mask := UInt8.ofNat ((1 <<< unusedBits) - 1)
    if (bytes.get! (bytes.size - 1) &&& mask) != 0 then
      throw s!"{context} BIT STRING has nonzero padding bits"
  pure { bytes, unusedBits }

private def parseBitString (value : DER.TLV) (context : String) :
    Except String BitString := do
  value.requireTag DER.Tag.bitString context
  parseBitStringContents value.contents context

private def requireOctetAligned (bits : BitString) (context : String) :
    Except String ByteArray := do
  if bits.unusedBits != 0 then
    throw s!"{context} BIT STRING is not octet-aligned"
  pure bits.bytes

private def parseNull (value : DER.TLV) (context : String) : Except String Unit := do
  value.requireTag DER.Tag.null context
  unless value.contents.isEmpty do
    throw s!"{context} NULL must have empty contents"

private def decodeAscii (bytes : ByteArray) (context : String) : Except String String := do
  for octet in bytes do
    if octet > 0x7f then
      throw s!"{context} is not IA5/ASCII"
  pure (String.fromUTF8! bytes)

private def isPrintableStringOctet (octet : UInt8) : Bool :=
  (octet ≥ 0x41 && octet ≤ 0x5a) ||
  (octet ≥ 0x61 && octet ≤ 0x7a) ||
  (octet ≥ 0x30 && octet ≤ 0x39) ||
  octet == 0x20 || octet == 0x27 || octet == 0x28 || octet == 0x29 ||
  octet == 0x2b || octet == 0x2c || octet == 0x2d || octet == 0x2e ||
  octet == 0x2f || octet == 0x3a || octet == 0x3d || octet == 0x3f

private def decodePrintableString (bytes : ByteArray) : Except String String := do
  for octet in bytes do
    unless isPrintableStringOctet octet do
      throw "Name PrintableString contains a forbidden character"
  pure (String.fromUTF8! bytes)

private def validUnicodeScalar (codepoint : Nat) : Bool :=
  codepoint ≤ 0x10ffff && !(codepoint ≥ 0xd800 && codepoint ≤ 0xdfff)

private def decodeBmpString (bytes : ByteArray) : Except String String := do
  if bytes.size % 2 != 0 then
    throw "Name BMPString has odd length"
  let mut result := ""
  for index in [0:bytes.size / 2] do
    let offset := index * 2
    let codepoint := (bytes.get! offset).toNat <<< 8 ||| (bytes.get! (offset + 1)).toNat
    unless validUnicodeScalar codepoint do
      throw "Name BMPString contains an invalid Unicode scalar"
    result := result.push (Char.ofNat codepoint)
  pure result

private def decodeUniversalString (bytes : ByteArray) : Except String String := do
  if bytes.size % 4 != 0 then
    throw "Name UniversalString length is not a multiple of four"
  let mut result := ""
  for index in [0:bytes.size / 4] do
    let offset := index * 4
    let codepoint :=
      (bytes.get! offset).toNat <<< 24 |||
      (bytes.get! (offset + 1)).toNat <<< 16 |||
      (bytes.get! (offset + 2)).toNat <<< 8 |||
      (bytes.get! (offset + 3)).toNat
    unless validUnicodeScalar codepoint do
      throw "Name UniversalString contains an invalid Unicode scalar"
    result := result.push (Char.ofNat codepoint)
  pure result

private def decodeNameText (value : DER.TLV) : Except String (Option String) := do
  if value.tag.tagClass != .universal || value.tag.constructed then
    return none
  match value.tag.number with
  | 12 =>
    let some text := String.fromUTF8? value.contents
      | throw "Name UTF8String contains malformed UTF-8"
    pure (some text)
  | 19 => pure (some (← decodePrintableString value.contents))
  | 22 => pure (some (← decodeAscii value.contents "Name IA5String"))
  | 28 => pure (some (← decodeUniversalString value.contents))
  | 30 => pure (some (← decodeBmpString value.contents))
  | _ => pure none

private def byteArrayLess (left right : ByteArray) : Bool := Id.run do
  let common := min left.size right.size
  for index in [0:common] do
    let a := left.get! index
    let b := right.get! index
    if a < b then return true
    if a > b then return false
  return left.size < right.size

private def parseAlgorithmIdentifier (value : DER.TLV) :
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

private def validateSignatureAlgorithm (algorithm : AlgorithmIdentifier) :
    Except String Unit := do
  if algorithm.oid == OID.ecdsaWithSha256 then
    if algorithm.parameters.isSome then
      throw "ecdsa-with-SHA256 AlgorithmIdentifier parameters must be absent"
  else if algorithm.oid == OID.ed25519 then
    if algorithm.parameters.isSome then
      throw "Ed25519 signature AlgorithmIdentifier parameters must be absent"
  else if algorithm.oid == OID.sha256WithRSAEncryption then
    match algorithm.parameters with
    | some parameters =>
      parseNull parameters "sha256WithRSAEncryption parameters"
    | none => pure ()

private def parseNameAttribute (value : DER.TLV) : Except String NameAttribute := do
  value.requireTag DER.Tag.sequence "AttributeTypeAndValue"
  let (oidValue, reader) ← value.reader.readTLV
  let oid ← oidValue.asOID
  let (attributeValue, reader) ← reader.readTLV
  reader.requireEnd "AttributeTypeAndValue"
  let text ← decodeNameText attributeValue
  pure { oid, value := attributeValue, text }

private def parseName (value : DER.TLV) : Except String Name := do
  value.requireTag DER.Tag.sequence "Name"
  let mut reader := value.reader
  let mut rdns := #[]
  let mut commonNames := #[]
  while !reader.atEnd do
    let (rdnValue, next) ← reader.readTLV
    rdnValue.requireTag DER.Tag.set "RelativeDistinguishedName"
    let mut attributeReader := rdnValue.reader
    if attributeReader.atEnd then
      throw "RelativeDistinguishedName SET must not be empty"
    let mut attributes := #[]
    let mut previousEncoding : Option ByteArray := none
    while !attributeReader.atEnd do
      let (attributeValue, nextAttribute) ← attributeReader.readTLV
      match previousEncoding with
      | some previous =>
        if byteArrayLess attributeValue.encoded previous then
          throw "RelativeDistinguishedName SET is not in DER lexicographic order"
      | none => pure ()
      let parsedAttribute ← parseNameAttribute attributeValue
      if parsedAttribute.oid == OID.commonName then
        let tag := parsedAttribute.value.tag
        unless tag.tagClass == .universal && !tag.constructed &&
            (tag.number == 12 || tag.number == 19 || tag.number == 20 ||
              tag.number == 28 || tag.number == 30) do
          throw "commonName must use a DirectoryString encoding"
        let some text := parsedAttribute.text
          | throw "commonName uses an unsupported DirectoryString encoding"
        if text.isEmpty || text.length > 64 then
          throw "commonName must contain between 1 and 64 characters"
        commonNames := commonNames.push text
      attributes := attributes.push parsedAttribute
      previousEncoding := some attributeValue.encoded
      attributeReader := nextAttribute
    rdns := rdns.push { attributes }
    reader := next
  pure { encoded := value.encoded, rdns, commonNames }

private def parseValidity (value : DER.TLV) : Except String Validity := do
  value.requireTag DER.Tag.sequence "Validity"
  let (notBeforeValue, reader) ← value.reader.readTLV
  let (notAfterValue, reader) ← reader.readTLV
  reader.requireEnd "Validity"
  pure {
    notBefore := ← Time.parse notBeforeValue
    notAfter := ← Time.parse notAfterValue
  }

private def parseRsaPublicKey (bytes : ByteArray) : Except String RSAPublicKey := do
  let value ← DER.decode bytes
  value.requireTag DER.Tag.sequence "RSAPublicKey"
  let (modulusValue, reader) ← value.reader.readTLV
  let (exponentValue, reader) ← reader.readTLV
  reader.requireEnd "RSAPublicKey"
  let modulus ←
    parseNonnegativeInteger modulusValue "RSA modulus" maxRsaModulusOctets
  let exponent ← parseNonnegativeInteger exponentValue "RSA public exponent" 8
  if modulus == 0 then
    throw "RSA modulus must be positive"
  if exponent < 3 || exponent % 2 == 0 then
    throw "RSA public exponent must be an odd integer at least 3"
  pure { modulus, exponent }

private def parseSubjectPublicKeyInfo (value : DER.TLV) :
    Except String SubjectPublicKeyInfo := do
  value.requireTag DER.Tag.sequence "SubjectPublicKeyInfo"
  let (algorithmValue, reader) ← value.reader.readTLV
  let algorithm ← parseAlgorithmIdentifier algorithmValue
  let (keyValue, reader) ← reader.readTLV
  reader.requireEnd "SubjectPublicKeyInfo"
  let keyBits ← parseBitString keyValue "subjectPublicKey"
  let keyBytes ← requireOctetAligned keyBits "subjectPublicKey"
  let key ←
    if algorithm.oid == OID.rsaEncryption then
      let some parameters := algorithm.parameters
        | throw "rsaEncryption parameters must be NULL"
      parseNull parameters "rsaEncryption parameters"
      pure (.rsa (← parseRsaPublicKey keyBytes))
    else if algorithm.oid == OID.rsassaPss then
      match algorithm.parameters with
      | some parameters =>
        parameters.requireTag DER.Tag.sequence "RSASSA-PSS public-key parameters"
      | none => pure ()
      pure (.rsa (← parseRsaPublicKey keyBytes))
    else if algorithm.oid == OID.ecPublicKey then
      let some parameters := algorithm.parameters
        | throw "id-ecPublicKey parameters must name a curve"
      let curve ← parameters.asOID
      unless curve == OID.prime256v1 do
        throw s!"unsupported EC named curve {curve}"
      unless keyBytes.size == 65 && keyBytes.get! 0 == 0x04 do
        throw "P-256 public key must be a 65-byte uncompressed point"
      pure (.p256 keyBytes)
    else if algorithm.oid == OID.ed25519 then
      if algorithm.parameters.isSome then
        throw "Ed25519 AlgorithmIdentifier parameters must be absent"
      unless keyBytes.size == 32 do
        throw s!"Ed25519 public key must contain exactly 32 bytes (got {keyBytes.size})"
      pure (.ed25519 keyBytes)
    else
      throw s!"unsupported SubjectPublicKeyInfo algorithm {algorithm.oid}"
  pure { encoded := value.encoded, algorithm, key }

private def parseSubjectAltName (extension : RawExtension) :
    Except String (ParsedExtension SubjectAltName) := do
  let value ← DER.decode extension.valueDER
  value.requireTag DER.Tag.sequence "subjectAltName"
  let mut reader := value.reader
  if reader.atEnd then
    throw "subjectAltName GeneralNames must not be empty"
  let mut dnsNames := #[]
  let mut ipAddresses := #[]
  while !reader.atEnd do
    let (generalName, next) ← reader.readTLV
    unless generalName.tag.tagClass == .contextSpecific && generalName.tag.number ≤ 8 do
      throw "subjectAltName contains an invalid GeneralName tag"
    let shouldBeConstructed :=
      generalName.tag.number == 0 || generalName.tag.number == 3 ||
        generalName.tag.number == 4 || generalName.tag.number == 5
    unless generalName.tag.constructed == shouldBeConstructed do
      throw "subjectAltName GeneralName has the wrong primitive/constructed form"
    if generalName.tag.constructed then
      -- Even choices that are not interpreted still have to contain DER, not
      -- an opaque BER island hidden inside the surrounding certificate.
      let _ ← DER.decodeAll generalName.contents
    if generalName.tag.number == 2 then
      if generalName.contents.isEmpty then
        throw "subjectAltName dNSName must not be empty"
      let dnsName ← decodeAscii generalName.contents "subjectAltName dNSName"
      if generalName.contents.foldl (fun found octet => found || octet == 0) false then
        throw "subjectAltName dNSName contains NUL"
      dnsNames := dnsNames.push dnsName
    else if generalName.tag.number == 7 then
      unless generalName.contents.size == 4 || generalName.contents.size == 16 do
        throw "subjectAltName iPAddress must contain 4 or 16 bytes"
      ipAddresses := ipAddresses.push generalName.contents
    else if generalName.tag.number == 1 || generalName.tag.number == 6 then
      if generalName.contents.isEmpty then
        throw "subjectAltName IA5String GeneralName must not be empty"
      let _ ← decodeAscii generalName.contents "subjectAltName IA5String GeneralName"
    else if generalName.tag.number == 8 then
      let _ ← OID.decodeContents generalName.contents
    reader := next
  pure {
    critical := extension.critical
    value := { dnsNames, ipAddresses }
    encoded := extension.encoded
  }

private def parseBasicConstraints (extension : RawExtension) :
    Except String (ParsedExtension BasicConstraints) := do
  let value ← DER.decode extension.valueDER
  value.requireTag DER.Tag.sequence "BasicConstraints"
  let mut reader := value.reader
  let mut ca := false
  if !reader.atEnd then
    let (first, next) ← reader.readTLV
    if first.tag == DER.Tag.boolean then
      ca ← parseBoolean first "BasicConstraints.cA"
      if !ca then
        throw "BasicConstraints.cA DEFAULT FALSE must be omitted in DER"
      reader := next
  let mut pathLenConstraint : Option Nat := none
  if !reader.atEnd then
    let (pathLen, next) ← reader.readTLV
    pathLenConstraint := some
      (← parseNonnegativeInteger pathLen "BasicConstraints.pathLenConstraint" 8)
    reader := next
  reader.requireEnd "BasicConstraints"
  if pathLenConstraint.isSome && !ca then
    throw "BasicConstraints.pathLenConstraint requires cA TRUE"
  pure {
    critical := extension.critical
    value := { ca, pathLenConstraint }
    encoded := extension.encoded
  }

private def keyUsageBit (bytes : ByteArray) (bit : Nat) : Bool :=
  let byteIndex := bit / 8
  byteIndex < bytes.size &&
    (bytes.get! byteIndex &&& (0x80 >>> UInt8.ofNat (bit % 8))) != 0

private def parseKeyUsage (extension : RawExtension) :
    Except String (ParsedExtension KeyUsage) := do
  let value ← DER.decode extension.valueDER
  let bits ← parseBitString value "KeyUsage"
  if bits.bytes.isEmpty then
    throw "KeyUsage must assert at least one bit"
  let lastOctet := bits.bytes.get! (bits.bytes.size - 1)
  -- DER removes every trailing zero from a named-bit list. The lowest
  -- significant bit in the final octet must therefore be asserted; checking
  -- only for an all-zero final octet would still accept redundant zero bits.
  let finalBitMask := UInt8.ofNat (1 <<< bits.unusedBits)
  if (lastOctet &&& finalBitMask) == 0 then
    throw "KeyUsage NamedBitList has non-minimal trailing zero bits"
  let significantBits := bits.bytes.size * 8 - bits.unusedBits
  if significantBits > 9 then
    throw "KeyUsage asserts an undefined bit"
  let usage : KeyUsage := {
    digitalSignature := keyUsageBit bits.bytes 0
    contentCommitment := keyUsageBit bits.bytes 1
    keyEncipherment := keyUsageBit bits.bytes 2
    dataEncipherment := keyUsageBit bits.bytes 3
    keyAgreement := keyUsageBit bits.bytes 4
    keyCertSign := keyUsageBit bits.bytes 5
    cRLSign := keyUsageBit bits.bytes 6
    encipherOnly := keyUsageBit bits.bytes 7
    decipherOnly := keyUsageBit bits.bytes 8
  }
  if (usage.encipherOnly || usage.decipherOnly) && !usage.keyAgreement then
    throw "KeyUsage encipherOnly/decipherOnly requires keyAgreement"
  pure {
    critical := extension.critical
    value := usage
    encoded := extension.encoded
  }

private def parseRawExtension (value : DER.TLV) : Except String RawExtension := do
  value.requireTag DER.Tag.sequence "Extension"
  let (oidValue, reader) ← value.reader.readTLV
  let oid ← oidValue.asOID
  let mut reader := reader
  let mut critical := false
  if !reader.atEnd then
    let (candidate, next) ← reader.readTLV
    if candidate.tag == DER.Tag.boolean then
      critical ← parseBoolean candidate "Extension.critical"
      if !critical then
        throw "Extension.critical DEFAULT FALSE must be omitted in DER"
      reader := next
  let (extensionValue, finalReader) ← reader.readTLV
  extensionValue.requireTag DER.Tag.octetString "Extension.extnValue"
  finalReader.requireEnd "Extension"
  pure {
    oid
    critical
    valueDER := extensionValue.contents
    encoded := value.encoded
  }

private def containsOID (extensions : Array OID) (oid : OID) : Bool :=
  extensions.any (· == oid)

private def parseExtensions (value : DER.TLV) : Except String Extensions := do
  value.requireTag DER.Tag.sequence "Extensions"
  let mut reader := value.reader
  if reader.atEnd then
    throw "Extensions SEQUENCE must not be empty"
  let mut seen := #[]
  let mut result : Extensions := {}
  while !reader.atEnd do
    if seen.size ≥ maxExtensions then
      throw s!"certificate contains more than {maxExtensions} extensions"
    let (extensionValue, next) ← reader.readTLV
    let extension ← parseRawExtension extensionValue
    if containsOID seen extension.oid then
      throw s!"duplicate X.509 extension {extension.oid}"
    seen := seen.push extension.oid
    if extension.oid == OID.subjectAltName then
      result := { result with subjectAltName := some (← parseSubjectAltName extension) }
    else if extension.oid == OID.basicConstraints then
      result := { result with basicConstraints := some (← parseBasicConstraints extension) }
    else if extension.oid == OID.keyUsage then
      result := { result with keyUsage := some (← parseKeyUsage extension) }
    else
      result := { result with unhandled := result.unhandled.push extension }
    reader := next
  pure result

private def parseVersion (value : DER.TLV) : Except String Version := do
  value.requireTag (contextTag 0 true) "TBSCertificate.version"
  let (integer, reader) ← value.reader.readTLV
  reader.requireEnd "TBSCertificate.version"
  let encoded ← parseNonnegativeInteger integer "TBSCertificate.version" 1
  match encoded with
  | 0 => throw "explicit v1 DEFAULT version must be omitted in DER"
  | 1 => pure .v2
  | 2 => pure .v3
  | _ => throw s!"unsupported X.509 version value {encoded}"

private def parseUniqueID (value : DER.TLV) (number : Nat) (context : String) :
    Except String BitString := do
  value.requireTag (contextTag number false) context
  parseBitStringContents value.contents context

private def parseTBSCertificate (value : DER.TLV) : Except String TBSCertificate := do
  value.requireTag DER.Tag.sequence "TBSCertificate"
  let (first, afterFirst) ← value.reader.readTLV
  let mut reader := afterFirst
  let mut current := first
  let version ←
    if first.tag == contextTag 0 true then
      let version ← parseVersion first
      let (serial, next) ← reader.readTLV
      current := serial
      reader := next
      pure version
    else
      pure .v1
  let serialNumber ←
    parseNonnegativeInteger current "CertificateSerialNumber" 20
  if serialNumber == 0 then
    throw "CertificateSerialNumber must be positive"

  let (signatureValue, next) ← reader.readTLV
  let signatureAlgorithm ← parseAlgorithmIdentifier signatureValue
  reader := next
  let (issuerValue, next) ← reader.readTLV
  let issuer ← parseName issuerValue
  if issuer.rdns.isEmpty then
    throw "certificate issuer Name must not be empty"
  reader := next
  let (validityValue, next) ← reader.readTLV
  let validity ← parseValidity validityValue
  reader := next
  let (subjectValue, next) ← reader.readTLV
  let subject ← parseName subjectValue
  reader := next
  let (spkiValue, next) ← reader.readTLV
  let subjectPublicKeyInfo ← parseSubjectPublicKeyInfo spkiValue
  reader := next

  let mut issuerUniqueID : Option BitString := none
  let mut subjectUniqueID : Option BitString := none
  let mut extensions : Extensions := {}
  let mut lastOptionalTag := 0
  while !reader.atEnd do
    let (optional, next) ← reader.readTLV
    unless optional.tag.tagClass == .contextSpecific &&
        optional.tag.number ≥ 1 && optional.tag.number ≤ 3 do
      throw "TBSCertificate contains an unexpected trailing field"
    if optional.tag.number ≤ lastOptionalTag then
      throw "TBSCertificate optional fields are duplicated or out of order"
    lastOptionalTag := optional.tag.number
    match optional.tag.number with
    | 1 =>
      if version == .v1 then
        throw "issuerUniqueID is not permitted in an X.509 v1 certificate"
      issuerUniqueID := some (← parseUniqueID optional 1 "issuerUniqueID")
    | 2 =>
      if version == .v1 then
        throw "subjectUniqueID is not permitted in an X.509 v1 certificate"
      subjectUniqueID := some (← parseUniqueID optional 2 "subjectUniqueID")
    | 3 =>
      unless version == .v3 do
        throw "extensions require an X.509 v3 certificate"
      optional.requireTag (contextTag 3 true) "TBSCertificate.extensions"
      let (extensionSequence, explicitReader) ← optional.reader.readTLV
      explicitReader.requireEnd "TBSCertificate.extensions"
      extensions ← parseExtensions extensionSequence
    | _ => throw "unreachable TBSCertificate optional field"
    reader := next

  if subject.rdns.isEmpty then
    match extensions.subjectAltName with
    | some san =>
      unless san.critical do
        throw "an empty subject Name requires a critical subjectAltName"
    | none => throw "an empty subject Name requires subjectAltName"

  pure {
    encoded := value.encoded
    version
    serialNumber
    signatureAlgorithm
    issuer
    validity
    subject
    subjectPublicKeyInfo
    issuerUniqueID
    subjectUniqueID
    extensions
  }

/-- Decode exactly one DER Certificate. -/
def decode (bytes : ByteArray) : Except String Certificate := do
  let certificateValue ← DER.decode bytes
  certificateValue.requireTag DER.Tag.sequence "Certificate"
  let (tbsValue, reader) ← certificateValue.reader.readTLV
  let tbsCertificate ← parseTBSCertificate tbsValue
  let (algorithmValue, reader) ← reader.readTLV
  let signatureAlgorithm ← parseAlgorithmIdentifier algorithmValue
  let (signatureValue, reader) ← reader.readTLV
  reader.requireEnd "Certificate"
  unless signatureAlgorithm.encoded == tbsCertificate.signatureAlgorithm.encoded do
    throw "Certificate signatureAlgorithm does not match TBSCertificate.signature"
  validateSignatureAlgorithm signatureAlgorithm
  let signatureBits ← parseBitString signatureValue "Certificate.signatureValue"
  let signature ← requireOctetAligned signatureBits "Certificate.signatureValue"
  if signature.isEmpty then
    throw "Certificate.signatureValue must not be empty"
  pure {
    encoded := certificateValue.encoded
    tbsCertificate
    signatureAlgorithm
    signature
  }

/-- Decode every exact `CERTIFICATE` block in a PEM bundle. -/
def decodePEM (text : String) : Except String (Array Certificate) := do
  let certificates ← PEM.decodeCertificates text
  certificates.mapM decode

end Certificate
end X509
end TLS13
