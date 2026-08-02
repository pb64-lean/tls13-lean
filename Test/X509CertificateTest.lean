module

public import TLS13.X509

public section

/-!
OpenSSL fixture KATs and malformed X.509 profile tests.
-/

open TLS13.X509

private def hexDigitValue? (char : Char) : Option UInt8 :=
  if '0' ≤ char ∧ char ≤ '9' then some (UInt8.ofNat (char.toNat - '0'.toNat))
  else if 'a' ≤ char ∧ char ≤ 'f' then some (UInt8.ofNat (char.toNat - 'a'.toNat + 10))
  else if 'A' ≤ char ∧ char ≤ 'F' then some (UInt8.ofNat (char.toNat - 'A'.toNat + 10))
  else none

private def decodeHex : List Char → ByteArray → Option ByteArray
  | [], out => some out
  | [_], _ => none
  | high :: low :: rest, out =>
    match hexDigitValue? high, hexDigitValue? low with
    | some high, some low => decodeHex rest (out.push (high * 16 + low))
    | _, _ => none

private def h (hex : String) : ByteArray :=
  match decodeHex hex.toList ByteArray.empty with
  | some bytes => bytes
  | none => panic! s!"malformed test hex: {hex}"

private def expectOk (label : String) (result : Except String α) : IO α :=
  match result with
  | .ok value => pure value
  | .error error => throw (IO.userError s!"{label}: unexpected error: {error}")

private def expectError (label : String) (result : Except String α) : IO Unit :=
  match result with
  | .ok _ => throw (IO.userError s!"{label}: malformed input was accepted")
  | .error _ => pure ()

private def check (label : String) (condition : Bool) : IO Unit := do
  unless condition do
    throw (IO.userError s!"{label}: assertion failed")

private def checkBytes (label : String) (got want : ByteArray) : IO Unit := do
  unless got == want do
    throw (IO.userError s!"{label}: byte mismatch")

private def natOfBytes (bytes : ByteArray) : Nat :=
  bytes.foldl (fun value octet => (value <<< 8) ||| octet.toNat) 0

private def makeTimeDER (tag : UInt8) (text : String) : ByteArray :=
  let contents := text.toUTF8
  (ByteArray.mk #[tag, UInt8.ofNat contents.size]) ++ contents

private def parseTime (tag : UInt8) (text : String) : Except String Timestamp := do
  Time.parse (← DER.decode (makeTimeDER tag text))

private def findBytes? (haystack needle : ByteArray) : Option Nat := Id.run do
  if needle.isEmpty || needle.size > haystack.size then
    return none
  for start in [0:haystack.size - needle.size + 1] do
    let mut equal := true
    for offset in [0:needle.size] do
      if haystack.get! (start + offset) != needle.get! offset then
        equal := false
    if equal then
      return some start
  none

private def setAtFound (bytes needle : ByteArray) (relative : Nat) (octet : UInt8) :
    Option ByteArray := do
  let start ← findBytes? bytes needle
  if relative ≥ needle.size then none else some (bytes.set! (start + relative) octet)

private def readFixtureDER (name : String) : IO ByteArray := do
  let pem ← IO.FS.readFile s!"Test/Fixtures/X509/{name}.pem"
  let ders ← expectOk s!"decode {name} PEM" (PEM.decodeCertificates pem)
  if ders.size != 1 then
    throw (IO.userError s!"{name}: expected one PEM certificate")
  pure ders[0]!

private def readFixture (name : String) : IO (ByteArray × Certificate) := do
  let der ← readFixtureDER name
  pure (der, ← expectOk s!"parse {name}" (Certificate.decode der))

private def checkCommon (label : String) (der : ByteArray) (certificate : Certificate)
    (serial : Nat) (commonName : String) (signatureOID : OID) : IO Unit := do
  let tbs := certificate.tbsCertificate
  check (label ++ " exact certificate") (certificate.encoded == der)
  check (label ++ " v3") (tbs.version == .v3)
  check (label ++ " serial") (tbs.serialNumber == serial)
  check (label ++ " issuer/subject exact DER") (tbs.issuer.encoded == tbs.subject.encoded)
  check (label ++ " issuer CN") (tbs.issuer.commonNames == #[commonName])
  check (label ++ " subject CN") (tbs.subject.commonNames == #[commonName])
  check (label ++ " notBefore epoch")
    (tbs.validity.notBefore.unixSeconds == 1704067200)
  check (label ++ " notAfter epoch")
    (tbs.validity.notAfter.unixSeconds == 2682374400)
  check (label ++ " UTCTime calendar")
    (tbs.validity.notBefore.year == 2024 && tbs.validity.notBefore.month == 1 &&
      tbs.validity.notBefore.day == 1)
  check (label ++ " GeneralizedTime calendar")
    (tbs.validity.notAfter.year == 2055 && tbs.validity.notAfter.month == 1 &&
      tbs.validity.notAfter.day == 1)
  check (label ++ " TBS signature OID") (tbs.signatureAlgorithm.oid == signatureOID)
  check (label ++ " outer signature OID") (certificate.signatureAlgorithm.oid == signatureOID)
  check (label ++ " signature algorithms exact")
    (tbs.signatureAlgorithm.encoded == certificate.signatureAlgorithm.encoded)
  check (label ++ " signature nonempty") (!certificate.signature.isEmpty)
  check (label ++ " unknown extensions retained")
    (tbs.extensions.unhandled.size == 2 &&
      tbs.extensions.unhandled.any (fun ext => ext.oid == OID.subjectKeyIdentifier) &&
      tbs.extensions.unhandled.any (fun ext => ext.oid == OID.authorityKeyIdentifier))

  -- Independently walk the outer framing and confirm the parser retained the
  -- original signed TBS TLV byte-for-byte.
  let outer ← expectOk (label ++ " outer TLV") (DER.decode der)
  let (rawTBS, _) ← expectOk (label ++ " raw TBS") outer.reader.readTLV
  checkBytes (label ++ " exact TBS retention") tbs.encoded rawTBS.encoded
  let (_, rawReader) ← expectOk (label ++ " raw version") rawTBS.reader.readTLV
  let (_, rawReader) ← expectOk (label ++ " raw serial") rawReader.readTLV
  let (_, rawReader) ← expectOk (label ++ " raw signature algorithm") rawReader.readTLV
  let (rawIssuer, rawReader) ← expectOk (label ++ " raw issuer") rawReader.readTLV
  let (_, rawReader) ← expectOk (label ++ " raw validity") rawReader.readTLV
  let (rawSubject, _) ← expectOk (label ++ " raw subject") rawReader.readTLV
  checkBytes (label ++ " exact issuer retention") tbs.issuer.encoded rawIssuer.encoded
  checkBytes (label ++ " exact subject retention") tbs.subject.encoded rawSubject.encoded

private def checkSAN (label : String) (certificate : Certificate)
    (dnsName : String) (ip : ByteArray) : IO Unit := do
  let some san := certificate.tbsCertificate.extensions.subjectAltName
    | throw (IO.userError s!"{label}: subjectAltName missing")
  check (label ++ " SAN present/noncritical") (!san.critical)
  check (label ++ " SAN DNS") (san.value.dnsNames == #[dnsName])
  check (label ++ " SAN IP count") (san.value.ipAddresses.size == 1)
  checkBytes (label ++ " SAN IP") san.value.ipAddresses[0]! ip

private def checkConstraints (label : String) (certificate : Certificate)
    (basicCritical keyUsageCritical : Bool) : IO (BasicConstraints × KeyUsage) := do
  let some basic := certificate.tbsCertificate.extensions.basicConstraints
    | throw (IO.userError s!"{label}: BasicConstraints missing")
  let some usage := certificate.tbsCertificate.extensions.keyUsage
    | throw (IO.userError s!"{label}: KeyUsage missing")
  check (label ++ " BasicConstraints critical") (basic.critical == basicCritical)
  check (label ++ " BasicConstraints leaf")
    (!basic.value.ca && basic.value.pathLenConstraint.isNone)
  check (label ++ " KeyUsage critical") (usage.critical == keyUsageCritical)
  pure (basic.value, usage.value)

private def testRSA : IO ByteArray := do
  let (der, certificate) ← readFixture "rsa2048"
  checkCommon "RSA" der certificate 4097 "rsa.example.test" OID.sha256WithRSAEncryption
  checkSAN "RSA" certificate "rsa.example.test" (h "7f000001")
  let (_, usage) ← checkConstraints "RSA" certificate true true
  check "RSA KeyUsage"
    (usage.digitalSignature && usage.keyEncipherment && !usage.keyAgreement &&
      !usage.keyCertSign)
  check "RSA SPKI OID"
    (certificate.tbsCertificate.subjectPublicKeyInfo.algorithm.oid == OID.rsaEncryption)
  let some rsaParameters :=
      certificate.tbsCertificate.subjectPublicKeyInfo.algorithm.parameters
    | throw (IO.userError "RSA SPKI parameters missing")
  check "RSA SPKI NULL parameters"
    (rsaParameters.tag == DER.Tag.null && rsaParameters.contents.isEmpty)
  let some rsaSignatureParameters := certificate.signatureAlgorithm.parameters
    | throw (IO.userError "RSA signature parameters missing")
  check "RSA signature NULL parameters"
    (rsaSignatureParameters.tag == DER.Tag.null &&
      rsaSignatureParameters.contents.isEmpty)
  let expectedModulus := natOfBytes (h (
    "9bb0d21cec3d676e2be15f54b1ad008d0549933a830dec3387ff041e9e239948" ++
    "5e33811d2cc8417565756326e5b624092874c3eb1f8655626f818e7b7ff8af7e" ++
    "0ecf9df5795c4ba03e92a7930adfbf90b775776c22a4a5b8ca822fd649a1f907" ++
    "81d4db594e1694a564d32d794fa6408d9970e92237c4000d76c169920ae24ab3" ++
    "99136d1828535021b5d9b802dd64e91d7e18ea4b9f993aeeaba1aeb4399f719c" ++
    "dbcb9e27214073aa84bfe14071dd19691a2add48622624da28ade07b6b6eb6dd" ++
    "932664e307b8e8af6497cc473f67564409906d8648d937952503f7be20680ce64" ++
    "aa70fe8d46042013b1316beb920f883d9e88283307361df6c4cfd4ba3953289"))
  match certificate.tbsCertificate.subjectPublicKeyInfo.key with
  | .rsa key =>
    check "RSA modulus exact" (key.modulus == expectedModulus)
    check "RSA exponent" (key.exponent == 65537)
  | _ => throw (IO.userError "RSA fixture parsed as the wrong public-key type")
  check "RSA signature length" (certificate.signature.size == 256)
  pure der

private def testP256 : IO ByteArray := do
  let (der, certificate) ← readFixture "p256"
  checkCommon "P-256" der certificate 4098 "p256.example.test" OID.ecdsaWithSha256
  checkSAN "P-256" certificate "p256.example.test"
    (h "20010db8000000000000000000000001")
  let (_, usage) ← checkConstraints "P-256" certificate false false
  check "P-256 KeyUsage"
    (usage.digitalSignature && usage.keyAgreement && !usage.keyEncipherment &&
      !usage.keyCertSign)
  check "P-256 SPKI OID"
    (certificate.tbsCertificate.subjectPublicKeyInfo.algorithm.oid == OID.ecPublicKey)
  let some curveParameters :=
      certificate.tbsCertificate.subjectPublicKeyInfo.algorithm.parameters
    | throw (IO.userError "P-256 named-curve parameters missing")
  let curveOID ← expectOk "P-256 curve OID" curveParameters.asOID
  check "P-256 named curve" (curveOID == OID.prime256v1)
  check "P-256 signature parameters absent"
    certificate.signatureAlgorithm.parameters.isNone
  let expectedPoint := h (
    "04ef7d75d9fd4736f75cce3250377f83a3f56b32bcd173897267f15f9700c6b9" ++
    "c89d376cb97c49cdc46b10dda24f6fb008a3d14f3498f8c3ba4c3cb7f63b94efcb")
  match certificate.tbsCertificate.subjectPublicKeyInfo.key with
  | .p256 point => checkBytes "P-256 point exact" point expectedPoint
  | _ => throw (IO.userError "P-256 fixture parsed as the wrong public-key type")
  pure der

private def testEd25519 : IO ByteArray := do
  let (der, certificate) ← readFixture "ed25519"
  checkCommon "Ed25519" der certificate 4099 "ed25519.example.test" OID.ed25519
  checkSAN "Ed25519" certificate "ed25519.example.test" (h "c0000237")
  let (_, usage) ← checkConstraints "Ed25519" certificate true false
  check "Ed25519 KeyUsage"
    (usage.digitalSignature && !usage.keyAgreement && !usage.keyEncipherment &&
      !usage.keyCertSign)
  check "Ed25519 SPKI OID"
    (certificate.tbsCertificate.subjectPublicKeyInfo.algorithm.oid == OID.ed25519)
  check "Ed25519 SPKI parameters absent"
    certificate.tbsCertificate.subjectPublicKeyInfo.algorithm.parameters.isNone
  check "Ed25519 signature parameters absent"
    certificate.signatureAlgorithm.parameters.isNone
  match certificate.tbsCertificate.subjectPublicKeyInfo.key with
  | .ed25519 key =>
    checkBytes "Ed25519 key exact" key
      (h "8b87969cf913c9acba1f8e695572a38b9cbd9d6e7320a6926505922e1fd15496")
  | _ => throw (IO.userError "Ed25519 fixture parsed as the wrong public-key type")
  check "Ed25519 signature length" (certificate.signature.size == 64)
  pure der

private def testTimes : IO Unit := do
  let positive : Array (String × UInt8 × String × Int × Nat) := #[
    ("UTC 1950 pivot", 0x17, "500101000000Z", -631152000, 1950),
    ("UTC epoch minus one", 0x17, "691231235959Z", -1, 1969),
    ("UTC epoch", 0x17, "700101000000Z", 0, 1970),
    ("UTC 2000 pivot", 0x17, "000101000000Z", 946684800, 2000),
    ("UTC leap day", 0x17, "000229123456Z", 951827696, 2000),
    ("UTC leap second", 0x17, "161231235960Z", 1483228800, 2016),
    ("UTC 2049 pivot", 0x17, "491231235959Z", 2524607999, 2049),
    ("Generalized year zero", 0x18, "00000101000000Z", -62167219200, 0),
    ("Generalized pre-2050", 0x18, "19500101000000Z", -631152000, 1950),
    ("Generalized epoch", 0x18, "19700101000000Z", 0, 1970),
    ("Generalized leap day", 0x18, "20000229123456Z", 951827696, 2000),
    ("Generalized 2050", 0x18, "20500101000000Z", 2524608000, 2050),
    ("Generalized 2400 leap day", 0x18, "24000229000000Z", 13574563200, 2400),
    ("Generalized maximum", 0x18, "99991231235959Z", 253402300799, 9999)
  ]
  for (label, tag, text, epoch, year) in positive do
    let parsed ← expectOk label (parseTime tag text)
    check (label ++ " epoch") (parsed.unixSeconds == epoch)
    check (label ++ " year") (parsed.year == year)

  let malformed : Array (String × UInt8 × String) := #[
    ("UTC missing Z", 0x17, "240101000000"),
    ("UTC lowercase z", 0x17, "240101000000z"),
    ("UTC missing seconds", 0x17, "2401010000Z"),
    ("UTC offset", 0x17, "240101000000+0000"),
    ("UTC fraction", 0x17, "240101000000.0Z"),
    ("UTC non-digit", 0x17, "2x0101000000Z"),
    ("UTC month zero", 0x17, "240001000000Z"),
    ("UTC month 13", 0x17, "241301000000Z"),
    ("UTC day zero", 0x17, "240100000000Z"),
    ("UTC April 31", 0x17, "240431000000Z"),
    ("UTC non-leap February 29", 0x17, "500229000000Z"),
    ("UTC hour 24", 0x17, "240101240000Z"),
    ("UTC minute 60", 0x17, "240101006000Z"),
    ("UTC second 61", 0x17, "240101000061Z"),
    ("Generalized 1900 non-leap", 0x18, "19000229000000Z"),
    ("Generalized 2100 non-leap", 0x18, "21000229000000Z")
  ]
  for (label, tag, text) in malformed do
    expectError label (parseTime tag text)
  expectError "validity wrong DER tag" (parseTime 0x16 "240101000000Z")

private def testPEMBundle : IO Unit := do
  let rsa ← IO.FS.readFile "Test/Fixtures/X509/rsa2048.pem"
  let p256 ← IO.FS.readFile "Test/Fixtures/X509/p256.pem"
  let ed25519 ← IO.FS.readFile "Test/Fixtures/X509/ed25519.pem"
  let certificates ←
    expectOk "parse certificate PEM bundle"
      (Certificate.decodePEM (rsa ++ "\n" ++ p256 ++ "\n" ++ ed25519))
  check "certificate PEM bundle count" (certificates.size == 3)
  check "certificate PEM bundle order"
    (certificates.map (·.tbsCertificate.serialNumber) == #[4097, 4098, 4099])

private def testMalformedCertificates (rsaDER p256DER edDER : ByteArray) : IO Unit := do
  expectError "certificate trailing bytes" (Certificate.decode (rsaDER.push 0))

  let some nonminimalSerial := setAtFound rsaDER (h "02021001") 2 0x00
    | throw (IO.userError "RSA serial pattern not found")
  expectError "non-minimal certificate serial" (Certificate.decode nonminimalSerial)

  let some localTime := setAtFound rsaDER "240101000000Z".toUTF8 12 0x2b
    | throw (IO.userError "RSA validity pattern not found")
  expectError "certificate local validity time" (Certificate.decode localTime)

  let some badBoolean := setAtFound rsaDER (h "0101ff") 2 0x01
    | throw (IO.userError "RSA critical BOOLEAN pattern not found")
  expectError "non-canonical extension BOOLEAN" (Certificate.decode badBoolean)

  let some badSAN := setAtFound rsaDER (h "87047f000001") 0 0x82
    | throw (IO.userError "RSA SAN IP pattern not found")
  expectError "malformed SAN dNSName" (Certificate.decode badSAN)

  let some absentSAN := setAtFound rsaDER (h "0603551d11") 4 0x12
    | throw (IO.userError "RSA subjectAltName OID pattern not found")
  let absentSANCertificate ←
    expectOk "certificate without subjectAltName" (Certificate.decode absentSAN)
  check "subjectAltName absence is distinct"
    absentSANCertificate.tbsCertificate.extensions.subjectAltName.isNone

  let encodedDNS := (h "8210") ++ "rsa.example.test".toUTF8
  let some ignoredURI := setAtFound rsaDER encodedDNS 0 0x86
    | throw (IO.userError "RSA SAN DNS pattern not found")
  let ignoredCertificate ←
    expectOk "unneeded SAN GeneralName choice" (Certificate.decode ignoredURI)
  let some ignoredSAN := ignoredCertificate.tbsCertificate.extensions.subjectAltName
    | throw (IO.userError "mutated RSA subjectAltName missing")
  check "unneeded SAN GeneralName is skipped"
    (ignoredSAN.value.dnsNames.isEmpty && ignoredSAN.value.ipAddresses.size == 1)

  let some malformedURI := setAtFound rsaDER encodedDNS 0 0xa6
    | throw (IO.userError "RSA SAN DNS pattern not found for constructed mutation")
  expectError "malformed skipped SAN GeneralName" (Certificate.decode malformedURI)

  let encodedCN := (h "0c10") ++ "rsa.example.test".toUTF8
  let some ia5CommonName := setAtFound rsaDER encodedCN 0 0x16
    | throw (IO.userError "RSA commonName pattern not found")
  expectError "commonName outside DirectoryString" (Certificate.decode ia5CommonName)

  let expectedPointPrefix := h "04ef7d75d9fd4736"
  let some compressedPoint := setAtFound p256DER expectedPointPrefix 0 0x02
    | throw (IO.userError "P-256 point pattern not found")
  expectError "compressed P-256 point" (Certificate.decode compressedPoint)

  let some wrongCurve := setAtFound p256DER (h "06082a8648ce3d030107") 9 0x08
    | throw (IO.userError "P-256 named-curve OID pattern not found")
  expectError "unsupported EC named curve" (Certificate.decode wrongCurve)

  let rsaCertificate ← expectOk "RSA parse for parameter mutation" (Certificate.decode rsaDER)
  let some tbsSignatureParameters :=
      rsaCertificate.tbsCertificate.signatureAlgorithm.parameters
    | throw (IO.userError "RSA TBS signature parameters missing")
  let some outerSignatureParameters := rsaCertificate.signatureAlgorithm.parameters
    | throw (IO.userError "RSA outer signature parameters missing")
  let invalidSignatureParameters :=
    (rsaDER.set! tbsSignatureParameters.offset 0x04).set!
      outerSignatureParameters.offset 0x04
  expectError "invalid RSA signature parameters"
    (Certificate.decode invalidSignatureParameters)

  let edOuter ← expectOk "Ed25519 outer for mutation" (DER.decode edDER)
  let (_, reader) ← expectOk "Ed25519 TBS for mutation" edOuter.reader.readTLV
  let (_, reader) ← expectOk "Ed25519 algorithm for mutation" reader.readTLV
  let (signatureValue, _) ← expectOk "Ed25519 signature for mutation" reader.readTLV
  let signatureEnd :=
    signatureValue.offset + signatureValue.headerSize + signatureValue.contents.size - 1
  let clearedSignature :=
    edDER.set! signatureEnd (edDER.get! signatureEnd &&& 0xfe)
  let badUnusedBits :=
    clearedSignature.set! (signatureValue.offset + signatureValue.headerSize) 1
  expectError "non-octet-aligned certificate signature" (Certificate.decode badUnusedBits)

  let some nonminimalKeyUsage := setAtFound edDER (h "03020780") 2 0x00
    | throw (IO.userError "Ed25519 KeyUsage pattern not found")
  expectError "non-minimal KeyUsage NamedBitList"
    (Certificate.decode nonminimalKeyUsage)

def main : IO Unit := do
  testTimes
  testPEMBundle
  let rsaDER ← testRSA
  let p256DER ← testP256
  let edDER ← testEd25519
  testMalformedCertificates rsaDER p256DER edDER
  IO.println "all X.509 certificate parser assertions passed"
