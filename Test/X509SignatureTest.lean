module

public import TLS13.X509

public section

/-!
OpenSSL, RFC 8032, and malformed-encoding tests for signature verification.
-/

open TLS13.X509

private def hexDigitValue? (char : Char) : Option UInt8 :=
  if '0' ≤ char ∧ char ≤ '9' then
    some (UInt8.ofNat (char.toNat - '0'.toNat))
  else if 'a' ≤ char ∧ char ≤ 'f' then
    some (UInt8.ofNat (char.toNat - 'a'.toNat + 10))
  else if 'A' ≤ char ∧ char ≤ 'F' then
    some (UInt8.ofNat (char.toNat - 'A'.toNat + 10))
  else
    none

private def decodeHex : List Char → ByteArray → Option ByteArray
  | [], output => some output
  | [_], _ => none
  | high :: low :: rest, output =>
    match hexDigitValue? high, hexDigitValue? low with
    | some high, some low =>
      decodeHex rest (output.push (high * 16 + low))
    | _, _ => none

private def h (hex : String) : ByteArray :=
  match decodeHex hex.toList ByteArray.empty with
  | some bytes => bytes
  | none => panic! s!"malformed test hex: {hex}"

private def expectOk (label : String) (result : Except String α) : IO α :=
  match result with
  | .ok value => pure value
  | .error error =>
    throw (IO.userError s!"{label}: unexpected error: {error}")

private def expectError (label : String) (result : Except String α) : IO Unit :=
  match result with
  | .ok _ => throw (IO.userError s!"{label}: malformed input was accepted")
  | .error _ => pure ()

private def check (label : String) (condition : Bool) : IO Unit := do
  unless condition do
    throw (IO.userError s!"{label}: assertion failed")

private def checkBytes (label : String) (got expected : ByteArray) : IO Unit :=
  check label (got == expected)

private def readCertificate (path : String) : IO Certificate := do
  let text ← IO.FS.readFile path
  let certificates ← expectOk path (Certificate.decodePEM text)
  if certificates.size != 1 then
    throw (IO.userError s!"{path}: expected exactly one certificate")
  pure certificates[0]!

private def flipped (bytes : ByteArray) (index : Nat) : ByteArray :=
  bytes.set! index (bytes.get! index ^^^ 0x01)

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
  return none

private def setAtFound
    (bytes needle : ByteArray) (relative : Nat) (octet : UInt8) :
    Option ByteArray := do
  let start ← findBytes? bytes needle
  if relative ≥ needle.size then none
  else some (bytes.set! (start + relative) octet)

private def checkCertificateSignature
    (label : String) (certificate : Certificate) : IO Unit := do
  let tbs := certificate.tbsCertificate
  let spki := tbs.subjectPublicKeyInfo
  check (label ++ " valid signature")
    (Signature.verifyX509 certificate.signatureAlgorithm spki
      tbs.encoded certificate.signature)

  let wrongMessage := flipped tbs.encoded (tbs.encoded.size / 2)
  check (label ++ " wrong message")
    (!Signature.verifyX509 certificate.signatureAlgorithm spki
      wrongMessage certificate.signature)

  let wrongSignature :=
    flipped certificate.signature (certificate.signature.size / 2)
  check (label ++ " flipped signature")
    (!Signature.verifyX509 certificate.signatureAlgorithm spki
      tbs.encoded wrongSignature)

  let truncated :=
    certificate.signature.extract 0 (certificate.signature.size - 1)
  check (label ++ " truncated signature")
    (!Signature.verifyX509 certificate.signatureAlgorithm spki
      tbs.encoded truncated)
  check (label ++ " trailing signature byte")
    (!Signature.verifyX509 certificate.signatureAlgorithm spki
      tbs.encoded (certificate.signature.push 0))

private def requireRSA (label : String) (certificate : Certificate) :
    IO RSAPublicKey :=
  match certificate.tbsCertificate.subjectPublicKeyInfo.key with
  | .rsa key => pure key
  | _ => throw (IO.userError s!"{label}: expected an RSA public key")

private def xorBytes (left right : ByteArray) : ByteArray := Id.run do
  if left.size != right.size then
    panic! "test xor length mismatch"
  let mut output := ByteArray.empty
  for index in [0:left.size] do
    output := output.push (left.get! index ^^^ right.get! index)
  return output

private def testConversions : IO Unit := do
  check "OS2IP empty" (RSA.os2ip ByteArray.empty == 0)
  check "OS2IP big endian" (RSA.os2ip (h "010001") == 65537)
  checkBytes "I2OSP leading zero" (← expectOk "I2OSP" (RSA.i2osp 65537 4))
    (h "00010001")
  checkBytes "I2OSP zero length" (← expectOk "I2OSP zero" (RSA.i2osp 0 0))
    ByteArray.empty
  expectError "I2OSP overflow" (RSA.i2osp 256 1)
  expectError "I2OSP positive zero length" (RSA.i2osp 1 0)
  check "modular exponentiation KAT" (RSA.modPow 4 13 497 == 445)
  check "modular exponentiation exponent zero" (RSA.modPow 7 0 13 == 1)

  let seed := "MGF1 boundary test".toUTF8
  let mask0 ← expectOk "MGF1 length 0" (RSA.mgf1Sha256 seed 0)
  let mask31 ← expectOk "MGF1 length 31" (RSA.mgf1Sha256 seed 31)
  let mask32 ← expectOk "MGF1 length 32" (RSA.mgf1Sha256 seed 32)
  let mask33 ← expectOk "MGF1 length 33" (RSA.mgf1Sha256 seed 33)
  check "MGF1 empty" mask0.isEmpty
  check "MGF1 requested lengths"
    (mask31.size == 31 && mask32.size == 32 && mask33.size == 33)
  checkBytes "MGF1 truncation consistency" mask31 (mask32.extract 0 31)
  checkBytes "MGF1 block consistency" mask32 (mask33.extract 0 32)
  checkBytes "MGF1 independent SHA-256 KAT" mask33
    (h "1b488764fdb960d918f60200a770566d5b6a499d1bfb6b496e496454b2e5f1a054")

private def testServerCertificateVerifyContent : IO Unit := do
  let transcriptHash :=
    h "000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f"
  let content ← expectOk "server CertificateVerify content"
    (Signature.serverCertificateVerifyContent transcriptHash)
  check "server CertificateVerify content length" (content.size == 130)
  checkBytes "server CertificateVerify content KAT" content (h (
    "20202020202020202020202020202020" ++
    "20202020202020202020202020202020" ++
    "20202020202020202020202020202020" ++
    "20202020202020202020202020202020" ++
    "544c5320312e332c20736572766572204365727469666963617465566572696679" ++
    "00" ++
    "000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f"))
  expectError "short CertificateVerify transcript hash"
    (Signature.serverCertificateVerifyContent (transcriptHash.extract 0 31))

private def testECDSAParser (certificate : Certificate) : IO Unit := do
  let (r, s) ← expectOk "fixture ECDSA DER"
    (Signature.parseECDSAP256Signature certificate.signature)
  check "ECDSA fixed scalar widths" (r.size == 32 && s.size == 32)

  expectError "ECDSA r zero"
    (Signature.parseECDSAP256Signature (h "3006020100020101"))
  expectError "ECDSA s zero"
    (Signature.parseECDSAP256Signature (h "3006020101020100"))
  expectError "ECDSA negative r"
    (Signature.parseECDSAP256Signature (h "3006020180020101"))
  expectError "ECDSA non-minimal r"
    (Signature.parseECDSAP256Signature (h "300702020001020101"))
  expectError "ECDSA trailing field"
    (Signature.parseECDSAP256Signature (h "3009020101020101020101"))
  expectError "ECDSA trailing outer byte"
    (Signature.parseECDSAP256Signature (h "300602010102010100"))
  expectError "ECDSA r equal to group order"
    (Signature.parseECDSAP256Signature (h (
      "3026022100" ++
      "ffffffff00000000ffffffffffffffffbce6faada7179e84f3b9cac2fc632551" ++
      "020101")))
  expectError "ECDSA s equal to group order"
    (Signature.parseECDSAP256Signature (h (
      "3026020101022100" ++
      "ffffffff00000000ffffffffffffffffbce6faada7179e84f3b9cac2fc632551")))

  let invalidPoint :=
    (ByteArray.mk #[0x04]) ++ ByteArray.mk (Array.replicate 64 0)
  check "ECDSA invalid public point"
    (!Signature.verify .ecdsaP256Sha256 (.p256 invalidPoint)
      certificate.tbsCertificate.encoded certificate.signature)
  check "ECDSA short public point"
    (!Signature.verify .ecdsaP256Sha256
      (.p256 (invalidPoint.extract 0 64))
      certificate.tbsCertificate.encoded certificate.signature)

private def testEd25519RFC8032 : IO Unit := do
  -- RFC 8032 section 7.1, test vector 1: empty message.
  let publicKey :=
    h "d75a980182b10ab7d54bfed3c964073a0ee172f3daa62325af021a68f707511a"
  let signature := h (
    "e5564300c360ac729086e2cc806e828a84877f1eb8e5d974d873e06522490155" ++
    "5fb8821590a33bacc61e39701cf9b46bd25bf5f0595bbe24655141438e7a100b")
  check "RFC 8032 Ed25519 empty-message vector"
    (Signature.verify .ed25519 (.ed25519 publicKey)
      ByteArray.empty signature)
  check "RFC 8032 Ed25519 wrong message"
    (!Signature.verify .ed25519 (.ed25519 publicKey)
      (h "00") signature)
  check "RFC 8032 Ed25519 flipped signature"
    (!Signature.verify .ed25519 (.ed25519 publicKey)
      ByteArray.empty (flipped signature 17))
  let groupOrderLittleEndian :=
    h "edd3f55c1a631258d69cf7a2def9de1400000000000000000000000000000010"
  let noncanonicalScalar :=
    (signature.extract 0 32) ++ groupOrderLittleEndian
  check "Ed25519 noncanonical S"
    (!Signature.verify .ed25519 (.ed25519 publicKey)
      ByteArray.empty noncanonicalScalar)
  check "Ed25519 short public key"
    (!Signature.verify .ed25519
      (.ed25519 (publicKey.extract 0 31)) ByteArray.empty signature)
  check "Ed25519 trailing signature byte"
    (!Signature.verify .ed25519 (.ed25519 publicKey)
      ByteArray.empty (signature.push 0))

private def pssAlgorithmWithParameters
    (label : String) (encoded : ByteArray) : IO AlgorithmIdentifier := do
  let parameters ← expectOk label (DER.decode encoded)
  pure {
    oid := OID.rsassaPss
    parameters := some parameters
    encoded := ByteArray.empty
  }

private def testPSSParameterParsing : IO Unit := do
  let validParameters := h (
    "3034" ++
    "a00f300d06096086480165030402010500" ++
    "a11c301a06092a864886f70d010108300d06096086480165030402010500" ++
    "a203020120")
  let validAlgorithm ←
    pssAlgorithmWithParameters "valid PSS parameters" validParameters
  let parsed ← expectOk "valid PSS parameter parse"
    (Signature.parsePSSSha256Parameters validAlgorithm)
  check "PSS parameter salt 32" (parsed.saltLength == 32)

  let defaultSalt := validParameters.set! (validParameters.size - 1) 0x14
  expectError "PSS explicitly encoded salt DEFAULT"
    (Signature.parsePSSSha256Parameters
      (← pssAlgorithmWithParameters "PSS default salt" defaultSalt))

  let explicitTrailer :=
    ((validParameters.set! 1 0x39) ++ h "a303020101")
  let trailerParameters ← expectOk "PSS explicitly encoded trailer field 1"
    (Signature.parsePSSSha256Parameters
      (← pssAlgorithmWithParameters "PSS trailer" explicitTrailer))
  check "PSS explicit trailer preserves salt"
    (trailerParameters.saltLength == 32)

  let unsupportedTrailer :=
    ((validParameters.set! 1 0x39) ++ h "a303020102")
  expectError "PSS unsupported trailer field"
    (Signature.parsePSSSha256Parameters
      (← pssAlgorithmWithParameters "PSS wrong trailer" unsupportedTrailer))

  let duplicateSalt :=
    ((validParameters.set! 1 0x39) ++ h "a203020120")
  expectError "PSS duplicate parameter"
    (Signature.parsePSSSha256Parameters
      (← pssAlgorithmWithParameters "PSS duplicate" duplicateSalt))

  let some wrongHash :=
      setAtFound validParameters (h "0609608648016503040201") 10 0x02
    | throw (IO.userError "PSS SHA-256 OID pattern not found")
  expectError "PSS unsupported hash"
    (Signature.parsePSSSha256Parameters
      (← pssAlgorithmWithParameters "PSS wrong hash" wrongHash))

  let some wrongMask :=
      setAtFound validParameters (h "06092a864886f70d010108") 10 0x09
    | throw (IO.userError "PSS MGF1 OID pattern not found")
  expectError "PSS unsupported mask generation function"
    (Signature.parsePSSSha256Parameters
      (← pssAlgorithmWithParameters "PSS wrong MGF" wrongMask))

  let wrongMaskHash := validParameters.set! 46 0x02
  expectError "PSS unsupported MGF1 hash"
    (Signature.parsePSSSha256Parameters
      (← pssAlgorithmWithParameters "PSS wrong MGF hash" wrongMaskHash))

  expectError "PSS SHA-1 defaults unsupported"
    (Signature.parsePSSSha256Parameters
      (← pssAlgorithmWithParameters "empty PSS parameters" (h "3000")))

private def recoveredRSAEncoding
    (key : RSAPublicKey) (signature : ByteArray) (encodedLength : Nat) :
    IO ByteArray := do
  let representative :=
    RSA.modPow (RSA.os2ip signature) key.exponent key.modulus
  expectOk "RSA recovered encoded message"
    (RSA.i2osp representative encodedLength)

private def testPKCS1
    (certificate : Certificate) (key : RSAPublicKey) : IO Unit := do
  let absentParameters : AlgorithmIdentifier :=
    { certificate.signatureAlgorithm with parameters := none }
  check "PKCS#1 signature accepts absent AlgorithmIdentifier parameters"
    (Signature.verifyX509 absentParameters
      certificate.tbsCertificate.subjectPublicKeyInfo
      certificate.tbsCertificate.encoded certificate.signature)
  let badParameters ← expectOk "PKCS#1 bad parameters DER"
    (DER.decode (h "020101"))
  let invalidParameters : AlgorithmIdentifier :=
    { certificate.signatureAlgorithm with parameters := some badParameters }
  check "PKCS#1 signature rejects non-NULL parameters"
    (!Signature.verifyX509 invalidParameters
      certificate.tbsCertificate.subjectPublicKeyInfo
      certificate.tbsCertificate.encoded certificate.signature)

  let modulusBits := key.modulus.log2 + 1
  let modulusOctets := (modulusBits + 7) / 8
  let digest := HaclStar.sha256 certificate.tbsCertificate.encoded
  let encoded ←
    recoveredRSAEncoding key certificate.signature modulusOctets
  check "PKCS#1 recovered encoding"
    (RSA.emsaPKCS1v15Sha256 digest encoded)
  let expected ← expectOk "PKCS#1 expected encoding"
    (RSA.encodePKCS1v15Sha256 digest modulusOctets)
  checkBytes "PKCS#1 exact full block" encoded expected

  check "PKCS#1 bad leading zero"
    (!RSA.emsaPKCS1v15Sha256 digest (encoded.set! 0 0x01))
  check "PKCS#1 wrong block type"
    (!RSA.emsaPKCS1v15Sha256 digest (encoded.set! 1 0x02))
  check "PKCS#1 altered FF padding"
    (!RSA.emsaPKCS1v15Sha256 digest (encoded.set! 7 0xfe))
  let separator := modulusOctets - 52
  check "PKCS#1 missing separator"
    (!RSA.emsaPKCS1v15Sha256 digest (encoded.set! separator 0xff))
  let digestInfoStart := modulusOctets - 51
  check "PKCS#1 altered DigestInfo"
    (!RSA.emsaPKCS1v15Sha256 digest
      (flipped encoded (digestInfoStart + 6)))
  check "PKCS#1 altered digest"
    (!RSA.emsaPKCS1v15Sha256 digest
      (flipped encoded (encoded.size - 1)))
  check "PKCS#1 truncated encoded message"
    (!RSA.emsaPKCS1v15Sha256 digest
      (encoded.extract 0 (encoded.size - 1)))
  check "PKCS#1 trailing encoded byte"
    (!RSA.emsaPKCS1v15Sha256 digest (encoded.push 0))

  let signatureEqualModulus ←
    expectOk "RSA modulus as signature" (RSA.i2osp key.modulus modulusOctets)
  check "RSA signature representative equal to modulus"
    (!RSA.verify key .pkcs1v15Sha256 certificate.tbsCertificate.encoded
      signatureEqualModulus)
  check "RSA invalid even exponent"
    (!RSA.verify { key with exponent := 2 } .pkcs1v15Sha256
      certificate.tbsCertificate.encoded certificate.signature)

private def testPSS
    (certificate : Certificate) (key : RSAPublicKey) : IO Unit := do
  let parameters ← expectOk "RSA-PSS parameters"
    (Signature.parsePSSSha256Parameters certificate.signatureAlgorithm)
  check "RSA-PSS salt length" (parameters.saltLength == 32)
  let unrestrictedPSSAlgorithm : AlgorithmIdentifier :=
    { certificate.signatureAlgorithm with
      parameters := none
      encoded := ByteArray.empty }
  let unrestrictedPSSSPKI : SubjectPublicKeyInfo :=
    { certificate.tbsCertificate.subjectPublicKeyInfo with
      algorithm := unrestrictedPSSAlgorithm }
  check "PSS-only SPKI without constraints"
    (Signature.verifyX509 certificate.signatureAlgorithm unrestrictedPSSSPKI
      certificate.tbsCertificate.encoded certificate.signature)
  let constrainedPSSSPKI : SubjectPublicKeyInfo :=
    { certificate.tbsCertificate.subjectPublicKeyInfo with
      algorithm := certificate.signatureAlgorithm }
  check "PSS-only SPKI with matching constraints"
    (Signature.verifyX509 certificate.signatureAlgorithm constrainedPSSSPKI
      certificate.tbsCertificate.encoded certificate.signature)
  let some rawPSSParameters := certificate.signatureAlgorithm.parameters
    | throw (IO.userError "RSA-PSS fixture lacks parameters")
  let strongerPSSParameters ← expectOk "stronger PSS key constraints"
    (DER.decode
      (rawPSSParameters.encoded.set!
        (rawPSSParameters.encoded.size - 1) 0x21))
  let strongerPSSAlgorithm : AlgorithmIdentifier :=
    { certificate.signatureAlgorithm with
      parameters := some strongerPSSParameters
      encoded := ByteArray.empty }
  let strongerPSSSPKI : SubjectPublicKeyInfo :=
    { certificate.tbsCertificate.subjectPublicKeyInfo with
      algorithm := strongerPSSAlgorithm }
  check "PSS-only SPKI rejects signature below minimum salt length"
    (!Signature.verifyX509 certificate.signatureAlgorithm strongerPSSSPKI
      certificate.tbsCertificate.encoded certificate.signature)

  let modulusBits := key.modulus.log2 + 1
  let encodedBits := modulusBits - 1
  let encodedLength := (encodedBits + 7) / 8
  let digest := HaclStar.sha256 certificate.tbsCertificate.encoded
  let encoded ←
    recoveredRSAEncoding key certificate.signature encodedLength
  check "PSS recovered encoding"
    (RSA.emsaPSSSha256 digest encoded encodedBits 32)
  check "PSS wrong salt policy"
    (!RSA.emsaPSSSha256 digest encoded encodedBits 31)
  check "PSS signature under wrong salt policy"
    (!RSA.verify key (.pssSha256 31)
      certificate.tbsCertificate.encoded certificate.signature)
  check "PSS wrong trailer"
    (!RSA.emsaPSSSha256 digest
      (encoded.set! (encoded.size - 1) 0xbd) encodedBits 32)
  check "PSS forbidden top maskedDB bit"
    (!RSA.emsaPSSSha256 digest
      (encoded.set! 0 (encoded.get! 0 ||| 0x80)) encodedBits 32)

  let dataBlockLength := encodedLength - HaclStar.sha256DigestLen - 1
  let maskedDataBlock := encoded.extract 0 dataBlockLength
  let encodedHash :=
    encoded.extract dataBlockLength
      (dataBlockLength + HaclStar.sha256DigestLen)
  let mask ← expectOk "PSS data-block mask"
    (RSA.mgf1Sha256 encodedHash dataBlockLength)
  let unusedTopBits := encodedLength * 8 - encodedBits
  let allowedFirstOctet := UInt8.ofNat (0xff >>> unusedTopBits)
  let dataBlock :=
    (xorBytes maskedDataBlock mask).set! 0
      ((xorBytes maskedDataBlock mask).get! 0 &&& allowedFirstOctet)
  let paddingLength :=
    encodedLength - HaclStar.sha256DigestLen - parameters.saltLength - 2
  check "PSS recovered delimiter"
    (dataBlock.get! paddingLength == 0x01)

  let remask (mutatedDataBlock : ByteArray) : ByteArray :=
    let masked := xorBytes mutatedDataBlock mask
    let masked := masked.set! 0 (masked.get! 0 &&& allowedFirstOctet)
    ((masked ++ encodedHash).push 0xbc)

  let dirtyPadding := dataBlock.set! 1 0x01
  check "PSS nonzero PS"
    (!RSA.emsaPSSSha256 digest (remask dirtyPadding) encodedBits 32)
  let badDelimiter := dataBlock.set! paddingLength 0x02
  check "PSS bad delimiter"
    (!RSA.emsaPSSSha256 digest (remask badDelimiter) encodedBits 32)
  let alteredSalt := flipped dataBlock (dataBlock.size - 1)
  check "PSS altered salt with stale hash"
    (!RSA.emsaPSSSha256 digest (remask alteredSalt) encodedBits 32)
  check "PSS altered encoded hash"
    (!RSA.emsaPSSSha256 digest
      (flipped encoded dataBlockLength) encodedBits 32)

  let signatureEqualModulus ←
    expectOk "PSS modulus as signature"
      (RSA.i2osp key.modulus ((modulusBits + 7) / 8))
  check "PSS signature representative equal to modulus"
    (!RSA.verify key (.pssSha256 32) certificate.tbsCertificate.encoded
      signatureEqualModulus)

  let noParameters : AlgorithmIdentifier :=
    { certificate.signatureAlgorithm with parameters := none }
  expectError "PSS signature parameters absent"
    (Signature.parsePSSSha256Parameters noParameters)
  check "PSS absent parameters reject dispatch"
    (!Signature.verifyX509 noParameters
      certificate.tbsCertificate.subjectPublicKeyInfo
      certificate.tbsCertificate.encoded certificate.signature)

private def testCertificateVerifySchemeCompatibility
    (rsa p256 ed25519 pss : Certificate) : IO Unit := do
  let rsaSPKI := rsa.tbsCertificate.subjectPublicKeyInfo
  let p256SPKI := p256.tbsCertificate.subjectPublicKeyInfo
  let ed25519SPKI := ed25519.tbsCertificate.subjectPublicKeyInfo
  let pssOnlySPKI : SubjectPublicKeyInfo :=
    { pss.tbsCertificate.subjectPublicKeyInfo with
      algorithm := { pss.signatureAlgorithm with encoded := ByteArray.empty } }

  check "CertificateVerify RSAE compatibility"
    (Signature.certificateVerifySchemeCompatible
      .rsaPssRsaeSha256 rsaSPKI)
  check "CertificateVerify RSAE rejects PSS-OID key"
    (!Signature.certificateVerifySchemeCompatible
      .rsaPssRsaeSha256 pssOnlySPKI)
  check "CertificateVerify PSS-OID compatibility"
    (Signature.certificateVerifySchemeCompatible
      .rsaPssPssSha256 pssOnlySPKI)
  check "CertificateVerify PSS-OID rejects RSAE key"
    (!Signature.certificateVerifySchemeCompatible
      .rsaPssPssSha256 rsaSPKI)
  check "CertificateVerify P-256 compatibility"
    (Signature.certificateVerifySchemeCompatible
      .ecdsaSecp256r1Sha256 p256SPKI)
  check "CertificateVerify Ed25519 compatibility"
    (Signature.certificateVerifySchemeCompatible
      .ed25519 ed25519SPKI)
  check "CertificateVerify key-type mismatch"
    (!Signature.certificateVerifySchemeCompatible
      .ecdsaSecp256r1Sha256 ed25519SPKI)

def main : IO Unit := do
  testConversions
  testServerCertificateVerifyContent
  testEd25519RFC8032
  testPSSParameterParsing

  let rsa ← readCertificate "Test/Fixtures/X509/rsa2048.pem"
  let p256 ← readCertificate "Test/Fixtures/X509/p256.pem"
  let ed25519 ← readCertificate "Test/Fixtures/X509/ed25519.pem"
  let pss ← readCertificate "Test/Fixtures/Signature/rsa-pss.pem"

  testCertificateVerifySchemeCompatibility rsa p256 ed25519 pss
  checkCertificateSignature "RSA PKCS#1 v1.5" rsa
  checkCertificateSignature "ECDSA P-256" p256
  checkCertificateSignature "Ed25519" ed25519
  checkCertificateSignature "RSA-PSS" pss

  testECDSAParser p256
  let rsaKey ← requireRSA "RSA PKCS#1 v1.5" rsa
  let pssKey ← requireRSA "RSA-PSS" pss
  testPKCS1 rsa rsaKey
  testPSS pss pssKey

  check "RSA PKCS#1 wrong public key"
    (!Signature.verifyX509 rsa.signatureAlgorithm
      pss.tbsCertificate.subjectPublicKeyInfo
      rsa.tbsCertificate.encoded rsa.signature)
  check "RSA-PSS wrong public key"
    (!Signature.verifyX509 pss.signatureAlgorithm
      rsa.tbsCertificate.subjectPublicKeyInfo
      pss.tbsCertificate.encoded pss.signature)
  let pssOnlyAlgorithm : AlgorithmIdentifier :=
    { pss.signatureAlgorithm with
      parameters := none
      encoded := ByteArray.empty }
  let pssOnlySPKI : SubjectPublicKeyInfo :=
    { pss.tbsCertificate.subjectPublicKeyInfo with
      algorithm := pssOnlyAlgorithm }
  check "PSS-only RSA key rejects PKCS#1 v1.5"
    (!Signature.verifyX509 rsa.signatureAlgorithm pssOnlySPKI
      rsa.tbsCertificate.encoded rsa.signature)
  check "signature scheme/key-type mismatch"
    (!Signature.verify .ecdsaP256Sha256
      ed25519.tbsCertificate.subjectPublicKeyInfo.key
      p256.tbsCertificate.encoded p256.signature)
  check "PSS signature rejected as PKCS#1 v1.5"
    (!Signature.verify .rsaPKCS1v15Sha256 (.rsa pssKey)
      pss.tbsCertificate.encoded pss.signature)
  check "PKCS#1 v1.5 signature rejected as PSS"
    (!Signature.verify (.rsaPSSSha256 32) (.rsa rsaKey)
      rsa.tbsCertificate.encoded rsa.signature)

  IO.println "all X.509 signature verification assertions passed"
