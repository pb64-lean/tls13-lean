module

public import HaclStar.Hex
public import TLS13.X509

public section

/-!
Pure known-answer tests for RFC 5929 `tls-server-end-point`.
-/

open TLS13.X509

private def check (label : String) (condition : Bool) : IO Unit := do
  unless condition do
    throw (IO.userError s!"{label}: assertion failed")

private def checkDigest
    (label : String) (got : ByteArray) (expectedHex : String) : IO Unit := do
  let gotHex := HaclStar.Hex.encode got
  unless gotHex == expectedHex do
    throw (IO.userError s!"{label}: got {gotHex}, expected {expectedHex}")

private def readCertificate (name : String) : IO Certificate := do
  let path := s!"Test/Fixtures/X509/{name}.pem"
  let text ← IO.FS.readFile path
  match Certificate.decodePEM text with
  | .ok certificates =>
    if certificates.size != 1 then
      throw (IO.userError s!"{path}: expected exactly one certificate")
    pure certificates[0]!
  | .error error => throw (IO.userError s!"{path}: {error}")

private def algorithm
    (oid : OID) (parameters : Option DER.TLV := none) : AlgorithmIdentifier :=
  { oid, parameters, encoded := ByteArray.empty }

private def oid (arcs : Array Nat) : OID := { arcs }

private def pssParameters (hashLastArc : UInt8) : DER.TLV :=
  -- RSASSA-PSS-params containing only
  -- [0] EXPLICIT AlgorithmIdentifier(id-sha256/id-sha384/id-sha512, NULL).
  let bytes := ByteArray.mk #[
    0x30, 0x11,
      0xa0, 0x0f,
        0x30, 0x0d,
          0x06, 0x09, 0x60, 0x86, 0x48, 0x01, 0x65, 0x03, 0x04, 0x02,
          hashLastArc,
          0x05, 0x00
  ]
  match DER.decode bytes with
  | .ok value => value
  | .error error => panic! s!"invalid test PSS DER: {error}"

private def withAlgorithm
    (certificate : Certificate) (signatureAlgorithm : AlgorithmIdentifier) :
    Certificate :=
  { certificate with signatureAlgorithm }

private def testFixtureKATs : IO Certificate := do
  let rsa ← readCertificate "rsa2048"
  let p256 ← readCertificate "p256"
  let ed25519 ← readCertificate "ed25519"

  check "RSA fixture selects SHA-256"
    (ChannelBinding.signatureHashAlgorithm rsa.signatureAlgorithm == .sha256)
  checkDigest "RSA exact DER SHA-256"
    (ChannelBinding.tlsServerEndPoint rsa)
    "76ded94d064ce19d8f8249f22c7f4185b996f2e6c565e4252a26c584643c1974"

  check "P-256 fixture selects SHA-256"
    (ChannelBinding.signatureHashAlgorithm p256.signatureAlgorithm == .sha256)
  checkDigest "P-256 exact DER SHA-256"
    (ChannelBinding.tlsServerEndPoint p256)
    "61a30c463b868f65c9e4b981b50b0bd7738852abdfad9024b592a7ef91962e39"

  -- Ed25519 exposes no separate signature digest, so the documented unknown
  -- algorithm fallback is SHA-256.
  check "Ed25519 fixture selects SHA-256 fallback"
    (ChannelBinding.signatureHashAlgorithm ed25519.signatureAlgorithm == .sha256)
  checkDigest "Ed25519 exact DER SHA-256 fallback"
    (ChannelBinding.tlsServerEndPoint ed25519)
    "fc004bfc4c5c744327350f514df7ed43270b3e6006d0656ade44c87145947b40"
  pure rsa

private def testDirectSelection (certificate : Certificate) : IO Unit := do
  let rsaSha384 := algorithm (oid #[1, 2, 840, 113549, 1, 1, 12])
  let rsaSha512 := algorithm (oid #[1, 2, 840, 113549, 1, 1, 13])
  let ecdsaSha384 := algorithm (oid #[1, 2, 840, 10045, 4, 3, 3])
  let ecdsaSha512 := algorithm (oid #[1, 2, 840, 10045, 4, 3, 4])

  check "RSA SHA-384 selection"
    (ChannelBinding.signatureHashAlgorithm rsaSha384 == .sha384)
  check "RSA SHA-512 selection"
    (ChannelBinding.signatureHashAlgorithm rsaSha512 == .sha512)
  check "ECDSA SHA-384 selection"
    (ChannelBinding.signatureHashAlgorithm ecdsaSha384 == .sha384)
  check "ECDSA SHA-512 selection"
    (ChannelBinding.signatureHashAlgorithm ecdsaSha512 == .sha512)

  check "SHA-384 digest dispatch"
    (ChannelBinding.tlsServerEndPoint (withAlgorithm certificate rsaSha384) ==
      HaclStar.sha384 certificate.encoded)
  check "SHA-512 digest dispatch"
    (ChannelBinding.tlsServerEndPoint (withAlgorithm certificate rsaSha512) ==
      HaclStar.sha512 certificate.encoded)

private def testPSSSelection (certificate : Certificate) : IO Unit := do
  let pssOID := oid #[1, 2, 840, 113549, 1, 1, 10]
  let pss256 := algorithm pssOID (some (pssParameters 0x01))
  let pss384 := algorithm pssOID (some (pssParameters 0x02))
  let pss512 := algorithm pssOID (some (pssParameters 0x03))
  let pssDefault := algorithm pssOID

  check "PSS SHA-256 selection"
    (ChannelBinding.signatureHashAlgorithm pss256 == .sha256)
  check "PSS SHA-384 selection"
    (ChannelBinding.signatureHashAlgorithm pss384 == .sha384)
  check "PSS SHA-512 selection"
    (ChannelBinding.signatureHashAlgorithm pss512 == .sha512)
  check "PSS default SHA-1 upgrades to SHA-256"
    (ChannelBinding.signatureHashAlgorithm pssDefault == .sha256)
  check "PSS SHA-256 digest dispatch"
    (ChannelBinding.tlsServerEndPoint (withAlgorithm certificate pss256) ==
      HaclStar.sha256 certificate.encoded)
  check "PSS SHA-384 digest dispatch"
    (ChannelBinding.tlsServerEndPoint (withAlgorithm certificate pss384) ==
      HaclStar.sha384 certificate.encoded)
  check "PSS SHA-512 digest dispatch"
    (ChannelBinding.tlsServerEndPoint (withAlgorithm certificate pss512) ==
      HaclStar.sha512 certificate.encoded)

  let emptyParameters ←
    match DER.decode (ByteArray.mk #[0x30, 0x00]) with
    | .ok value => pure value
    | .error error => throw (IO.userError s!"PSS default test setup: {error}")
  let explicitDefaults := algorithm pssOID (some emptyParameters)
  check "PSS empty parameters default SHA-1 upgrades to SHA-256"
    (ChannelBinding.signatureHashAlgorithm explicitDefaults == .sha256)

  let malformedParameters ←
    match DER.decode (ByteArray.mk #[0x05, 0x00]) with
    | .ok value => pure value
    | .error error => throw (IO.userError s!"malformed PSS test setup: {error}")
  let malformed := algorithm pssOID (some malformedParameters)
  check "malformed PSS fallback"
    (ChannelBinding.signatureHashAlgorithm malformed == .sha256)

  let badHashParameters := ByteArray.mk #[
    0x30, 0x12,
      0xa0, 0x10,
        0x30, 0x0e,
          0x06, 0x09, 0x60, 0x86, 0x48, 0x01, 0x65, 0x03, 0x04, 0x02,
          0x03,
          0x02, 0x01, 0x00
  ]
  let badHashParameters ←
    match DER.decode badHashParameters with
    | .ok value => pure value
    | .error error => throw (IO.userError s!"bad PSS hash test setup: {error}")
  let badHash := algorithm pssOID (some badHashParameters)
  check "PSS hash with malformed AlgorithmIdentifier parameters fallback"
    (ChannelBinding.signatureHashAlgorithm badHash == .sha256)

  -- A valid SHA-512 [0] followed by a malformed [1] proves that the selector
  -- validates the complete PSS parameter structure before retaining SHA-512.
  let badMaskParameters := ByteArray.mk #[
    0x30, 0x15,
      0xa0, 0x0f,
        0x30, 0x0d,
          0x06, 0x09, 0x60, 0x86, 0x48, 0x01, 0x65, 0x03, 0x04, 0x02,
          0x03,
          0x05, 0x00,
      0xa1, 0x02, 0x05, 0x00
  ]
  let badMaskParameters ←
    match DER.decode badMaskParameters with
    | .ok value => pure value
    | .error error => throw (IO.userError s!"bad PSS mask test setup: {error}")
  let badMask := algorithm pssOID (some badMaskParameters)
  check "PSS malformed MGF1 field fallback"
    (ChannelBinding.signatureHashAlgorithm badMask == .sha256)

private def testFallbackSelection (certificate : Certificate) : IO Unit := do
  let md5 := algorithm (oid #[1, 2, 840, 113549, 1, 1, 4])
  let sha1 := algorithm (oid #[1, 2, 840, 113549, 1, 1, 5])
  let unknown := algorithm (oid #[1, 2, 3, 4, 5])
  for (label, candidate) in #[
      ("MD5", md5),
      ("SHA-1", sha1),
      ("unknown", unknown)
    ] do
    check s!"{label} selection fallback"
      (ChannelBinding.signatureHashAlgorithm candidate == .sha256)
    check s!"{label} digest fallback"
      (ChannelBinding.tlsServerEndPoint (withAlgorithm certificate candidate) ==
        HaclStar.sha256 certificate.encoded)

  let integerParameter ←
    match DER.decode (ByteArray.mk #[0x02, 0x01, 0x00]) with
    | .ok value => pure value
    | .error error => throw (IO.userError s!"parameter test setup: {error}")
  let malformedRsaSha512 :=
    algorithm (oid #[1, 2, 840, 113549, 1, 1, 13]) (some integerParameter)
  let nullParameter ←
    match DER.decode (ByteArray.mk #[0x05, 0x00]) with
    | .ok value => pure value
    | .error error => throw (IO.userError s!"parameter test setup: {error}")
  let malformedEcdsaSha512 :=
    algorithm (oid #[1, 2, 840, 10045, 4, 3, 4]) (some nullParameter)
  check "malformed RSA SHA-512 parameters fallback"
    (ChannelBinding.signatureHashAlgorithm malformedRsaSha512 == .sha256)
  check "malformed ECDSA SHA-512 parameters fallback"
    (ChannelBinding.signatureHashAlgorithm malformedEcdsaSha512 == .sha256)

def main : IO Unit := do
  let certificate ← testFixtureKATs
  testDirectSelection certificate
  testPSSSelection certificate
  testFallbackSelection certificate
  IO.println "all X.509 channel-binding assertions passed"
