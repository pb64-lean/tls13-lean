module

public import TLS13.X509

public section

/-!
OpenSSL chain fixtures and pure path-validation policy tests.
-/

open TLS13.X509

private def check (label : String) (condition : Bool) : IO Unit := do
  unless condition do
    throw (IO.userError s!"{label}: assertion failed")

private def readCertificate (name : String) : IO Certificate := do
  let path := s!"Test/Fixtures/Chain/{name}.pem"
  let text ← IO.FS.readFile path
  match Certificate.decodePEM text with
  | .ok certificates =>
    if certificates.size != 1 then
      throw (IO.userError s!"{path}: expected exactly one certificate")
    pure certificates[0]!
  | .error error =>
    throw (IO.userError s!"{path}: {error}")

private def expectVerified
    (label : String) (result : Except Chain.Failure Chain.VerifiedChain) :
    IO Chain.VerifiedChain :=
  match result with
  | .ok verified => pure verified
  | .error failure =>
    throw (IO.userError s!"{label}: unexpected failure: {failure}")

private def expectFailure
    (label : String) (result : Except Chain.Failure Chain.VerifiedChain)
    (expected : Chain.Failure) : IO Unit :=
  match result with
  | .error actual =>
    check label (actual == expected)
  | .ok _ =>
    throw (IO.userError s!"{label}: invalid chain was accepted")

private def atTestTime : IO Int := do
  match Time.ofComponents 2026 7 19 0 0 0 with
  | .ok timestamp => pure timestamp.unixSeconds
  | .error error => throw (IO.userError s!"test timestamp: {error}")

private def flippedMiddle (bytes : ByteArray) : ByteArray :=
  bytes.set! (bytes.size / 2) (bytes.get! (bytes.size / 2) ^^^ 0x01)

private def withKeyCertSign
    (certificate : Certificate) (enabled : Bool) : Certificate :=
  match certificate.tbsCertificate.extensions.keyUsage with
  | none => certificate
  | some usage =>
    let extensions := {
      certificate.tbsCertificate.extensions with
      keyUsage := some {
        usage with value := { usage.value with keyCertSign := enabled }
      }
    }
    { certificate with
      tbsCertificate := { certificate.tbsCertificate with extensions } }

private def withDigitalSignature
    (certificate : Certificate) (enabled : Bool) : Certificate :=
  match certificate.tbsCertificate.extensions.keyUsage with
  | none => certificate
  | some usage =>
    let extensions := {
      certificate.tbsCertificate.extensions with
      keyUsage := some {
        usage with value := { usage.value with digitalSignature := enabled }
      }
    }
    { certificate with
      tbsCertificate := { certificate.tbsCertificate with extensions } }

private def withPathLen
    (certificate : Certificate) (pathLen : Option Nat) : Certificate :=
  match certificate.tbsCertificate.extensions.basicConstraints with
  | none => certificate
  | some constraints =>
    let extensions := {
      certificate.tbsCertificate.extensions with
      basicConstraints := some {
        constraints with
        value := { constraints.value with pathLenConstraint := pathLen }
      }
    }
    { certificate with
      tbsCertificate := { certificate.tbsCertificate with extensions } }

private def withCriticalUnknown (certificate : Certificate) : Certificate :=
  let unknown : RawExtension := {
    oid := { arcs := #[1, 3, 6, 1, 4, 1, 55555, 5] }
    critical := true
    valueDER := ByteArray.mk #[0x05, 0x00]
    encoded := ByteArray.empty
  }
  let extensions := {
    certificate.tbsCertificate.extensions with
    unhandled := certificate.tbsCertificate.extensions.unhandled.push unknown
  }
  { certificate with
    tbsCertificate := { certificate.tbsCertificate with extensions } }

private def withSubject
    (certificate : Certificate) (subject : Name) : Certificate :=
  { certificate with
    tbsCertificate := { certificate.tbsCertificate with subject } }

private def testTrustStorePEM (validRoot pathLenRoot : Certificate) :
    IO Unit := do
  let first ← IO.FS.readFile "Test/Fixtures/Chain/valid-root.pem"
  let second ← IO.FS.readFile "Test/Fixtures/Chain/pathlen-root.pem"
  let store ←
    match Chain.TrustStore.decodePEM (first ++ "\n" ++ second) with
    | .ok store => pure store
    | .error error =>
      throw (IO.userError s!"trust bundle: unexpected error: {error}")
  check "multi-anchor PEM count" (store.anchors.size == 2)
  check "multi-anchor PEM order"
    (store.anchors[0]!.encoded == validRoot.encoded &&
      store.anchors[1]!.encoded == pathLenRoot.encoded)
  match Chain.TrustStore.decodePEM "not a certificate" with
  | .error _ => pure ()
  | .ok _ => throw (IO.userError "empty trust bundle was accepted")

private def testValidPath
    (now : Int) (leaf intermediate root : Certificate) : IO Unit := do
  let trust : Chain.TrustStore := { anchors := #[root] }
  let verified ← expectVerified "valid three-certificate chain"
    (Chain.validate now leaf #[intermediate] trust)
  check "verified leaf retained" (verified.leaf.encoded == leaf.encoded)
  check "verified anchor retained" (verified.anchor.encoded == root.encoded)
  check "leaf-to-anchor path length" (verified.path.size == 3)
  check "leaf-to-anchor path order"
    (verified.path[0]!.encoded == leaf.encoded &&
      verified.path[1]!.encoded == intermediate.encoded &&
      verified.path[2]!.encoded == root.encoded)
  check "leaf issuer raw DER matches intermediate subject"
    (leaf.tbsCertificate.issuer.encoded ==
      intermediate.tbsCertificate.subject.encoded)
  check "intermediate issuer raw DER matches root subject"
    (intermediate.tbsCertificate.issuer.encoded ==
      root.tbsCertificate.subject.encoded)

  let sentRoot ← expectVerified "server-presented trusted root"
    (Chain.validate now leaf #[intermediate, root] trust)
  check "presented root terminates at exact store anchor"
    (sentRoot.anchor.encoded == root.encoded && sentRoot.path.size == 3)

  -- Validity endpoints are inclusive.
  let _ ← expectVerified "notBefore boundary"
    (Chain.validate leaf.tbsCertificate.validity.notBefore.unixSeconds
      leaf #[intermediate] trust)
  let _ ← expectVerified "notAfter boundary"
    (Chain.validate leaf.tbsCertificate.validity.notAfter.unixSeconds
      leaf #[intermediate] trust)

  -- A self-signed certificate terminates only when the exact certificate is
  -- an anchor. Its self-signature is not treated as another path link.
  let signingRoot := withDigitalSignature root true
  let direct ← expectVerified "direct self-signed TLS target anchor"
    (Chain.validate now signingRoot #[] { anchors := #[signingRoot] })
  check "direct anchor path" (direct.path.size == 1)
  expectFailure "self-signed target KeyUsage lacks digitalSignature"
    (Chain.validate now root #[] trust)
    (.leafDigitalSignatureMissing root.tbsCertificate.serialNumber)
  expectFailure "untrusted self-signed TLS target"
    (Chain.validate now signingRoot #[] { anchors := #[] })
    (.unknownIssuer signingRoot.tbsCertificate.serialNumber)

private def testBacktracking
    (now : Int) (leaf intermediate root wrongIssuer : Certificate) : IO Unit := do
  -- Give an unrelated wrong-key certificate the same parsed subject Name. It
  -- is searched first and fails signature verification; the valid second
  -- candidate must still be tried.
  let sameNameWrongKey := withSubject wrongIssuer intermediate.tbsCertificate.subject
  let verified ← expectVerified "same-name issuer backtracking"
    (Chain.validate now leaf #[sameNameWrongKey, intermediate] { anchors := #[root] })
  check "backtracking chose valid intermediate"
    (verified.path[1]!.encoded == intermediate.encoded)

private def testFailures
    (now : Int)
    (validLeaf validIntermediate validRoot : Certificate)
    (notCALeaf notCAIntermediate : Certificate)
    (expiredLeaf expiredIntermediate : Certificate)
    (pathLenLeaf pathLenIntermediate pathLenRoot : Certificate) : IO Unit := do
  expectFailure "unknown root"
    (Chain.validate now validLeaf #[validIntermediate] { anchors := #[] })
    (.unknownIssuer validIntermediate.tbsCertificate.serialNumber)

  expectFailure "intermediate is not a CA"
    (Chain.validate now notCALeaf #[notCAIntermediate]
      { anchors := #[validRoot] })
    (.notCA notCAIntermediate.tbsCertificate.serialNumber)

  expectFailure "expired intermediate"
    (Chain.validate now expiredLeaf #[expiredIntermediate]
      { anchors := #[validRoot] })
    (.expired expiredIntermediate.tbsCertificate.serialNumber
      expiredIntermediate.tbsCertificate.validity.notAfter.unixSeconds now)

  expectFailure "root pathLenConstraint"
    (Chain.validate now pathLenLeaf #[pathLenIntermediate]
      { anchors := #[pathLenRoot] })
    (.pathLenExceeded pathLenRoot.tbsCertificate.serialNumber 0 1)

  let badSignature := {
    validLeaf with signature := flippedMiddle validLeaf.signature
  }
  expectFailure "bad leaf signature"
    (Chain.validate now badSignature #[validIntermediate]
      { anchors := #[validRoot] })
    (.badSignature validLeaf.tbsCertificate.serialNumber
      validIntermediate.tbsCertificate.serialNumber)

  let noCertificateSigning := withKeyCertSign validIntermediate false
  expectFailure "issuer KeyUsage lacks keyCertSign"
    (Chain.validate now validLeaf #[noCertificateSigning]
      { anchors := #[validRoot] })
    (.keyCertSignMissing validIntermediate.tbsCertificate.serialNumber)

  let noDigitalSignature := withDigitalSignature validLeaf false
  expectFailure "leaf KeyUsage lacks digitalSignature"
    (Chain.validate now noDigitalSignature #[validIntermediate]
      { anchors := #[validRoot] })
    (.leafDigitalSignatureMissing validLeaf.tbsCertificate.serialNumber)

  let rootWithoutCertificateSigning := withKeyCertSign validRoot false
  expectFailure "anchor KeyUsage lacks keyCertSign"
    (Chain.validate now validLeaf #[validIntermediate]
      { anchors := #[rootWithoutCertificateSigning] })
    (.keyCertSignMissing validRoot.tbsCertificate.serialNumber)

  let unknownCritical := withCriticalUnknown validLeaf
  expectFailure "unhandled critical extension"
    (Chain.validate now unknownCritical #[validIntermediate]
      { anchors := #[validRoot] })
    (.unhandledCriticalExtension validLeaf.tbsCertificate.serialNumber
      { arcs := #[1, 3, 6, 1, 4, 1, 55555, 5] })

  let criticalAnchor := withCriticalUnknown validRoot
  expectFailure "unhandled critical extension on anchor"
    (Chain.validate now validLeaf #[validIntermediate]
      { anchors := #[criticalAnchor] })
    (.unhandledCriticalExtension validRoot.tbsCertificate.serialNumber
      { arcs := #[1, 3, 6, 1, 4, 1, 55555, 5] })

  expectFailure "not-yet-valid leaf"
    (Chain.validate
      (validLeaf.tbsCertificate.validity.notBefore.unixSeconds - 1)
      validLeaf #[validIntermediate] { anchors := #[validRoot] })
    (.notYetValid validLeaf.tbsCertificate.serialNumber
      validLeaf.tbsCertificate.validity.notBefore.unixSeconds
      (validLeaf.tbsCertificate.validity.notBefore.unixSeconds - 1))

  expectFailure "maximum path depth"
    (Chain.validate now validLeaf #[validIntermediate]
      { anchors := #[validRoot] } 2)
    (.maximumDepthExceeded 2)

  let sameNameWrongKey :=
    withSubject notCAIntermediate validIntermediate.tbsCertificate.subject
  expectFailure "global issuer-attempt limit"
    (Chain.validate now validLeaf #[sameNameWrongKey, validIntermediate]
      { anchors := #[validRoot] } Chain.defaultMaximumDepth 1)
    (.maximumIssuerAttemptsExceeded 1)

  -- One intermediate is allowed at pathLen=1; the intermediate's own
  -- pathLen=0 also correctly permits an end-entity leaf.
  let _ ← expectVerified "pathLen inclusive allowance"
    (Chain.validate now validLeaf #[validIntermediate]
      { anchors := #[withPathLen validRoot (some 1)] })

def main : IO Unit := do
  let now ← atTestTime
  let validLeaf ← readCertificate "valid-leaf"
  let validIntermediate ← readCertificate "valid-intermediate"
  let validRoot ← readCertificate "valid-root"
  let notCALeaf ← readCertificate "not-ca-leaf"
  let notCAIntermediate ← readCertificate "not-ca-intermediate"
  let expiredLeaf ← readCertificate "expired-leaf"
  let expiredIntermediate ← readCertificate "expired-intermediate"
  let pathLenLeaf ← readCertificate "pathlen-leaf"
  let pathLenIntermediate ← readCertificate "pathlen-intermediate"
  let pathLenRoot ← readCertificate "pathlen-root"

  testTrustStorePEM validRoot pathLenRoot
  testValidPath now validLeaf validIntermediate validRoot
  testBacktracking now validLeaf validIntermediate validRoot notCAIntermediate
  testFailures now
    validLeaf validIntermediate validRoot
    notCALeaf notCAIntermediate
    expiredLeaf expiredIntermediate
    pathLenLeaf pathLenIntermediate pathLenRoot
  IO.println "all X.509 chain-validation assertions passed"
