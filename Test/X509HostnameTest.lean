module

public import TLS13.X509

public section

/-!
Pure libpq-style server-name verification tests.
-/

open TLS13.X509

private def check (label : String) (condition : Bool) : IO Unit := do
  unless condition do
    throw (IO.userError s!"{label}: assertion failed")

private def readCertificate (path : String) : IO Certificate := do
  let text ← IO.FS.readFile path
  match Certificate.decodePEM text with
  | .ok certificates =>
    if certificates.size != 1 then
      throw (IO.userError s!"{path}: expected exactly one certificate")
    pure certificates[0]!
  | .error error => throw (IO.userError s!"{path}: {error}")

private def expectMatch
    (label host : String) (certificate : Certificate) : IO Unit :=
  match Hostname.verifyHostname host certificate with
  | .ok () => pure ()
  | .error failure =>
    throw (IO.userError s!"{label}: unexpected failure: {failure}")

private def expectFailure
    (label host : String) (certificate : Certificate)
    (expected : Hostname.Failure) : IO Unit :=
  match Hostname.verifyHostname host certificate with
  | .error actual => check label (actual == expected)
  | .ok () => throw (IO.userError s!"{label}: mismatched hostname was accepted")

private def withSAN
    (certificate : Certificate) (dnsNames : Array String)
    (ipAddresses : Array ByteArray) : Certificate :=
  let san : ParsedExtension SubjectAltName := {
    critical := false
    value := { dnsNames, ipAddresses }
    encoded := ByteArray.empty
  }
  let extensions := {
    certificate.tbsCertificate.extensions with subjectAltName := some san
  }
  { certificate with
    tbsCertificate := { certificate.tbsCertificate with extensions } }

private def withoutSAN (certificate : Certificate) : Certificate :=
  let extensions := {
    certificate.tbsCertificate.extensions with subjectAltName := none
  }
  { certificate with
    tbsCertificate := { certificate.tbsCertificate with extensions } }

private def withCommonNames
    (certificate : Certificate) (commonNames : Array String) : Certificate :=
  let subject := { certificate.tbsCertificate.subject with commonNames }
  { certificate with
    tbsCertificate := { certificate.tbsCertificate with subject } }

private def testDNSNames (rsa : Certificate) : IO Unit := do
  expectMatch "exact SAN dNSName" "rsa.example.test" rsa
  expectMatch "case-insensitive SAN dNSName" "RSA.Example.TEST" rsa
  expectMatch "single trailing DNS dot" "rsa.example.test." rsa
  expectFailure "wrong SAN dNSName" "other.example.test" rsa
    .dnsSubjectAltNameMismatch

  let wildcard := withSAN rsa #["*.example.com"] #[]
  expectMatch "wildcard one label" "a.example.com" wildcard
  expectMatch "wildcard case-insensitive suffix" "A.Example.COM" wildcard
  expectFailure "wildcard cannot cross dot" "a.b.example.com" wildcard
    .dnsSubjectAltNameMismatch
  expectFailure "wildcard cannot match apex" "example.com" wildcard
    .dnsSubjectAltNameMismatch
  expectFailure "wildcard label cannot be empty" ".example.com" wildcard
    .invalidHost

  for pattern in #[
      "foo*.example.com",
      "*foo.example.com",
      "*.*.example.com",
      "example.*.com"
    ] do
    let candidate := withSAN rsa #[pattern] #[]
    expectFailure s!"forbidden wildcard {pattern}" "foobar.example.com" candidate
      .dnsSubjectAltNameMismatch

private def testIPAddresses (rsa p256 : Certificate) : IO Unit := do
  expectMatch "IPv4 SAN exact" "127.0.0.1" rsa
  expectFailure "IPv4 SAN mismatch" "127.0.0.2" rsa .ipAddressMismatch

  -- libpq deliberately recognizes inet_aton-compatible IPv4 spellings.
  expectMatch "IPv4 shorthand" "127.1" rsa
  expectMatch "IPv4 octal" "0177.0.0.1" rsa
  expectMatch "IPv4 hexadecimal" "0x7f000001" rsa
  expectFailure "IPv4 trailing dot is a DNS reference" "127.0.0.1." rsa
    .dnsSubjectAltNameMismatch

  expectMatch "IPv6 compressed" "2001:db8::1" p256
  expectMatch "IPv6 expanded/case-insensitive" "2001:0DB8:0:0:0:0:0:1" p256
  expectFailure "IPv6 SAN mismatch" "2001:db8::2" p256 .ipAddressMismatch
  expectFailure "IPv6 zone rejected" "2001:db8::1%eth0" p256 .invalidHost
  expectFailure "bracketed IPv6 rejected" "[2001:db8::1]" p256 .invalidHost

  let mappedIPv6 := withSAN rsa #[] #[ByteArray.mk #[
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0xff, 0xff, 127, 0, 0, 1
  ]]
  expectMatch "IPv4-mapped IPv6 SAN exact" "::ffff:127.0.0.1" mappedIPv6
  expectFailure "IPv4 does not match 16-byte mapped IPv6 SAN"
    "127.0.0.1" mappedIPv6 .ipAddressMismatch

  let dnsOnlyIPText := withSAN rsa #["127.0.0.1"] #[]
  expectFailure "IP does not match dNSName" "127.0.0.1" dnsOnlyIPText
    .ipAddressMismatch

  let cnOnlyIPText :=
    withCommonNames (withoutSAN rsa) #["127.0.0.1"]
  expectFailure "IP does not match Common Name" "127.0.0.1" cnOnlyIPText
    .ipAddressMismatch

private def testSANPrecedence
    (rsa expiredLeaf commonNameOnly : Certificate) : IO Unit := do
  -- This real fixture has CN=expired-path.example.test but
  -- SAN dNSName=chain.example.test.
  expectMatch "real SAN identity" "chain.example.test" expiredLeaf
  expectFailure "SAN suppresses matching CN"
    "expired-path.example.test" expiredLeaf .dnsSubjectAltNameMismatch

  let ipOnlySAN :=
    withCommonNames (withSAN rsa #[] #[ByteArray.mk #[127, 0, 0, 1]])
      #["cn.example.test"]
  expectFailure "SAN without dNSName still suppresses CN"
    "cn.example.test" ipOnlySAN .dnsSubjectAltNameMismatch

  expectMatch "CN fallback without SAN"
    "m3-rsa-pss.example.test" commonNameOnly
  expectMatch "CN fallback case-insensitive"
    "M3-RSA-PSS.Example.TEST" commonNameOnly
  expectMatch "CN fallback trailing dot"
    "m3-rsa-pss.example.test." commonNameOnly
  expectFailure "CN fallback mismatch"
    "other.example.test" commonNameOnly .commonNameMismatch

  let wildcardCN :=
    withCommonNames commonNameOnly #["*.fallback.example"]
  expectMatch "CN wildcard fallback" "one.fallback.example" wildcardCN
  expectFailure "CN wildcard depth" "a.b.fallback.example" wildcardCN
    .commonNameMismatch

  let noIdentity := withCommonNames commonNameOnly #[]
  expectFailure "missing CN without SAN"
    "missing.example.test" noIdentity .commonNameMissing

private def testInvalidHosts (rsa : Certificate) : IO Unit := do
  expectFailure "empty host" "" rsa .invalidHost
  expectFailure "root dot host" "." rsa .invalidHost
  expectFailure "double dot host" "rsa..example.test" rsa .invalidHost
  expectFailure "reference wildcard" "*.example.test" rsa .invalidHost
  expectFailure "non-ASCII host" "éxample.test" rsa .nonASCIIHost

def main : IO Unit := do
  let rsa ← readCertificate "Test/Fixtures/X509/rsa2048.pem"
  let p256 ← readCertificate "Test/Fixtures/X509/p256.pem"
  let expiredLeaf ←
    readCertificate "Test/Fixtures/Chain/expired-leaf.pem"
  let commonNameOnly ←
    readCertificate "Test/Fixtures/Signature/rsa-pss.pem"

  testDNSNames rsa
  testIPAddresses rsa p256
  testSANPrecedence rsa expiredLeaf commonNameOnly
  testInvalidHosts rsa
  IO.println "all X.509 hostname-verification assertions passed"
