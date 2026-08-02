module

public import Std.Net.Addr
public import TLS13.X509.Certificate

public section

/-!
Pure server-name verification for PostgreSQL's `sslmode=verify-full`.

DNS identities are ASCII case-insensitive and support only a whole leftmost
wildcard label. Internationalized names are not converted: callers must pass
IDNA A-label (punycode) form. IP literals are converted to network-order bytes
and compared only with subjectAltName iPAddress values.
-/

namespace TLS13
namespace X509
namespace Hostname

inductive Failure where
  | invalidHost
  | nonASCIIHost
  | ipAddressMismatch
  | dnsSubjectAltNameMismatch
  | commonNameMissing
  | commonNameMismatch
  deriving Repr, BEq, DecidableEq

namespace Failure

def render : Failure → String
  | .invalidHost => "connection host is not a valid DNS name or IP literal"
  | .nonASCIIHost =>
      "connection host is non-ASCII; provide its IDNA A-label form"
  | .ipAddressMismatch =>
      "certificate subjectAltName does not contain the connection IP address"
  | .dnsSubjectAltNameMismatch =>
      "certificate subjectAltName does not match the connection DNS name"
  | .commonNameMissing =>
      "certificate has neither subjectAltName nor a Common Name"
  | .commonNameMismatch =>
      "certificate Common Name does not match the connection DNS name"

end Failure

instance : ToString Failure := ⟨Failure.render⟩

private def asciiLower (octet : UInt8) : UInt8 :=
  if octet ≥ 0x41 && octet ≤ 0x5a then octet + 0x20 else octet

private def isASCII (bytes : ByteArray) : Bool :=
  bytes.data.all (· < 0x80)

private def asciiCaseEqual (left right : ByteArray) : Bool := Id.run do
  if left.size != right.size then
    return false
  for index in [0:left.size] do
    if asciiLower (left.get! index) != asciiLower (right.get! index) then
      return false
  return true

private def countOctet (bytes : ByteArray) (wanted : UInt8) : Nat :=
  bytes.foldl (fun count octet => if octet == wanted then count + 1 else count) 0

/-- Match one certificate DNS identity against an ASCII reference hostname.

The only wildcard form is `*.` at the start with no other `*`. It consumes one
nonempty label and cannot cross a dot. -/
def dnsNameMatches (pattern host : String) : Bool := Id.run do
  let pattern := pattern.toUTF8
  let host := host.toUTF8
  if !isASCII pattern || !isASCII host then
    return false
  if asciiCaseEqual pattern host then
    return true
  if pattern.size < 3 ||
      pattern.get! 0 != 0x2a ||
      pattern.get! 1 != 0x2e ||
      countOctet pattern 0x2a != 1 then
    return false
  let suffix := pattern.extract 1 pattern.size
  if host.size ≤ suffix.size then
    return false
  let labelSize := host.size - suffix.size
  unless asciiCaseEqual suffix (host.extract labelSize host.size) do
    return false
  let leftmostLabel := host.extract 0 labelSize
  !leftmostLabel.isEmpty && !leftmostLabel.data.any (· == 0x2e)

private def splitIPv4Parts (input : ByteArray) : Option (Array ByteArray) :=
    Id.run do
  if input.isEmpty then
    return none
  let mut parts := #[]
  let mut start := 0
  for offset in [0:input.size] do
    if input.get! offset == 0x2e then
      if offset == start || parts.size == 3 then
        return none
      parts := parts.push (input.extract start offset)
      start := offset + 1
  if start == input.size then
    return none
  parts := parts.push (input.extract start input.size)
  if parts.isEmpty || parts.size > 4 then none else some parts

private def digitValue? (base : Nat) (octet : UInt8) : Option Nat :=
  let value? :=
    if octet ≥ 0x30 && octet ≤ 0x39 then
      some (octet.toNat - 0x30)
    else if octet ≥ 0x61 && octet ≤ 0x66 then
      some (octet.toNat - 0x61 + 10)
    else if octet ≥ 0x41 && octet ≤ 0x46 then
      some (octet.toNat - 0x41 + 10)
    else
      none
  value?.bind fun value => if value < base then some value else none

/-- Parse one `inet_aton`-style component. PostgreSQL deliberately accepts
legacy decimal, octal, and hexadecimal IPv4 spellings, so hostname
classification must recognize them before considering the input a DNS name. -/
private def parseIPv4Number (input : ByteArray) : Option Nat := Id.run do
  if input.isEmpty then
    return none
  let (base, start) :=
    if input.size > 2 && input.get! 0 == 0x30 &&
        (input.get! 1 == 0x78 || input.get! 1 == 0x58) then
      (16, 2)
    else if input.size > 1 && input.get! 0 == 0x30 then
      (8, 1)
    else
      (10, 0)
  if start == input.size then
    return none
  let mut value := 0
  for offset in [start:input.size] do
    let some digit := digitValue? base (input.get! offset)
      | return none
    value := value * base + digit
    if value > 0xffffffff then
      return none
  return some value

private def uint32Bytes (value : Nat) : ByteArray :=
  ByteArray.mk #[
    UInt8.ofNat (value >>> 24),
    UInt8.ofNat (value >>> 16),
    UInt8.ofNat (value >>> 8),
    UInt8.ofNat value
  ]

private def parseIPv4 (host : String) : Option ByteArray := do
  let parts ← splitIPv4Parts host.toUTF8
  let values ← parts.mapM parseIPv4Number
  let value ←
    match values.size with
    | 1 =>
      let value := values[0]!
      if value ≤ 0xffffffff then some value else none
    | 2 =>
      let first := values[0]!
      let second := values[1]!
      if first ≤ 0xff && second ≤ 0xffffff then
        some ((first <<< 24) ||| second)
      else none
    | 3 =>
      let first := values[0]!
      let second := values[1]!
      let third := values[2]!
      if first ≤ 0xff && second ≤ 0xff && third ≤ 0xffff then
        some ((first <<< 24) ||| (second <<< 16) ||| third)
      else none
    | 4 =>
      let first := values[0]!
      let second := values[1]!
      let third := values[2]!
      let fourth := values[3]!
      if first ≤ 0xff && second ≤ 0xff &&
          third ≤ 0xff && fourth ≤ 0xff then
        some ((first <<< 24) ||| (second <<< 16) |||
          (third <<< 8) ||| fourth)
      else none
    | _ => none
  pure (uint32Bytes value)

private def parseIPv6 (host : String) : Option ByteArray := do
  -- Std's parser accepts zone suffixes, but X.509 iPAddress contains only an
  -- address. Reject zones instead of silently discarding identity-bearing
  -- input.
  if host.toUTF8.data.any (· == 0x25) then
    none
  else
    let address ← Std.Net.IPv6Addr.ofString host
    let mut result := ByteArray.empty
    for segment in address.segments.toArray do
      result := result.push (UInt8.ofNat (segment.toNat >>> 8))
      result := result.push (UInt8.ofNat segment.toNat)
    pure result

/-- Parse an IPv4 or IPv6 literal into network-order bytes. IPv4 follows
libpq's deliberate `inet_aton` compatibility; IPv6 follows `inet_pton`. -/
def parseIPLiteral (host : String) : Option ByteArray :=
  (parseIPv4 host).orElse fun _ => parseIPv6 host

private def validateHost (host : String) : Except Failure String := do
  if host.isEmpty then
    throw .invalidHost
  let raw := host.toUTF8
  if raw.data.any (· == 0x00) then
    throw .invalidHost
  if !isASCII raw then
    throw .nonASCIIHost
  pure host

private def normalizeDNSHost (host : String) : Except Failure String := do
  let raw := host.toUTF8
  let normalized :=
    if raw.get! (raw.size - 1) == 0x2e then
      String.fromUTF8! (raw.extract 0 (raw.size - 1))
    else
      host
  if normalized.isEmpty then
    throw .invalidHost
  pure normalized

private def validDNSReference (host : String) : Bool := Id.run do
  let raw := host.toUTF8
  if raw.isEmpty || raw.get! 0 == 0x2e ||
      raw.get! (raw.size - 1) == 0x2e then
    return false
  let mut previousDot := false
  for octet in raw do
    if octet ≤ 0x20 || octet ≥ 0x7f ||
        octet == 0x2a || octet == 0x25 ||
        octet == 0x3a || octet == 0x2f ||
        octet == 0x5b || octet == 0x5c || octet == 0x5d then
      return false
    if octet == 0x2e then
      if previousDot then
        return false
      previousDot := true
    else
      previousDot := false
  return true

/-- Verify `host` against the leaf certificate using libpq-style identity
rules tightened to modern SAN semantics.

IP literals match only SAN iPAddress bytes. DNS names use only SAN dNSName
when the SAN extension is present at all; Common Name fallback is permitted
only when the certificate has no SAN extension. -/
def verifyHostname (host : String) (leaf : Certificate) :
    Except Failure Unit := do
  let host ← validateHost host
  match parseIPLiteral host with
  | some address =>
    let addresses :=
      match leaf.tbsCertificate.extensions.subjectAltName with
      | some san => san.value.ipAddresses
      | none => #[]
    unless addresses.any (· == address) do
      throw .ipAddressMismatch
  | none =>
    let host ← normalizeDNSHost host
    unless validDNSReference host do
      throw .invalidHost
    match leaf.tbsCertificate.extensions.subjectAltName with
    | some san =>
      unless san.value.dnsNames.any (dnsNameMatches · host) do
        throw .dnsSubjectAltNameMismatch
    | none =>
      let some commonName := leaf.tbsCertificate.subject.commonNames[0]?
        | throw .commonNameMissing
      unless dnsNameMatches commonName host do
        throw .commonNameMismatch

end Hostname
end X509
end TLS13
