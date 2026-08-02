module

public import TLS13.X509

public section

/-!
Strict DER/OID/PEM tests. The negative corpus deliberately covers BER forms
that a certificate parser must never accept.
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

private def hexNibble (value : UInt8) : Char :=
  let value := value.toNat
  if value < 10 then
    Char.ofNat ('0'.toNat + value)
  else
    Char.ofNat ('a'.toNat + value - 10)

private def hexEncode (bytes : ByteArray) : String :=
  bytes.foldl (fun out octet =>
    out.push (hexNibble (octet / 16)) |>.push (hexNibble (octet % 16))) ""

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
    throw (IO.userError
      s!"{label}:\n  got  {hexEncode got}\n  want {hexEncode want}")

private def repeated (count : Nat) (octet : UInt8 := 0) : ByteArray :=
  ByteArray.mk (Array.replicate count octet)

private def armor (label body newline : String) : String :=
  s!"-----BEGIN {label}-----{newline}{body}{newline}-----END {label}-----"

private def testDER : IO Unit := do
  let nestedBytes := h "3006020101040141"
  let nested ← expectOk "nested sequence" (DER.decode nestedBytes)
  check "sequence tag" (nested.tag == DER.Tag.sequence)
  checkBytes "sequence exact encoding" nested.encoded nestedBytes
  checkBytes "sequence contents" nested.contents (h "020101040141")
  let (integer, children) ← expectOk "sequence integer" nested.reader.readTLV
  check "integer tag" (integer.tag == DER.Tag.integer)
  checkBytes "integer exact encoding" integer.encoded (h "020101")
  let (octets, children) ← expectOk "sequence octets" children.readTLV
  check "octet-string tag" (octets.tag == DER.Tag.octetString)
  checkBytes "octet-string contents" octets.contents (h "41")
  discard <| expectOk "sequence children end" (children.requireEnd "SEQUENCE")

  let lengthCases : Array (String × ByteArray × Nat) := #[
    ("short length 127", h "047f" ++ repeated 127, 127),
    ("long length 128", h "048180" ++ repeated 128, 128),
    ("long length 255", h "0481ff" ++ repeated 255, 255),
    ("long length 256", h "04820100" ++ repeated 256, 256)
  ]
  for (label, encoded, expectedSize) in lengthCases do
    let value ← expectOk label (DER.decode encoded)
    check label (value.contents.size == expectedSize)
    checkBytes (label ++ " exact encoding") value.encoded encoded

  let high31 ← expectOk "high tag 31" (DER.decode (h "9f1f00"))
  check "high tag 31 class" (high31.tag.tagClass == .contextSpecific)
  check "high tag 31 number" (high31.tag.number == 31)
  check "high tag 31 primitive" (!high31.tag.constructed)
  let high128 ← expectOk "high tag 128" (DER.decode (h "bf810000"))
  check "high tag 128 class" (high128.tag.tagClass == .contextSpecific)
  check "high tag 128 number" (high128.tag.number == 128)
  check "high tag 128 constructed" high128.tag.constructed

  -- Exact-root decoding rejects a second value, while the cursor and decodeAll
  -- deliberately support bounded sequences of TLVs.
  let adjacent := h "0201010500"
  expectError "trailing TLV" (DER.decode adjacent)
  let values ← expectOk "decodeAll adjacent TLVs" (DER.decodeAll adjacent)
  check "decodeAll adjacent TLV count" (values.size == 2)
  let (first, cursor) ← expectOk "cursor first adjacent TLV" (DER.Reader.ofBytes adjacent).readTLV
  check "cursor first adjacent tag" (first.tag == DER.Tag.integer)
  let (second, cursor) ← expectOk "cursor second adjacent TLV" cursor.readTLV
  check "cursor second adjacent tag" (second.tag == DER.Tag.null)
  discard <| expectOk "cursor adjacent end" cursor.requireEnd

  -- A constructed value is framed without eagerly trusting its children.
  let malformedChildOuter ← expectOk "bounded outer framing" (DER.decode (h "30030402ff"))
  expectError "bounded child overrun" malformedChildOuter.reader.readTLV

  let malformed : Array (String × ByteArray) := #[
    ("empty input", ByteArray.empty),
    ("truncated identifier/length", h "02"),
    ("declared content overrun", h "040201"),
    ("truncated long length", h "0482"),
    ("partially truncated long length", h "048201"),
    ("indefinite length", h "30800000"),
    ("long form for short length", h "04817f" ++ repeated 127),
    ("long length leading zero", h "04820080" ++ repeated 128),
    ("reserved length ff", h "04ff"),
    ("non-minimal high tag", h "9f1e00"),
    ("leading zero high tag group", h "9f801f00"),
    ("unterminated high tag", h "9f81"),
    ("oversized high tag", h "9f" ++ repeated 17 0x81 ++ h "00"),
    ("end-of-contents tag", h "0000"),
    ("reserved universal tag", h "0f00"),
    ("primitive sequence", h "1000"),
    ("primitive set", h "1100"),
    ("constructed integer", h "2200"),
    ("constructed bit string", h "2300"),
    ("constructed octet string", h "2400"),
    ("constructed OID", h "26012a"),
    ("constructed UTF8String", h "2c00")
  ]
  for (label, encoded) in malformed do
    expectError label (DER.decode encoded)

  let canonicalForms := #[
    h "3000", h "3100", h "030100", h "0400", h "0c00", h "a000"
  ]
  for encoded in canonicalForms do
    discard <| expectOk ("canonical DER form " ++ hexEncode encoded) (DER.decode encoded)

private def testOID : IO Unit := do
  let cases : Array (String × ByteArray × Array Nat × String) := #[
    ("OID 0.0", h "060100", #[0, 0], "0.0"),
    ("OID 1.39", h "06014f", #[1, 39], "1.39"),
    ("OID 2.0", h "060150", #[2, 0], "2.0"),
    ("OID multi-octet first subidentifier", h "0603883703", #[2, 999, 3], "2.999.3"),
    ("sha256WithRSAEncryption", h "06092a864886f70d01010b",
      #[1, 2, 840, 113549, 1, 1, 11], "1.2.840.113549.1.1.11")
  ]
  for (label, encoded, arcs, dotted) in cases do
    let oid ← expectOk label (DER.decodeOID encoded)
    check (label ++ " arcs") (oid.arcs == arcs)
    check (label ++ " dotted") (toString oid == dotted)

  let malformed : Array (String × ByteArray) := #[
    ("empty OID", h "0600"),
    ("unterminated first OID subidentifier", h "060180"),
    ("unterminated later OID subidentifier", h "06022a86"),
    ("non-minimal first OID subidentifier", h "0602802a"),
    ("non-minimal later OID subidentifier", h "06032a8001"),
    ("oversized OID subidentifier", h "0622" ++ repeated 33 0x81 ++ h "00"),
    ("wrong OID tag", h "0500"),
    ("constructed OID tag", h "26012a")
  ]
  for (label, encoded) in malformed do
    expectError label (DER.decodeOID encoded)

  expectError "OID too few arcs" (OID.ofArcs #[1])
  expectError "OID invalid first arc" (OID.ofArcs #[3, 0])
  expectError "OID invalid second arc" (OID.ofArcs #[1, 40])
  let constant ← expectOk "checked OID construction" (OID.ofArcs #[2, 5, 4, 3])
  check "checked OID rendering" (toString constant == "2.5.4.3")

private def testPEM : IO Unit := do
  let tinyDER := h "3003020101"
  let tinyBase64 := "MAMCAQE="
  for (label, newline) in #[
      ("PEM LF", "\n"),
      ("PEM CRLF", "\r\n"),
      ("PEM CR", "\r")
    ] do
    let certificates ← expectOk label
      (PEM.decodeCertificates (armor "CERTIFICATE" tinyBase64 newline))
    check (label ++ " count") (certificates.size == 1)
    checkBytes (label ++ " DER") certificates[0]! tinyDER

  let whitespaceBody :=
    "explanatory text before\n" ++
    "-----BEGIN CERTIFICATE-----\n" ++
    "M A M C\tA Q E =\n" ++
    "-----END CERTIFICATE-----\n" ++
    "explanatory text after"
  let whitespaceCerts ← expectOk "PEM body whitespace/explanatory text"
    (PEM.decodeCertificates whitespaceBody)
  checkBytes "PEM body whitespace DER" whitespaceCerts[0]! tinyDER

  let boundaryWhitespace :=
    "-----BEGIN CERTIFICATE----- \t\r\n" ++
    tinyBase64 ++ "\r\n" ++
    "-----END CERTIFICATE-----\t "
  let boundaryWhitespaceCerts ← expectOk "PEM boundary trailing whitespace"
    (PEM.decodeCertificates boundaryWhitespace)
  checkBytes "PEM boundary trailing whitespace DER" boundaryWhitespaceCerts[0]! tinyDER

  let emptyLabelBlocks ← expectOk "generic PEM empty label"
    (PEM.decode (armor "" "TQ==" "\n"))
  check "generic PEM empty label count" (emptyLabelBlocks.size == 1)
  check "generic PEM empty label preserved" (emptyLabelBlocks[0]!.label == "")
  checkBytes "canonical two-pad Base64" emptyLabelBlocks[0]!.der ("M".toUTF8)

  let secondDER := h "0500"
  let mixedBundle :=
    armor "X509 CERTIFICATE" "BQA=" "\n" ++ "\n" ++
    armor "CERTIFICATE" tinyBase64 "\n" ++ "\n" ++
    armor "CERTIFICATE" "BQA=" "\n"
  let blocks ← expectOk "generic PEM mixed bundle" (PEM.decodeBlocks mixedBundle)
  check "generic PEM mixed bundle count" (blocks.size == 3)
  check "generic PEM historical label" (blocks[0]!.label == "X509 CERTIFICATE")
  checkBytes "generic PEM historical DER" blocks[0]!.der secondDER
  let certificates ← expectOk "certificate PEM projection" (PEM.decodeCertificates mixedBundle)
  check "certificate PEM projection count" (certificates.size == 2)
  checkBytes "certificate PEM first" certificates[0]! tinyDER
  checkBytes "certificate PEM second" certificates[1]! secondDER
  expectError "historical label is not CERTIFICATE"
    (PEM.decodeCertificates (armor "X509 CERTIFICATE" tinyBase64 "\n"))
  expectError "PEM text with no certificates"
    (PEM.decodeCertificates "only explanatory text")
  expectError "empty PEM certificate body"
    (PEM.decodeCertificates (armor "CERTIFICATE" "" "\n"))

  let malformed : Array (String × String) := #[
    ("unclosed PEM block",
      "-----BEGIN CERTIFICATE-----\nMAMCAQE="),
    ("mismatched PEM footer",
      "-----BEGIN CERTIFICATE-----\nMAMCAQE=\n-----END PUBLIC KEY-----"),
    ("nested PEM block",
      "-----BEGIN CERTIFICATE-----\n-----BEGIN CERTIFICATE-----\nMAMCAQE=\n" ++
        "-----END CERTIFICATE-----\n-----END CERTIFICATE-----"),
    ("stray PEM footer", "-----END CERTIFICATE-----"),
    ("malformed PEM begin", "-----BEGIN CERTIFICATE----\nMAMCAQE="),
    ("malformed PEM missing boundary space",
      "-----BEGINCERTIFICATE-----\nMAMCAQE=\n-----ENDCERTIFICATE-----\n" ++
        armor "CERTIFICATE" tinyBase64 "\n"),
    ("malformed PEM label leading separator",
      armor "-CERTIFICATE" tinyBase64 "\n"),
    ("malformed PEM label doubled separator",
      armor "X509--CERTIFICATE" tinyBase64 "\n"),
    ("invalid PEM Base64 alphabet", armor "CERTIFICATE" "MAMC$QE=" "\n"),
    ("invalid PEM Base64 length", armor "CERTIFICATE" "AAA" "\n"),
    ("internal PEM Base64 padding", armor "CERTIFICATE" "AA=A" "\n"),
    ("excess PEM Base64 padding", armor "CERTIFICATE" "A===" "\n"),
    ("nonzero two-pad bits", armor "CERTIFICATE" "AB==" "\n"),
    ("nonzero one-pad bits", armor "CERTIFICATE" "AAB=" "\n"),
    ("legacy PEM header",
      "-----BEGIN CERTIFICATE-----\nProc-Type: 4,ENCRYPTED\nMAMCAQE=\n" ++
        "-----END CERTIFICATE-----"),
    ("malformed later PEM block",
      armor "CERTIFICATE" tinyBase64 "\n" ++ "\n" ++
        "-----BEGIN CERTIFICATE-----\nMAMC$QE=\n-----END CERTIFICATE-----")
  ]
  for (label, text) in malformed do
    expectError label (PEM.decodeBlocks text)

def main : IO Unit := do
  testDER
  testOID
  testPEM
  IO.println "all strict DER/OID/PEM assertions passed"
