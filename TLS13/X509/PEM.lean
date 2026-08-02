module

public section

/-!
RFC 7468-style textual armor decoding.

The scanner accepts LF, CRLF, or CR line endings, explanatory text outside
blocks, multiple blocks, and ASCII whitespace within the Base64 body. Armor
boundaries and labels are exact and Base64 is required to be canonical.
-/

namespace TLS13
namespace X509
namespace PEM

/-- One decoded textual-armor block. -/
structure Block where
  label : String
  der : ByteArray
  deriving BEq, Inhabited

private structure OpenBlock where
  label : String
  body : ByteArray

private def beginPrefix : String := "-----BEGIN "
private def endPrefix : String := "-----END "
private def boundarySuffix : String := "-----"

/-- Split all three newline conventions without changing other bytes. -/
private def splitLines (text : String) : Array String := Id.run do
  let raw := text.toUTF8
  let mut lines := #[]
  let mut start := 0
  let mut offset := 0
  while offset < raw.size do
    let octet := raw.get! offset
    if octet == 0x0a || octet == 0x0d then
      lines := lines.push (String.fromUTF8! (raw.extract start offset))
      if octet == 0x0d && offset + 1 < raw.size && raw.get! (offset + 1) == 0x0a then
        offset := offset + 2
      else
        offset := offset + 1
      start := offset
    else
      offset := offset + 1
  lines.push (String.fromUTF8! (raw.extract start raw.size))

private def isLabelChar (octet : UInt8) : Bool :=
  (octet ≥ 0x21 && octet ≤ 0x2c) || (octet ≥ 0x2e && octet ≤ 0x7e)

/-- RFC 7468 label shape: empty, or printable label characters separated by a
single space or hyphen with no leading, trailing, or doubled separators. -/
private def validLabel (label : String) : Bool := Id.run do
  let raw := label.toUTF8
  if raw.isEmpty then
    return true
  let mut needChar := true
  for octet in raw do
    if isLabelChar octet then
      needChar := false
    else if (octet == 0x20 || octet == 0x2d) && !needChar then
      needChar := true
    else
      return false
  return !needChar

private def stripBoundaryTrailingWhitespace (line : String) : String := Id.run do
  let raw := line.toUTF8
  let mut stop := raw.size
  while stop > 0 && (raw.get! (stop - 1) == 0x20 || raw.get! (stop - 1) == 0x09) do
    stop := stop - 1
  String.fromUTF8! (raw.extract 0 stop)

private def boundaryLabel? (marker : String) (line : String) : Option String := do
  let line := stripBoundaryTrailingWhitespace line
  if !line.startsWith marker || !line.endsWith boundarySuffix then
    none
  else
    let raw := line.toUTF8
    let prefixSize := marker.toUTF8.size
    let suffixSize := boundarySuffix.toUTF8.size
    if raw.size < prefixSize + suffixSize then
      none
    else
      let label ← String.fromUTF8? (raw.extract prefixSize (raw.size - suffixSize))
      if validLabel label then some label else none

private def beginLabel? (line : String) : Option String :=
  boundaryLabel? beginPrefix line

private def endLabel? (line : String) : Option String :=
  boundaryLabel? endPrefix line

private def looksLikeBeginBoundary (line : String) : Bool :=
  line.startsWith "-----BEGIN"

private def looksLikeEndBoundary (line : String) : Bool :=
  line.startsWith "-----END"

private def isAsciiWhitespace (octet : UInt8) : Bool :=
  octet == 0x09 || octet == 0x0a || octet == 0x0b ||
    octet == 0x0c || octet == 0x0d || octet == 0x20

private def appendBodyLine (body : ByteArray) (line : String) : ByteArray := Id.run do
  let mut out := body
  for octet in line.toUTF8 do
    if !isAsciiWhitespace octet then
      out := out.push octet
  out

private def base64Value? (octet : UInt8) : Option Nat :=
  if octet ≥ 65 && octet ≤ 90 then some (octet.toNat - 65)
  else if octet ≥ 97 && octet ≤ 122 then some (octet.toNat - 71)
  else if octet ≥ 48 && octet ≤ 57 then some (octet.toNat + 4)
  else if octet == 43 then some 62
  else if octet == 47 then some 63
  else none

/-- Strict RFC 4648 Base64 after PEM whitespace removal. -/
private def decodeBase64 (raw : ByteArray) : Except String ByteArray := do
  if raw.size % 4 != 0 then
    throw s!"PEM Base64 length {raw.size} is not a multiple of four"
  if raw.isEmpty then
    return ByteArray.empty
  let padding :=
    if raw.get! (raw.size - 1) == 61 then
      if raw.get! (raw.size - 2) == 61 then 2 else 1
    else
      0
  let mut out := ByteArray.empty
  for group in [0:raw.size / 4] do
    let offset := group * 4
    let lastGroup := offset + 4 == raw.size
    let digits := if lastGroup then 4 - padding else 4
    let mut bits := 0
    for index in [0:digits] do
      match base64Value? (raw.get! (offset + index)) with
      | some value => bits := (bits <<< 6) ||| value
      | none => throw s!"invalid PEM Base64 character at offset {offset + index}"
    for index in [digits:4] do
      if raw.get! (offset + index) != 61 then
        throw s!"invalid PEM Base64 padding at offset {offset + index}"
    match digits with
    | 4 =>
      out := out.push (UInt8.ofNat (bits >>> 16 &&& 0xff))
      out := out.push (UInt8.ofNat (bits >>> 8 &&& 0xff))
      out := out.push (UInt8.ofNat (bits &&& 0xff))
    | 3 =>
      if bits &&& 0x3 != 0 then
        throw "non-canonical PEM Base64: nonzero padding bits"
      out := out.push (UInt8.ofNat (bits >>> 10 &&& 0xff))
      out := out.push (UInt8.ofNat (bits >>> 2 &&& 0xff))
    | 2 =>
      if bits &&& 0xf != 0 then
        throw "non-canonical PEM Base64: nonzero padding bits"
      out := out.push (UInt8.ofNat (bits >>> 4 &&& 0xff))
    | _ => throw "invalid PEM Base64 padding"
  pure out

/-- Decode every well-formed textual-armor block in `text`.

Non-boundary explanatory text outside blocks is ignored, as permitted by
RFC 7468. A line beginning with a five-hyphen BEGIN/END token but having a
malformed boundary, a stray END, nested BEGIN, bad Base64, or an unclosed block
rejects the whole input. -/
def decodeBlocks (text : String) : Except String (Array Block) := do
  let mut blocks := #[]
  let mut current : Option OpenBlock := none
  for line in splitLines text do
    match current with
    | none =>
      match beginLabel? line with
      | some label =>
        current := some { label, body := ByteArray.empty }
      | none =>
        if looksLikeBeginBoundary line then
          throw "malformed PEM BEGIN boundary"
        if (endLabel? line).isSome || looksLikeEndBoundary line then
          throw "PEM END boundary without a matching BEGIN"
    | some openBlock =>
      match endLabel? line with
      | some label =>
        if label != openBlock.label then
          throw s!"PEM END label {label} does not match BEGIN label {openBlock.label}"
        let der ← decodeBase64 openBlock.body
        blocks := blocks.push { label, der }
        current := none
      | none =>
        if (beginLabel? line).isSome || looksLikeBeginBoundary line then
          throw s!"nested or malformed PEM BEGIN boundary inside {openBlock.label}"
        if looksLikeEndBoundary line then
          throw s!"malformed PEM END boundary inside {openBlock.label}"
        current := some { openBlock with body := appendBodyLine openBlock.body line }
  match current with
  | some openBlock => throw s!"PEM block {openBlock.label} has no END boundary"
  | none => pure blocks

/-- Short name for generic textual-armor decoding. -/
def decode (text : String) : Except String (Array Block) :=
  decodeBlocks text

/-- Decode exact `CERTIFICATE` blocks from a PEM bundle.

Other well-formed armor types are ignored, but malformed armor anywhere rejects
the bundle. At least one nonempty certificate is required. -/
def decodeCertificates (text : String) : Except String (Array ByteArray) := do
  let blocks ← decodeBlocks text
  let mut certificates := #[]
  for block in blocks do
    if block.label == "CERTIFICATE" then
      if block.der.isEmpty then
        throw "PEM CERTIFICATE block has an empty body"
      certificates := certificates.push block.der
  if certificates.isEmpty then
    throw "PEM bundle contains no CERTIFICATE blocks"
  pure certificates

end PEM
end X509
end TLS13
