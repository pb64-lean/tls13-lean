module

public import TLS13.X509.OID

public section

/-!
A checked ASN.1 DER cursor.

`Reader.readTLV` validates exactly one identifier/length/value framing layer.
Constructed contents are intentionally parsed only when a caller creates a
reader with `TLV.reader`; this keeps the cursor usable for implicitly tagged
X.509 fields while still rejecting BER-only identifier and length encodings.
-/

namespace TLS13
namespace X509
namespace DER

/-- Resource limit for a high-tag-number identifier. Sixteen base-128 octets
already cover a 112-bit tag number and avoid unbounded big-integer growth on
hostile certificate input. -/
def maxTagNumberOctets : Nat := 16

/-- The four ASN.1 identifier classes. -/
inductive TagClass where
  | universal
  | application
  | contextSpecific
  | private_
  deriving Repr, BEq, DecidableEq, Inhabited

/-- A decoded ASN.1 identifier. `number` is a `Nat`, with the generous
resource bound documented by `maxTagNumberOctets`. -/
structure Tag where
  tagClass : TagClass
  constructed : Bool
  number : Nat
  deriving Repr, BEq, DecidableEq, Inhabited

namespace Tag

def boolean : Tag := { tagClass := .universal, constructed := false, number := 1 }
def integer : Tag := { tagClass := .universal, constructed := false, number := 2 }
def bitString : Tag := { tagClass := .universal, constructed := false, number := 3 }
def octetString : Tag := { tagClass := .universal, constructed := false, number := 4 }
def null : Tag := { tagClass := .universal, constructed := false, number := 5 }
def objectIdentifier : Tag := { tagClass := .universal, constructed := false, number := 6 }
def sequence : Tag := { tagClass := .universal, constructed := true, number := 16 }
def set : Tag := { tagClass := .universal, constructed := true, number := 17 }
def utcTime : Tag := { tagClass := .universal, constructed := false, number := 23 }
def generalizedTime : Tag := { tagClass := .universal, constructed := false, number := 24 }

end Tag

/-- One DER value. `encoded` is the byte-for-byte original TLV, retained for
TBSCertificate signature verification and raw issuer/subject comparison. -/
structure TLV where
  tag : Tag
  contents : ByteArray
  encoded : ByteArray
  /-- Absolute offset in the reader that produced this value. -/
  offset : Nat
  /-- Identifier plus length size, in bytes. -/
  headerSize : Nat
  deriving BEq, Inhabited

/-- A checked cursor over a bounded byte string. `origin` lets readers over
nested contents continue to report offsets relative to the original input. -/
structure Reader where
  bytes : ByteArray
  offset : Nat := 0
  origin : Nat := 0
  deriving Inhabited

namespace Reader

/-- Construct a reader at the start of a byte string. -/
def ofBytes (bytes : ByteArray) : Reader :=
  { bytes }

/-- Absolute position of the cursor. -/
def position (r : Reader) : Nat :=
  r.origin + r.offset

def remaining (r : Reader) : Nat :=
  r.bytes.size - r.offset

def atEnd (r : Reader) : Bool :=
  r.offset == r.bytes.size

/-- Take exactly `count` bytes or report truncation. -/
def take (r : Reader) (count : Nat) : Except String (ByteArray × Reader) := do
  if r.offset > r.bytes.size || count > r.remaining then
    throw s!"truncated DER input at offset {r.position}: need {count} bytes, have {r.remaining}"
  let stop := r.offset + count
  pure (r.bytes.extract r.offset stop, { r with offset := stop })

/-- Read one byte or report truncation. -/
def readByte (r : Reader) : Except String (UInt8 × Reader) := do
  let (bytes, r) ← r.take 1
  pure (bytes.get! 0, r)

/-- Require the cursor to be exactly at the end of its bounded input. -/
def requireEnd (r : Reader) (context : String := "DER value") : Except String Unit := do
  unless r.atEnd do
    throw s!"{context} has {r.remaining} trailing bytes at offset {r.position}"

/-- DER primitive/constructed form required for a known universal tag.
`none` leaves a future or unknown universal tag uninterpreted. -/
private def expectedUniversalForm? (number : Nat) : Option Bool :=
  match number with
  | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 9 | 10 | 12 | 13 | 14
  | 18 | 19 | 20 | 21 | 22 | 23 | 24 | 25 | 26 | 27 | 28
  | 30 | 31 | 32 | 33 | 34 | 35 | 36 => some false
  | 8 | 11 | 16 | 17 | 29 => some true
  | _ => none

private def validateTag (tag : Tag) (offset : Nat) : Except String Unit := do
  if tag.tagClass != .universal then
    return
  if tag.number == 0 then
    throw s!"DER forbids the end-of-contents tag at offset {offset}"
  if tag.number == 15 then
    throw s!"reserved universal tag 15 at offset {offset}"
  match expectedUniversalForm? tag.number with
  | some expected =>
    if tag.constructed != expected then
      let want := if expected then "constructed" else "primitive"
      throw s!"universal tag {tag.number} must be {want} in DER at offset {offset}"
  | none => pure ()

private def tagClassOfBits : Nat → TagClass
  | 0 => .universal
  | 1 => .application
  | 2 => .contextSpecific
  | _ => .private_

/-- Read one canonical DER TLV and return the advanced cursor. -/
def readTLV (r : Reader) : Except String (TLV × Reader) := do
  if r.offset > r.bytes.size then
    throw s!"invalid DER cursor offset {r.position}"
  let start := r.offset
  let absoluteStart := r.position
  let (first, afterFirst) ← r.readByte
  let firstNat := first.toNat
  let tagClass := tagClassOfBits (firstNat >>> 6)
  let constructed := (firstNat &&& 0x20) != 0
  let lowTag := firstNat &&& 0x1f

  let mut cursor := afterFirst
  let mut tagNumber := lowTag
  if lowTag == 0x1f then
    let highStart := cursor.position
    let mut firstGroup := true
    let mut terminated := false
    let mut groupCount := 0
    tagNumber := 0
    while !terminated do
      if groupCount ≥ maxTagNumberOctets then
        throw s!"high-tag-number identifier exceeds {maxTagNumberOctets} octets at offset {highStart}"
      let (octet, next) ← cursor.readByte
      if firstGroup && (octet.toNat &&& 0x7f) == 0 then
        throw s!"non-minimal high-tag-number encoding at offset {highStart}"
      tagNumber := (tagNumber <<< 7) ||| (octet.toNat &&& 0x7f)
      cursor := next
      groupCount := groupCount + 1
      terminated := octet < 0x80
      firstGroup := false
    if tagNumber < 31 then
      throw s!"high-tag-number form used for tag {tagNumber} at offset {absoluteStart}"

  let tag : Tag := { tagClass, constructed, number := tagNumber }
  validateTag tag absoluteStart

  let lengthOffset := cursor.position
  let (firstLength, afterLengthFirst) ← cursor.readByte
  cursor := afterLengthFirst
  let mut contentLength := firstLength.toNat
  if firstLength == 0x80 then
    throw s!"indefinite length is forbidden in DER at offset {lengthOffset}"
  else if firstLength == 0xff then
    throw s!"reserved DER length octet ff at offset {lengthOffset}"
  else if firstLength ≥ 0x80 then
    let lengthOctets := firstLength.toNat &&& 0x7f
    let lengthStart := cursor.position
    let (encodedLength, afterEncodedLength) ← cursor.take lengthOctets
    if encodedLength.get! 0 == 0 then
      throw s!"DER length has a leading zero at offset {lengthStart}"
    contentLength := 0
    for octet in encodedLength do
      contentLength := (contentLength <<< 8) ||| octet.toNat
    if contentLength < 128 then
      throw s!"non-minimal long-form DER length {contentLength} at offset {lengthOffset}"
    cursor := afterEncodedLength

  if contentLength > cursor.remaining then
    throw s!"truncated DER contents at offset {cursor.position}: declared {contentLength} bytes, have {cursor.remaining}"
  let contentStart := cursor.offset
  let (contents, afterContents) ← cursor.take contentLength
  let encoded := r.bytes.extract start afterContents.offset
  let headerSize := contentStart - start
  pure ({ tag, contents, encoded, offset := absoluteStart, headerSize }, afterContents)

end Reader

namespace TLV

/-- A bounded reader over this value's contents. -/
def reader (tlv : TLV) : Reader :=
  {
    bytes := tlv.contents
    origin := tlv.offset + tlv.headerSize
  }

/-- Require an exact identifier, useful for schema-directed X.509 parsing. -/
def requireTag (tlv : TLV) (expected : Tag) (context : String := "DER value") :
    Except String Unit := do
  unless tlv.tag == expected do
    throw s!"{context} has unexpected tag class/number at offset {tlv.offset}"

/-- Decode this value as an OBJECT IDENTIFIER. -/
def asOID (tlv : TLV) : Except String OID := do
  tlv.requireTag Tag.objectIdentifier "OBJECT IDENTIFIER"
  OID.decodeContents tlv.contents

end TLV

/-- Decode exactly one DER value, rejecting trailing bytes. -/
def decode (bytes : ByteArray) : Except String TLV := do
  let (tlv, rest) ← (Reader.ofBytes bytes).readTLV
  rest.requireEnd
  pure tlv

/-- Decode every TLV in a bounded byte string. -/
def decodeAll (bytes : ByteArray) : Except String (Array TLV) := do
  let mut reader := Reader.ofBytes bytes
  let mut values := #[]
  while !reader.atEnd do
    let (value, next) ← reader.readTLV
    values := values.push value
    reader := next
  pure values

/-- Decode exactly one DER OBJECT IDENTIFIER. -/
def decodeOID (bytes : ByteArray) : Except String OID := do
  (← decode bytes).asOID

end DER
end X509
end TLS13
