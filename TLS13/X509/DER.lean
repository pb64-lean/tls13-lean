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

-- The cursor primitives and `readTLV` itself are written as pure `if`/`match`
-- chains (not `do` with `while`, whose `Loop.forIn` is a `partial def`) so the
-- retention and re-decode laws at the end of this file can reason about them
-- by case analysis.

/-- Take exactly `count` bytes or report truncation. -/
def take (r : Reader) (count : Nat) : Except String (ByteArray × Reader) :=
  if r.offset > r.bytes.size || count > r.remaining then
    .error s!"truncated DER input at offset {r.position}: need {count} bytes, have {r.remaining}"
  else
    .ok (r.bytes.extract r.offset (r.offset + count), { r with offset := r.offset + count })

/-- Read one byte or report truncation. -/
def readByte (r : Reader) : Except String (UInt8 × Reader) :=
  match r.take 1 with
  | .error e => .error e
  | .ok (bytes, r) => .ok (bytes.get! 0, r)

/-- Require the cursor to be exactly at the end of its bounded input. -/
def requireEnd (r : Reader) (context : String := "DER value") : Except String Unit :=
  if r.atEnd then
    .ok ()
  else
    .error s!"{context} has {r.remaining} trailing bytes at offset {r.position}"

/-- DER primitive/constructed form required for a known universal tag.
`none` leaves a future or unknown universal tag uninterpreted. -/
private def expectedUniversalForm? (number : Nat) : Option Bool :=
  match number with
  | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 9 | 10 | 12 | 13 | 14
  | 18 | 19 | 20 | 21 | 22 | 23 | 24 | 25 | 26 | 27 | 28
  | 30 | 31 | 32 | 33 | 34 | 35 | 36 => some false
  | 8 | 11 | 16 | 17 | 29 => some true
  | _ => none

private def validateTag (tag : Tag) (offset : Nat) : Except String Unit :=
  if tag.tagClass != .universal then
    .ok ()
  else if tag.number == 0 then
    .error s!"DER forbids the end-of-contents tag at offset {offset}"
  else if tag.number == 15 then
    .error s!"reserved universal tag 15 at offset {offset}"
  else
    match expectedUniversalForm? tag.number with
    | some expected =>
      if tag.constructed != expected then
        let want := if expected then "constructed" else "primitive"
        .error s!"universal tag {tag.number} must be {want} in DER at offset {offset}"
      else
        .ok ()
    | none => .ok ()

private def tagClassOfBits : Nat → TagClass
  | 0 => .universal
  | 1 => .application
  | 2 => .contextSpecific
  | _ => .private_

/-- The `Nat` value of big-endian base-256 length octets. -/
def lengthValue (octets : ByteArray) : Nat :=
  octets.foldl (fun value octet => (value <<< 8) ||| octet.toNat) 0

/-- Read the base-128 octet groups of a high-tag-number identifier, from a
cursor, the absolute offset of the first group (used only in error reports),
the accumulator, a first-group flag, and the remaining octet fuel implementing
the `maxTagNumberOctets` resource bound. -/
def readTagNumber : Reader → Nat → Nat → Bool → Nat → Except String (Nat × Reader)
  | _, highStart, _, _, 0 =>
    .error s!"high-tag-number identifier exceeds {maxTagNumberOctets} octets at offset {highStart}"
  | r, highStart, acc, firstGroup, fuel + 1 =>
    match r.readByte with
    | .error e => .error e
    | .ok (octet, next) =>
      if firstGroup && (octet.toNat &&& 0x7f) == 0 then
        .error s!"non-minimal high-tag-number encoding at offset {highStart}"
      else if octet < 0x80 then
        .ok ((acc <<< 7) ||| (octet.toNat &&& 0x7f), next)
      else
        readTagNumber next highStart ((acc <<< 7) ||| (octet.toNat &&& 0x7f))
          false fuel

/-- Read a full identifier tag number given its already-consumed first octet.
`identStart` is the absolute offset of the identifier, used only in error
reports. -/
def readNumber (first : UInt8) (r : Reader) (identStart : Nat) :
    Except String (Nat × Reader) :=
  if first.toNat &&& 0x1f == 0x1f then
    match readTagNumber r r.position 0 true maxTagNumberOctets with
    | .error e => .error e
    | .ok (number, next) =>
      if number < 31 then
        .error s!"high-tag-number form used for tag {number} at offset {identStart}"
      else
        .ok (number, next)
  else
    .ok (first.toNat &&& 0x1f, r)

/-- Read one canonical DER length (short or minimal long form). -/
def readLength (r : Reader) : Except String (Nat × Reader) :=
  match r.readByte with
  | .error e => .error e
  | .ok (first, afterFirst) =>
    if first == 0x80 then
      .error s!"indefinite length is forbidden in DER at offset {r.position}"
    else if first == 0xff then
      .error s!"reserved DER length octet ff at offset {r.position}"
    else if first ≥ 0x80 then
      match afterFirst.take (first.toNat &&& 0x7f) with
      | .error e => .error e
      | .ok (encodedLength, afterLength) =>
        if encodedLength.get! 0 == 0 then
          .error s!"DER length has a leading zero at offset {afterFirst.position}"
        else if lengthValue encodedLength < 128 then
          .error s!"non-minimal long-form DER length {lengthValue encodedLength} at offset {r.position}"
        else
          .ok (lengthValue encodedLength, afterLength)
    else
      .ok (first.toNat, afterFirst)

/-- Read one canonical DER TLV and return the advanced cursor. -/
def readTLV (r : Reader) : Except String (TLV × Reader) :=
  if r.offset > r.bytes.size then
    .error s!"invalid DER cursor offset {r.position}"
  else
    match r.readByte with
    | .error e => .error e
    | .ok (first, afterFirst) =>
      match readNumber first afterFirst r.position with
      | .error e => .error e
      | .ok (number, afterTag) =>
        match validateTag
            { tagClass := tagClassOfBits (first.toNat >>> 6)
              constructed := (first.toNat &&& 0x20) != 0
              number } r.position with
        | .error e => .error e
        | .ok () =>
          match readLength afterTag with
          | .error e => .error e
          | .ok (contentLength, afterLength) =>
            if contentLength > afterLength.remaining then
              .error s!"truncated DER contents at offset {afterLength.position}: declared {contentLength} bytes, have {afterLength.remaining}"
            else
              match afterLength.take contentLength with
              | .error e => .error e
              | .ok (contents, afterContents) =>
                .ok
                  ({ tag :=
                      { tagClass := tagClassOfBits (first.toNat >>> 6)
                        constructed := (first.toNat &&& 0x20) != 0
                        number }
                     contents
                     encoded := r.bytes.extract r.offset afterContents.offset
                     offset := r.position
                     headerSize := afterLength.offset - r.offset },
                    afterContents)

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
def decode (bytes : ByteArray) : Except String TLV :=
  match (Reader.ofBytes bytes).readTLV with
  | .error e => .error e
  | .ok (tlv, rest) =>
    match rest.requireEnd with
    | .error e => .error e
    | .ok () => .ok tlv

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
