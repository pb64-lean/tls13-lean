module

public section

/-!
Hex encoding/decoding for `ByteArray`. Used pervasively by crypto known-answer
tests and for rendering keys/transcripts while debugging the handshake.
-/

namespace HaclStar
namespace Hex

private def digitVal? (c : Char) : Option UInt8 :=
  if '0' ≤ c ∧ c ≤ '9' then some (UInt8.ofNat (c.toNat - '0'.toNat))
  else if 'a' ≤ c ∧ c ≤ 'f' then some (UInt8.ofNat (c.toNat - 'a'.toNat + 10))
  else if 'A' ≤ c ∧ c ≤ 'F' then some (UInt8.ofNat (c.toNat - 'A'.toNat + 10))
  else none

private def decodeGo : List Char → ByteArray → Option ByteArray
  | [], acc => some acc
  | [_], _ => none
  | a :: b :: rest, acc =>
    match digitVal? a, digitVal? b with
    | some hi, some lo => decodeGo rest (acc.push (hi * 16 + lo))
    | _, _ => none

/-- Decode a hex string into bytes. Returns `none` on odd length or a non-hex
character. Whitespace is not permitted. -/
def decode? (s : String) : Option ByteArray :=
  decodeGo s.toList ByteArray.empty

/-- Decode a hex literal, panicking on malformed input. For test vectors. -/
def decode! (s : String) : ByteArray :=
  match decode? s with
  | some b => b
  | none => panic! s!"Hex.decode!: malformed hex string {s}"

private def loNibble (b : UInt8) : Char :=
  let n := b.toNat
  if n < 10 then Char.ofNat ('0'.toNat + n) else Char.ofNat ('a'.toNat + n - 10)

/-- Lowercase hex encoding, two characters per byte. -/
def encode (bs : ByteArray) : String :=
  bs.foldl (fun acc b => acc.push (loNibble (b / 16)) |>.push (loNibble (b % 16))) ""

end Hex
end HaclStar
