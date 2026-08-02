module

public section

/-!
ASN.1 object identifiers.

The public constructor is useful for constants, while `ofArcs` is the checked
constructor for data assembled at runtime. `decodeContents` accepts the content
octets of a DER OBJECT IDENTIFIER and rejects non-minimal base-128 encodings.
-/

namespace TLS13
namespace X509

/-- An ASN.1 object identifier, represented as its numeric arcs. Values returned
by `ofArcs` and `decodeContents` satisfy the ASN.1 first/second-arc rules. -/
structure OID where
  arcs : Array Nat
  deriving Repr, BEq, DecidableEq

namespace OID

/-- Resource limit for one base-128 OID subidentifier. Real-world X.509 OID
arcs are tiny; 32 octets still permit a 224-bit arc while preventing a peer
from making repeated `Nat` shifts grow without bound. -/
def maxSubidentifierOctets : Nat := 32

/-- Checked construction of an ASN.1 object identifier. -/
def ofArcs (arcs : Array Nat) : Except String OID := do
  if arcs.size < 2 then
    throw "OID must contain at least two arcs"
  let first := arcs[0]!
  let second := arcs[1]!
  if first > 2 then
    throw s!"OID first arc must be 0, 1, or 2 (got {first})"
  if first < 2 && second > 39 then
    throw s!"OID second arc must be at most 39 when the first arc is {first} (got {second})"
  pure { arcs }

/-- Checked construction from a list of arcs. -/
def ofList (arcs : List Nat) : Except String OID :=
  ofArcs arcs.toArray

/-- Dotted-decimal rendering, for diagnostics and algorithm dispatch. -/
def toDottedString (oid : OID) : String :=
  ".".intercalate (oid.arcs.toList.map (fun arc => toString arc))

instance : ToString OID where
  toString := toDottedString

instance : Inhabited OID where
  default := { arcs := #[0, 0] }

/-- Read one minimal, big-endian base-128 subidentifier. -/
private def decodeSubidentifier (contents : ByteArray) (start : Nat) :
    Except String (Nat × Nat) := do
  if start ≥ contents.size then
    throw s!"truncated OID subidentifier at offset {start}"
  let mut offset := start
  let mut value := 0
  let mut first := true
  let mut octetCount := 0
  while offset < contents.size do
    if octetCount ≥ maxSubidentifierOctets then
      throw s!"OID subidentifier exceeds {maxSubidentifierOctets} octets at offset {start}"
    let octet := contents.get! offset
    -- A leading zero continuation group is the base-128 analogue of a
    -- leading 00 length octet and is not a valid OID encoding.
    if first && octet == 0x80 then
      throw s!"non-minimal OID subidentifier at offset {start}"
    value := (value <<< 7) ||| (octet.toNat &&& 0x7f)
    offset := offset + 1
    octetCount := octetCount + 1
    if octet < 0x80 then
      return (value, offset)
    first := false
  throw s!"unterminated OID subidentifier at offset {start}"

/-- Decode the content octets of a DER OBJECT IDENTIFIER.

The first two arcs share one base-128 subidentifier, which is why values such
as `2.999` legitimately use more than one octet. -/
def decodeContents (contents : ByteArray) : Except String OID := do
  if contents.isEmpty then
    throw "OBJECT IDENTIFIER has empty contents"
  let (firstCombined, firstEnd) ← decodeSubidentifier contents 0
  let (first, second) :=
    if firstCombined < 40 then
      (0, firstCombined)
    else if firstCombined < 80 then
      (1, firstCombined - 40)
    else
      (2, firstCombined - 80)
  let mut arcs := #[first, second]
  let mut offset := firstEnd
  while offset < contents.size do
    let (arc, next) ← decodeSubidentifier contents offset
    arcs := arcs.push arc
    offset := next
  ofArcs arcs

end OID
end X509
end TLS13
