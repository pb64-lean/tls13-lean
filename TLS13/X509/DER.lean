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

/-!
## Retention, re-decode, and canonicity laws

Kernel-checked theorems about the executable decoder above; there is no
shadow model. The load-bearing property is **exact-slice retention**
(`Reader.readTLV_encoded`, `decode_encoded`): a successful parse retains, byte
for byte, exactly the input slice it consumed. Certificate signature
verification and issuer/subject Name comparison rely on `TBSCertificate.encoded`
and `Name.encoded` being byte-identical to the parsed input, and those fields
are `TLV.encoded` slices. On top of retention sit the **re-decode identity**
(`readTLV_encoded_decode`, `decode_idem`), **encoding uniqueness**
(`decode_inj`), **trailing-data rejection** (`decode_append_ne_ok`), and
canonical-form laws for the length and identifier octets
(`Reader.readLength_minimal`, `Reader.readNumber_low`, and the BER rejection
lemmas). -/

/-! ### `ByteArray.get!` bridges

Core Lean is still sparse on `ByteArray.get!` lemmas, so the bridges to
`getElem` live here. -/

private theorem get!_eq_getElem {a : ByteArray} {i : Nat} (h : i < a.size) :
    a.get! i = a[i] := by
  rcases a with ⟨data⟩
  show data[i]! = _
  rw [getElem!_pos data i h]
  rfl

private theorem get!_append_left {a b : ByteArray} {i : Nat} (h : i < a.size) :
    (a ++ b).get! i = a.get! i := by
  rw [get!_eq_getElem (by simp [ByteArray.size_append]; omega),
    get!_eq_getElem h, ByteArray.getElem_append_left h]

private theorem extract_get! {a : ByteArray} {s e k : Nat} (hk : s + k < e)
    (he : e ≤ a.size) : (a.extract s e).get! k = a.get! (s + k) := by
  have hsize : (a.extract s e).size = e - s := by
    rw [ByteArray.size_extract]
    omega
  rw [get!_eq_getElem (by omega), ByteArray.getElem_extract,
    get!_eq_getElem (by omega)]

/-! ### Componentwise congruence helpers -/

private theorem reader_eq {r₁ r₂ : Reader} (hb : r₁.bytes = r₂.bytes)
    (ho : r₁.offset = r₂.offset) (hg : r₁.origin = r₂.origin) : r₁ = r₂ := by
  cases r₁; cases r₂; simp_all

private theorem tlv_eq {t₁ t₂ : TLV} (htag : t₁.tag = t₂.tag)
    (hc : t₁.contents = t₂.contents) (he : t₁.encoded = t₂.encoded)
    (ho : t₁.offset = t₂.offset) (hh : t₁.headerSize = t₂.headerSize) :
    t₁ = t₂ := by
  cases t₁; cases t₂; simp_all

private theorem reader_with_offset {r r' : Reader} {x : Nat}
    (h : r' = { r with offset := x }) :
    r'.bytes = r.bytes ∧ r'.offset = x ∧ r'.origin = r.origin := by
  subst h; exact ⟨rfl, rfl, rfl⟩

namespace Reader

/-! ### Cursor primitive specifications -/

/-- Everything a successful `take` says: the count fit in the input, the
returned bytes are the exact slice at the cursor, and the cursor advanced by
exactly `count`. -/
theorem take_eq_ok {r : Reader} {count : Nat} {bs : ByteArray} {r' : Reader}
    (h : r.take count = .ok (bs, r')) :
    r.offset + count ≤ r.bytes.size ∧
    bs = r.bytes.extract r.offset (r.offset + count) ∧
    r' = { r with offset := r.offset + count } := by
  unfold take at h
  split at h
  · cases h
  · rename_i hcond
    simp only [Bool.or_eq_true, decide_eq_true_eq, not_or, Nat.not_lt] at hcond
    have hrem : count ≤ r.bytes.size - r.offset := hcond.2
    simp only [Except.ok.injEq, Prod.mk.injEq] at h
    exact ⟨by omega, h.1.symm, h.2.symm⟩

/-- `take` succeeds whenever the requested count fits. -/
theorem take_ok_of_le {r : Reader} {count : Nat}
    (h : r.offset + count ≤ r.bytes.size) :
    r.take count = .ok (r.bytes.extract r.offset (r.offset + count),
      { r with offset := r.offset + count }) := by
  unfold take
  rw [if_neg]
  simp only [Bool.or_eq_true, decide_eq_true_eq, not_or, Nat.not_lt]
  exact ⟨by omega, show count ≤ r.bytes.size - r.offset by omega⟩

/-- Everything a successful `readByte` says. -/
theorem readByte_eq_ok {r : Reader} {b : UInt8} {r' : Reader}
    (h : r.readByte = .ok (b, r')) :
    r.offset < r.bytes.size ∧ b = r.bytes.get! r.offset ∧
    r' = { r with offset := r.offset + 1 } := by
  unfold readByte at h
  split at h
  · cases h
  · rename_i bs r₁ heq
    obtain ⟨hle, hbs, hr₁⟩ := take_eq_ok heq
    simp only [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨hb, hr'⟩ := h
    subst hbs hr₁
    refine ⟨by omega, ?_, hr'.symm⟩
    rw [← hb, extract_get! (by omega) (by omega)]
    rfl

/-- `readByte` succeeds whenever a byte remains, returning it. -/
theorem readByte_ok_of_lt {r : Reader} (h : r.offset < r.bytes.size) :
    r.readByte = .ok (r.bytes.get! r.offset,
      { r with offset := r.offset + 1 }) := by
  unfold readByte
  rw [take_ok_of_le (by omega)]
  show Except.ok ((r.bytes.extract r.offset (r.offset + 1)).get! 0,
    ({ r with offset := r.offset + 1 } : Reader)) = _
  rw [extract_get! (by omega) (by omega)]
  rfl

/-- A successful `requireEnd` means the cursor consumed its whole input. -/
theorem requireEnd_eq_ok {r : Reader} {context : String}
    (h : r.requireEnd context = .ok ()) : r.offset = r.bytes.size := by
  unfold requireEnd at h
  split at h
  · rename_i hend
    simp only [atEnd, beq_iff_eq] at hend
    exact hend
  · cases h

/-- `requireEnd` accepts an exhausted cursor. -/
theorem requireEnd_ok {r : Reader} {context : String}
    (h : r.offset = r.bytes.size) : r.requireEnd context = .ok () := by
  unfold requireEnd
  rw [if_pos]
  show r.atEnd = true
  simp [atEnd, h]

/-! ### Byte-window agreement

`Agrees p q n` says the next `n` bytes under both cursors exist and coincide.
The decoder only ever inspects bytes it consumes, so a successful parse
transports along `Agrees` — this is what turns exact-slice retention into the
re-decode identity and trailing-data rejection. -/

private def Agrees (p q : Reader) (n : Nat) : Prop :=
  p.offset + n ≤ p.bytes.size ∧ q.offset + n ≤ q.bytes.size ∧
  ∀ k, k < n → p.bytes.get! (p.offset + k) = q.bytes.get! (q.offset + k)

private theorem Agrees.mono {p q : Reader} {n m : Nat} (h : Agrees p q n)
    (hm : m ≤ n) : Agrees p q m := by
  obtain ⟨h1, h2, h3⟩ := h
  exact ⟨by omega, by omega, fun k hk => h3 k (by omega)⟩

/-- Advancing both cursors by the same distance preserves agreement on the
remaining window. Cursor components are taken as equations so the lemma
applies to the opaque cursors produced by the step lemmas. -/
private theorem Agrees.advance {p q p₁ q₁ : Reader} {n d : Nat}
    (h : Agrees p q n) (hd : d ≤ n)
    (hpb : p₁.bytes = p.bytes) (hpo : p₁.offset = p.offset + d)
    (hqb : q₁.bytes = q.bytes) (hqo : q₁.offset = q.offset + d) :
    Agrees p₁ q₁ (n - d) := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨by rw [hpb, hpo]; omega, by rw [hqb, hqo]; omega, ?_⟩
  intro k hk
  rw [hpb, hpo, hqb, hqo, Nat.add_assoc, Nat.add_assoc]
  exact h3 (d + k) (by omega)

/-- Agreeing cursors yield equal slices. -/
private theorem Agrees.extract_eq {p q : Reader} {n c : Nat}
    (h : Agrees p q n) (hc : c ≤ n) :
    p.bytes.extract p.offset (p.offset + c) =
      q.bytes.extract q.offset (q.offset + c) := by
  obtain ⟨h1, h2, h3⟩ := h
  apply ByteArray.ext_getElem
  · rw [ByteArray.size_extract, ByteArray.size_extract]
    omega
  · intro i hi hi'
    have hin : i < c := by
      rw [ByteArray.size_extract] at hi
      omega
    rw [ByteArray.getElem_extract, ByteArray.getElem_extract]
    have := h3 i (by omega)
    rw [get!_eq_getElem (by omega), get!_eq_getElem (by omega)] at this
    exact this

/-- Agreeing cursors read the same byte and advance in lockstep. -/
private theorem readByte_agrees {p q : Reader} {n : Nat} (h : Agrees p q n)
    (hn : 1 ≤ n) :
    q.readByte = .ok (p.bytes.get! p.offset,
      { q with offset := q.offset + 1 }) := by
  obtain ⟨h1, h2, h3⟩ := h
  rw [readByte_ok_of_lt (by omega)]
  have := h3 0 (by omega)
  rw [Nat.add_zero, Nat.add_zero] at this
  rw [← this]

/-- Agreeing cursors take the same slice and advance in lockstep. -/
private theorem take_agrees {p q : Reader} {n c : Nat} (h : Agrees p q n)
    (hc : c ≤ n) :
    q.take c = .ok (p.bytes.extract p.offset (p.offset + c),
      { q with offset := q.offset + c }) := by
  rw [take_ok_of_le (by have := h.2.1; omega), ← h.extract_eq hc]

/-! ### Cursor-state facts for the compound readers -/

/-- A successful `readTagNumber` preserves the buffer, advances, and stays in
bounds. -/
private theorem readTagNumber_ok_state {fuel : Nat} :
    ∀ {r : Reader} {highStart acc : Nat} {firstGroup : Bool} {m : Nat}
      {r' : Reader},
      readTagNumber r highStart acc firstGroup fuel = .ok (m, r') →
      r'.bytes = r.bytes ∧ r'.origin = r.origin ∧
      r.offset < r'.offset ∧ r'.offset ≤ r.bytes.size := by
  induction fuel with
  | zero =>
    intro r hs acc fg m r' h
    exact absurd h (by simp [readTagNumber])
  | succ fuel ih =>
    intro r hs acc fg m r' h
    unfold readTagNumber at h
    split at h
    · cases h
    · rename_i octet next heq
      obtain ⟨hlt, hoct, hnext⟩ := readByte_eq_ok heq
      obtain ⟨hnb, hno, hng⟩ := reader_with_offset hnext
      split at h
      · cases h
      · split at h
        · simp only [Except.ok.injEq, Prod.mk.injEq] at h
          obtain ⟨hm, hr'⟩ := h
          subst hr'
          exact ⟨hnb, hng, by omega, by omega⟩
        · obtain ⟨h1, h2, h3, h4⟩ := ih h
          refine ⟨h1.trans hnb, h2.trans hng, by omega, ?_⟩
          rw [hnb] at h4
          omega

/-- A successful `readNumber` preserves the buffer and stays in bounds. -/
private theorem readNumber_ok_state {first : UInt8} {r : Reader} {i m : Nat}
    {r' : Reader} (h : readNumber first r i = .ok (m, r'))
    (hr : r.offset ≤ r.bytes.size) :
    r'.bytes = r.bytes ∧ r'.origin = r.origin ∧
    r.offset ≤ r'.offset ∧ r'.offset ≤ r.bytes.size := by
  unfold readNumber at h
  split at h
  · split at h
    · cases h
    · rename_i number next heq
      split at h
      · cases h
      · simp only [Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨hm, hr'⟩ := h
        subst hr'
        obtain ⟨h1, h2, h3, h4⟩ := readTagNumber_ok_state heq
        exact ⟨h1, h2, by omega, h4⟩
  · simp only [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨hm, hr'⟩ := h
    subst hr'
    exact ⟨rfl, rfl, Nat.le_refl _, hr⟩

/-- A successful `readLength` preserves the buffer, advances, and stays in
bounds. -/
private theorem readLength_ok_state {r : Reader} {len : Nat} {r' : Reader}
    (h : readLength r = .ok (len, r')) :
    r'.bytes = r.bytes ∧ r'.origin = r.origin ∧
    r.offset < r'.offset ∧ r'.offset ≤ r.bytes.size := by
  unfold readLength at h
  split at h
  · cases h
  · rename_i first afterFirst heq
    obtain ⟨hlt, hfirst, hAF⟩ := readByte_eq_ok heq
    obtain ⟨hab, hao, hag⟩ := reader_with_offset hAF
    split at h
    · cases h
    · split at h
      · cases h
      · split at h
        · split at h
          · cases h
          · rename_i encodedLength afterLength htake
            obtain ⟨hble, hbs, hAL⟩ := take_eq_ok htake
            obtain ⟨hlb, hlo, hlg⟩ := reader_with_offset hAL
            split at h
            · cases h
            · split at h
              · cases h
              · simp only [Except.ok.injEq, Prod.mk.injEq] at h
                obtain ⟨hlen, hr'⟩ := h
                subst hr'
                rw [hab] at hlb
                rw [hab, hao] at hble
                refine ⟨hlb, hlg.trans hag, ?_, ?_⟩ <;> rw [hlo, hao] <;> omega
        · simp only [Except.ok.injEq, Prod.mk.injEq] at h
          obtain ⟨hlen, hr'⟩ := h
          subst hr'
          exact ⟨hab, hag, by omega, by omega⟩

/-! ### Exact-slice retention -/

/-- The complete specification of a successful `readTLV`: the cursor advances
within bounds over the same buffer, and the returned `TLV` retains the exact
consumed slice — `encoded` is the input from the starting offset to the final
offset, and `contents` is that slice with the header removed. -/
theorem readTLV_spec {r : Reader} {tlv : TLV} {r' : Reader}
    (h : r.readTLV = .ok (tlv, r')) :
    r'.bytes = r.bytes ∧ r'.origin = r.origin ∧
    r.offset < r'.offset ∧ r'.offset ≤ r.bytes.size ∧
    tlv.offset = r.position ∧
    r.offset + tlv.headerSize ≤ r'.offset ∧
    tlv.encoded = r.bytes.extract r.offset r'.offset ∧
    tlv.contents = r.bytes.extract (r.offset + tlv.headerSize) r'.offset := by
  unfold readTLV at h
  split at h
  · cases h
  rename_i hoff
  split at h
  · cases h
  rename_i first afterFirst h1
  split at h
  · cases h
  rename_i number afterTag h2
  split at h
  · cases h
  rename_i h3
  split at h
  · cases h
  rename_i contentLength afterLength h4
  split at h
  · cases h
  rename_i hrem
  split at h
  · cases h
  rename_i contents afterContents h5
  simp only [Except.ok.injEq, Prod.mk.injEq] at h
  obtain ⟨htlv, hr'⟩ := h
  subst hr'
  obtain ⟨hlt1, hfirst, hAF⟩ := readByte_eq_ok h1
  obtain ⟨hafb, hafo, hafg⟩ := reader_with_offset hAF
  obtain ⟨hatb, hatg, hato1, hato2⟩ :=
    readNumber_ok_state h2 (by rw [hafb, hafo]; omega)
  obtain ⟨halb, halg, halo1, halo2⟩ := readLength_ok_state h4
  obtain ⟨htk, hcont, hAC⟩ := take_eq_ok h5
  obtain ⟨hacb, haco, hacg⟩ := reader_with_offset hAC
  have hb2 : afterTag.bytes = r.bytes := hatb.trans hafb
  have hb3 : afterLength.bytes = r.bytes := halb.trans hb2
  have hb4 : afterContents.bytes = r.bytes := by rw [hacb, hb3]
  have hg2 : afterTag.origin = r.origin := hatg.trans hafg
  have hg3 : afterLength.origin = r.origin := halg.trans hg2
  have hg4 : afterContents.origin = r.origin := by rw [hacg, hg3]
  rw [hafb] at hato2
  rw [hb2] at halo2
  rw [hb3] at htk
  have hto : tlv.offset = r.position := by rw [← htlv]
  have hth : tlv.headerSize = afterLength.offset - r.offset := by rw [← htlv]
  have hte : tlv.encoded = r.bytes.extract r.offset afterContents.offset := by
    rw [← htlv]
  have htc : tlv.contents = contents := by rw [← htlv]
  refine ⟨hb4, hg4, by omega, by omega, hto, by omega, hte, ?_⟩
  rw [htc, hcont, hb3]
  have e2 : afterLength.offset + contentLength = afterContents.offset := by
    omega
  have e1 : afterLength.offset = r.offset + tlv.headerSize := by omega
  rw [e2, e1]

/-- **Exact-slice retention**: a successful `readTLV` yields a `TLV` whose
`encoded` field is byte-identical to the input slice the cursor consumed. -/
theorem readTLV_encoded {r : Reader} {tlv : TLV} {r' : Reader}
    (h : r.readTLV = .ok (tlv, r')) :
    tlv.encoded = r.bytes.extract r.offset r'.offset :=
  (readTLV_spec h).2.2.2.2.2.2.1

/-- The retained `contents` are the consumed slice with the header removed. -/
theorem readTLV_contents {r : Reader} {tlv : TLV} {r' : Reader}
    (h : r.readTLV = .ok (tlv, r')) :
    tlv.contents = r.bytes.extract (r.offset + tlv.headerSize) r'.offset :=
  (readTLV_spec h).2.2.2.2.2.2.2

/-- The retained encoding is exactly header plus contents in size. -/
theorem readTLV_sizes {r : Reader} {tlv : TLV} {r' : Reader}
    (h : r.readTLV = .ok (tlv, r')) :
    tlv.encoded.size = tlv.headerSize + tlv.contents.size := by
  obtain ⟨hb, hg, h1, h2, h3, h4, h5, h6⟩ := readTLV_spec h
  rw [h5, h6, ByteArray.size_extract, ByteArray.size_extract]
  omega

/-! ### The decoder reads only the bytes it consumes

Each step lemma transports a successful parse from cursor `p` to any cursor
`q` that agrees with it on exactly the consumed window. -/

/-- `validateTag` acceptance does not depend on the reported offset. -/
private theorem validateTag_ok {tag : Tag} {o o' : Nat}
    (h : validateTag tag o = .ok ()) : validateTag tag o' = .ok () := by
  unfold validateTag at h ⊢
  split at h
  · rename_i hc1
    rw [if_pos hc1]
  · rename_i hc1
    rw [if_neg hc1]
    split at h
    · cases h
    rename_i hc2
    rw [if_neg hc2]
    split at h
    · cases h
    rename_i hc3
    rw [if_neg hc3]
    split at h
    · rename_i expected hf
      split at h
      · simp at h
      rename_i hc4
      rw [if_neg hc4]
    · rename_i hf
      rfl

private theorem readTagNumber_agrees {fuel : Nat} :
    ∀ {p : Reader} {hs acc : Nat} {fg : Bool} {m : Nat} {p' q : Reader}
      {hs' : Nat},
      readTagNumber p hs acc fg fuel = .ok (m, p') →
      Agrees p q (p'.offset - p.offset) →
      readTagNumber q hs' acc fg fuel =
        .ok (m, { q with offset := q.offset + (p'.offset - p.offset) }) := by
  induction fuel with
  | zero =>
    intro p hs acc fg m p' q hs' h hag
    exact absurd h (by simp [readTagNumber])
  | succ fuel ih =>
    intro p hs acc fg m p' q hs' h hag
    obtain ⟨hsb, hsg, hso1, hso2⟩ := readTagNumber_ok_state h
    unfold readTagNumber at h ⊢
    split at h
    · cases h
    rename_i octet next heq
    obtain ⟨hlt, hoct, hN⟩ := readByte_eq_ok heq
    obtain ⟨hnb, hno, hng⟩ := reader_with_offset hN
    have hqrb : q.readByte = .ok (octet, { q with offset := q.offset + 1 }) := by
      rw [readByte_agrees hag (by omega), ← hoct]
    simp only [hqrb]
    split at h
    · cases h
    rename_i hc1
    rw [if_neg hc1]
    split at h
    · rename_i hc2
      rw [if_pos hc2]
      simp only [Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨hm, hp'⟩ := h
      subst hp'
      rw [← hm]
      have hd : next.offset - p.offset = 1 := by omega
      rw [hd]
    · rename_i hc2
      rw [if_neg hc2]
      obtain ⟨hrb2, hrg2, hro1, hro2⟩ := readTagNumber_ok_state h
      have hadv : Agrees next ({ q with offset := q.offset + 1 } : Reader)
          ((p'.offset - p.offset) - 1) :=
        hag.advance (by omega) hnb hno rfl rfl
      have hidx : (p'.offset - p.offset) - 1 = p'.offset - next.offset := by
        omega
      rw [hidx] at hadv
      rw [ih (hs' := hs') h hadv]
      have hXY : q.offset + 1 + (p'.offset - next.offset) =
          q.offset + (p'.offset - p.offset) := by omega
      exact congrArg Except.ok
        (congrArg (Prod.mk m) (reader_eq rfl hXY rfl))

private theorem readNumber_agrees {first : UInt8} {p : Reader} {i m : Nat}
    {p' q : Reader} {i' : Nat}
    (h : readNumber first p i = .ok (m, p'))
    (hag : Agrees p q (p'.offset - p.offset)) :
    readNumber first q i' =
      .ok (m, { q with offset := q.offset + (p'.offset - p.offset) }) := by
  unfold readNumber at h ⊢
  split at h
  · rename_i hc
    rw [if_pos hc]
    split at h
    · cases h
    rename_i number next heq
    split at h
    · cases h
    rename_i hn31
    simp only [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨hm, hp'⟩ := h
    subst hp'
    simp only [readTagNumber_agrees (hs' := q.position) heq hag]
    rw [if_neg hn31, hm]
  · rename_i hc
    rw [if_neg hc]
    simp only [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨hm, hp'⟩ := h
    subst hp'
    rw [← hm]
    refine congrArg Except.ok
      (congrArg (Prod.mk (first.toNat &&& 0x1f)) (reader_eq rfl ?_ rfl))
    show q.offset = q.offset + (p.offset - p.offset)
    omega

private theorem readLength_agrees {p : Reader} {len : Nat} {p' q : Reader}
    (h : readLength p = .ok (len, p'))
    (hag : Agrees p q (p'.offset - p.offset)) :
    readLength q =
      .ok (len, { q with offset := q.offset + (p'.offset - p.offset) }) := by
  obtain ⟨hsb, hsg, hso1, hso2⟩ := readLength_ok_state h
  unfold readLength at h ⊢
  split at h
  · cases h
  rename_i first afterFirst heq
  obtain ⟨hlt, hfirst, hAF⟩ := readByte_eq_ok heq
  obtain ⟨hab, hao, haor⟩ := reader_with_offset hAF
  have hqrb : q.readByte = .ok (first, { q with offset := q.offset + 1 }) := by
    rw [readByte_agrees hag (by omega), ← hfirst]
  simp only [hqrb]
  split at h
  · cases h
  rename_i hc1
  rw [if_neg hc1]
  split at h
  · cases h
  rename_i hc2
  rw [if_neg hc2]
  split at h
  · rename_i hc3
    rw [if_pos hc3]
    split at h
    · cases h
    rename_i encodedLength afterLength htake
    split at h
    · cases h
    rename_i hz
    split at h
    · cases h
    rename_i hmin
    simp only [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨hlen, hp'⟩ := h
    subst hp'
    obtain ⟨htkb, htkbs, hAL⟩ := take_eq_ok htake
    obtain ⟨hlb, hlo, hlg⟩ := reader_with_offset hAL
    have hadv : Agrees afterFirst ({ q with offset := q.offset + 1 } : Reader)
        ((afterLength.offset - p.offset) - 1) :=
      hag.advance (by omega) hab hao rfl rfl
    have hidx : (afterLength.offset - p.offset) - 1 = first.toNat &&& 0x7f := by
      omega
    rw [hidx] at hadv
    have hqtk := take_agrees hadv (Nat.le_refl _)
    rw [← htkbs] at hqtk
    simp only [hqtk]
    rw [if_neg hz, if_neg hmin, ← hlen]
    refine congrArg Except.ok
      (congrArg (Prod.mk (lengthValue encodedLength)) (reader_eq rfl ?_ rfl))
    show q.offset + 1 + (first.toNat &&& 0x7f) =
      q.offset + (afterLength.offset - p.offset)
    omega
  · rename_i hc3
    rw [if_neg hc3]
    simp only [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨hlen, hp'⟩ := h
    subst hp'
    rw [← hlen]
    refine congrArg Except.ok
      (congrArg (Prod.mk first.toNat) (reader_eq rfl ?_ rfl))
    show q.offset + 1 = q.offset + (afterFirst.offset - p.offset)
    omega

/-- A successful `readTLV` transports to any cursor that agrees on the
consumed window: the same `TLV` is produced up to the reported absolute
offset, and the cursor advances by the same distance. -/
private theorem readTLV_agrees {p : Reader} {tlv : TLV} {p' q : Reader}
    (h : p.readTLV = .ok (tlv, p'))
    (hag : Agrees p q (p'.offset - p.offset)) :
    q.readTLV = .ok ({ tlv with offset := q.position },
      { q with offset := q.offset + (p'.offset - p.offset) }) := by
  obtain ⟨hsb, hsg, hso1, hso2, hto, hthle, hte, htc⟩ := readTLV_spec h
  unfold readTLV at h ⊢
  split at h
  · cases h
  rename_i hoff
  split at h
  · cases h
  rename_i first afterFirst h1
  split at h
  · cases h
  rename_i number afterTag h2
  split at h
  · cases h
  rename_i h3
  split at h
  · cases h
  rename_i contentLength afterLength h4
  split at h
  · cases h
  rename_i hrem
  split at h
  · cases h
  rename_i contents afterContents h5
  simp only [Except.ok.injEq, Prod.mk.injEq] at h
  obtain ⟨htlv, hp'⟩ := h
  subst hp'
  obtain ⟨hlt1, hfirst, hAF⟩ := readByte_eq_ok h1
  obtain ⟨hafb, hafo, hafg⟩ := reader_with_offset hAF
  obtain ⟨hatb, hatg, hato1, hato2⟩ :=
    readNumber_ok_state h2 (by rw [hafb, hafo]; omega)
  obtain ⟨halb, halg, halo1, halo2⟩ := readLength_ok_state h4
  obtain ⟨htk, hcont, hAC⟩ := take_eq_ok h5
  obtain ⟨hacb, haco, hacg⟩ := reader_with_offset hAC
  have hb2 : afterTag.bytes = p.bytes := hatb.trans hafb
  have hb3 : afterLength.bytes = p.bytes := halb.trans hb2
  rw [hafb] at hato2
  rw [hb2] at halo2
  rw [hb3] at htk
  -- Reduce the `q`-side decode step by step.
  rw [if_neg (show ¬q.offset > q.bytes.size by have := hag.2.1; omega)]
  have hqrb : q.readByte = .ok (first, { q with offset := q.offset + 1 }) := by
    rw [readByte_agrees hag (by omega), ← hfirst]
  simp only [hqrb]
  have hadv1 : Agrees afterFirst ({ q with offset := q.offset + 1 } : Reader)
      ((afterContents.offset - p.offset) - 1) :=
    hag.advance (by omega) hafb hafo rfl rfl
  have hqrn := readNumber_agrees (i' := q.position) h2
    (hadv1.mono (by omega))
  simp only [hqrn]
  simp only [validateTag_ok (o' := q.position) h3]
  have hadv2 : Agrees afterTag
      ({ bytes := q.bytes,
         offset := q.offset + 1 + (afterTag.offset - afterFirst.offset),
         origin := q.origin } : Reader)
      ((afterContents.offset - p.offset) - (afterTag.offset - p.offset)) :=
    hag.advance (by omega) hb2 (by omega) rfl
      (by show q.offset + 1 + (afterTag.offset - afterFirst.offset) =
            q.offset + (afterTag.offset - p.offset)
          omega)
  have hagL : Agrees afterTag
      ({ bytes := q.bytes,
         offset := q.offset + 1 + (afterTag.offset - afterFirst.offset),
         origin := q.origin } : Reader)
      (afterLength.offset - afterTag.offset) := hadv2.mono (by omega)
  have hqrl := readLength_agrees h4 hagL
  simp only [hqrl]
  split
  · rename_i hcq
    exfalso
    have hcq' : contentLength > q.bytes.size -
        (q.offset + 1 + (afterTag.offset - afterFirst.offset) +
          (afterLength.offset - afterTag.offset)) := hcq
    have := hag.2.1
    omega
  rename_i hcq
  have hadv3 : Agrees afterLength
      ({ bytes := q.bytes,
         offset := q.offset + 1 + (afterTag.offset - afterFirst.offset) +
           (afterLength.offset - afterTag.offset),
         origin := q.origin } : Reader)
      ((afterContents.offset - p.offset) - (afterLength.offset - p.offset)) :=
    hag.advance (by omega) hb3 (by omega) rfl
      (by show q.offset + 1 + (afterTag.offset - afterFirst.offset) +
            (afterLength.offset - afterTag.offset) =
            q.offset + (afterLength.offset - p.offset)
          omega)
  have hagT : Agrees afterLength
      ({ bytes := q.bytes,
         offset := q.offset + 1 + (afterTag.offset - afterFirst.offset) +
           (afterLength.offset - afterTag.offset),
         origin := q.origin } : Reader)
      contentLength := hadv3.mono (by omega)
  have hqtk := take_agrees hagT (Nat.le_refl _)
  rw [← hcont] at hqtk
  simp only [hqtk]
  simp only [Except.ok.injEq, Prod.mk.injEq]
  refine ⟨tlv_eq ?_ ?_ ?_ ?_ ?_, reader_eq rfl ?_ rfl⟩
  · rw [← htlv]
  · rw [← htlv]
  · show q.bytes.extract q.offset
        (q.offset + 1 + (afterTag.offset - afterFirst.offset) +
          (afterLength.offset - afterTag.offset) + contentLength) =
      ({ tlv with offset := q.position } : TLV).encoded
    have hx := hag.extract_eq (Nat.le_refl _)
    have e3 : p.offset + (afterContents.offset - p.offset) =
        afterContents.offset := by omega
    have e4 : q.offset + (afterContents.offset - p.offset) =
        q.offset + 1 + (afterTag.offset - afterFirst.offset) +
          (afterLength.offset - afterTag.offset) + contentLength := by omega
    rw [e3, e4] at hx
    rw [← hx]
    exact hte.symm
  · rw [← htlv]
  · have hh : tlv.headerSize = afterLength.offset - p.offset := by rw [← htlv]
    show q.offset + 1 + (afterTag.offset - afterFirst.offset) +
        (afterLength.offset - afterTag.offset) - q.offset = tlv.headerSize
    omega
  · show q.offset + 1 + (afterTag.offset - afterFirst.offset) +
        (afterLength.offset - afterTag.offset) + contentLength =
      q.offset + (afterContents.offset - p.offset)
    omega

/-! ### Canonical length and identifier octet forms

The BER encodings excluded by DER are rejected structurally: the indefinite
and reserved length octets never parse, the long form is only ever accepted
for lengths of 128 and above (so every length has exactly one accepted
encoding), and small tag numbers are only ever produced by the low-tag-number
identifier form. -/

/-- **Minimal-length canonicity**: a parsed length is below 128 exactly when
it came from the one-octet short form. In particular the long form never
yields a small length, and the short form never yields a large one. -/
theorem readLength_minimal {r : Reader} {len : Nat} {r' : Reader}
    (h : readLength r = .ok (len, r')) :
    len < 128 ↔ r'.offset = r.offset + 1 := by
  unfold readLength at h
  split at h
  · cases h
  rename_i first afterFirst heq
  obtain ⟨hlt, hfirst, hAF⟩ := readByte_eq_ok heq
  obtain ⟨hab, hao, haor⟩ := reader_with_offset hAF
  split at h
  · cases h
  rename_i hc1
  split at h
  · cases h
  rename_i hc2
  split at h
  · rename_i hc3
    split at h
    · cases h
    rename_i encodedLength afterLength htake
    split at h
    · cases h
    rename_i hz
    split at h
    · cases h
    rename_i hmin
    simp only [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨hlen, hr'⟩ := h
    subst hr'
    obtain ⟨htkle, htkbs, hAL⟩ := take_eq_ok htake
    obtain ⟨hlb, hlo, hlg⟩ := reader_with_offset hAL
    constructor
    · intro hcontra
      rw [← hlen] at hcontra
      exact absurd hcontra hmin
    · intro hoff
      exfalso
      have hc : first.toNat &&& 0x7f = first.toNat % 128 := by
        have h7f : (0x7f : Nat) = 2 ^ 7 - 1 := rfl
        rw [h7f, Nat.and_two_pow_sub_one_eq_mod]
      have h80 : (0x80 : UInt8).toNat = 128 := rfl
      have hub : first.toNat < 256 := UInt8.toNat_lt_size first
      have h128 : first.toNat ≥ 128 := by
        have := UInt8.le_iff_toNat_le.mp hc3
        omega
      have hne : first.toNat ≠ 128 := by
        intro habs
        exact hc1 (by simp only [beq_iff_eq]
                      exact UInt8.toNat_inj.mp (by omega))
      omega
  · rename_i hc3
    simp only [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨hlen, hr'⟩ := h
    subst hr'
    have h80 : (0x80 : UInt8).toNat = 128 := rfl
    have hlt128 : first.toNat < 128 := by
      rw [UInt8.not_le] at hc3
      have := UInt8.lt_iff_toNat_lt.mp hc3
      omega
    constructor
    · intro _
      omega
    · intro _
      omega

/-- The indefinite-length octet `0x80` is rejected wherever it appears as a
first length octet. -/
theorem readLength_indefinite {r : Reader}
    (hlt : r.offset < r.bytes.size) (hbyte : r.bytes.get! r.offset = 0x80)
    (x : Nat × Reader) : readLength r ≠ .ok x := by
  intro h
  unfold readLength at h
  rw [readByte_ok_of_lt hlt, hbyte] at h
  simp at h

/-- The reserved length octet `0xff` is rejected wherever it appears as a
first length octet. -/
theorem readLength_reserved {r : Reader}
    (hlt : r.offset < r.bytes.size) (hbyte : r.bytes.get! r.offset = 0xff)
    (x : Nat × Reader) : readLength r ≠ .ok x := by
  intro h
  unfold readLength at h
  rw [readByte_ok_of_lt hlt, hbyte] at h
  simp at h

/-- **Minimal-identifier canonicity**: a tag number below 31 is only ever
produced by the low-tag-number form, which consumes nothing beyond the
identifier octet itself; the high-tag-number form rejects such values. -/
theorem readNumber_low {first : UInt8} {r : Reader} {i m : Nat} {r' : Reader}
    (h : readNumber first r i = .ok (m, r')) (hm : m < 31) :
    r' = r ∧ m = first.toNat &&& 0x1f := by
  unfold readNumber at h
  split at h
  · split at h
    · cases h
    rename_i number next heq
    split at h
    · cases h
    rename_i hn31
    simp only [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨hnm, hr'⟩ := h
    subst hnm
    exact absurd hm hn31
  · simp only [Except.ok.injEq, Prod.mk.injEq] at h
    exact ⟨h.2.symm, h.1.symm⟩

end Reader

/-! ### Root decoding laws -/

/-- **Exact retention at the root**: `decode` accepts a byte string exactly
when it is one complete TLV, so the retained `encoded` field is the entire
input, byte for byte. -/
theorem decode_encoded {bytes : ByteArray} {tlv : TLV}
    (h : decode bytes = .ok tlv) : tlv.encoded = bytes := by
  unfold decode at h
  split at h
  · cases h
  rename_i tlv₀ rest heq
  split at h
  · cases h
  rename_i hend
  simp only [Except.ok.injEq] at h
  subst h
  obtain ⟨hb, hg, h1, h2, h3, h4, h5, h6⟩ := Reader.readTLV_spec heq
  have hoff := Reader.requireEnd_eq_ok hend
  rw [h5]
  show bytes.extract 0 rest.offset = bytes
  have hsz : rest.offset = bytes.size := by
    rw [hoff]
    show rest.bytes.size = bytes.size
    rw [hb]
    rfl
  rw [hsz, ByteArray.extract_zero_size]

/-- **Encoding uniqueness**: each `TLV` value has exactly one accepted
encoding — DER canonicity as seen through the strict parser. -/
theorem decode_inj {b₁ b₂ : ByteArray} {tlv : TLV}
    (h₁ : decode b₁ = .ok tlv) (h₂ : decode b₂ = .ok tlv) : b₁ = b₂ := by
  rw [← decode_encoded h₁, ← decode_encoded h₂]

/-- `decode` consumes exactly its input: header and contents sizes add up to
the input size. -/
theorem decode_size {bytes : ByteArray} {tlv : TLV}
    (h : decode bytes = .ok tlv) :
    tlv.headerSize + tlv.contents.size = bytes.size := by
  have henc := decode_encoded h
  unfold decode at h
  split at h
  · cases h
  rename_i tlv₀ rest heq
  split at h
  · cases h
  simp only [Except.ok.injEq] at h
  subst h
  rw [← henc, Reader.readTLV_sizes heq]

/-- **Re-decode identity**: the slice retained by any successful `readTLV` —
even one taken mid-stream or from nested contents — is itself one complete
DER value, and decoding it reproduces the same `TLV` (reported at offset 0)
with nothing left over. -/
theorem readTLV_encoded_decode {r : Reader} {tlv : TLV} {r' : Reader}
    (h : r.readTLV = .ok (tlv, r')) :
    decode tlv.encoded = .ok { tlv with offset := 0 } := by
  obtain ⟨hb, hg, h1, h2, h3, h4, h5, h6⟩ := Reader.readTLV_spec h
  have hsize : tlv.encoded.size = r'.offset - r.offset := by
    rw [h5, ByteArray.size_extract]
    omega
  have hagr : Reader.Agrees r (Reader.ofBytes tlv.encoded)
      (r'.offset - r.offset) := by
    refine ⟨by omega, ?_, ?_⟩
    · show 0 + (r'.offset - r.offset) ≤ tlv.encoded.size
      omega
    · intro k hk
      show r.bytes.get! (r.offset + k) = tlv.encoded.get! (0 + k)
      rw [Nat.zero_add, h5, extract_get! (by omega) (by omega)]
  have hql := Reader.readTLV_agrees h hagr
  unfold decode
  simp only [hql]
  rw [Reader.requireEnd_ok
    (show (0 : Nat) + (r'.offset - r.offset) = tlv.encoded.size by omega)]
  rfl

/-- Re-decode identity at the root: `decode` is idempotent through the
retained encoding. -/
theorem decode_idem {bytes : ByteArray} {tlv : TLV}
    (h : decode bytes = .ok tlv) : decode tlv.encoded = .ok tlv := by
  rw [decode_encoded h]
  exact h

/-- **Trailing data is rejected**: appending anything to an accepted encoding
makes `decode` fail — the root decoder consumes exactly one value. -/
theorem decode_append_ne_ok {bytes extra : ByteArray} {tlv : TLV}
    (h : decode bytes = .ok tlv) (hextra : extra.size ≠ 0) (tlv' : TLV) :
    decode (bytes ++ extra) ≠ .ok tlv' := by
  intro habs
  unfold decode at h habs
  split at h
  · cases h
  rename_i tlv₀ rest heq
  split at h
  · cases h
  rename_i hend
  have hoff := Reader.requireEnd_eq_ok hend
  obtain ⟨hb, hg, h1, h2, h3, h4, h5, h6⟩ := Reader.readTLV_spec heq
  have hrsize : rest.offset = bytes.size := by
    rw [hoff]
    show rest.bytes.size = bytes.size
    rw [hb]
    rfl
  have hszap : (bytes ++ extra).size = bytes.size + extra.size :=
    ByteArray.size_append
  have hagr : Reader.Agrees (Reader.ofBytes bytes)
      (Reader.ofBytes (bytes ++ extra))
      (rest.offset - (Reader.ofBytes bytes).offset) := by
    refine ⟨?_, ?_, ?_⟩
    · show (0 : Nat) + (rest.offset - 0) ≤ bytes.size
      omega
    · show (0 : Nat) + (rest.offset - 0) ≤ (bytes ++ extra).size
      omega
    · intro k hk
      show bytes.get! (0 + k) = (bytes ++ extra).get! (0 + k)
      rw [Nat.zero_add]
      have h0 : (Reader.ofBytes bytes).offset = 0 := rfl
      rw [h0] at hk
      exact (get!_append_left (by omega)).symm
  have hql := Reader.readTLV_agrees heq hagr
  simp only [hql] at habs
  split at habs
  · cases habs
  rename_i hend2
  have hq := Reader.requireEnd_eq_ok hend2
  have hq' : (0 : Nat) + (rest.offset - (Reader.ofBytes bytes).offset) =
      (bytes ++ extra).size := hq
  have h0 : (Reader.ofBytes bytes).offset = 0 := rfl
  omega

end DER
end X509
end TLS13
