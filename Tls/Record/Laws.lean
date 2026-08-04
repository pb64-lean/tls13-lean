module

public import Tls.Record
-- The open∘seal law quantifies over the opaque AEAD binding, so its statement
-- names the HACL* functions.
public import HaclStar.Aead
-- The §7.3 / §7.2 key-derivation laws are stated against the RFC 8446
-- specification and its refinement by `TLS13.KeySchedule`.
public import TLS13.KeySchedule.Refinement
import all Tls.Record

public section

namespace Tls
namespace Record

/-!
Kernel-checked laws about the executable record layer in `Tls.Record`.

Everything here is proved about the very functions the client and server
state machines run; there is no shadow model. The centerpiece is
`Decoder.feed_conservation`: a successful `feed` neither invents, drops,
nor reorders bytes — re-encoding the emitted records and appending the
retained buffer reproduces the exact input stream.
-/

/-! ## ByteArray helpers

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
  rw [get!_eq_getElem (by simp [ByteArray.size_append]; omega), get!_eq_getElem h,
    ByteArray.getElem_append_left h]

private theorem get!_push {a : ByteArray} {u : UInt8} {i : Nat}
    (h : i < a.size + 1) :
    (a.push u).get! i = if i < a.size then a.get! i else u := by
  rcases a with ⟨data⟩
  have h' : i < data.size + 1 := h
  show (data.push u)[i]! = if i < data.size then data[i]! else u
  rw [getElem!_pos (data.push u) i (by simp [Array.size_push]; omega),
    Array.getElem_push]
  by_cases hi : i < data.size
  · rw [dif_pos hi, if_pos hi, getElem!_pos data i hi]
  · rw [dif_neg hi, if_neg hi]

/-- The `Except Error` monad operations, reduced to constructors. -/
private theorem except_bind_ok {α β : Type} (a : α) (f : α → Except Error β) :
    (Except.ok a >>= f) = f a := rfl
private theorem except_bind_error {α β : Type} (e : Error)
    (f : α → Except Error β) :
    ((Except.error e : Except Error α) >>= f) = Except.error e := rfl
private theorem except_pure {α : Type} (a : α) :
    (pure a : Except Error α) = Except.ok a := rfl
private theorem except_throw {α : Type} (e : Error) :
    (throw e : Except Error α) = Except.error e := rfl
private theorem except_map_throw {α β : Type} (f : α → β) (e : Error) :
    (f <$> (throw e : Except Error α)) = (Except.error e : Except Error β) := rfl

/-- Peel an `unless c do throw e` guard out of a successful `do` block. The
guard elaborates to a join point that `split at` cannot enter, so unification
against this term-level shape does the work instead. -/
private theorem unless_ok {α : Type} {c : Bool} {e : Error}
    {f : PUnit → Except Error α} {b : α}
    (h : (if c = true then (pure PUnit.unit : Except Error PUnit) >>= f
          else (throw e : Except Error PUnit) >>= f) = .ok b) :
    c = true ∧ f PUnit.unit = .ok b := by
  by_cases hc : c = true
  · rw [if_pos hc] at h; exact ⟨hc, h⟩
  · rw [if_neg hc] at h; cases h

/-! ## Content types -/

/-- Decoding inverts encoding on content-type bytes. -/
theorem ContentType.ofUInt8?_toUInt8 (ct : ContentType) :
    ContentType.ofUInt8? ct.toUInt8 = some ct := by
  cases ct <;> rfl

/-- Encoding inverts decoding: a successfully decoded content type
re-encodes to the original byte. -/
theorem ContentType.toUInt8_eq_of_ofUInt8? {value : UInt8} {ct : ContentType}
    (h : ContentType.ofUInt8? value = some ct) : ct.toUInt8 = value := by
  unfold ContentType.ofUInt8? at h
  split at h <;> simp_all
  all_goals (subst h; rfl)

/-! ## The five-byte record header -/

theorem size_encodeHeader (contentType : ContentType) (version : UInt16)
    (fragmentLength : Nat) :
    (encodeHeader contentType version fragmentLength).size = headerLength := rfl

theorem RawRecord.size_header (record : RawRecord) :
    record.header.size = headerLength := rfl

theorem RawRecord.size_encode (record : RawRecord) :
    record.encode.size = headerLength + record.fragment.size := by
  simp [RawRecord.encode, ByteArray.size_append, RawRecord.size_header]

/-! ### Byte (de)composition

These are the only bit-level identities the record layer needs. They are
proved *arithmetically* — `Nat.shiftLeft_add_eq_or_of_lt` turns a big-endian
recomposition into `a * 2 ^ i + b`, which `omega` finishes — rather than by
`bv_decide`, so no LRAT certificate enters the trusted computing base. -/

/-- Disjoint `|||` is `+`: the low `i` bits of the left operand are clear. -/
private theorem or_add_lt {a b i : Nat} (hb : b < 2 ^ i) :
    a * 2 ^ i ||| b = a * 2 ^ i + b := by
  rw [show a * 2 ^ i = a <<< i from (Nat.shiftLeft_eq a i).symm,
    ← Nat.shiftLeft_add_eq_or_of_lt hb]

private theorem hi_lo_recompose (v : UInt16) :
    ((v >>> 8).toUInt8.toUInt16 <<< 8 ||| v.toUInt8.toUInt16) = v := by
  apply UInt16.toNat_inj.mp
  have hv := v.toNat_lt
  simp only [UInt16.toNat_or, UInt16.toNat_shiftLeft, UInt8.toNat_toUInt16,
    UInt16.toNat_toUInt8, UInt16.toNat_shiftRight,
    show UInt16.toNat 8 % 16 = 8 from rfl, Nat.shiftLeft_eq,
    Nat.shiftRight_eq_div_pow]
  rw [show v.toNat / 2 ^ 8 % 2 ^ 8 * 2 ^ 8 % 2 ^ 16 = v.toNat / 2 ^ 8 * 2 ^ 8 from by
      omega,
    or_add_lt (i := 8)]
  all_goals omega

private theorem recompose_hi (x y : UInt8) :
    ((x.toUInt16 <<< 8 ||| y.toUInt16) >>> 8).toUInt8 = x := by
  apply UInt8.toNat_inj.mp
  have hx := x.toNat_lt
  have hy := y.toNat_lt
  simp only [UInt16.toNat_toUInt8, UInt16.toNat_shiftRight, UInt16.toNat_or,
    UInt16.toNat_shiftLeft, UInt8.toNat_toUInt16,
    show UInt16.toNat 8 % 16 = 8 from rfl, Nat.shiftLeft_eq,
    Nat.shiftRight_eq_div_pow]
  rw [show x.toNat * 2 ^ 8 % 2 ^ 16 = x.toNat * 2 ^ 8 from by omega,
    or_add_lt (i := 8)]
  all_goals omega

private theorem recompose_lo (x y : UInt8) :
    (x.toUInt16 <<< 8 ||| y.toUInt16).toUInt8 = y := by
  apply UInt8.toNat_inj.mp
  have hx := x.toNat_lt
  have hy := y.toNat_lt
  simp only [UInt16.toNat_toUInt8, UInt16.toNat_or, UInt16.toNat_shiftLeft,
    UInt8.toNat_toUInt16, show UInt16.toNat 8 % 16 = 8 from rfl,
    Nat.shiftLeft_eq]
  rw [show x.toNat * 2 ^ 8 % 2 ^ 16 = x.toNat * 2 ^ 8 from by omega,
    or_add_lt (i := 8)]
  all_goals omega

/-- XOR with a fixed byte is injective. -/
private theorem xor_cancel_left {a b c : UInt8} (h : a ^^^ b = a ^^^ c) : b = c := by
  have hc := congrArg (a ^^^ ·) h
  simp only [← UInt8.xor_assoc, UInt8.xor_self, UInt8.zero_xor] at hc
  exact hc

/-- Reading byte 0 of an encoded header (with anything appended) returns the
content-type byte. -/
theorem get!_encodeHeader_append_zero (contentType : ContentType)
    (version : UInt16) (fragmentLength : Nat) (rest : ByteArray) :
    (encodeHeader contentType version fragmentLength ++ rest).get! 0 =
      contentType.toUInt8 := by
  rw [get!_append_left (by rw [size_encodeHeader]; decide)]
  rfl

/-- Reading bytes 1-2 of an encoded header returns the protocol version. -/
theorem getUInt16_encodeHeader_append_version (contentType : ContentType)
    (version : UInt16) (fragmentLength : Nat) (rest : ByteArray) :
    getUInt16 (encodeHeader contentType version fragmentLength ++ rest) 1 =
      version := by
  unfold getUInt16
  rw [get!_append_left (by rw [size_encodeHeader]; decide),
    get!_append_left (by rw [size_encodeHeader]; decide)]
  show ((version >>> 8).toUInt8.toUInt16 <<< 8 ||| version.toUInt8.toUInt16) =
    version
  exact hi_lo_recompose version

/-- Reading bytes 3-4 of an encoded header returns the fragment length,
provided it fits in 16 bits (every legal TLS record length does). -/
theorem getUInt16_encodeHeader_append_length (contentType : ContentType)
    (version : UInt16) {fragmentLength : Nat} (rest : ByteArray)
    (h : fragmentLength < 65536) :
    (getUInt16 (encodeHeader contentType version fragmentLength ++ rest)
        3).toNat = fragmentLength := by
  unfold getUInt16
  rw [get!_append_left (by rw [size_encodeHeader]; decide),
    get!_append_left (by rw [size_encodeHeader]; decide)]
  show (((UInt16.ofNat fragmentLength >>> 8).toUInt8.toUInt16 <<< 8 |||
    (UInt16.ofNat fragmentLength).toUInt8.toUInt16)).toNat = fragmentLength
  rw [hi_lo_recompose, UInt16.toNat_ofNat', Nat.mod_eq_of_lt h]

/-! ## Record framing -/

/-- Byte-wise extensionality through `get!`. -/
private theorem ext_get! {a b : ByteArray} (hs : a.size = b.size)
    (h : ∀ i, i < a.size → a.get! i = b.get! i) : a = b := by
  apply ByteArray.ext_getElem hs
  intro i hi hi'
  rw [← get!_eq_getElem hi, ← get!_eq_getElem hi']
  exact h i hi

/-- A five-byte header is determined by the five reads the decoder performs. -/
private theorem header_eq_extract {b : ByteArray} {ct : ContentType}
    {v : UInt16} {n : Nat} (hsize : headerLength ≤ b.size)
    (h0 : ct.toUInt8 = b.get! 0)
    (h1 : (v >>> 8).toUInt8 = b.get! 1)
    (h2 : v.toUInt8 = b.get! 2)
    (h3 : (UInt16.ofNat n >>> 8).toUInt8 = b.get! 3)
    (h4 : (UInt16.ofNat n).toUInt8 = b.get! 4) :
    encodeHeader ct v n = b.extract 0 headerLength := by
  apply ext_get!
  · rw [size_encodeHeader, ByteArray.size_extract]
    omega
  · intro i hi
    rw [size_encodeHeader] at hi
    have hbi : (b.extract 0 headerLength).get! i = b.get! i := by
      rw [get!_eq_getElem (by rw [ByteArray.size_extract]; omega),
        ByteArray.getElem_extract, get!_eq_getElem (by omega)]
      simp
    rw [hbi]
    match i, hi with
    | 0, _ => exact h0
    | 1, _ => exact h1
    | 2, _ => exact h2
    | 3, _ => exact h3
    | 4, _ => exact h4

/-- Splitting a byte array at a header boundary and a record boundary and
re-appending the pieces is the identity. -/
private theorem extract_stitch (b : ByteArray) {mid : Nat}
    (h5 : headerLength ≤ mid) (hmid : mid ≤ b.size) :
    b.extract 0 headerLength ++ b.extract headerLength mid ++
      b.extract mid b.size = b := by
  rw [ByteArray.extract_append_extract, Nat.min_eq_left (Nat.zero_le _),
    Nat.max_eq_right h5, ByteArray.extract_append_extract,
    Nat.min_eq_left (Nat.zero_le _), Nat.max_eq_right hmid]
  exact ByteArray.extract_zero_size

/-- **Framing is conservative**: a record framed out of `buffered` re-encodes,
together with the unconsumed remainder, to exactly the input bytes. The
decoder preserves the received `legacy_record_version` precisely so this holds
byte-for-byte. -/
theorem decodeStep_conservation {buffered rest : ByteArray}
    {record : RawRecord}
    (h : decodeStep buffered = .ok (some (record, rest))) :
    record.encode ++ rest = buffered := by
  unfold decodeStep at h
  split at h
  · simp at h
  · split at h
    · simp at h
    · rename_i ct hct
      split at h
      · simp at h
      · split at h
        · simp at h
        · simp only [Except.ok.injEq, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨hrec, hrest⟩ := h
          subst hrec
          subst hrest
          simp only [RawRecord.encode, RawRecord.header]
          have hlen5' : headerLength ≤ buffered.size := by omega
          have hcomplete' :
              headerLength + (getUInt16 buffered 3).toNat ≤ buffered.size := by
            omega
          have hfragsize :
              (buffered.extract headerLength
                (headerLength + (getUInt16 buffered 3).toNat)).size =
                (getUInt16 buffered 3).toNat := by
            rw [ByteArray.size_extract]
            omega
          rw [hfragsize]
          rw [header_eq_extract hlen5'
            (ContentType.toUInt8_eq_of_ofUInt8? hct)
            (show (getUInt16 buffered 1 >>> 8).toUInt8 = buffered.get! 1 from
              recompose_hi (buffered.get! 1) (buffered.get! 2))
            (show (getUInt16 buffered 1).toUInt8 = buffered.get! 2 from
              recompose_lo (buffered.get! 1) (buffered.get! 2))
            (show (UInt16.ofNat (getUInt16 buffered 3).toNat >>> 8).toUInt8 =
                buffered.get! 3 by
              rw [UInt16.ofNat_toNat]
              exact recompose_hi (buffered.get! 3) (buffered.get! 4))
            (show (UInt16.ofNat (getUInt16 buffered 3).toNat).toUInt8 =
                buffered.get! 4 by
              rw [UInt16.ofNat_toNat]
              exact recompose_lo (buffered.get! 3) (buffered.get! 4))]
          exact extract_stitch buffered (by omega) hcomplete'

/-- Fragment-length bounds under which `decodeStep` accepts a record's exact
wire encoding: TLSCiphertext limits for outer `application_data` records,
TLSPlaintext limits for everything else. -/
def RawRecord.WellFormed (record : RawRecord) : Prop :=
  match record.contentType with
  | .applicationData =>
      aeadTagLength + 1 ≤ record.fragment.size ∧
        record.fragment.size ≤ maxCiphertextLength
  | _ => record.fragment.size ≤ maxPlaintextLength

private theorem checkFragmentLength_wellFormed {record : RawRecord}
    (h : record.WellFormed) :
    checkFragmentLength record.contentType record.fragment.size = .ok () := by
  obtain ⟨ct, v, frag⟩ := record
  cases ct with
  | applicationData =>
      have hlo : aeadTagLength + 1 ≤ frag.size := h.1
      have hhi : frag.size ≤ maxCiphertextLength := h.2
      show checkFragmentLength .applicationData frag.size = .ok ()
      unfold checkFragmentLength
      rw [if_pos (by decide), if_neg (by omega), if_neg (by omega)]
  | changeCipherSpec =>
      have h' : frag.size ≤ maxPlaintextLength := h
      show checkFragmentLength .changeCipherSpec frag.size = .ok ()
      unfold checkFragmentLength
      rw [if_neg (by decide), if_neg (by omega)]
  | alert =>
      have h' : frag.size ≤ maxPlaintextLength := h
      show checkFragmentLength .alert frag.size = .ok ()
      unfold checkFragmentLength
      rw [if_neg (by decide), if_neg (by omega)]
  | handshake =>
      have h' : frag.size ≤ maxPlaintextLength := h
      show checkFragmentLength .handshake frag.size = .ok ()
      unfold checkFragmentLength
      rw [if_neg (by decide), if_neg (by omega)]

private theorem WellFormed.fragment_lt_65536 {record : RawRecord}
    (h : record.WellFormed) : record.fragment.size < 65536 := by
  unfold RawRecord.WellFormed at h
  split at h
  · have := h.2
    simp only [maxCiphertextLength] at this
    omega
  · simp only [maxPlaintextLength] at h
    omega

/-- **Round trip with explicit residual**: the decoder accepts the exact wire
encoding of any well-formed record and returns it unchanged, consuming
nothing beyond it. -/
theorem decodeStep_encode_append {record : RawRecord} (rest : ByteArray)
    (h : record.WellFormed) :
    decodeStep (record.encode ++ rest) = .ok (some (record, rest)) := by
  obtain ⟨ct, v, frag⟩ := record
  have hlt : frag.size < 65536 := WellFormed.fragment_lt_65536 h
  have hcheck : checkFragmentLength ct frag.size = .ok () :=
    checkFragmentLength_wellFormed h
  rw [show RawRecord.encode ⟨ct, v, frag⟩ ++ rest =
      encodeHeader ct v frag.size ++ (frag ++ rest) by
    simp [RawRecord.encode, RawRecord.header, ByteArray.append_assoc]]
  have hXsize : (encodeHeader ct v frag.size ++ (frag ++ rest)).size =
      headerLength + (frag.size + rest.size) := by
    rw [ByteArray.size_append, ByteArray.size_append, size_encodeHeader]
  have hlen : (getUInt16 (encodeHeader ct v frag.size ++ (frag ++ rest))
      3).toNat = frag.size :=
    getUInt16_encodeHeader_append_length ct v (frag ++ rest) hlt
  have hif1 : ¬ ((encodeHeader ct v frag.size ++ (frag ++ rest)).size <
      headerLength) := by
    rw [hXsize]
    omega
  have hif2 : ¬ ((encodeHeader ct v frag.size ++ (frag ++ rest)).size <
      headerLength + frag.size) := by
    rw [hXsize]
    omega
  have hextract1 : (encodeHeader ct v frag.size ++ (frag ++ rest)).extract
      headerLength (headerLength + frag.size) = frag := by
    rw [ByteArray.extract_append]
    rw [show (encodeHeader ct v frag.size).extract headerLength
        (headerLength + frag.size) = ByteArray.empty from
      ByteArray.extract_eq_empty_iff.mpr
        (by rw [size_encodeHeader]; omega)]
    rw [ByteArray.empty_append, size_encodeHeader, Nat.sub_self,
      Nat.add_sub_cancel_left]
    exact ByteArray.extract_append_eq_left rfl
  have hextract2 : (encodeHeader ct v frag.size ++ (frag ++ rest)).extract
      (headerLength + frag.size)
      ((encodeHeader ct v frag.size ++ (frag ++ rest)).size) = rest := by
    rw [hXsize, ByteArray.extract_append]
    rw [show (encodeHeader ct v frag.size).extract (headerLength + frag.size)
        (headerLength + (frag.size + rest.size)) = ByteArray.empty from
      ByteArray.extract_eq_empty_iff.mpr
        (by rw [size_encodeHeader]; omega)]
    rw [ByteArray.empty_append, size_encodeHeader, Nat.add_sub_cancel_left,
      Nat.add_sub_cancel_left]
    exact ByteArray.extract_append_eq_right rfl rfl
  simp only [decodeStep, get!_encodeHeader_append_zero,
    ContentType.ofUInt8?_toUInt8, hlen, hcheck, hif1, hif2, if_false,
    getUInt16_encodeHeader_append_version, hextract1, hextract2]

/-- `decodeBuffered` on a buffer whose head is incomplete returns it
untouched. -/
private theorem decodeBuffered_step_none {b : ByteArray}
    {recs : Array RawRecord} (hstep : decodeStep b = .ok none) :
    decodeBuffered b recs = .ok (b, recs) := by
  rw [decodeBuffered]
  split <;> simp_all

/-- `decodeBuffered` consumes one record at a time. -/
private theorem decodeBuffered_step_some {b rest : ByteArray}
    {recs : Array RawRecord} {record : RawRecord}
    (hstep : decodeStep b = .ok (some (record, rest))) :
    decodeBuffered b recs = decodeBuffered rest (recs.push record) := by
  rw [decodeBuffered]
  split <;> simp_all

private theorem decodeBuffered_step_error {b : ByteArray}
    {recs : Array RawRecord} {e : Error} (hstep : decodeStep b = .error e) :
    decodeBuffered b recs = .error e := by
  rw [decodeBuffered]
  split <;> simp_all

theorem encodeRawRecords_empty : encodeRawRecords #[] = ByteArray.empty := rfl

theorem encodeRawRecords_push (records : Array RawRecord)
    (record : RawRecord) :
    encodeRawRecords (records.push record) =
      encodeRawRecords records ++ record.encode := by
  unfold encodeRawRecords
  rw [Array.foldl_push]

/-- Conservation for the framing loop: re-encoding everything framed so far
and appending the residual reproduces the accumulated input. -/
theorem decodeBuffered_conservation {buffered residual : ByteArray}
    {records emitted : Array RawRecord}
    (h : decodeBuffered buffered records = .ok (residual, emitted)) :
    encodeRawRecords emitted ++ residual =
      encodeRawRecords records ++ buffered := by
  match hstep : decodeStep buffered with
  | .error e =>
      rw [decodeBuffered_step_error hstep] at h
      cases h
  | .ok none =>
      rw [decodeBuffered_step_none hstep] at h
      simp only [Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨h1, h2⟩ := h
      subst h1
      subst h2
      rfl
  | .ok (some (record, rest)) =>
      rw [decodeBuffered_step_some hstep] at h
      have ih := decodeBuffered_conservation h
      rw [encodeRawRecords_push, ByteArray.append_assoc,
        decodeStep_conservation hstep] at ih
      exact ih
  termination_by buffered.size
  decreasing_by exact decodeStep_size_lt hstep

/-- A successful framing pass leaves no complete record (and no detectable
header error) in the residual buffer. -/
theorem decodeBuffered_residual {buffered residual : ByteArray}
    {records emitted : Array RawRecord}
    (h : decodeBuffered buffered records = .ok (residual, emitted)) :
    decodeStep residual = .ok none := by
  match hstep : decodeStep buffered with
  | .error e =>
      rw [decodeBuffered_step_error hstep] at h
      cases h
  | .ok none =>
      rw [decodeBuffered_step_none hstep] at h
      simp only [Except.ok.injEq, Prod.mk.injEq] at h
      rw [← h.1]
      exact hstep
  | .ok (some (record, rest)) =>
      rw [decodeBuffered_step_some hstep] at h
      exact decodeBuffered_residual h
  termination_by buffered.size
  decreasing_by exact decodeStep_size_lt hstep

/-- **Conservation (the record layer neither invents nor drops bytes)**: for
any successful `feed`, re-encoding the emitted records and appending the
retained buffer reproduces the prior buffer plus the chunk, byte for byte. -/
theorem Decoder.feed_conservation {decoder next : Decoder}
    {chunk : ByteArray} {records : Array RawRecord}
    (h : decoder.feed chunk = .ok (next, records)) :
    encodeRawRecords records ++ next.buffered =
      decoder.buffered ++ chunk := by
  unfold Decoder.feed at h
  cases hd : decodeBuffered (decoder.buffered ++ chunk) #[] with
  | error e =>
      rw [hd, except_bind_error] at h
      cases h
  | ok out =>
      obtain ⟨residual, emitted⟩ := out
      rw [hd, except_bind_ok] at h
      simp only [except_pure, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨h1, h2⟩ := h
      subst h1
      subst h2
      have := decodeBuffered_conservation hd
      rwa [encodeRawRecords_empty, ByteArray.empty_append] at this

/-- After a successful `feed`, the retained buffer holds no complete record:
everything frameable was emitted. -/
theorem Decoder.feed_residual {decoder next : Decoder} {chunk : ByteArray}
    {records : Array RawRecord}
    (h : decoder.feed chunk = .ok (next, records)) :
    decodeStep next.buffered = .ok none := by
  unfold Decoder.feed at h
  cases hd : decodeBuffered (decoder.buffered ++ chunk) #[] with
  | error e =>
      rw [hd, except_bind_error] at h
      cases h
  | ok out =>
      obtain ⟨residual, emitted⟩ := out
      rw [hd, except_bind_ok] at h
      simp only [except_pure, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨h1, h2⟩ := h
      subst h1
      exact decodeBuffered_residual hd

private theorem wellFormed_mk {ct : ContentType} {v : UInt16}
    {frag : ByteArray}
    (h : match ct with
      | .applicationData =>
          aeadTagLength + 1 ≤ frag.size ∧ frag.size ≤ maxCiphertextLength
      | _ => frag.size ≤ maxPlaintextLength) :
    RawRecord.WellFormed ⟨ct, v, frag⟩ := by
  cases ct <;> exact h

/-- Frames produced by the decoder satisfy the encoder-side length bounds. -/
theorem decodeStep_wellFormed {buffered rest : ByteArray}
    {record : RawRecord}
    (h : decodeStep buffered = .ok (some (record, rest))) :
    record.WellFormed := by
  unfold decodeStep at h
  split at h
  · simp at h
  · split at h
    · simp at h
    · rename_i ct hct
      split at h
      · simp at h
      · rename_i hcheck
        split at h
        · simp at h
        · simp only [Except.ok.injEq, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨hrec, hrest⟩ := h
          have hsize : (buffered.extract headerLength
              (headerLength + (getUInt16 buffered 3).toNat)).size =
              (getUInt16 buffered 3).toNat := by
            rw [ByteArray.size_extract]
            omega
          rw [← hrec]
          apply wellFormed_mk
          cases ct with
          | applicationData =>
              unfold checkFragmentLength at hcheck
              rw [if_pos (by decide)] at hcheck
              split at hcheck
              · cases hcheck
              · split at hcheck
                · cases hcheck
                · refine ⟨?_, ?_⟩ <;> (rw [hsize]; omega)
          | changeCipherSpec =>
              unfold checkFragmentLength at hcheck
              rw [if_neg (by decide)] at hcheck
              split at hcheck
              · cases hcheck
              · rw [hsize]
                omega
          | alert =>
              unfold checkFragmentLength at hcheck
              rw [if_neg (by decide)] at hcheck
              split at hcheck
              · cases hcheck
              · rw [hsize]
                omega
          | handshake =>
              unfold checkFragmentLength at hcheck
              rw [if_neg (by decide)] at hcheck
              split at hcheck
              · cases hcheck
              · rw [hsize]
                omega

/-- Framing is stable under additional input: a complete frame at the head
of the buffer decodes identically no matter how many bytes follow it. -/
theorem decodeStep_append_some {buffered rest : ByteArray}
    {record : RawRecord} (chunk : ByteArray)
    (h : decodeStep buffered = .ok (some (record, rest))) :
    decodeStep (buffered ++ chunk) = .ok (some (record, rest ++ chunk)) := by
  rw [← decodeStep_conservation h, ByteArray.append_assoc]
  exact decodeStep_encode_append (rest ++ chunk) (decodeStep_wellFormed h)

private theorem decodeBuffered_accum {b res : ByteArray}
    {acc ems : Array RawRecord} (recs : Array RawRecord)
    (h : decodeBuffered b acc = .ok (res, ems)) :
    decodeBuffered b (recs ++ acc) = .ok (res, recs ++ ems) := by
  match hstep : decodeStep b with
  | .error e =>
      rw [decodeBuffered_step_error hstep] at h
      cases h
  | .ok none =>
      rw [decodeBuffered_step_none hstep] at h
      simp only [Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨h1, h2⟩ := h
      subst h1
      subst h2
      exact decodeBuffered_step_none hstep
  | .ok (some (record, rest)) =>
      rw [decodeBuffered_step_some hstep] at h
      have ih := decodeBuffered_accum (recs := recs) h
      rw [Array.append_push] at ih
      rw [decodeBuffered_step_some hstep]
      exact ih
  termination_by b.size
  decreasing_by exact decodeStep_size_lt hstep

private theorem decodeBuffered_extend {b res chunk : ByteArray}
    {recs ems : Array RawRecord}
    (h : decodeBuffered b recs = .ok (res, ems)) :
    decodeBuffered (b ++ chunk) recs = decodeBuffered (res ++ chunk) ems := by
  match hstep : decodeStep b with
  | .error e =>
      rw [decodeBuffered_step_error hstep] at h
      cases h
  | .ok none =>
      rw [decodeBuffered_step_none hstep] at h
      simp only [Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨h1, h2⟩ := h
      subst h1
      subst h2
      rfl
  | .ok (some (record, rest)) =>
      rw [decodeBuffered_step_some hstep] at h
      rw [decodeBuffered_step_some (decodeStep_append_some chunk hstep)]
      exact decodeBuffered_extend h
  termination_by b.size
  decreasing_by exact decodeStep_size_lt hstep

/-- **Fragmentation independence**: transport chunk boundaries are
irrelevant. Feeding `c1` and then `c2` yields exactly the records and
residual of feeding `c1 ++ c2` at once. -/
theorem Decoder.feed_append {d d1 d2 : Decoder} {c1 c2 : ByteArray}
    {r1 r2 : Array RawRecord}
    (h1 : d.feed c1 = .ok (d1, r1)) (h2 : d1.feed c2 = .ok (d2, r2)) :
    d.feed (c1 ++ c2) = .ok (d2, r1 ++ r2) := by
  unfold Decoder.feed at h1 h2 ⊢
  cases hd1 : decodeBuffered (d.buffered ++ c1) #[] with
  | error e =>
      rw [hd1, except_bind_error] at h1
      cases h1
  | ok out1 =>
      obtain ⟨res1, ems1⟩ := out1
      rw [hd1, except_bind_ok] at h1
      simp only [except_pure, Except.ok.injEq, Prod.mk.injEq] at h1
      obtain ⟨hb1, hr1⟩ := h1
      cases hd2 : decodeBuffered (d1.buffered ++ c2) #[] with
      | error e =>
          rw [hd2, except_bind_error] at h2
          cases h2
      | ok out2 =>
          obtain ⟨res2, ems2⟩ := out2
          rw [hd2, except_bind_ok] at h2
          simp only [except_pure, Except.ok.injEq, Prod.mk.injEq] at h2
          obtain ⟨hb2, hr2⟩ := h2
          have hd1' : decodeBuffered (d.buffered ++ c1) #[] =
              .ok (d1.buffered, r1) := by
            rw [hd1, ← hb1, hr1]
          have hd2' : decodeBuffered (d1.buffered ++ c2) #[] =
              .ok (d2.buffered, r2) := by
            rw [hd2, ← hb2, hr2]
          have hext := decodeBuffered_extend (chunk := c2) hd1'
          have haccum := decodeBuffered_accum (recs := r1) hd2'
          rw [Array.append_empty] at haccum
          rw [show d.buffered ++ (c1 ++ c2) = d.buffered ++ c1 ++ c2 from
            ByteArray.append_assoc.symm]
          rw [hext, haccum, except_bind_ok]
          simp only [except_pure]

/-! ## Sequence numbers and nonces -/

theorem size_sequenceBytes (seq : UInt64) :
    (sequenceBytes seq).size = aeadIvLength := rfl

/-- The sequence encoding is lossless. -/
theorem sequenceBytes_inj (s t : UInt64)
    (h : sequenceBytes s = sequenceBytes t) : s = t := by
  unfold sequenceBytes at h
  simp only [ByteArray.mk.injEq, Array.mk.injEq, List.cons.injEq, and_true] at h
  obtain ⟨-, -, -, -, h56, h48, h40, h32, h24, h16, h8, h0⟩ := h
  apply UInt64.toNat_inj.mp
  have hs := s.toNat_lt
  have ht := t.toNat_lt
  simp only [← UInt8.toNat_inj, UInt64.toNat_toUInt8, UInt64.toNat_shiftRight,
    show UInt64.toNat 56 % 64 = 56 from rfl,
    show UInt64.toNat 48 % 64 = 48 from rfl,
    show UInt64.toNat 40 % 64 = 40 from rfl,
    show UInt64.toNat 32 % 64 = 32 from rfl,
    show UInt64.toNat 24 % 64 = 24 from rfl,
    show UInt64.toNat 16 % 64 = 16 from rfl,
    show UInt64.toNat 8 % 64 = 8 from rfl,
    Nat.shiftRight_eq_div_pow] at h56 h48 h40 h32 h24 h16 h8 h0
  omega

theorem size_xorBytes (count : Nat) (a b : ByteArray) :
    (xorBytes count a b).size = count := by
  induction count with
  | zero => rfl
  | succ n ih => simp [xorBytes, ByteArray.size_push, ih]

theorem get!_xorBytes {count i : Nat} (a b : ByteArray) (h : i < count) :
    (xorBytes count a b).get! i = a.get! i ^^^ b.get! i := by
  induction count with
  | zero => omega
  | succ n ih =>
      show ((xorBytes n a b).push _).get! i = _
      rw [get!_push (by rw [size_xorBytes]; omega)]
      rcases Nat.lt_or_ge i n with hi | hi
      · rw [if_pos (by rw [size_xorBytes]; exact hi)]
        exact ih hi
      · have hin : i = n := by omega
        subst hin
        rw [if_neg (by rw [size_xorBytes]; omega)]

private theorem nonce_ok {keys : TrafficKeys} {n : ByteArray}
    (h : keys.nonce = .ok n) :
    keys.iv.size = aeadIvLength ∧
      n = xorBytes aeadIvLength keys.iv (sequenceBytes keys.seq) := by
  unfold TrafficKeys.nonce at h
  split at h <;>
    simp_all [except_bind_ok, except_bind_error, except_pure, except_throw]

/-- A successful nonce always has the AEAD IV width. -/
theorem TrafficKeys.size_nonce {keys : TrafficKeys} {n : ByteArray}
    (h : keys.nonce = .ok n) : n.size = aeadIvLength := by
  rw [(nonce_ok h).2, size_xorBytes]

/-- Byte `i` of the nonce is the IV byte XOR the padded big-endian sequence
byte (RFC 8446 §5.3). -/
theorem TrafficKeys.get!_nonce {keys : TrafficKeys} {n : ByteArray} {i : Nat}
    (h : keys.nonce = .ok n) (hi : i < aeadIvLength) :
    n.get! i = keys.iv.get! i ^^^ (sequenceBytes keys.seq).get! i := by
  rw [(nonce_ok h).2, get!_xorBytes _ _ hi]

/-- The per-record nonce of a traffic epoch, as a function of its static IV and
the record sequence number (RFC 8446 §5.3). `TrafficKeys.nonce` computes exactly
this; naming it separately lets the nonce laws below talk about the nonce of a
sequence number the state machine has not reached yet. -/
def nonceOf (iv : ByteArray) (seq : UInt64) : ByteArray :=
  xorBytes aeadIvLength iv (sequenceBytes seq)

theorem TrafficKeys.nonce_eq {keys : TrafficKeys} {n : ByteArray}
    (h : keys.nonce = .ok n) : n = nonceOf keys.iv keys.seq := (nonce_ok h).2

/-- For a fixed static IV, the nonce determines the record sequence number:
XOR with a constant is a bijection and the sequence encoding is lossless. -/
theorem nonceOf_inj {iv : ByteArray} {s t : UInt64}
    (h : nonceOf iv s = nonceOf iv t) : s = t := by
  have e : ∀ i, i < aeadIvLength →
      iv.get! i ^^^ (sequenceBytes s).get! i =
        iv.get! i ^^^ (sequenceBytes t).get! i := by
    intro i hi
    rw [← get!_xorBytes (count := aeadIvLength) iv (sequenceBytes s) hi,
      ← get!_xorBytes (count := aeadIvLength) iv (sequenceBytes t) hi]
    show (nonceOf iv s).get! i = (nonceOf iv t).get! i
    rw [h]
  have h56 := e 4 (by decide)
  have h48 := e 5 (by decide)
  have h40 := e 6 (by decide)
  have h32 := e 7 (by decide)
  have h24 := e 8 (by decide)
  have h16 := e 9 (by decide)
  have h8 := e 10 (by decide)
  have h0 := e 11 (by decide)
  simp only [show ∀ s : UInt64, (sequenceBytes s).get! 4 = (s >>> 56).toUInt8
      from fun _ => rfl,
    show ∀ s : UInt64, (sequenceBytes s).get! 5 = (s >>> 48).toUInt8
      from fun _ => rfl,
    show ∀ s : UInt64, (sequenceBytes s).get! 6 = (s >>> 40).toUInt8
      from fun _ => rfl,
    show ∀ s : UInt64, (sequenceBytes s).get! 7 = (s >>> 32).toUInt8
      from fun _ => rfl,
    show ∀ s : UInt64, (sequenceBytes s).get! 8 = (s >>> 24).toUInt8
      from fun _ => rfl,
    show ∀ s : UInt64, (sequenceBytes s).get! 9 = (s >>> 16).toUInt8
      from fun _ => rfl,
    show ∀ s : UInt64, (sequenceBytes s).get! 10 = (s >>> 8).toUInt8
      from fun _ => rfl,
    show ∀ s : UInt64, (sequenceBytes s).get! 11 = s.toUInt8
      from fun _ => rfl] at h56 h48 h40 h32 h24 h16 h8 h0
  refine sequenceBytes_inj s t ?_
  unfold sequenceBytes
  rw [xor_cancel_left h56, xor_cancel_left h48, xor_cancel_left h40,
    xor_cancel_left h32, xor_cancel_left h24, xor_cancel_left h16,
    xor_cancel_left h8, xor_cancel_left h0]

/-- For a fixed IV, distinct sequence numbers give distinct nonces. -/
theorem TrafficKeys.nonce_inj {k1 k2 : TrafficKeys} {n : ByteArray}
    (hiv : k1.iv = k2.iv) (h1 : k1.nonce = .ok n) (h2 : k2.nonce = .ok n) :
    k1.seq = k2.seq :=
  nonceOf_inj (iv := k1.iv)
    (by rw [← TrafficKeys.nonce_eq h1, hiv]; exact TrafficKeys.nonce_eq h2)

/-! ## Traffic-key state -/

/-- `advance` succeeds exactly below the final sequence number, incrementing
it and touching nothing else. -/
theorem advance_ok_iff {keys keys' : TrafficKeys} :
    advance keys = .ok keys' ↔
      keys.seq ≠ (0xffffffffffffffff : UInt64) ∧
        keys' = { keys with seq := keys.seq + 1 } := by
  unfold advance
  by_cases hmax : keys.seq = (0xffffffffffffffff : UInt64)
  · simp only [hmax, beq_self_eq_true, if_true, except_throw,
      except_bind_error]
    simp
  · simp only [beq_iff_eq, hmax, if_false, except_pure, except_bind_ok]
    simp [hmax, eq_comm]

/-- `advance` refuses to wrap the sequence number. -/
theorem advance_error_iff {keys : TrafficKeys} {e : Error} :
    advance keys = .error e ↔
      keys.seq = (0xffffffffffffffff : UInt64) ∧ e = .sequenceExhausted := by
  unfold advance
  by_cases hmax : keys.seq = (0xffffffffffffffff : UInt64)
  · simp only [hmax, beq_self_eq_true, if_true, except_throw,
      except_bind_error]
    simp [eq_comm]
  · simp only [beq_iff_eq, hmax, if_false, except_pure, except_bind_ok]
    simp

private theorem mkTrafficKeys_ok {secret key iv : ByteArray}
    {keys : TrafficKeys} (h : mkTrafficKeys secret key iv = .ok keys) :
    keys.seq = 0 ∧ keys.secret = secret := by
  unfold mkTrafficKeys at h
  split at h
  · split at h
    · cases h; exact ⟨rfl, rfl⟩
    · cases h
  · cases h

private theorem deriveTrafficKeys_ok {secret : ByteArray} {keys : TrafficKeys}
    (h : deriveTrafficKeys secret = .ok keys) :
    keys.seq = 0 ∧ keys.secret = secret := by
  unfold deriveTrafficKeys at h
  cases hv : validateSecret secret with
  | error e =>
      rw [hv, except_bind_error] at h
      cases h
  | ok u =>
      rw [hv, except_bind_ok] at h
      exact mkTrafficKeys_ok h

/-- A fresh key schedule starts at sequence number zero. -/
theorem seq_deriveTrafficKeys {secret : ByteArray} {keys : TrafficKeys}
    (h : deriveTrafficKeys secret = .ok keys) : keys.seq = 0 :=
  (deriveTrafficKeys_ok h).1

/-- A key update resets the record sequence number to zero. -/
theorem TrafficKeys.seq_update {keys keys' : TrafficKeys}
    (h : keys.update = .ok keys') : keys'.seq = 0 := by
  unfold TrafficKeys.update at h
  cases hs : updateTrafficSecret keys.secret with
  | error e =>
      rw [hs] at h
      rw [except_bind_error] at h
      cases h
  | ok next =>
      rw [hs] at h
      rw [except_bind_ok] at h
      exact seq_deriveTrafficKeys h

/-- A key update moves to the RFC 8446 §7.2 successor traffic secret: the new
epoch's secret is `updateTrafficSecret` of the old one, so a KeyUpdate really
does change the epoch, not merely the sequence number. -/
theorem TrafficKeys.secret_update {keys keys' : TrafficKeys}
    (h : keys.update = .ok keys') :
    updateTrafficSecret keys.secret = .ok keys'.secret := by
  unfold TrafficKeys.update at h
  cases hs : updateTrafficSecret keys.secret with
  | error e =>
      rw [hs] at h
      rw [except_bind_error] at h
      cases h
  | ok next =>
      rw [hs] at h
      rw [except_bind_ok] at h
      rw [(deriveTrafficKeys_ok h).2]

/-! ## RFC 8446 §7.3 and §7.2: the record layer's own derivations

The record layer performs three of the specification's derivations itself: the
AEAD key and static IV of an epoch (§7.3) and the successor traffic secret of a
KeyUpdate (§7.2). All three are `HKDF-Expand-Label` with the **empty byte
string** as context — not the hash of an empty transcript — which is exactly the
distinction `TLS13.KeySchedule.Spec.emptyContext_rfc8446` records.

As in `open_seal`, the laws are parametric: they hold for *any* `Spec.Hkdf` the
HACL\* bindings implement, so they constrain the derivation structure and assume
nothing about what HKDF computes. -/

private theorem mkTrafficKeys_fields {secret key iv : ByteArray}
    {keys : TrafficKeys} (h : mkTrafficKeys secret key iv = .ok keys) :
    keys.secret = secret ∧ keys.key = key ∧ keys.iv = iv ∧ keys.seq = 0 := by
  unfold mkTrafficKeys at h
  split at h
  · split at h
    · cases h; exact ⟨rfl, rfl, rfl, rfl⟩
    · cases h
  · cases h

/-- `keys` is the RFC 8446 §7.3 record-protection state of traffic secret
`secret`: the AEAD key and the static IV are `HKDF-Expand-Label` of the secret
under `"key"` and `"iv"` with an empty context and this cipher suite's lengths,
and the record sequence number starts at zero. -/
def TrafficKeys.DerivedFrom (H : TLS13.KeySchedule.Spec.Hkdf) (keys : TrafficKeys)
    (secret : ByteArray) : Prop :=
  keys.secret = secret ∧
    keys.key = TLS13.KeySchedule.Spec.trafficKey H secret aeadKeyLength ∧
    keys.iv = TLS13.KeySchedule.Spec.trafficIv H secret aeadIvLength ∧
    keys.seq = 0

/-- The traffic secret an epoch's record-protection state was derived from. -/
theorem TrafficKeys.DerivedFrom.secret_eq {H : TLS13.KeySchedule.Spec.Hkdf}
    {keys : TrafficKeys} {secret : ByteArray} (h : keys.DerivedFrom H secret) :
    keys.secret = secret := h.1

/-- **`deriveTrafficKeys` is RFC 8446 §7.3.** -/
theorem deriveTrafficKeys_spec {H : TLS13.KeySchedule.Spec.Hkdf}
    (hi : TLS13.KeySchedule.Implements H) {secret : ByteArray} {keys : TrafficKeys}
    (h : deriveTrafficKeys secret = .ok keys) : keys.DerivedFrom H secret := by
  unfold deriveTrafficKeys at h
  cases hv : validateSecret secret with
  | error e => rw [hv, except_bind_error] at h; cases h
  | ok u =>
      rw [hv, except_bind_ok] at h
      obtain ⟨hsec, hkey, hiv, hseq⟩ := mkTrafficKeys_fields h
      refine ⟨hsec, ?_, ?_, hseq⟩
      · rw [hkey]
        exact TLS13.KeySchedule.expandLabel_spec hi secret .key ByteArray.empty
          aeadKeyLength
      · rw [hiv]
        exact TLS13.KeySchedule.expandLabel_spec hi secret .iv ByteArray.empty
          aeadIvLength

/-- **`updateTrafficSecret` is RFC 8446 §7.2**: `HKDF-Expand-Label` of the
current secret under `"traffic upd"` with an empty context, at hash length. -/
theorem updateTrafficSecret_spec {H : TLS13.KeySchedule.Spec.Hkdf}
    (hi : TLS13.KeySchedule.Implements H) {secret next : ByteArray}
    (h : updateTrafficSecret secret = .ok next) :
    next = TLS13.KeySchedule.Spec.nextTrafficSecret H secret := by
  unfold updateTrafficSecret at h
  cases hv : validateSecret secret with
  | error e => rw [hv, except_bind_error] at h; cases h
  | ok u =>
      rw [hv, except_bind_ok] at h
      obtain ⟨_, h⟩ := unless_ok h
      cases h
      rw [show (TLS13.KeySchedule.hashLen : Nat) = H.hashLen from hi.hashLen_eq.symm]
      exact TLS13.KeySchedule.expandLabel_spec hi secret .trafficUpd ByteArray.empty
        H.hashLen

/-- **A KeyUpdate installs the §7.2 successor epoch, derived per §7.3.** The
new state's traffic secret is `HKDF-Expand-Label(old, "traffic upd", "", 32)`
and its key, IV and sequence number are that secret's §7.3 record-protection
state. -/
theorem TrafficKeys.update_spec {H : TLS13.KeySchedule.Spec.Hkdf}
    (hi : TLS13.KeySchedule.Implements H) {keys keys' : TrafficKeys}
    (h : keys.update = .ok keys') :
    keys'.DerivedFrom H (TLS13.KeySchedule.Spec.nextTrafficSecret H keys.secret) := by
  unfold TrafficKeys.update at h
  cases hs : updateTrafficSecret keys.secret with
  | error e => rw [hs, except_bind_error] at h; cases h
  | ok next =>
      rw [hs, except_bind_ok] at h
      rw [← updateTrafficSecret_spec hi hs]
      exact deriveTrafficKeys_spec hi h

/-! ## Seal and open

Laws about record protection. The AEAD itself is an opaque HACL* FFI
binding, so the open∘seal identity is stated parametrically: *given* that
the binding inverts on identical key, nonce, and additional data, `open`
recovers exactly what `seal` protected, and both directions advance the
sequence number identically. -/

/-- No TLS content-type byte is zero, so the inner content type is never
mistaken for padding. -/
theorem ContentType.toUInt8_ne_zero (ct : ContentType) : ct.toUInt8 ≠ 0 := by
  cases ct <;> decide

theorem size_zeroBytes (count : Nat) : (zeroBytes count).size = count := by
  induction count with
  | zero => rfl
  | succ n ih => simp [zeroBytes, ByteArray.size_push, ih]

theorem get!_zeroBytes {count i : Nat} (h : i < count) :
    (zeroBytes count).get! i = 0 := by
  induction count with
  | zero => omega
  | succ n ih =>
      show ((zeroBytes n).push 0).get! i = 0
      rw [get!_push (by rw [size_zeroBytes]; omega)]
      rcases Nat.lt_or_ge i n with hi | hi
      · rw [if_pos (by rw [size_zeroBytes]; exact hi)]
        exact ih hi
      · rw [if_neg (by rw [size_zeroBytes]; omega)]

theorem size_innerPlaintext (ct : ContentType) (fragment : ByteArray)
    (paddingLength : Nat) :
    (innerPlaintext ct fragment paddingLength).size =
      fragment.size + 1 + paddingLength := by
  simp [innerPlaintext, ByteArray.size_append, ByteArray.size_push,
    size_zeroBytes]

private theorem get!_append_right {a b : ByteArray} {i : Nat}
    (h1 : a.size ≤ i) (h2 : i < a.size + b.size) :
    (a ++ b).get! i = b.get! (i - a.size) := by
  rw [get!_eq_getElem (by rw [ByteArray.size_append]; omega),
    get!_eq_getElem (by omega),
    ByteArray.getElem_append_right h1]

/-- The inner content-type byte sits directly after the content. -/
private theorem get!_innerPlaintext_type (ct : ContentType)
    (fragment : ByteArray) (paddingLength : Nat) :
    (innerPlaintext ct fragment paddingLength).get! fragment.size =
      ct.toUInt8 := by
  unfold innerPlaintext
  rw [get!_append_left (by rw [ByteArray.size_push]; omega),
    get!_push (by omega), if_neg (by omega)]

/-- Every byte after the inner content type is zero padding. -/
private theorem get!_innerPlaintext_pad {ct : ContentType}
    {fragment : ByteArray} {paddingLength i : Nat}
    (hlo : fragment.size + 1 ≤ i) (hhi : i < fragment.size + 1 + paddingLength) :
    (innerPlaintext ct fragment paddingLength).get! i = 0 := by
  unfold innerPlaintext
  rw [get!_append_right (by rw [ByteArray.size_push]; omega)
    (by rw [ByteArray.size_push, size_zeroBytes]; omega)]
  rw [ByteArray.size_push]
  exact get!_zeroBytes (by omega)

private theorem lastNonZero_innerPlaintext (ct : ContentType)
    (fragment : ByteArray) (paddingLength : Nat) :
    ∀ k, k ≤ paddingLength →
      lastNonZero (innerPlaintext ct fragment paddingLength)
          (fragment.size + 1 + k) =
        some fragment.size := by
  intro k
  induction k with
  | zero =>
      intro _
      show lastNonZero _ (fragment.size + 1) = _
      simp only [lastNonZero, get!_innerPlaintext_type]
      rw [if_pos (by
        cases ct <;> decide)]
  | succ n ih =>
      intro hk
      show lastNonZero (innerPlaintext ct fragment paddingLength)
        ((fragment.size + 1 + n) + 1) = some fragment.size
      simp only [lastNonZero]
      rw [get!_innerPlaintext_pad (by omega) (by omega),
        if_neg (by decide)]
      exact ih (by omega)

/-- The padding scan finds exactly the inner content-type position. -/
theorem findInnerContentType_innerPlaintext (ct : ContentType)
    (fragment : ByteArray) (paddingLength : Nat) :
    findInnerContentType (innerPlaintext ct fragment paddingLength) =
      some fragment.size := by
  unfold findInnerContentType
  rw [size_innerPlaintext]
  exact lastNonZero_innerPlaintext ct fragment paddingLength paddingLength
    (Nat.le_refl paddingLength)

private theorem get!_extract {a : ByteArray} {start stop i : Nat}
    (hstop : stop ≤ a.size) (h : i < stop - start) :
    (a.extract start stop).get! i = a.get! (start + i) := by
  have hsz : i < (a.extract start stop).size := by
    rw [ByteArray.size_extract]
    omega
  rw [get!_eq_getElem hsz, ByteArray.getElem_extract,
    get!_eq_getElem (show start + i < a.size by omega)]

/-- Truncating the inner plaintext at the content-type position recovers the
original fragment. -/
private theorem extract_innerPlaintext (ct : ContentType)
    (fragment : ByteArray) (paddingLength : Nat) :
    (innerPlaintext ct fragment paddingLength).extract 0 fragment.size =
      fragment := by
  apply ext_get!
  · rw [ByteArray.size_extract, size_innerPlaintext]
    omega
  · intro i hi
    have hi' : i < fragment.size := by
      rw [ByteArray.size_extract, size_innerPlaintext] at hi
      omega
    have hstop : fragment.size ≤ (innerPlaintext ct fragment paddingLength).size := by
      rw [size_innerPlaintext]
      omega
    rw [get!_extract hstop (by omega), Nat.zero_add]
    unfold innerPlaintext
    rw [get!_append_left (by rw [ByteArray.size_push]; omega),
      get!_push (by omega), if_pos hi']

/-- **`seal` advances the sequence number exactly once** and preserves the
secret, key, and IV: the returned traffic state is the input with `seq`
incremented and nothing else changed. -/
theorem seal_keys {keys next : TrafficKeys} {contentType : ContentType}
    {fragment wire : ByteArray} {paddingLength : Nat}
    (h : «seal» keys contentType fragment paddingLength = .ok (next, wire)) :
    next = { keys with seq := keys.seq + 1 } := by
  unfold «seal» at h
  split at h
  · cases h
  · split at h
    · cases h
    · split at h
      · cases h
      · split at h
        · cases h
        · rename_i nextKeys hadv
          split at h
          · cases h
          · split at h
            · cases h
            · split at h
              · cases h
              · simp only [Except.ok.injEq, Prod.mk.injEq] at h
                rw [← h.1]
                exact (advance_ok_iff.mp hadv).2

theorem seal_seq {keys next : TrafficKeys} {contentType : ContentType}
    {fragment wire : ByteArray} {paddingLength : Nat}
    (h : «seal» keys contentType fragment paddingLength = .ok (next, wire)) :
    next.seq = keys.seq + 1 := by
  rw [seal_keys h]

theorem seal_key_eq {keys next : TrafficKeys} {contentType : ContentType}
    {fragment wire : ByteArray} {paddingLength : Nat}
    (h : «seal» keys contentType fragment paddingLength = .ok (next, wire)) :
    next.key = keys.key := by
  rw [seal_keys h]

theorem seal_iv_eq {keys next : TrafficKeys} {contentType : ContentType}
    {fragment wire : ByteArray} {paddingLength : Nat}
    (h : «seal» keys contentType fragment paddingLength = .ok (next, wire)) :
    next.iv = keys.iv := by
  rw [seal_keys h]

theorem seal_secret_eq {keys next : TrafficKeys} {contentType : ContentType}
    {fragment wire : ByteArray} {paddingLength : Nat}
    (h : «seal» keys contentType fragment paddingLength = .ok (next, wire)) :
    next.secret = keys.secret := by
  rw [seal_keys h]

/-- **`seal` never revisits a sequence number**: it refuses to protect a record
once the counter is exhausted, so the number increases by one *without
wrapping*. This is what turns single-threaded key state into nonce
non-reuse. -/
theorem seal_seq_succ {keys next : TrafficKeys} {contentType : ContentType}
    {fragment wire : ByteArray} {paddingLength : Nat}
    (h : «seal» keys contentType fragment paddingLength = .ok (next, wire)) :
    next.seq.toNat = keys.seq.toNat + 1 := by
  have hkeys := seal_keys h
  have hne : keys.seq ≠ (0xffffffffffffffff : UInt64) := by
    unfold «seal» at h
    split at h
    · cases h
    · split at h
      · cases h
      · split at h
        · cases h
        · split at h
          · cases h
          · rename_i nextKeys hadv
            exact (advance_ok_iff.mp hadv).1
  rw [hkeys]
  show (keys.seq + 1).toNat = keys.seq.toNat + 1
  have hlt : keys.seq.toNat < 2 ^ 64 := UInt64.toNat_lt keys.seq
  have hmax : keys.seq.toNat ≠ 2 ^ 64 - 1 := fun hc =>
    hne (UInt64.toNat_inj.mp (by rw [hc]; rfl))
  rw [UInt64.toNat_add]
  show (keys.seq.toNat + (1 : UInt64).toNat) % 2 ^ 64 = keys.seq.toNat + 1
  rw [show (1 : UInt64).toNat = 1 from rfl, Nat.mod_eq_of_lt (by omega)]

/-- A successful `seal` consumed exactly the epoch's nonce for the sequence
number it was applied at. -/
theorem seal_nonce {keys next : TrafficKeys} {contentType : ContentType}
    {fragment wire : ByteArray} {paddingLength : Nat}
    (h : «seal» keys contentType fragment paddingLength = .ok (next, wire)) :
    keys.nonce = .ok (nonceOf keys.iv keys.seq) := by
  unfold «seal» at h
  split at h
  · cases h
  · split at h
    · cases h
    · split at h
      · cases h
      · split at h
        · cases h
        · split at h
          · cases h
          · split at h
            · cases h
            · rename_i nonce hnonce
              rw [hnonce, TrafficKeys.nonce_eq hnonce]

/-- **`open` inverts `seal`, modulo the opaque AEAD.** `haead` states that
the HACL* binding round-trips on identical key, nonce, and additional data —
it is an `@[extern] opaque` FFI import, so this is the precise boundary of
what Lean can know about it. Under that assumption, a successful `seal`
produced the wire encoding of a single well-formed TLSCiphertext record, and
`open` under the same initial keys returns the original content type,
fragment, and padding length together with the identically advanced traffic
state. -/
theorem open_seal
    (haead : ∀ key nonce aad plaintext,
      HaclStar.ChaCha20Poly1305.decrypt key nonce aad
          (HaclStar.ChaCha20Poly1305.encrypt key nonce aad plaintext) =
        some plaintext)
    {keys next : TrafficKeys} {contentType : ContentType}
    {fragment wire : ByteArray} {paddingLength : Nat}
    (h : «seal» keys contentType fragment paddingLength = .ok (next, wire)) :
    ∃ ciphertext : ByteArray,
      wire = encodeHeader .applicationData legacyRecordVersion
          ciphertext.size ++ ciphertext ∧
      RawRecord.WellFormed ⟨.applicationData, legacyRecordVersion, ciphertext⟩ ∧
      «open» keys ⟨.applicationData, legacyRecordVersion, ciphertext⟩ =
        .ok (next, { contentType, fragment, paddingLength }) := by
  unfold «seal» at h
  split at h
  · cases h
  · rename_i u hval
    split at h
    · cases h
    · rename_i hfrag
      split at h
      · cases h
      · rename_i hinnerLen
        split at h
        · cases h
        · rename_i nextKeys hadv
          split at h
          · cases h
          · rename_i hctLen
            split at h
            · cases h
            · rename_i nonce hnonce
              split at h
              · cases h
              · rename_i hsize
                simp only [Except.ok.injEq, Prod.mk.injEq] at h
                obtain ⟨hnext, hwire⟩ := h
                have hcs : (sealedCiphertext keys contentType fragment
                    paddingLength nonce).size =
                    fragment.size + 1 + paddingLength + aeadTagLength :=
                  Decidable.of_not_not hsize
                refine ⟨sealedCiphertext keys contentType fragment
                  paddingLength nonce, ?_, ?_, ?_⟩
                · rw [← hwire, hcs]
                · show aeadTagLength + 1 ≤
                      (sealedCiphertext keys contentType fragment paddingLength
                        nonce).size ∧
                    (sealedCiphertext keys contentType fragment paddingLength
                      nonce).size ≤ maxCiphertextLength
                  rw [hcs]
                  exact ⟨by omega, Nat.le_of_not_lt hctLen⟩
                · have hdec : HaclStar.ChaCha20Poly1305.decrypt keys.key nonce
                      (RawRecord.header ⟨.applicationData, legacyRecordVersion,
                        sealedCiphertext keys contentType fragment paddingLength
                          nonce⟩)
                      (sealedCiphertext keys contentType fragment paddingLength
                        nonce) =
                      some (innerPlaintext contentType fragment
                        paddingLength) := by
                    rw [show RawRecord.header ⟨.applicationData,
                        legacyRecordVersion, sealedCiphertext keys contentType
                          fragment paddingLength nonce⟩ =
                        encodeHeader .applicationData legacyRecordVersion
                          (sealedCiphertext keys contentType fragment
                            paddingLength nonce).size from rfl]
                    rw [hcs]
                    rw [show sealedCiphertext keys contentType fragment
                        paddingLength nonce =
                        HaclStar.ChaCha20Poly1305.encrypt keys.key nonce
                          (encodeHeader .applicationData legacyRecordVersion
                            (fragment.size + 1 + paddingLength +
                              aeadTagLength))
                          (innerPlaintext contentType fragment paddingLength)
                      from rfl]
                    exact haead keys.key nonce _ _
                  have hg_short : ¬(fragment.size + 1 + paddingLength +
                      aeadTagLength < aeadTagLength + 1) := by
                    omega
                  have hsub : fragment.size + 1 + paddingLength +
                      aeadTagLength - aeadTagLength =
                      fragment.size + 1 + paddingLength := by
                    omega
                  have hpad : fragment.size + 1 + paddingLength -
                      fragment.size - 1 = paddingLength := by
                    omega
                  unfold «open»
                  simp only [hval, hadv, hnonce, hdec, hcs, hnext, hsub, hpad,
                    hctLen, hg_short, hinnerLen, hfrag,
                    size_innerPlaintext, findInnerContentType_innerPlaintext,
                    get!_innerPlaintext_type, ContentType.ofUInt8?_toUInt8,
                    extract_innerPlaintext]
                  simp
                  decide

/-- **Record-layer round trip**: the wire bytes of a successful `seal` frame
back (via `decodeStep`) as exactly one record with no residual, and that
record `open`s — under the AEAD round-trip assumption — to the original
plaintext with the identically advanced keys. -/
theorem decodeStep_seal_open
    (haead : ∀ key nonce aad plaintext,
      HaclStar.ChaCha20Poly1305.decrypt key nonce aad
          (HaclStar.ChaCha20Poly1305.encrypt key nonce aad plaintext) =
        some plaintext)
    {keys next : TrafficKeys} {contentType : ContentType}
    {fragment wire : ByteArray} {paddingLength : Nat}
    (h : «seal» keys contentType fragment paddingLength = .ok (next, wire)) :
    ∃ record : RawRecord,
      decodeStep wire = .ok (some (record, ByteArray.empty)) ∧
      «open» keys record =
        .ok (next, { contentType, fragment, paddingLength }) := by
  obtain ⟨ciphertext, hwire, hwf, hopen⟩ := open_seal haead h
  refine ⟨⟨.applicationData, legacyRecordVersion, ciphertext⟩, ?_, hopen⟩
  have hencode : wire =
      RawRecord.encode ⟨.applicationData, legacyRecordVersion, ciphertext⟩ ++
        ByteArray.empty := by
    rw [ByteArray.append_empty, hwire]
    rfl
  rw [hencode]
  exact decodeStep_encode_append ByteArray.empty hwf

/-! ## Nonce non-reuse across a connection

No theorem about `seal` *alone* can establish that a connection never reuses a
nonce: a Lean `TrafficKeys` is an ordinary value, so a caller who keeps a copy
can seal twice at the same sequence number. Non-reuse is a property of a *run*
of the write path — of the sequence of `seal` calls a state machine actually
performs, each applied to the state the previous one returned.

`WriteRun` is that run, made explicit: it records every record protected, the
nonce it consumed, and the traffic-secret epoch that consumed it. Sequence
numbers restart at zero on every KeyUpdate (`TrafficKeys.seq_update`), so nonces
*do* repeat across epochs; the trace is therefore tagged by epoch secret and the
theorem is scoped accordingly. `WriteRun.nodup` is the result: the tagged trace
of any run has no repeats, assuming only that the epochs' traffic secrets are
distinct (`secrets.Nodup`) — which is a property of HKDF, an opaque HACL\*
binding here, and so is a hypothesis exactly like the AEAD round trip in
`open_seal`. -/

/-- A write-side run of one connection direction.
`WriteRun before after secrets nonces` holds when a state machine starting from
write traffic state `before` (`none` when no epoch has been installed yet)
reached `after` by protecting records, using the traffic-secret epochs `secrets`
(oldest first) and consuming exactly `nonces`, in order, each paired with the
secret of the epoch that consumed it.

Every step is pinned to the executable record layer: `protect` carries an actual
successful `seal` of the state the previous step returned, together with the
`TrafficKeys.nonce` that `seal` used. Nothing here models the record layer — a
`WriteRun` witness *is* a certificate about real `seal` calls. -/
inductive WriteRun : Option TrafficKeys → Option TrafficKeys → List ByteArray →
    List (ByteArray × ByteArray) → Prop where
  /-- No traffic epoch was ever installed, so nothing was protected. -/
  | idle : WriteRun none none [] []
  /-- The run ends in epoch `keys` without protecting anything more. -/
  | done (keys : TrafficKeys) : WriteRun (some keys) (some keys) [keys.secret] []
  /-- One record protected under the current epoch: `seal` consumed exactly the
  epoch's nonce at its current sequence number and returned the state the rest
  of the run continues from. -/
  | protect {keys next : TrafficKeys} {dst : Option TrafficKeys}
      {contentType : ContentType} {fragment wire nonce : ByteArray}
      {paddingLength : Nat} {secrets : List ByteArray}
      {nonces : List (ByteArray × ByteArray)}
      (hnonce : keys.nonce = .ok nonce)
      (hseal : «seal» keys contentType fragment paddingLength = .ok (next, wire))
      (hrest : WriteRun (some next) dst secrets nonces) :
      WriteRun (some keys) dst secrets ((keys.secret, nonce) :: nonces)
  /-- The current epoch is abandoned for a fresh one: `TrafficKeys.update` after
  a KeyUpdate, or the key schedule's handshake → application transition. The new
  epoch is unconstrained here; that distinct epochs really do have distinct
  secrets is exactly the `secrets.Nodup` hypothesis of `WriteRun.nodup`. -/
  | rekey {keys next : TrafficKeys} {dst : Option TrafficKeys}
      {secrets : List ByteArray} {nonces : List (ByteArray × ByteArray)}
      (hrest : WriteRun (some next) dst secrets nonces) :
      WriteRun (some keys) dst (keys.secret :: secrets) nonces
  /-- The first epoch is installed; nothing could have been protected before. -/
  | install {keys : TrafficKeys} {dst : Option TrafficKeys}
      {secrets : List ByteArray} {nonces : List (ByteArray × ByteArray)}
      (hrest : WriteRun (some keys) dst secrets nonces) :
      WriteRun none dst secrets nonces

/-- The epoch a run starts in heads its epoch list. -/
theorem WriteRun.secrets_head {keys : TrafficKeys} {dst : Option TrafficKeys}
    {secrets : List ByteArray} {nonces : List (ByteArray × ByteArray)}
    (h : WriteRun (some keys) dst secrets nonces) :
    ∃ rest, secrets = keys.secret :: rest := by
  generalize hsrc : (some keys : Option TrafficKeys) = src at h
  induction h generalizing keys with
  | idle => cases hsrc
  | done k => cases hsrc; exact ⟨[], rfl⟩
  | protect hnonce hseal hrest ih =>
      cases hsrc
      obtain ⟨rest, hrest'⟩ := ih rfl
      exact ⟨rest, by rw [hrest', seal_secret_eq hseal]⟩
  | rekey hrest ih => cases hsrc; exact ⟨_, rfl⟩
  | install hrest ih => cases hsrc

/-- Every nonce a run consumes is attributed to one of the run's epochs. -/
theorem WriteRun.mem_secrets {src dst : Option TrafficKeys}
    {secrets : List ByteArray} {nonces : List (ByteArray × ByteArray)}
    (h : WriteRun src dst secrets nonces) : ∀ p ∈ nonces, p.1 ∈ secrets := by
  induction h with
  | idle => intro p hp; cases hp
  | done k => intro p hp; cases hp
  | protect hnonce hseal hrest ih =>
      intro p hp
      cases hp with
      | head =>
          obtain ⟨rest, hrest'⟩ := WriteRun.secrets_head hrest
          rw [hrest', seal_secret_eq hseal]
          exact List.mem_cons_self
      | tail _ hp => exact ih p hp
  | rekey hrest ih => intro p hp; exact List.mem_cons_of_mem _ (ih p hp)
  | install hrest ih => exact ih

/-- Everything a run still consumes under the epoch it is currently in uses that
epoch's IV at a sequence number at or after the current one. Records protected
under a *later* epoch carry that epoch's secret, and the epochs are distinct, so
they cannot masquerade as this one. -/
theorem WriteRun.mem_epoch {keys : TrafficKeys} {dst : Option TrafficKeys}
    {secrets : List ByteArray} {nonces : List (ByteArray × ByteArray)}
    (h : WriteRun (some keys) dst secrets nonces) (hfresh : secrets.Nodup) :
    ∀ p ∈ nonces, p.1 = keys.secret →
      ∃ s : UInt64, keys.seq.toNat ≤ s.toNat ∧ p.2 = nonceOf keys.iv s := by
  generalize hsrc : (some keys : Option TrafficKeys) = src at h
  induction h generalizing keys with
  | idle => cases hsrc
  | done k => intro p hp; cases hp
  | protect hnonce hseal hrest ih =>
      cases hsrc
      intro p hp _
      cases hp with
      | head => exact ⟨_, Nat.le_refl _, TrafficKeys.nonce_eq hnonce⟩
      | tail _ hp =>
          obtain ⟨s, hle, heq⟩ :=
            ih hfresh rfl p hp (by rw [seal_secret_eq hseal]; assumption)
          refine ⟨s, ?_, ?_⟩
          · rw [seal_seq_succ hseal] at hle; omega
          · rw [heq, seal_iv_eq hseal]
  | rekey hrest ih =>
      cases hsrc
      intro p hp hp1
      exact absurd (hp1 ▸ WriteRun.mem_secrets hrest p hp)
        (List.nodup_cons.mp hfresh).1
  | install hrest ih => cases hsrc

/-- **Nonce non-reuse.** Across a whole write-side run, no two records were
protected under the same traffic secret with the same nonce.

Within one epoch this is forced by the implementation: `seal` uses the nonce of
the current sequence number and returns the state with that number advanced
without wrapping (`seal_seq_succ`), and for a fixed static IV the nonce
determines the sequence number (`nonceOf_inj`, from `sequenceBytes` injectivity).
Across epochs it rests on the single hypothesis `hfresh`: the traffic secrets the
connection used are distinct. TLS derives each of them with HKDF-Expand-Label,
which is an opaque HACL\* binding here, so that step is assumed rather than
proved — as with the AEAD round trip in `open_seal`. -/
theorem WriteRun.nodup {src dst : Option TrafficKeys}
    {secrets : List ByteArray} {nonces : List (ByteArray × ByteArray)}
    (h : WriteRun src dst secrets nonces) (hfresh : secrets.Nodup) :
    nonces.Nodup := by
  induction h with
  | idle => exact List.nodup_nil
  | done k => exact List.nodup_nil
  | protect hnonce hseal hrest ih =>
      rename_i keys next _ _ _ _ nonce _ _ _
      refine List.nodup_cons.mpr ⟨?_, ih hfresh⟩
      intro hmem
      obtain ⟨s, hle, heq⟩ :=
        WriteRun.mem_epoch hrest hfresh _ hmem (seal_secret_eq hseal).symm
      have hnonce' : nonce = nonceOf keys.iv keys.seq :=
        TrafficKeys.nonce_eq hnonce
      rw [seal_iv_eq hseal] at heq
      have hseq : keys.seq = s := nonceOf_inj (by rw [← hnonce', ← heq])
      rw [seal_seq_succ hseal, ← hseq] at hle
      omega
  | rekey hrest ih => exact ih (List.nodup_cons.mp hfresh).2
  | install hrest ih => exact ih hfresh

/-- The write-side effect of one state-machine step, phrased as a transformer
over whatever the connection does next. Steps compose by `Extends.trans`, so a
whole run's `WriteRun` is assembled from one lemma per engine operation without
ever naming an intermediate trace. -/
def Extends (before after : Option TrafficKeys) : Prop :=
  ∀ dst secrets nonces, WriteRun after dst secrets nonces →
    ∃ opened emitted, WriteRun before dst (opened ++ secrets) (emitted ++ nonces)

/-- A step that leaves the write traffic state alone protects nothing. -/
theorem Extends.refl (a : Option TrafficKeys) : Extends a a :=
  fun _ _ _ h => ⟨[], [], h⟩

theorem Extends.trans {a b c : Option TrafficKeys}
    (h1 : Extends a b) (h2 : Extends b c) : Extends a c := by
  intro dst secrets nonces h
  obtain ⟨o2, e2, h2'⟩ := h2 dst secrets nonces h
  obtain ⟨o1, e1, h1'⟩ := h1 dst _ _ h2'
  exact ⟨o1 ++ o2, e1 ++ e2, by rwa [List.append_assoc, List.append_assoc]⟩

theorem Extends.protect {keys next : TrafficKeys} {contentType : ContentType}
    {fragment wire nonce : ByteArray} {paddingLength : Nat}
    (hnonce : keys.nonce = .ok nonce)
    (hseal : «seal» keys contentType fragment paddingLength = .ok (next, wire)) :
    Extends (some keys) (some next) :=
  fun _ _ _ h => ⟨[], [(keys.secret, nonce)], WriteRun.protect hnonce hseal h⟩

/-- Protecting one record with the state machine's own write keys, storing the
returned state back. -/
theorem Extends.of_seal {keys next : TrafficKeys} {contentType : ContentType}
    {fragment wire : ByteArray} {paddingLength : Nat}
    (h : «seal» keys contentType fragment paddingLength = .ok (next, wire)) :
    Extends (some keys) (some next) :=
  Extends.protect (seal_nonce h) h

/-- Replacing the write epoch outright (KeyUpdate, or handshake → application
traffic keys). -/
theorem Extends.rekey (keys next : TrafficKeys) :
    Extends (some keys) (some next) :=
  fun _ _ _ h => ⟨[keys.secret], [], WriteRun.rekey h⟩

/-- Installing the first write epoch. -/
theorem Extends.install (keys : TrafficKeys) : Extends none (some keys) :=
  fun _ _ _ h => ⟨[], [], WriteRun.install h⟩

/-- Read back the run a chain of steps certifies. -/
theorem Extends.run {before after : Option TrafficKeys} (h : Extends before after) :
    ∃ secrets nonces, WriteRun before after secrets nonces := by
  cases after with
  | none =>
      obtain ⟨o, e, h'⟩ := h none [] [] WriteRun.idle
      exact ⟨_, _, h'⟩
  | some k =>
      obtain ⟨o, e, h'⟩ := h (some k) _ _ (WriteRun.done k)
      exact ⟨_, _, h'⟩

/-! ## Discharging `secrets.Nodup` from the key schedule

`WriteRun.nodup` takes the distinctness of the run's traffic secrets as a
hypothesis. It need not: TLS does not pick those secrets arbitrarily, it derives
each one with `HKDF-Expand-Label` at a specific label over a specific context
(RFC 8446 §7.1) and rolls it forward with `"traffic upd"` (§7.2). If that
primitive is injective — `TLS13.KeySchedule.Spec.ExpandLabelInjective`, the one
named assumption — then an epoch's traffic secret determines the whole
derivation, and a run whose epochs are *strictly increasing in the schedule's
own order* automatically has distinct secrets.

`EpochsFrom` is that "strictly increasing" property of a run's secret list, and
`SpecExtends` is the `Extends` transformer refined to carry it. The engines
prove `SpecExtends` step by step exactly as they prove `Extends`; the extra
obligation appears only where an epoch is actually installed. -/

open TLS13.KeySchedule

/-- The epoch a write traffic state is in: `none` before any epoch is installed,
and otherwise the key-schedule node whose traffic secret the state carries. -/
def EpochOf (H : Spec.Hkdf) : Option Spec.Epoch → Option TrafficKeys → Prop
  | none, none => True
  | some e, some k => k.secret = e.secret H
  | _, _ => False

/-- A state that carries the traffic secret of epoch `e` is in epoch `e`. -/
theorem EpochOf.intro {H : Spec.Hkdf} {e : Spec.Epoch} {k : TrafficKeys}
    (h : k.secret = e.secret H) : EpochOf H (some e) (some k) := h

theorem EpochOf.idle {H : Spec.Hkdf} : EpochOf H none none := trivial

/-- The traffic secret of the epoch a state is in. -/
theorem EpochOf.secret_eq {H : Spec.Hkdf} {e : Spec.Epoch} {k : TrafficKeys}
    (h : EpochOf H (some e) (some k)) : k.secret = e.secret H := h

/-- A state that carries traffic keys is in a definite epoch. -/
theorem EpochOf.some_inv {H : Spec.Hkdf} {o : Option Spec.Epoch} {k : TrafficKeys}
    (h : EpochOf H o (some k)) : ∃ e, o = some e ∧ k.secret = e.secret H := by
  cases o with
  | none => exact ((h : False)).elim
  | some e => exact ⟨e, rfl, h⟩

/-- A state with no traffic keys is in no epoch. -/
theorem EpochOf.none_inv {H : Spec.Hkdf} {o : Option Spec.Epoch}
    (h : EpochOf H o none) : o = none := by
  cases o with
  | none => rfl
  | some e => exact ((h : False)).elim

/-- The traffic-secret list of a run, described by the key schedule: it is the
list of secrets of a strictly increasing sequence of epochs, each of them a §7.1
derivation (`Spec.Epoch.Valid`) rather than a bare update, and none of them
earlier than `o`. -/
def EpochsFrom (H : Spec.Hkdf) (o : Option Spec.Epoch) (secrets : List ByteArray) :
    Prop :=
  ∃ epochs : List Spec.Epoch,
    secrets = epochs.map (Spec.Epoch.secret H) ∧
      List.Pairwise Spec.Epoch.Lt epochs ∧
      ∀ e ∈ epochs, e.Valid ∧ Spec.Epoch.LeOpt o e

/-- Forgetting a lower bound on a run's epochs. -/
theorem EpochsFrom.mono {H : Spec.Hkdf} {o o' : Option Spec.Epoch}
    {secrets : List ByteArray} (hle : ∀ e, Spec.Epoch.LeOpt o' e → Spec.Epoch.LeOpt o e)
    (h : EpochsFrom H o' secrets) : EpochsFrom H o secrets := by
  obtain ⟨epochs, hmap, hchain, hmem⟩ := h
  exact ⟨epochs, hmap, hchain, fun e he => ⟨(hmem e he).1, hle e (hmem e he).2⟩⟩

/-- **A run whose epochs strictly increase never repeats a traffic secret.**
The distinctness `WriteRun.nodup` asks for is a *consequence* of the schedule
once `HKDF-Expand-Label` is injective, because the secret of an epoch determines
that epoch (`Spec.Epoch.eq_of_secret_eq`). -/
theorem EpochsFrom.nodup {H : Spec.Hkdf} (hinj : Spec.ExpandLabelInjective H)
    {o : Option Spec.Epoch} {secrets : List ByteArray} (h : EpochsFrom H o secrets) :
    secrets.Nodup := by
  obtain ⟨epochs, hmap, hchain, hmem⟩ := h
  subst hmap
  induction epochs with
  | nil => exact List.nodup_nil
  | cons e rest ih =>
      obtain ⟨hhead, htail⟩ := List.pairwise_cons.mp hchain
      refine List.nodup_cons.mpr ⟨?_, ih htail (fun x hx => hmem x (List.mem_cons_of_mem _ hx))⟩
      intro hcontra
      obtain ⟨x, hx, hxe⟩ := List.mem_map.mp hcontra
      exact (hhead x hx).ne
        (Spec.Epoch.eq_of_secret_eq hinj (hmem e List.mem_cons_self).1
          (hmem x (List.mem_cons_of_mem _ hx)).1 hxe.symm)

/-- `Extends`, refined by the key schedule: a step from a write state in epoch
`o` to one in epoch `o'`, which extends any strictly-increasing-epoch run of the
rest of the connection to a strictly-increasing-epoch run of the whole. -/
def SpecExtends (H : Spec.Hkdf) (o o' : Option Spec.Epoch)
    (before after : Option TrafficKeys) : Prop :=
  ∀ dst secrets nonces, WriteRun after dst secrets nonces → EpochsFrom H o' secrets →
    ∃ opened emitted, WriteRun before dst (opened ++ secrets) (emitted ++ nonces) ∧
      EpochsFrom H o (opened ++ secrets)

theorem SpecExtends.refl {H : Spec.Hkdf} (o : Option Spec.Epoch)
    (a : Option TrafficKeys) : SpecExtends H o o a a :=
  fun _ _ _ h hl => ⟨[], [], h, hl⟩

theorem SpecExtends.trans {H : Spec.Hkdf} {o₁ o₂ o₃ : Option Spec.Epoch}
    {a b c : Option TrafficKeys} (h1 : SpecExtends H o₁ o₂ a b)
    (h2 : SpecExtends H o₂ o₃ b c) : SpecExtends H o₁ o₃ a c := by
  intro dst secrets nonces h hl
  obtain ⟨p2, e2, h2', hl2⟩ := h2 dst secrets nonces h hl
  obtain ⟨p1, e1, h1', hl1⟩ := h1 dst _ _ h2' hl2
  exact ⟨p1 ++ p2, e1 ++ e2, by rwa [List.append_assoc, List.append_assoc],
    by rwa [List.append_assoc]⟩

/-- Protecting one record leaves the epoch alone. -/
theorem SpecExtends.of_seal {H : Spec.Hkdf} {o : Option Spec.Epoch}
    {keys next : TrafficKeys} {contentType : ContentType}
    {fragment wire : ByteArray} {paddingLength : Nat}
    (h : «seal» keys contentType fragment paddingLength = .ok (next, wire)) :
    SpecExtends H o o (some keys) (some next) :=
  fun _ _ _ hrun hl =>
    ⟨[], [(keys.secret, _)], WriteRun.protect (seal_nonce h) h hrun, hl⟩

/-- Installing the first epoch: nothing was protected before it. -/
theorem SpecExtends.install {H : Spec.Hkdf} {o' : Option Spec.Epoch}
    {keys : TrafficKeys} : SpecExtends H none o' none (some keys) :=
  fun _ _ _ hrun hl => ⟨[], [], WriteRun.install hrun, hl.mono (fun _ _ => trivial)⟩

/-- **Replacing the write epoch, accounted for by the schedule.** The step
abandons epoch `e` for a strictly later epoch `e'`; the abandoned epoch joins the
run's epoch list ahead of everything the rest of the connection uses. -/
theorem SpecExtends.rekey {H : Spec.Hkdf} {e e' : Spec.Epoch}
    {keys next : TrafficKeys} (hsecret : keys.secret = e.secret H)
    (hvalid : e.Valid) (hlt : e.Lt e') :
    SpecExtends H (some e) (some e') (some keys) (some next) := by
  intro dst secrets nonces hrun hl
  obtain ⟨epochs, hmap, hchain, hmem⟩ := hl
  refine ⟨[keys.secret], [], WriteRun.rekey hrun, e :: epochs, ?_, ?_, ?_⟩
  · rw [hmap, hsecret]; rfl
  · exact List.pairwise_cons.mpr
      ⟨fun x hx => Spec.Epoch.lt_of_lt_of_le hlt (hmem x hx).2, hchain⟩
  · intro x hx
    cases hx with
    | head => exact ⟨hvalid, Spec.Epoch.Le.refl e⟩
    | tail _ hx =>
        exact ⟨(hmem x hx).1,
          Or.inr (Spec.Epoch.lt_of_lt_of_le hlt (hmem x hx).2)⟩

/-- A stretch of the write path that stays inside one epoch: it may protect any
number of records, but the traffic secret it ends on is the one it started on.
This is the shape of every engine step except the three that install an epoch,
and it composes by `trans`. -/
def WithinEpoch (H : Spec.Hkdf) (before after : Option TrafficKeys) : Prop :=
  ∀ o, EpochOf H o before → EpochOf H o after ∧ SpecExtends H o o before after

/-- Apply a `WithinEpoch` step to the epoch the connection is in. -/
theorem WithinEpoch.apply {H : Spec.Hkdf} {a b : Option TrafficKeys}
    (h : WithinEpoch H a b) {o : Option Spec.Epoch} (ho : EpochOf H o a) :
    EpochOf H o b ∧ SpecExtends H o o a b := h o ho

theorem WithinEpoch.refl {H : Spec.Hkdf} (a : Option TrafficKeys) :
    WithinEpoch H a a := fun o ho => ⟨ho, SpecExtends.refl o a⟩

theorem WithinEpoch.trans {H : Spec.Hkdf} {a b c : Option TrafficKeys}
    (h1 : WithinEpoch H a b) (h2 : WithinEpoch H b c) : WithinEpoch H a c :=
  fun o ho => ⟨(h2 o (h1 o ho).1).1, (h1 o ho).2.trans (h2 o (h1 o ho).1).2⟩

/-- Protecting one record with the state machine's own write keys. `seal`
advances the sequence number and leaves the traffic secret alone, so the epoch
is unchanged. -/
theorem WithinEpoch.of_seal {H : Spec.Hkdf} {keys next : TrafficKeys}
    {contentType : ContentType} {fragment wire : ByteArray} {paddingLength : Nat}
    (h : «seal» keys contentType fragment paddingLength = .ok (next, wire)) :
    WithinEpoch H (some keys) (some next) := by
  intro o ho
  obtain ⟨e, rfl, hsec⟩ := EpochOf.some_inv ho
  exact ⟨EpochOf.intro (by rw [seal_secret_eq h]; exact hsec), SpecExtends.of_seal h⟩

/-- Read back the run a chain of refined steps certifies, together with the
strictly increasing epoch list that makes its traffic secrets distinct. -/
theorem SpecExtends.run {H : Spec.Hkdf} {o o' : Option Spec.Epoch}
    {before after : Option TrafficKeys} (h : SpecExtends H o o' before after)
    (hafter : EpochOf H o' after) (hvalid : ∀ e, o' = some e → e.Valid) :
    ∃ secrets nonces, WriteRun before after secrets nonces ∧ EpochsFrom H o secrets := by
  cases o' with
  | none =>
      cases after with
      | none =>
          obtain ⟨p, e, h', hl⟩ := h none [] [] WriteRun.idle ⟨[], rfl, List.Pairwise.nil,
            fun _ hx => absurd hx (List.not_mem_nil)⟩
          exact ⟨_, _, h', hl⟩
      | some k => exact absurd hafter (fun x => x)
  | some e' =>
      cases after with
      | none => exact absurd hafter (fun x => x)
      | some k =>
          obtain ⟨p, em, h', hl⟩ := h (some k) _ _ (WriteRun.done k)
            ⟨[e'], by rw [(hafter : k.secret = e'.secret H)]; rfl,
              List.pairwise_singleton _ _,
              fun x hx => by
                cases hx with
                | head => exact ⟨hvalid e' rfl, Spec.Epoch.Le.refl e'⟩
                | tail _ hx => exact absurd hx (List.not_mem_nil)⟩
          exact ⟨_, _, h', hl⟩

/-- **Nonce non-reuse with the epoch hypothesis discharged.** Given a refined run
— one whose every epoch change is accounted for by the key schedule — and the
injectivity of `HKDF-Expand-Label`, no (traffic secret, nonce) pair repeats. The
`secrets.Nodup` hypothesis of `WriteRun.nodup` is *proved* here rather than
assumed; what remains assumed is `hinj`, a property of the primitive. -/
theorem SpecExtends.nonce_nodup {H : Spec.Hkdf} (hinj : Spec.ExpandLabelInjective H)
    {o o' : Option Spec.Epoch} {before after : Option TrafficKeys}
    (h : SpecExtends H o o' before after) (hafter : EpochOf H o' after)
    (hvalid : ∀ e, o' = some e → e.Valid) :
    ∃ secrets nonces, WriteRun before after secrets nonces ∧ nonces.Nodup := by
  obtain ⟨secrets, nonces, hrun, hl⟩ := h.run hafter hvalid
  exact ⟨secrets, nonces, hrun, hrun.nodup (hl.nodup hinj)⟩

end Record
end Tls
