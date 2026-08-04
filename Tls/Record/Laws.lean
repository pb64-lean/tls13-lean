module

public import Tls.Record
import all Tls.Record
import Std.Tactic.BVDecide
public meta import Std.Tactic.BVDecide.Reflect

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

private theorem hi_lo_recompose (v : UInt16) :
    ((v >>> 8).toUInt8.toUInt16 <<< 8 ||| v.toUInt8.toUInt16) = v := by
  bv_decide

private theorem recompose_hi (x y : UInt8) :
    ((x.toUInt16 <<< 8 ||| y.toUInt16) >>> 8).toUInt8 = x := by
  bv_decide

private theorem recompose_lo (x y : UInt8) :
    (x.toUInt16 <<< 8 ||| y.toUInt16).toUInt8 = y := by
  bv_decide

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

/-! ## Sequence numbers and nonces -/

theorem size_sequenceBytes (seq : UInt64) :
    (sequenceBytes seq).size = aeadIvLength := rfl

/-- The sequence encoding is lossless. -/
theorem sequenceBytes_inj (s t : UInt64)
    (h : sequenceBytes s = sequenceBytes t) : s = t := by
  unfold sequenceBytes at h
  simp only [ByteArray.mk.injEq, Array.mk.injEq, List.cons.injEq, and_true] at h
  obtain ⟨-, -, -, -, h56, h48, h40, h32, h24, h16, h8, h0⟩ := h
  bv_decide

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

/-- For a fixed IV, distinct sequence numbers give distinct nonces: XOR with
a constant is a bijection and the sequence encoding is lossless. -/
theorem TrafficKeys.nonce_inj {k1 k2 : TrafficKeys} {n : ByteArray}
    (hiv : k1.iv = k2.iv) (h1 : k1.nonce = .ok n) (h2 : k2.nonce = .ok n) :
    k1.seq = k2.seq := by
  have e : ∀ i, i < aeadIvLength →
      k1.iv.get! i ^^^ (sequenceBytes k1.seq).get! i =
        k1.iv.get! i ^^^ (sequenceBytes k2.seq).get! i := by
    intro i hi
    rw [← TrafficKeys.get!_nonce h1 hi, hiv, ← TrafficKeys.get!_nonce h2 hi]
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
  bv_decide

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

end Record
end Tls
