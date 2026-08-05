module

public import Tls.Server
public import Tls.Record.Laws
public import TLS13.KeySchedule.Refinement
import all Tls.Server
import all Tls.Record

public section

namespace Tls
namespace Server

/-!
Kernel-checked laws about the executable server state machine in `Tls.Server`.

Two results live here.

**Nonce non-reuse.** `Tls.Record.Laws` proves the arithmetic — one epoch, one
sequence number per record, no wrap, an injective nonce — but cannot rule out a
caller sealing twice with a retained copy of a `TrafficKeys`. This module
supplies the missing half for the server: every record the engine protects,
including the whole encrypted handshake flight, is sealed with traffic keys
threaded single-threadedly through its own state. `run_nonce_nodup` exposes the
actual `(AEAD key, nonce)` trace and proves that one run has no repeats when the
concrete AEAD keys installed in that finite run are distinct. The same honesty
notes as `Tls.Client.Laws` apply: the
theorem is about this engine's own emissions along one chain of states, not
about a caller who clones a `State`; and it covers the write direction only.
Distinctness across epochs is an `aeadKeys.Nodup` hypothesis in
`run_nonce_nodup` and remains an explicit finite-run condition in
`run_nonce_trace_spec`; the latter also returns the traffic-secret bookkeeping
trace and proves that it traverses strictly increasing RFC 8446 §7.1 / §7.2
derivation histories. A fixed-size KDF cannot be globally injective, so
structural epoch order is not misreported as deterministic byte distinctness.

**The HelloRetryRequest comparison is a byte comparison.**
`checkRetryClientHello_body_eq` connects the second-ClientHello check the server
actually runs to `Handshake.parseClientHello_body_injective`: comparing the
parsed fields is as strong as comparing the message bodies byte for byte.
-/

private theorem except_bind_ok_inv {α β : Type} {m : Except Error α}
    {f : α → Except Error β} {b : β} (h : (m >>= f) = .ok b) :
    ∃ a, m = .ok a ∧ f a = .ok b := by
  cases m with
  | error e => cases h
  | ok a => exact ⟨a, rfl, h⟩

private theorem unless_ok {α : Type} {c : Bool} {e : Error}
    {f : PUnit → Except Error α} {b : α}
    (h : (if c = true then (pure PUnit.unit : Except Error PUnit) >>= f
          else (throw e : Except Error PUnit) >>= f) = .ok b) :
    c = true ∧ f PUnit.unit = .ok b := by
  by_cases hc : c = true
  · rw [if_pos hc] at h; exact ⟨hc, h⟩
  · rw [if_neg hc] at h; cases h

private theorem if_throw_ok {α : Type} {c : Bool} {e : Error}
    {f : PUnit → Except Error α} {b : α}
    (h : (if c = true then (throw e : Except Error PUnit) >>= f
          else (pure PUnit.unit : Except Error PUnit) >>= f) = .ok b) :
    c = false ∧ f PUnit.unit = .ok b := by
  by_cases hc : c = true
  · rw [if_pos hc] at h; cases h
  · rw [if_neg hc] at h
    exact ⟨Bool.eq_false_iff.mpr hc, h⟩

private theorem liftRecord_ok {α : Type} {r : Except Record.Error α} {v : α}
    (h : liftRecord r = .ok v) : r = .ok v := by
  unfold liftRecord at h
  cases r with
  | error e => simp [Except.mapError] at h
  | ok a => simpa [Except.mapError] using h

private theorem requireWriteKeys_ok {state : State} {keys : Record.TrafficKeys}
    (h : requireWriteKeys state = .ok keys) : state.writeKeys? = some keys := by
  unfold requireWriteKeys at h
  cases hw : state.writeKeys? with
  | none => rw [hw] at h; cases h
  | some k => rw [hw] at h; cases h; rfl

private theorem requireWriteKeys_isSome {state : State}
    {keys : Record.TrafficKeys} (h : requireWriteKeys state = .ok keys) :
    state.writeKeys?.isSome = true := by
  rw [requireWriteKeys_ok h]; rfl

private theorem requireReadKeys_isSome {state : State}
    {keys : Record.TrafficKeys} (h : requireReadKeys state = .ok keys) :
    state.readKeys?.isSome = true := by
  unfold requireReadKeys at h
  split at h
  · rename_i hk; rw [hk]; rfl
  · cases h

private theorem extends_fresh (before : Option Record.TrafficKeys)
    (keys : Record.TrafficKeys) : Record.Extends before (some keys) := by
  cases before with
  | none => exact Record.Extends.install keys
  | some k => exact Record.Extends.rekey k keys

private theorem byteArray_eq_of_beq {a b : ByteArray} (h : (a == b) = true) :
    a = b := by
  have h' : (a.data == b.data) = true := h
  have hd : a.data = b.data := eq_of_beq h'
  cases a; cases b; simp_all

/-- **The retry comparison is a byte comparison.** RFC 8446 §4.1.2 requires a
second ClientHello to repeat the first one unchanged except for a short list of
permitted edits. `checkRetryClientHello` enforces that by comparing the *parsed*
fields; this theorem says that is exactly as strong as comparing the bytes: for
two ClientHellos that both offered TLS 1.3, passing the check and taking none of
the permitted extension changes forces the two message bodies to be identical.

It is `Handshake.parseClientHello_canonical` — through
`Handshake.parseClientHello_body_injective` — that carries the field comparison
back to the wire, so the canonicity law is what this check rests on rather than
a parallel result.

The `hexts` hypothesis is where the permitted edits live: a client that replaces
its `key_share`, drops `early_data`, updates a PSK binder or changes padding
changes the extension list on purpose, and then the bodies legitimately differ —
`checkRetryClientHello` still pins every *other* field, `retryStableExtensions`
included. -/
theorem checkRetryClientHello_body_eq {msg₁ msg₂ : Handshake.Message}
    {ch₁ ch₂ : Handshake.ClientHello} {group : Handshake.NamedGroup}
    (h₁ : Handshake.parseClientHello msg₁ = .ok ch₁)
    (h₂ : Handshake.parseClientHello msg₂ = .ok ch₂)
    (h13 : ch₁.offersTls13 = true)
    (hcheck : checkRetryClientHello ch₁ ch₂ group = .ok ())
    (hexts : ch₁.extensions = ch₂.extensions) :
    msg₁.body = msg₂.body := by
  unfold checkRetryClientHello at hcheck
  simp only [pure_bind] at hcheck
  obtain ⟨hrandom, hcheck⟩ := unless_ok hcheck
  obtain ⟨hsid, hcheck⟩ := unless_ok hcheck
  obtain ⟨hcs, hcheck⟩ := unless_ok hcheck
  exact Handshake.parseClientHello_body_injective h₁ h₂
    (Handshake.parseClientHello_extensions_of_offersTls13 h₁ h13)
    (byteArray_eq_of_beq hrandom).symm
    (byteArray_eq_of_beq hsid).symm
    (eq_of_beq hcs).symm
    hexts


/-- The write side of one engine step: how the connection's own `seal` calls
advanced its write traffic state. `Tls.Record.Laws.Extends` composes these, so a
whole run's `WriteRun` — the records protected and the nonces consumed — is
assembled from one lemma per engine operation. -/
def WriteEffect (before after : State) : Prop :=
  Record.Extends before.writeKeys? after.writeKeys?

private theorem sealHandshakeFlight_write {keys keys' : Record.TrafficKeys}
    {flight : ByteArray} {offset : Nat} {wireBytes wireOut : ByteArray}
    (h : sealHandshakeFlight keys flight offset wireBytes = .ok (keys', wireOut)) :
    Record.Extends (some keys) (some keys') := by
  unfold sealHandshakeFlight at h
  split at h
  · cases h; exact Record.Extends.refl _
  · simp only [] at h
    split at h
    · cases h
    · rename_i nextKeys record hseal
      exact Record.Extends.trans (Record.Extends.of_seal (liftRecord_ok hseal))
        (sealHandshakeFlight_write h)
  termination_by flight.size - offset
  decreasing_by
    have : 0 < Record.maxPlaintextLength := by decide
    omega

private theorem sealChunks_write {keys keys' : Record.TrafficKeys}
    {plaintext : ByteArray} {offset : Nat} {records records' : Array ByteArray}
    (h : sealChunks keys plaintext offset records = .ok (keys', records')) :
    Record.Extends (some keys) (some keys') := by
  unfold sealChunks at h
  split at h
  · cases h; exact Record.Extends.refl _
  · simp only [] at h
    split at h
    · cases h
    · rename_i nextKeys wire hpair
      exact Record.Extends.trans (Record.Extends.of_seal (liftRecord_ok hpair))
        (sealChunks_write h)
  termination_by plaintext.size - offset
  decreasing_by
    have : 0 < Record.maxPlaintextLength := by decide
    omega

theorem sealApplication_write {state : State} {plaintext : ByteArray}
    {out : Output} (h : sealApplication state plaintext = .ok out) :
    WriteEffect state out.state := by
  unfold sealApplication at h
  simp only [pure_bind] at h
  split at h
  · split at h
    · cases h
    · split at h
      · cases h; exact Record.Extends.refl _
      · obtain ⟨keys, hk, h⟩ := except_bind_ok_inv h
        obtain ⟨sealed, hs, h⟩ := except_bind_ok_inv h
        obtain ⟨nextKeys, records⟩ := sealed
        cases h
        show Record.Extends state.writeKeys? (some nextKeys)
        rw [requireWriteKeys_ok hk]
        exact sealChunks_write hs
  · cases h

private theorem emitCloseNotify_write {state next : State} {wire : ByteArray}
    (h : emitCloseNotify state = .ok (next, wire)) : WriteEffect state next := by
  unfold emitCloseNotify at h
  split at h
  · cases h; exact Record.Extends.refl _
  · obtain ⟨keys, hk, h⟩ := except_bind_ok_inv h
    obtain ⟨sealed, hs, h⟩ := except_bind_ok_inv h
    obtain ⟨sealedKeys, wireBytes⟩ := sealed
    cases h
    show Record.Extends state.writeKeys? (some sealedKeys)
    rw [requireWriteKeys_ok hk]
    exact Record.Extends.of_seal (liftRecord_ok hs)

theorem closeNotify_write {state : State} {out : Output}
    (h : closeNotify state = .ok out) : WriteEffect state out.state := by
  unfold closeNotify at h
  simp only [pure_bind] at h
  split at h
  case isFalse => cases h
  obtain ⟨pair, hp, h⟩ := except_bind_ok_inv h
  obtain ⟨next, wire⟩ := pair
  cases h
  exact emitCloseNotify_write hp

theorem sealFatalAlert_write {state : State} {description : UInt8} {out : Output}
    (h : sealFatalAlert state description = .ok out) :
    WriteEffect state out.state := by
  unfold sealFatalAlert at h
  simp only [pure_bind] at h
  split at h
  · cases h
  · split at h
    · rename_i writeKeys hkeys
      obtain ⟨sealed, hs, h⟩ := except_bind_ok_inv h
      obtain ⟨nextKeys, wire⟩ := sealed
      cases h
      show Record.Extends state.writeKeys? (some nextKeys)
      rw [hkeys]
      exact Record.Extends.of_seal (liftRecord_ok hs)
    · rename_i hkeys
      obtain ⟨_, h⟩ := unless_ok h
      obtain ⟨wire, _, h⟩ := except_bind_ok_inv h
      cases h
      show Record.Extends state.writeKeys? state.writeKeys?
      exact Record.Extends.refl _

/-- Once `close_notify` has closed the local write direction, even a fatal alert
is suppressed: RFC 9846 requires that no further records be sent. -/
theorem sealFatalAlert_localClosed {state : State} {description : UInt8}
    (hclosed : state.localClosed = true) :
    sealFatalAlert state description = .error .connectionClosed := by
  unfold sealFatalAlert
  rw [if_pos hclosed]
  rfl

private theorem processAlert_write {state next : State} {fragment : ByteArray}
    {duringHandshake : Bool} {wire : ByteArray}
    (h : processAlert state fragment duringHandshake = .ok (next, wire)) :
    WriteEffect state next := by
  unfold processAlert at h
  simp only [pure_bind] at h
  split at h
  case isFalse => cases h
  split at h
  · split at h
    · cases h
    · cases h
      exact Record.Extends.refl _
  · split at h
    · cases h
      exact Record.Extends.refl _
    · cases h

private theorem sendKeyUpdateResponse_write {state next : State} {wire : ByteArray}
    (h : sendKeyUpdateResponse state = .ok (next, wire)) :
    WriteEffect state next := by
  unfold sendKeyUpdateResponse at h
  split at h
  · obtain ⟨_, _, h⟩ := except_bind_ok_inv h
    obtain ⟨keys, hk, h⟩ := except_bind_ok_inv h
    obtain ⟨sealed, hs, h⟩ := except_bind_ok_inv h
    obtain ⟨advancedKeys, wireBytes⟩ := sealed
    obtain ⟨updatedKeys, hu, h⟩ := except_bind_ok_inv h
    cases h
    show Record.Extends state.writeKeys? (some updatedKeys)
    rw [requireWriteKeys_ok hk]
    exact Record.Extends.trans (Record.Extends.of_seal (liftRecord_ok hs))
      (Record.Extends.rekey advancedKeys updatedKeys)
  · cases h
    exact Record.Extends.refl _

private theorem sendKeyUpdateResponse_readKeys {state next : State}
    {wire : ByteArray} (h : sendKeyUpdateResponse state = .ok (next, wire)) :
    next.readKeys? = state.readKeys? := by
  unfold sendKeyUpdateResponse at h
  split at h
  · obtain ⟨_, _, h⟩ := except_bind_ok_inv h
    obtain ⟨keys, hk, h⟩ := except_bind_ok_inv h
    obtain ⟨sealed, hs, h⟩ := except_bind_ok_inv h
    obtain ⟨advancedKeys, wireBytes⟩ := sealed
    obtain ⟨updatedKeys, hu, h⟩ := except_bind_ok_inv h
    cases h
    rfl
  · cases h
    rfl

private theorem sendKeyUpdateResponse_at_limit {state : State}
    (hlimit : maxSendingKeyUpdates ≤ state.sendingKeyUpdates) :
    sendKeyUpdateResponse state = .ok (state, ByteArray.empty) := by
  unfold sendKeyUpdateResponse
  rw [if_neg (Nat.not_lt_of_ge hlimit)]
  rfl

private theorem acceptKeyUpdate_write {state next : State}
    {message : Handshake.Message} {wire : ByteArray}
    (h : acceptKeyUpdate state message = .ok (next, wire)) :
    WriteEffect state next := by
  unfold acceptKeyUpdate at h
  obtain ⟨_, _, h⟩ := except_bind_ok_inv h
  obtain ⟨_, _, h⟩ := except_bind_ok_inv h
  obtain ⟨_, _, h⟩ := except_bind_ok_inv h
  split at h
  · cases h; exact Record.Extends.refl _
  · simp only [] at h
    split at h
    · cases h; exact Record.Extends.refl _
    · have hw := sendKeyUpdateResponse_write h
      exact hw

/-- The server flight is protected under a freshly derived handshake epoch, one
record per 2^14-byte fragment, and the application epoch replaces it afterwards:
every nonce the flight consumes is accounted for. -/
private theorem completeClientHello_write {state next : State}
    {hello : Handshake.ClientHello} {group : Handshake.NamedGroup}
    {transcriptPrefix wire : ByteArray}
    (h : completeClientHello state hello group transcriptPrefix = .ok (next, wire)) :
    WriteEffect state next := by
  unfold completeClientHello at h
  simp only [pure_bind] at h
  obtain ⟨exchanged, _, h⟩ := except_bind_ok_inv h
  obtain ⟨serverPublic, sharedSecret⟩ := exchanged
  obtain ⟨_, h⟩ := unless_ok h
  obtain ⟨serverHello, _, h⟩ := except_bind_ok_inv h
  obtain ⟨serverWriteKeys, _, h⟩ := except_bind_ok_inv h
  obtain ⟨clientReadKeys, _, h⟩ := except_bind_ok_inv h
  obtain ⟨encryptedExtensions, _, h⟩ := except_bind_ok_inv h
  obtain ⟨certificate, _, h⟩ := except_bind_ok_inv h
  split at h
  case h_2 => cases h
  obtain ⟨_, h⟩ := unless_ok h
  obtain ⟨certVerify, _, h⟩ := except_bind_ok_inv h
  obtain ⟨serverFinished, _, h⟩ := except_bind_ok_inv h
  obtain ⟨serverApplicationKeys, _, h⟩ := except_bind_ok_inv h
  obtain ⟨clientApplicationKeys, _, h⟩ := except_bind_ok_inv h
  obtain ⟨flightSealed, hflight, h⟩ := except_bind_ok_inv h
  obtain ⟨flightKeys, sealedFlight⟩ := flightSealed
  obtain ⟨serverHelloWire, _, h⟩ := except_bind_ok_inv h
  have hgoal : Record.Extends state.writeKeys? (some serverApplicationKeys) :=
    Record.Extends.trans (extends_fresh state.writeKeys? serverWriteKeys)
      (Record.Extends.trans (sealHandshakeFlight_write hflight)
        (Record.Extends.rekey flightKeys serverApplicationKeys))
  split at h
  · cases h; exact hgoal
  · obtain ⟨ccsWire, _, h⟩ := except_bind_ok_inv h
    cases h
    exact hgoal

private theorem sendHelloRetryRequest_write {state next : State}
    {message : Handshake.Message} {hello : Handshake.ClientHello}
    {group : Handshake.NamedGroup} {wire : ByteArray}
    (h : sendHelloRetryRequest state message hello group = .ok (next, wire)) :
    WriteEffect state next := by
  unfold sendHelloRetryRequest at h
  simp only [pure_bind] at h
  obtain ⟨retry, _, h⟩ := except_bind_ok_inv h
  obtain ⟨messageHash, _, h⟩ := except_bind_ok_inv h
  obtain ⟨retryWire, _, h⟩ := except_bind_ok_inv h
  split at h
  · obtain ⟨ccsWire, _, h⟩ := except_bind_ok_inv h
    cases h
    exact Record.Extends.refl _
  · cases h
    exact Record.Extends.refl _

private theorem acceptClientHello_write {state next : State}
    {message : Handshake.Message} {wire : ByteArray}
    (h : acceptClientHello state message = .ok (next, wire)) :
    WriteEffect state next := by
  unfold acceptClientHello at h
  obtain ⟨hello, _, h⟩ := except_bind_ok_inv h
  obtain ⟨_, _, h⟩ := except_bind_ok_inv h
  obtain ⟨_, _, h⟩ := except_bind_ok_inv h
  split at h <;>
    first
      | (obtain ⟨group, _, h⟩ := except_bind_ok_inv h
         split at h
         · exact completeClientHello_write h
         · exact sendHelloRetryRequest_write h)
      | (split at h <;>
          first
            | cases h
            | (split at h <;>
                first
                  | cases h
                  | (obtain ⟨_, _, h⟩ := except_bind_ok_inv h
                     exact completeClientHello_write h)))
      | cases h

private theorem acceptClientFinished_write {state next : State}
    {message : Handshake.Message}
    (h : acceptClientFinished state message = .ok next) :
    WriteEffect state next := by
  unfold acceptClientFinished at h
  simp only [pure_bind] at h
  obtain ⟨finished, _, h⟩ := except_bind_ok_inv h
  split at h <;>
    first
      | (cases h <;> exact Record.Extends.refl _)
      | (split at h <;>
          first
            | (cases h <;> exact Record.Extends.refl _)
            | (split at h <;> (cases h <;> exact Record.Extends.refl _)))


private theorem processHandshakeBuffer_write {state next : State} {wire : ByteArray}
    (h : processHandshakeBuffer state = .ok (next, wire)) :
    WriteEffect state next := by
  unfold processHandshakeBuffer at h
  split at h
  · cases h
  · cases h; exact Record.Extends.refl _
  · rename_i message rest htake
    simp only [pure_bind] at h
    split at h
    · obtain ⟨_, h⟩ := unless_ok h
      obtain ⟨_, h⟩ := unless_ok h
      have hw := acceptClientHello_write h
      exact hw
    · obtain ⟨_, h⟩ := unless_ok h
      obtain ⟨_, h⟩ := unless_ok h
      have hw := acceptClientHello_write h
      exact hw
    · obtain ⟨_, h⟩ := unless_ok h
      obtain ⟨_, h⟩ := unless_ok h
      obtain ⟨stateF, hfin, h⟩ := except_bind_ok_inv h
      cases h
      have hw := acceptClientFinished_write hfin
      exact hw
    · split at h
      · obtain ⟨_, h⟩ := unless_ok h
        exact acceptKeyUpdate_write
          (state := { state with handshakeBuffered := rest }) h
      · cases h

private theorem processProtectedRecord_write {state next : State}
    {record : Record.RawRecord} {plain wire : ByteArray}
    (h : processProtectedRecord state record = .ok (next, plain, wire)) :
    WriteEffect state next := by
  unfold processProtectedRecord at h
  simp only [pure_bind] at h
  obtain ⟨readKeys, _, h⟩ := except_bind_ok_inv h
  obtain ⟨opened, _, h⟩ := except_bind_ok_inv h
  obtain ⟨nextReadKeys, plaintext⟩ := opened
  split at h
  · cases h
    exact Record.Extends.refl _
  · split at h <;>
      first
        | (obtain ⟨_, h⟩ := unless_ok h
           obtain ⟨_, h⟩ := unless_ok h
           cases h
           exact Record.Extends.refl _)
        | (obtain ⟨_, h⟩ := if_throw_ok h
           obtain ⟨pair, hpb, h⟩ := except_bind_ok_inv h
           obtain ⟨stateH, wireH⟩ := pair
           cases h
           have hw := processHandshakeBuffer_write hpb
           exact hw)
        | (obtain ⟨_, h⟩ := unless_ok h
           obtain ⟨pair, hpa, h⟩ := except_bind_ok_inv h
           obtain ⟨stateA, wireA⟩ := pair
           cases h
           have hw := processAlert_write hpa
           exact hw)
        | cases h

private theorem feedPlaintextClientHello_write {state next : State}
    {fragment wire : ByteArray}
    (h : feedPlaintextClientHello state fragment = .ok (next, wire)) :
    WriteEffect state next := by
  unfold feedPlaintextClientHello at h
  simp only [pure_bind] at h
  obtain ⟨_, h⟩ := if_throw_ok h
  have hw := processHandshakeBuffer_write h
  exact hw

private theorem processRecord_write {state next : State}
    {record : Record.RawRecord} {plain wire : ByteArray}
    (h : processRecord state record = .ok (next, plain, wire)) :
    WriteEffect state next := by
  unfold processRecord at h
  simp only [pure_bind] at h
  split at h <;> split at h <;>
    first
      | (obtain ⟨pair, hfp, h⟩ := except_bind_ok_inv h
         obtain ⟨stateP, wireP⟩ := pair
         cases h
         have hw := feedPlaintextClientHello_write hfp
         exact hw)
      | (obtain ⟨_, h⟩ := unless_ok h
         obtain ⟨_, h⟩ := unless_ok h
         cases h
         exact Record.Extends.refl _)
      | (obtain ⟨_, h⟩ := unless_ok h
         obtain ⟨pair, hpa, h⟩ := except_bind_ok_inv h
         obtain ⟨stateA, wireA⟩ := pair
         cases h
         have hw := processAlert_write hpa
         exact hw)
      | exact processProtectedRecord_write h
      | cases h

private theorem processRecords_write {state : State}
    {records : List Record.RawRecord} {plaintext wireBytes : ByteArray}
    {out : Output}
    (h : processRecords state records plaintext wireBytes = .ok out) :
    WriteEffect state out.state := by
  induction records generalizing state plaintext wireBytes with
  | nil =>
      unfold processRecords at h
      cases h
      exact Record.Extends.refl _
  | cons record rest ih =>
      unfold processRecords at h
      split at h
      · cases h
        exact Record.Extends.refl _
      · split at h
        · cases h
        · rename_i stateN cleartext outbound hpr
          have h1 := processRecord_write hpr
          have h2 := ih h
          exact Record.Extends.trans h1 h2

private theorem processRecords_write_error {state : State}
    {records : List Record.RawRecord} {plaintext wireBytes : ByteArray}
    {failure : Failure}
    (h : processRecords state records plaintext wireBytes = .error failure) :
    WriteEffect state failure.state := by
  induction records generalizing state plaintext wireBytes with
  | nil => unfold processRecords at h; cases h
  | cons record rest ih =>
      unfold processRecords at h
      split at h
      · cases h
      · split at h
        · cases h
          exact Record.Extends.refl _
        · rename_i stateN cleartext outbound hpr
          have h1 := processRecord_write hpr
          have h2 := ih h
          exact Record.Extends.trans h1 h2

theorem feedWithFailure_write {initial : State} {chunk : ByteArray} {out : Output}
    (h : feedWithFailure initial chunk = .ok out) :
    WriteEffect initial out.state := by
  unfold feedWithFailure at h
  split at h
  · cases h
    exact Record.Extends.refl _
  · split at h
    · cases h
    · have hw := processRecords_write h
      exact hw

theorem feedWithFailure_write_error {initial : State} {chunk : ByteArray}
    {failure : Failure} (h : feedWithFailure initial chunk = .error failure) :
    WriteEffect initial failure.state := by
  unfold feedWithFailure at h
  split at h
  · cases h
  · split at h
    · cases h; exact Record.Extends.refl _
    · have hw := processRecords_write_error h
      exact hw

theorem feed_write {state : State} {chunk : ByteArray} {out : Output}
    (h : feed state chunk = .ok out) : WriteEffect state out.state := by
  unfold feed at h
  cases hf : feedWithFailure state chunk with
  | error failure => rw [hf] at h; cases h
  | ok output =>
      rw [hf] at h
      simp only [Except.mapError] at h
      cases h
      exact feedWithFailure_write hf

theorem step_write {state : State} {op : Op} {out : Output}
    (h : step state op = .ok out) : WriteEffect state out.state := by
  unfold step at h
  split at h
  · exact feed_write h
  · exact sealApplication_write h
  · exact closeNotify_write h
  · exact sealFatalAlert_write h

theorem run_write {ops : List Op} : ∀ {state : State} {out : Output},
    run state ops = .ok out → WriteEffect state out.state := by
  induction ops with
  | nil =>
      intro state out h
      unfold run at h; cases h; exact Record.Extends.refl _
  | cons op rest ih =>
      intro state out h
      unfold run at h
      split at h
      · cases h
      · rename_i out1 hstep
        split at h
        · cases h
        · rename_i final hrun
          have h1 := step_write hstep
          have h2 := ih hrun
          cases h
          exact Record.Extends.trans h1 h2

/-! ## Handshake state invariants -/

/-- Structural invariant of a server connection, in two clauses.

**An established connection has installed the client application traffic epoch
and consumed the values the handshake needed to get there** — the expected
client Finished and the pre-computed client application keys are gone. Before
the connection is established that clause says nothing, which is right: those
are exactly the states that legitimately hold them.

**Once the server has sent its flight it can always protect a record.** The
server installs its write epoch one transition earlier than the client does —
in `completeClientHello`, on the way into `waitingClientFinished`, because the
flight it emits right there is already encrypted — so the clause is indexed by
phase rather than being a bare `connected → …`: it holds from
`waitingClientFinished` onwards. It is what makes `sealApplication`,
`closeNotify`, `sealFatalAlert` and a KeyUpdate response total on an
established connection: none of them can fail for want of a write epoch.

**A server still waiting for a ClientHello holds no traffic epoch at all** — in
either direction. This is the mirror of the client's
`Tls.Client.State.WellFormed.noReadKeys` / `noWriteKeys`, and it covers the
HelloRetryRequest detour too: `sendHelloRetryRequest` installs nothing, so a
server in `waitingSecondClientHello` is still keyless. Two things follow. It can
decrypt nothing before it has answered a ClientHello, so it can deliver no
plaintext; and `completeClientHello` *installs* the connection's first write
epoch rather than replacing one, which is what `run_nonce_trace_spec` needs to
start its structural epoch history at `none`.

`start_wellFormed` establishes all three and `feed`, `feedWithFailure`,
`sealApplication`, `closeNotify`, `sealFatalAlert` and whole `run`s preserve
them. How the connection becomes established — the client Finished was verified
against the expected value — is the transition law
`acceptClientFinished_verified` below. -/
def State.WellFormed (state : State) : Prop :=
  (state.phase = .connected →
    state.readKeys?.isSome = true ∧
      state.expectedClientFinished? = none ∧
      state.clientApplicationKeys? = none) ∧
  (state.phase = .waitingClientFinished ∨ state.phase = .connected →
    state.writeKeys?.isSome = true) ∧
  (state.phase = .waitingClientHello ∨ state.phase = .waitingSecondClientHello →
    state.readKeys? = none ∧ state.writeKeys? = none)

/-- The established-connection clause, as a projection. -/
theorem State.WellFormed.connected {state : State} (h : state.WellFormed)
    (hc : state.phase = .connected) :
    state.readKeys?.isSome = true ∧ state.expectedClientFinished? = none ∧
      state.clientApplicationKeys? = none := h.1 hc

/-- **A server that has sent its flight holds a write epoch.** -/
theorem State.WellFormed.writeKeys {state : State} (h : state.WellFormed)
    (hp : state.phase = .waitingClientFinished ∨ state.phase = .connected) :
    state.writeKeys?.isSome = true := h.2.1 hp

/-- **A server still waiting for a ClientHello holds no read epoch**, so it can
decrypt nothing and therefore deliver nothing. The mirror of
`Tls.Client.State.WellFormed.noReadKeys`. -/
theorem State.WellFormed.noReadKeys {state : State} (h : state.WellFormed)
    (hp : state.phase = .waitingClientHello ∨
      state.phase = .waitingSecondClientHello) :
    state.readKeys? = none := (h.2.2 hp).1

/-- **A server still waiting for a ClientHello holds no write epoch either.** -/
theorem State.WellFormed.noWriteKeys {state : State} (h : state.WellFormed)
    (hp : state.phase = .waitingClientHello ∨
      state.phase = .waitingSecondClientHello) :
    state.writeKeys? = none := (h.2.2 hp).2

/-- Transfer the invariant across a state update that changes no field it
mentions, except by installing read or write traffic keys. -/
private theorem wellFormed_transfer {s t : State} (hinv : s.WellFormed)
    (hphase : t.phase = s.phase)
    (hread : t.readKeys? = s.readKeys? ∨
      (∃ k, t.readKeys? = some k) ∧ s.readKeys?.isSome = true)
    (h1 : t.expectedClientFinished? = s.expectedClientFinished?)
    (h2 : t.clientApplicationKeys? = s.clientApplicationKeys?)
    (hwrite : t.writeKeys? = s.writeKeys? ∨
      (∃ k, t.writeKeys? = some k) ∧ s.writeKeys?.isSome = true) :
    t.WellFormed := by
  refine ⟨fun hc => ?_, fun hp => ?_, fun hp => ⟨?_, ?_⟩⟩
  · obtain ⟨b, c, d⟩ := hinv.1 (hphase ▸ hc)
    refine ⟨?_, by rw [h1]; exact c, by rw [h2]; exact d⟩
    cases hread with
    | inl hr => rw [hr]; exact b
    | inr hr => obtain ⟨⟨k, hk⟩, -⟩ := hr; rw [hk]; rfl
  · cases hwrite with
    | inl hw => rw [hw]; exact hinv.2.1 (by rw [← hphase]; exact hp)
    | inr hw => obtain ⟨⟨k, hk⟩, -⟩ := hw; rw [hk]; rfl
  · cases hread with
    | inl hr => rw [hr]; exact (hinv.2.2 (by rw [← hphase]; exact hp)).1
    | inr hr =>
        obtain ⟨-, hs⟩ := hr
        rw [(hinv.2.2 (by rw [← hphase]; exact hp)).1] at hs
        exact absurd hs (by decide)
  · cases hwrite with
    | inl hw => rw [hw]; exact (hinv.2.2 (by rw [← hphase]; exact hp)).2
    | inr hw =>
        obtain ⟨-, hs⟩ := hw
        rw [(hinv.2.2 (by rw [← hphase]; exact hp)).2] at hs
        exact absurd hs (by decide)

/-- A fresh server connection is waiting for the ClientHello, so both clauses
hold vacuously. -/
theorem start_wellFormed (config : Config) : (start config).WellFormed := by
  refine ⟨fun hc => (by cases hc), fun hp => ?_, fun _ => ⟨rfl, rfl⟩⟩
  rcases hp with hp | hp <;> cases hp

theorem sealFatalAlert_wellFormed {state : State} {description : UInt8}
    {out : Output} (h : sealFatalAlert state description = .ok out)
    (hinv : state.WellFormed) : out.state.WellFormed := by
  unfold sealFatalAlert at h
  simp only [pure_bind] at h
  split at h
  · cases h
  · split at h
    · rename_i writeKeys hkeys
      obtain ⟨sealed, hs, h⟩ := except_bind_ok_inv h
      obtain ⟨nextKeys, wire⟩ := sealed
      cases h
      exact wellFormed_transfer hinv rfl (.inl rfl) rfl rfl
        (.inr ⟨⟨_, rfl⟩, by rw [hkeys]; rfl⟩)
    · rename_i hkeys
      obtain ⟨_, h⟩ := unless_ok h
      obtain ⟨wire, _, h⟩ := except_bind_ok_inv h
      cases h
      exact wellFormed_transfer hinv rfl (.inl rfl) rfl rfl (.inl rfl)

private theorem emitCloseNotify_wellFormed {state next : State} {wire : ByteArray}
    (h : emitCloseNotify state = .ok (next, wire)) (hinv : state.WellFormed) :
    next.WellFormed := by
  unfold emitCloseNotify at h
  split at h
  · cases h; exact hinv
  · obtain ⟨keys, hk, h⟩ := except_bind_ok_inv h
    obtain ⟨sealed, hs, h⟩ := except_bind_ok_inv h
    obtain ⟨sealedKeys, wireBytes⟩ := sealed
    cases h
    exact wellFormed_transfer hinv rfl (.inl rfl) rfl rfl
      (.inr ⟨⟨_, rfl⟩, requireWriteKeys_isSome hk⟩)

theorem sealApplication_wellFormed {state : State} {plaintext : ByteArray}
    {out : Output} (h : sealApplication state plaintext = .ok out)
    (hinv : state.WellFormed) : out.state.WellFormed := by
  unfold sealApplication at h
  simp only [pure_bind] at h
  split at h
  · split at h
    · cases h
    · split at h
      · cases h; exact hinv
      · obtain ⟨keys, hk, h⟩ := except_bind_ok_inv h
        obtain ⟨sealed, hs, h⟩ := except_bind_ok_inv h
        obtain ⟨nextKeys, records⟩ := sealed
        cases h
        exact wellFormed_transfer hinv rfl (.inl rfl) rfl rfl
          (.inr ⟨⟨_, rfl⟩, requireWriteKeys_isSome hk⟩)
  · cases h

theorem closeNotify_wellFormed {state : State} {out : Output}
    (h : closeNotify state = .ok out) (hinv : state.WellFormed) :
    out.state.WellFormed := by
  unfold closeNotify at h
  simp only [pure_bind] at h
  split at h
  case isFalse => cases h
  obtain ⟨pair, hp, h⟩ := except_bind_ok_inv h
  obtain ⟨next, wire⟩ := pair
  cases h
  exact emitCloseNotify_wellFormed hp hinv

private theorem processAlert_wellFormed {state next : State} {fragment : ByteArray}
    {duringHandshake : Bool} {wire : ByteArray}
    (h : processAlert state fragment duringHandshake = .ok (next, wire))
    (hinv : state.WellFormed) : next.WellFormed := by
  unfold processAlert at h
  simp only [pure_bind] at h
  split at h
  case isFalse => cases h
  split at h
  · split at h
    · cases h
    · cases h
      exact wellFormed_transfer hinv rfl (.inl rfl) rfl rfl (.inl rfl)
  · split at h
    · cases h
      exact hinv
    · cases h

private theorem sendKeyUpdateResponse_wellFormed {state next : State}
    {wire : ByteArray} (h : sendKeyUpdateResponse state = .ok (next, wire))
    (hinv : state.WellFormed) : next.WellFormed := by
  unfold sendKeyUpdateResponse at h
  split at h
  · obtain ⟨_, _, h⟩ := except_bind_ok_inv h
    obtain ⟨keys, hk, h⟩ := except_bind_ok_inv h
    obtain ⟨sealed, hs, h⟩ := except_bind_ok_inv h
    obtain ⟨advancedKeys, wireBytes⟩ := sealed
    obtain ⟨updatedKeys, hu, h⟩ := except_bind_ok_inv h
    cases h
    exact wellFormed_transfer hinv rfl (.inl rfl) rfl rfl
      (.inr ⟨⟨_, rfl⟩, requireWriteKeys_isSome hk⟩)
  · cases h
    exact hinv

private theorem acceptKeyUpdate_wellFormed {state next : State}
    {message : Handshake.Message} {wire : ByteArray}
    (h : acceptKeyUpdate state message = .ok (next, wire))
    (hinv : state.WellFormed) : next.WellFormed := by
  unfold acceptKeyUpdate at h
  obtain ⟨_, _, h⟩ := except_bind_ok_inv h
  obtain ⟨_, hrk, h⟩ := except_bind_ok_inv h
  obtain ⟨_, _, h⟩ := except_bind_ok_inv h
  split at h
  · cases h
    exact wellFormed_transfer hinv rfl
      (.inr ⟨⟨_, rfl⟩, requireReadKeys_isSome hrk⟩) rfl rfl (.inl rfl)
  · simp only [] at h
    split at h
    · cases h
      exact wellFormed_transfer hinv rfl
        (.inr ⟨⟨_, rfl⟩, requireReadKeys_isSome hrk⟩) rfl rfl (.inl rfl)
    · exact sendKeyUpdateResponse_wellFormed h
        (wellFormed_transfer hinv rfl
          (.inr ⟨⟨_, rfl⟩, requireReadKeys_isSome hrk⟩) rfl rfl (.inl rfl))

private theorem completeClientHello_wellFormed {state next : State}
    {hello : Handshake.ClientHello} {group : Handshake.NamedGroup}
    {transcriptPrefix wire : ByteArray}
    (h : completeClientHello state hello group transcriptPrefix = .ok (next, wire)) :
    next.WellFormed := by
  unfold completeClientHello at h
  simp only [pure_bind] at h
  obtain ⟨exchanged, _, h⟩ := except_bind_ok_inv h
  obtain ⟨serverPublic, sharedSecret⟩ := exchanged
  obtain ⟨_, h⟩ := unless_ok h
  obtain ⟨serverHello, _, h⟩ := except_bind_ok_inv h
  obtain ⟨serverWriteKeys, _, h⟩ := except_bind_ok_inv h
  obtain ⟨clientReadKeys, _, h⟩ := except_bind_ok_inv h
  obtain ⟨encryptedExtensions, _, h⟩ := except_bind_ok_inv h
  obtain ⟨certificate, _, h⟩ := except_bind_ok_inv h
  split at h
  case h_2 => cases h
  obtain ⟨_, h⟩ := unless_ok h
  obtain ⟨certVerify, _, h⟩ := except_bind_ok_inv h
  obtain ⟨serverFinished, _, h⟩ := except_bind_ok_inv h
  obtain ⟨serverApplicationKeys, _, h⟩ := except_bind_ok_inv h
  obtain ⟨clientApplicationKeys, _, h⟩ := except_bind_ok_inv h
  obtain ⟨flightSealed, hflight, h⟩ := except_bind_ok_inv h
  obtain ⟨flightKeys, sealedFlight⟩ := flightSealed
  obtain ⟨serverHelloWire, _, h⟩ := except_bind_ok_inv h
  split at h
  · cases h
    exact ⟨fun hc => (by cases hc), fun _ => rfl,
      fun hp => (by rcases hp with hp | hp <;> cases hp)⟩
  · obtain ⟨ccsWire, _, h⟩ := except_bind_ok_inv h
    cases h
    exact ⟨fun hc => (by cases hc), fun _ => rfl,
      fun hp => (by rcases hp with hp | hp <;> cases hp)⟩

private theorem sendHelloRetryRequest_wellFormed {state next : State}
    {message : Handshake.Message} {hello : Handshake.ClientHello}
    {group : Handshake.NamedGroup} {wire : ByteArray}
    (h : sendHelloRetryRequest state message hello group = .ok (next, wire))
    (hkeys : state.readKeys? = none ∧ state.writeKeys? = none) :
    next.WellFormed := by
  unfold sendHelloRetryRequest at h
  simp only [pure_bind] at h
  obtain ⟨retry, _, h⟩ := except_bind_ok_inv h
  obtain ⟨messageHash, _, h⟩ := except_bind_ok_inv h
  obtain ⟨retryWire, _, h⟩ := except_bind_ok_inv h
  split at h
  · obtain ⟨ccsWire, _, h⟩ := except_bind_ok_inv h
    cases h
    exact ⟨fun hc => (by cases hc),
      fun hp => (by rcases hp with hp | hp <;> cases hp), fun _ => hkeys⟩
  · cases h
    exact ⟨fun hc => (by cases hc),
      fun hp => (by rcases hp with hp | hp <;> cases hp), fun _ => hkeys⟩

private theorem acceptClientHello_wellFormed {state next : State}
    {message : Handshake.Message} {wire : ByteArray}
    (h : acceptClientHello state message = .ok (next, wire))
    (hkeys : state.readKeys? = none ∧ state.writeKeys? = none) :
    next.WellFormed := by
  unfold acceptClientHello at h
  obtain ⟨hello, _, h⟩ := except_bind_ok_inv h
  obtain ⟨_, _, h⟩ := except_bind_ok_inv h
  obtain ⟨_, _, h⟩ := except_bind_ok_inv h
  split at h <;>
    first
      | (obtain ⟨group, _, h⟩ := except_bind_ok_inv h
         split at h
         · exact completeClientHello_wellFormed h
         · exact sendHelloRetryRequest_wellFormed h hkeys)
      | (split at h <;>
          first
            | cases h
            | (split at h <;>
                first
                  | cases h
                  | (obtain ⟨_, _, h⟩ := except_bind_ok_inv h
                     exact completeClientHello_wellFormed h)))
      | cases h

/-- **The server becomes connected only by verifying the client Finished**
against the value it computed when it built its own flight. This is the only
transition into `Phase.connected`. -/
theorem acceptClientFinished_verified {state next : State}
    {message : Handshake.Message}
    (h : acceptClientFinished state message = .ok next) :
    ∃ finished expected,
      Handshake.parseFinished message = .ok finished ∧
        state.expectedClientFinished? = some expected ∧
        constantTimeEq expected finished.verifyData = true := by
  unfold acceptClientFinished at h
  simp only [pure_bind] at h
  obtain ⟨finished, hfin, h⟩ := except_bind_ok_inv h
  split at h
  · rename_i expected hexp
    split at h
    · rename_i hverify
      exact ⟨finished, expected, liftHandshake_ok hfin, hexp, hverify⟩
    · cases h
  · cases h

/-- The transition into `connected`: the client application epoch moves into
`readKeys?`, and the write epoch installed back in `completeClientHello` is
carried over unchanged — which is why this is the one preservation lemma that
needs its predecessor's `waitingClientFinished` clause as an input. -/
private theorem acceptClientFinished_wellFormed {state next : State}
    {message : Handshake.Message}
    (h : acceptClientFinished state message = .ok next)
    (hwrite : state.writeKeys?.isSome = true) : next.WellFormed := by
  unfold acceptClientFinished at h
  simp only [pure_bind] at h
  obtain ⟨finished, _, h⟩ := except_bind_ok_inv h
  split at h
  · split at h
    · split at h
      · cases h
        exact ⟨fun _ => ⟨rfl, rfl, rfl⟩, fun _ => hwrite,
          fun hp => (by rcases hp with hp | hp <;> cases hp)⟩
      · cases h
    · cases h
  · cases h

private theorem processHandshakeBuffer_wellFormed {state next : State}
    {wire : ByteArray} (h : processHandshakeBuffer state = .ok (next, wire))
    (hinv : state.WellFormed) : next.WellFormed := by
  unfold processHandshakeBuffer at h
  split at h
  · cases h
  · cases h; exact hinv
  · rename_i message rest htake
    simp only [pure_bind] at h
    split at h
    · rename_i hph
      obtain ⟨_, h⟩ := unless_ok h
      obtain ⟨_, h⟩ := unless_ok h
      exact acceptClientHello_wellFormed h (hinv.2.2 (.inl hph))
    · rename_i hph
      obtain ⟨_, h⟩ := unless_ok h
      obtain ⟨_, h⟩ := unless_ok h
      exact acceptClientHello_wellFormed h (hinv.2.2 (.inr hph))
    · rename_i hph
      obtain ⟨_, h⟩ := unless_ok h
      obtain ⟨_, h⟩ := unless_ok h
      obtain ⟨stateF, hfin, h⟩ := except_bind_ok_inv h
      cases h
      exact acceptClientFinished_wellFormed hfin (hinv.2.1 (.inl hph))
    · split at h
      · obtain ⟨_, h⟩ := unless_ok h
        exact acceptKeyUpdate_wellFormed h
          (wellFormed_transfer hinv rfl (.inl rfl) rfl rfl (.inl rfl))
      · cases h

private theorem processProtectedRecord_wellFormed {state next : State}
    {record : Record.RawRecord} {plain wire : ByteArray}
    (h : processProtectedRecord state record = .ok (next, plain, wire))
    (hinv : state.WellFormed) : next.WellFormed := by
  unfold processProtectedRecord at h
  simp only [pure_bind] at h
  obtain ⟨readKeys, hrk, h⟩ := except_bind_ok_inv h
  obtain ⟨opened, _, h⟩ := except_bind_ok_inv h
  obtain ⟨nextReadKeys, plaintext⟩ := opened
  have hinv' : ({ state with readKeys? := some nextReadKeys } : State).WellFormed :=
    wellFormed_transfer hinv rfl
      (.inr ⟨⟨_, rfl⟩, requireReadKeys_isSome hrk⟩) rfl rfl (.inl rfl)
  split at h
  · cases h
    exact hinv'
  · split at h <;>
      first
        | (obtain ⟨_, h⟩ := unless_ok h
           obtain ⟨_, h⟩ := unless_ok h
           cases h
           exact hinv')
        | (obtain ⟨_, h⟩ := if_throw_ok h
           obtain ⟨pair, hpb, h⟩ := except_bind_ok_inv h
           obtain ⟨stateH, wireH⟩ := pair
           cases h
           exact processHandshakeBuffer_wellFormed hpb hinv')
        | (obtain ⟨_, h⟩ := unless_ok h
           obtain ⟨pair, hpa, h⟩ := except_bind_ok_inv h
           obtain ⟨stateA, wireA⟩ := pair
           cases h
           exact processAlert_wellFormed hpa hinv')
        | cases h

private theorem feedPlaintextClientHello_wellFormed {state next : State}
    {fragment wire : ByteArray}
    (h : feedPlaintextClientHello state fragment = .ok (next, wire))
    (hinv : state.WellFormed) : next.WellFormed := by
  unfold feedPlaintextClientHello at h
  simp only [pure_bind] at h
  obtain ⟨_, h⟩ := if_throw_ok h
  exact processHandshakeBuffer_wellFormed h
    (wellFormed_transfer hinv rfl (.inl rfl) rfl rfl (.inl rfl))

private theorem processRecord_wellFormed {state next : State}
    {record : Record.RawRecord} {plain wire : ByteArray}
    (h : processRecord state record = .ok (next, plain, wire))
    (hinv : state.WellFormed) : next.WellFormed := by
  unfold processRecord at h
  simp only [pure_bind] at h
  split at h <;> split at h <;>
    first
      | (obtain ⟨pair, hfp, h⟩ := except_bind_ok_inv h
         obtain ⟨stateP, wireP⟩ := pair
         cases h
         exact feedPlaintextClientHello_wellFormed hfp hinv)
      | (obtain ⟨_, h⟩ := unless_ok h
         obtain ⟨_, h⟩ := unless_ok h
         cases h
         exact hinv)
      | (obtain ⟨_, h⟩ := unless_ok h
         obtain ⟨pair, hpa, h⟩ := except_bind_ok_inv h
         obtain ⟨stateA, wireA⟩ := pair
         cases h
         exact processAlert_wellFormed hpa hinv)
      | exact processProtectedRecord_wellFormed h hinv
      | cases h

private theorem processRecords_wellFormed {records : List Record.RawRecord} :
    ∀ {state : State} {plaintext wireBytes : ByteArray} {out : Output},
      processRecords state records plaintext wireBytes = .ok out →
        state.WellFormed → out.state.WellFormed := by
  induction records with
  | nil =>
      intro state plaintext wireBytes out h hinv
      unfold processRecords at h
      cases h
      exact hinv
  | cons record rest ih =>
      intro state plaintext wireBytes out h hinv
      unfold processRecords at h
      split at h
      · cases h
        exact hinv
      · split at h
        · cases h
        · rename_i stateN cleartext outbound hpr
          exact ih h (processRecord_wellFormed hpr hinv)

theorem feedWithFailure_wellFormed {initial : State} {chunk : ByteArray}
    {out : Output} (h : feedWithFailure initial chunk = .ok out)
    (hinv : initial.WellFormed) : out.state.WellFormed := by
  unfold feedWithFailure at h
  split at h
  · cases h
    exact hinv
  · split at h
    · cases h
    · exact processRecords_wellFormed h
        ⟨fun hc => hinv.1 hc, fun hp => hinv.2.1 hp, fun hp => hinv.2.2 hp⟩

theorem feed_wellFormed {state : State} {chunk : ByteArray} {out : Output}
    (h : feed state chunk = .ok out) (hinv : state.WellFormed) :
    out.state.WellFormed := by
  unfold feed at h
  cases hf : feedWithFailure state chunk with
  | error failure => rw [hf] at h; cases h
  | ok output =>
      rw [hf] at h
      simp only [Except.mapError] at h
      cases h
      exact feedWithFailure_wellFormed hf hinv

theorem step_wellFormed {state : State} {op : Op} {out : Output}
    (h : step state op = .ok out) (hinv : state.WellFormed) :
    out.state.WellFormed := by
  unfold step at h
  split at h
  · exact feed_wellFormed h hinv
  · exact sealApplication_wellFormed h hinv
  · exact closeNotify_wellFormed h hinv
  · exact sealFatalAlert_wellFormed h hinv

/-- **The invariant survives a whole run.** -/
theorem run_wellFormed {ops : List Op} : ∀ {state : State} {out : Output},
    run state ops = .ok out → state.WellFormed → out.state.WellFormed := by
  induction ops with
  | nil =>
      intro state out h hinv
      unfold run at h; cases h; exact hinv
  | cons op rest ih =>
      intro state out h hinv
      unfold run at h
      split at h
      · cases h
      · rename_i out1 hstep
        split at h
        · cases h
        · rename_i final hrun
          have h2 := ih hrun (step_wellFormed hstep hinv)
          cases h
          exact h2

/-! ## Transition laws -/

private theorem phase_eq_of_beq {p q : Phase} (h : (p == q) = true) : p = q := by
  cases p <;> cases q <;> first | rfl | exact absurd h (by decide)

/-- **Application data is protected only by an established connection whose
local write direction is open.** A peer `close_notify` does not close this
direction. -/
theorem sealApplication_connected {state : State} {plaintext : ByteArray}
    {out : Output} (h : sealApplication state plaintext = .ok out) :
    state.phase = .connected ∧ state.localClosed = false := by
  unfold sealApplication at h
  simp only [pure_bind] at h
  obtain ⟨hp, h⟩ := unless_ok h
  obtain ⟨hcl, h⟩ := if_throw_ok h
  exact ⟨phase_eq_of_beq hp, by simpa using hcl⟩

/-- **`close_notify` is sent only by an established connection.** -/
theorem closeNotify_connected {state : State} {out : Output}
    (h : closeNotify state = .ok out) : state.phase = .connected := by
  unfold closeNotify at h
  simp only [pure_bind] at h
  obtain ⟨hp, h⟩ := unless_ok h
  exact phase_eq_of_beq hp

/-- **Inbound transport is ignored after the peer half-closes.** Once the
peer's `close_notify` has been received, feeding any later chunk returns the
same state and no plaintext or outbound bytes. The local write direction stays
available until the caller sends its own `close_notify`. -/
theorem feedWithFailure_peerClosed_ignored {state : State} {chunk : ByteArray}
    (hclosed : state.peerClosed = true) :
    feedWithFailure state chunk = .ok { state } := by
  unfold feedWithFailure
  rw [if_pos hclosed]

/-! ### Inbound application data

The mirror of `sealApplication_connected`. Outbound, the engine refuses to
protect application data unless the connection is established; inbound, this is
the statement that the caller never *receives* application-data plaintext from
any other state. Both directions are needed: an engine that leaked pre-handshake
bytes to the caller would be just as broken as one that sent them.

The chain is one lemma per level, each in the combined form "either we were
already connected, or this level produced plaintext — then the successor state
is connected". The disjunction is what lets a single induction over a whole feed
work: `processRecords` accumulates plaintext across records, so a record that
delivers nothing must still carry the connectedness established by an earlier
one. -/

private theorem emitCloseNotify_phase {state next : State} {wire : ByteArray}
    (h : emitCloseNotify state = .ok (next, wire)) : next.phase = state.phase := by
  unfold emitCloseNotify at h
  split at h
  · cases h; rfl
  · obtain ⟨keys, hk, h⟩ := except_bind_ok_inv h
    obtain ⟨sealed, hs, h⟩ := except_bind_ok_inv h
    obtain ⟨sealedKeys, wireBytes⟩ := sealed
    cases h
    rfl

private theorem processAlert_phase {state next : State} {fragment : ByteArray}
    {duringHandshake : Bool} {wire : ByteArray}
    (h : processAlert state fragment duringHandshake = .ok (next, wire)) :
    next.phase = state.phase := by
  unfold processAlert at h
  simp only [pure_bind] at h
  split at h
  case isFalse => cases h
  split at h
  · split at h
    · cases h
    · cases h
      rfl
  · split at h
    · cases h
      rfl
    · cases h

private theorem sendKeyUpdateResponse_phase {state next : State} {wire : ByteArray}
    (h : sendKeyUpdateResponse state = .ok (next, wire)) :
    next.phase = state.phase := by
  unfold sendKeyUpdateResponse at h
  split at h
  · obtain ⟨_, _, h⟩ := except_bind_ok_inv h
    obtain ⟨keys, hk, h⟩ := except_bind_ok_inv h
    obtain ⟨sealed, hs, h⟩ := except_bind_ok_inv h
    obtain ⟨advancedKeys, wireBytes⟩ := sealed
    obtain ⟨updatedKeys, hu, h⟩ := except_bind_ok_inv h
    cases h
    rfl
  · cases h
    rfl

private theorem acceptKeyUpdate_phase {state next : State}
    {message : Handshake.Message} {wire : ByteArray}
    (h : acceptKeyUpdate state message = .ok (next, wire)) :
    next.phase = state.phase := by
  unfold acceptKeyUpdate at h
  obtain ⟨_, _, h⟩ := except_bind_ok_inv h
  obtain ⟨_, _, h⟩ := except_bind_ok_inv h
  obtain ⟨_, _, h⟩ := except_bind_ok_inv h
  split at h
  · cases h; rfl
  · simp only [] at h
    split at h
    · cases h; rfl
    · have hp := sendKeyUpdateResponse_phase h
      exact hp

/-- Post-handshake messages do not leave `connected`: the only handshake
message the engine accepts there is a KeyUpdate, which changes epochs, not
phases. -/
private theorem processHandshakeBuffer_connected {state next : State}
    {wire : ByteArray} (h : processHandshakeBuffer state = .ok (next, wire))
    (hc : state.phase = .connected) : next.phase = .connected := by
  unfold processHandshakeBuffer at h
  split at h
  · cases h
  · cases h; exact hc
  · rename_i message rest htake
    simp only [pure_bind] at h
    split at h
    · rename_i hph
      have hph' : state.phase = Phase.waitingClientHello := hph
      rw [hc] at hph'; cases hph'
    · rename_i hph
      have hph' : state.phase = Phase.waitingSecondClientHello := hph
      rw [hc] at hph'; cases hph'
    · rename_i hph
      have hph' : state.phase = Phase.waitingClientFinished := hph
      rw [hc] at hph'; cases hph'
    · split at h
      · obtain ⟨_, h⟩ := unless_ok h
        rw [acceptKeyUpdate_phase h]
        exact hc
      · cases h

/-- The delivery point: a protected record hands plaintext up only from the
`applicationData` branch, which refuses to run unless the phase is
`connected`. -/
private theorem processProtectedRecord_plaintext {state next : State}
    {record : Record.RawRecord} {plain wire : ByteArray}
    (h : processProtectedRecord state record = .ok (next, plain, wire))
    (hp : state.phase = .connected ∨ plain.isEmpty = false) :
    next.phase = .connected := by
  unfold processProtectedRecord at h
  simp only [pure_bind] at h
  obtain ⟨readKeys, _, h⟩ := except_bind_ok_inv h
  obtain ⟨opened, _, h⟩ := except_bind_ok_inv h
  obtain ⟨nextReadKeys, plaintext⟩ := opened
  split at h
  · cases h
    rcases hp with hc | hne
    · exact hc
    · exact absurd hne (by decide)
  · split at h
    · obtain ⟨hph, h⟩ := unless_ok h
      obtain ⟨_, h⟩ := unless_ok h
      cases h
      exact phase_eq_of_beq hph
    · obtain ⟨_, h⟩ := if_throw_ok h
      obtain ⟨pair, hpb, h⟩ := except_bind_ok_inv h
      obtain ⟨stateH, wireH⟩ := pair
      cases h
      rcases hp with hc | hne
      · exact processHandshakeBuffer_connected hpb hc
      · exact absurd hne (by decide)
    · obtain ⟨_, h⟩ := unless_ok h
      obtain ⟨pair, hpa, h⟩ := except_bind_ok_inv h
      obtain ⟨stateA, wireA⟩ := pair
      cases h
      rcases hp with hc | hne
      · have hph := processAlert_phase hpa
        exact hph.trans hc
      · exact absurd hne (by decide)
    · cases h

private theorem processRecord_plaintext {state next : State}
    {record : Record.RawRecord} {plain wire : ByteArray}
    (h : processRecord state record = .ok (next, plain, wire))
    (hp : state.phase = .connected ∨ plain.isEmpty = false) :
    next.phase = .connected := by
  unfold processRecord at h
  simp only [pure_bind] at h
  split at h
  · -- waitingClientHello: no plaintext is ever produced, and the phase is not
    -- `connected`, so both disjuncts are impossible.
    rename_i hph
    have hph' : state.phase = Phase.waitingClientHello := hph
    split at h <;>
      first
        | (obtain ⟨pair, _, h⟩ := except_bind_ok_inv h
           obtain ⟨stateP, wireP⟩ := pair
           cases h
           rcases hp with hc | hne
           · rw [hc] at hph'; cases hph'
           · exact absurd hne (by decide))
        | (obtain ⟨_, h⟩ := unless_ok h
           obtain ⟨pair, _, h⟩ := except_bind_ok_inv h
           obtain ⟨stateA, wireA⟩ := pair
           cases h
           rcases hp with hc | hne
           · rw [hc] at hph'; cases hph'
           · exact absurd hne (by decide))
        | cases h
  · rename_i hph
    have hph' : state.phase = Phase.waitingSecondClientHello := hph
    split at h <;>
      first
        | (obtain ⟨pair, _, h⟩ := except_bind_ok_inv h
           obtain ⟨stateP, wireP⟩ := pair
           cases h
           rcases hp with hc | hne
           · rw [hc] at hph'; cases hph'
           · exact absurd hne (by decide))
        | (obtain ⟨_, h⟩ := unless_ok h
           obtain ⟨_, h⟩ := unless_ok h
           cases h
           rcases hp with hc | hne
           · rw [hc] at hph'; cases hph'
           · exact absurd hne (by decide))
        | (obtain ⟨_, h⟩ := unless_ok h
           obtain ⟨pair, _, h⟩ := except_bind_ok_inv h
           obtain ⟨stateA, wireA⟩ := pair
           cases h
           rcases hp with hc | hne
           · rw [hc] at hph'; cases hph'
           · exact absurd hne (by decide))
        | cases h
  · rename_i hph
    have hph' : state.phase = Phase.waitingClientFinished := hph
    split at h <;>
      first
        | (obtain ⟨_, h⟩ := unless_ok h
           obtain ⟨_, h⟩ := unless_ok h
           cases h
           rcases hp with hc | hne
           · rw [hc] at hph'; cases hph'
           · exact absurd hne (by decide))
        | exact processProtectedRecord_plaintext h hp
        | cases h
  · rename_i hph
    have hph' : state.phase = Phase.connected := hph
    split at h <;>
      first
        | exact processProtectedRecord_plaintext h (.inl hph')
        | cases h

private theorem append_isEmpty_false {a b : ByteArray}
    (h : (a ++ b).isEmpty = false) : a.isEmpty = false ∨ b.isEmpty = false := by
  simp only [ByteArray.isEmpty, beq_iff_eq, Bool.eq_false_iff, ne_eq,
    ByteArray.size_append] at h ⊢
  omega

/-- `connected` is absorbing across a whole feed. -/
private theorem processRecords_connected {records : List Record.RawRecord} :
    ∀ {state : State} {plaintext wireBytes : ByteArray} {out : Output},
      processRecords state records plaintext wireBytes = .ok out →
        state.phase = .connected → out.state.phase = .connected := by
  induction records with
  | nil =>
      intro state plaintext wireBytes out h hc
      unfold processRecords at h
      cases h
      exact hc
  | cons record rest ih =>
      intro state plaintext wireBytes out h hc
      unfold processRecords at h
      split at h
      · cases h
        exact hc
      · split at h
        · cases h
        · rename_i stateN cleartext outbound hpr
          exact ih h (processRecord_plaintext hpr (.inl hc))

private theorem processRecords_plaintext {records : List Record.RawRecord} :
    ∀ {state : State} {plaintext wireBytes : ByteArray} {out : Output},
      processRecords state records plaintext wireBytes = .ok out →
        (plaintext.isEmpty = false → state.phase = .connected) →
        out.plaintext.isEmpty = false → out.state.phase = .connected := by
  induction records with
  | nil =>
      intro state plaintext wireBytes out h hacc hne
      unfold processRecords at h
      cases h
      exact hacc hne
  | cons record rest ih =>
      intro state plaintext wireBytes out h hacc hne
      unfold processRecords at h
      split at h
      · cases h
        exact hacc hne
      · split at h
        · cases h
        · rename_i stateN cleartext outbound hpr
          refine ih h (fun hcat => ?_) hne
          rcases append_isEmpty_false hcat with hpl | hcl
          · exact processRecord_plaintext hpr (.inl (hacc hpl))
          · exact processRecord_plaintext hpr (.inr hcl)

/-- **Application-data plaintext reaches the caller only from an established
connection** — the inbound counterpart of `sealApplication_connected`. If a feed
hands back any plaintext at all, the state it hands back with it is
`connected`. -/
theorem feedWithFailure_plaintext_connected {initial : State} {chunk : ByteArray}
    {out : Output} (h : feedWithFailure initial chunk = .ok out)
    (hne : out.plaintext.isEmpty = false) : out.state.phase = .connected := by
  unfold feedWithFailure at h
  split at h
  · cases h
    have hemp : ByteArray.empty.isEmpty = true := by decide
    rw [hemp] at hne
    cases hne
  · split at h
    · cases h
    · exact processRecords_plaintext h (fun hemp => absurd hemp (by decide)) hne

/-- `feed` never leaves an established connection. -/
theorem feedWithFailure_connected {initial : State} {chunk : ByteArray}
    {out : Output} (h : feedWithFailure initial chunk = .ok out)
    (hc : initial.phase = .connected) : out.state.phase = .connected := by
  unfold feedWithFailure at h
  split at h
  · cases h
    exact hc
  · split at h
    · cases h
    · exact processRecords_connected h hc

theorem feed_plaintext_connected {state : State} {chunk : ByteArray} {out : Output}
    (h : feed state chunk = .ok out) (hne : out.plaintext.isEmpty = false) :
    out.state.phase = .connected := by
  unfold feed at h
  cases hf : feedWithFailure state chunk with
  | error failure => rw [hf] at h; cases h
  | ok output =>
      rw [hf] at h
      cases h
      exact feedWithFailure_plaintext_connected hf hne

theorem feed_connected {state : State} {chunk : ByteArray} {out : Output}
    (h : feed state chunk = .ok out) (hc : state.phase = .connected) :
    out.state.phase = .connected := by
  unfold feed at h
  cases hf : feedWithFailure state chunk with
  | error failure => rw [hf] at h; cases h
  | ok output =>
      rw [hf] at h
      cases h
      exact feedWithFailure_connected hf hc

private theorem sealApplication_phase {state : State} {plaintext : ByteArray}
    {out : Output} (h : sealApplication state plaintext = .ok out) :
    out.state.phase = state.phase := by
  unfold sealApplication at h
  simp only [pure_bind] at h
  split at h
  · split at h
    · cases h
    · split at h
      · cases h; rfl
      · obtain ⟨keys, hk, h⟩ := except_bind_ok_inv h
        obtain ⟨sealed, hs, h⟩ := except_bind_ok_inv h
        obtain ⟨nextKeys, records⟩ := sealed
        cases h
        rfl
  · cases h

private theorem closeNotify_phase {state : State} {out : Output}
    (h : closeNotify state = .ok out) : out.state.phase = state.phase := by
  unfold closeNotify at h
  simp only [pure_bind] at h
  split at h
  case isFalse => cases h
  obtain ⟨pair, hp, h⟩ := except_bind_ok_inv h
  obtain ⟨next, wire⟩ := pair
  cases h
  exact emitCloseNotify_phase hp

private theorem sealFatalAlert_phase {state : State} {description : UInt8}
    {out : Output} (h : sealFatalAlert state description = .ok out) :
    out.state.phase = state.phase := by
  unfold sealFatalAlert at h
  simp only [pure_bind] at h
  split at h
  · cases h
  · split at h
    · rename_i writeKeys hkeys
      obtain ⟨sealed, hs, h⟩ := except_bind_ok_inv h
      obtain ⟨nextKeys, wire⟩ := sealed
      cases h
      rfl
    · rename_i hkeys
      obtain ⟨_, h⟩ := unless_ok h
      obtain ⟨wire, _, h⟩ := except_bind_ok_inv h
      cases h
      rfl

private theorem sealApplication_plaintext {state : State} {plaintext : ByteArray}
    {out : Output} (h : sealApplication state plaintext = .ok out) :
    out.plaintext = ByteArray.empty := by
  unfold sealApplication at h
  simp only [pure_bind] at h
  split at h
  · split at h
    · cases h
    · split at h
      · cases h; rfl
      · obtain ⟨keys, hk, h⟩ := except_bind_ok_inv h
        obtain ⟨sealed, hs, h⟩ := except_bind_ok_inv h
        obtain ⟨nextKeys, records⟩ := sealed
        cases h
        rfl
  · cases h

private theorem closeNotify_plaintext {state : State} {out : Output}
    (h : closeNotify state = .ok out) : out.plaintext = ByteArray.empty := by
  unfold closeNotify at h
  simp only [pure_bind] at h
  split at h
  case isFalse => cases h
  obtain ⟨pair, hp, h⟩ := except_bind_ok_inv h
  obtain ⟨next, wire⟩ := pair
  cases h
  rfl

private theorem sealFatalAlert_plaintext {state : State} {description : UInt8}
    {out : Output} (h : sealFatalAlert state description = .ok out) :
    out.plaintext = ByteArray.empty := by
  unfold sealFatalAlert at h
  simp only [pure_bind] at h
  split at h
  · cases h
  · split at h
    · rename_i writeKeys hkeys
      obtain ⟨sealed, hs, h⟩ := except_bind_ok_inv h
      obtain ⟨nextKeys, wire⟩ := sealed
      cases h
      rfl
    · rename_i hkeys
      obtain ⟨_, h⟩ := unless_ok h
      obtain ⟨wire, _, h⟩ := except_bind_ok_inv h
      cases h
      rfl

/-- Only `feed` produces plaintext; the send/close/alert operations return
none, so the law lifts to a single step unchanged. -/
theorem step_plaintext_connected {state : State} {op : Op} {out : Output}
    (h : step state op = .ok out) (hne : out.plaintext.isEmpty = false) :
    out.state.phase = .connected := by
  unfold step at h
  split at h
  · exact feed_plaintext_connected h hne
  · rw [sealApplication_plaintext h] at hne; cases hne
  · rw [closeNotify_plaintext h] at hne; cases hne
  · rw [sealFatalAlert_plaintext h] at hne; cases hne

theorem step_connected {state : State} {op : Op} {out : Output}
    (h : step state op = .ok out) (hc : state.phase = .connected) :
    out.state.phase = .connected := by
  unfold step at h
  split at h
  · exact feed_connected h hc
  · rw [sealApplication_phase h]; exact hc
  · rw [closeNotify_phase h]; exact hc
  · rw [sealFatalAlert_phase h]; exact hc

theorem run_connected {ops : List Op} : ∀ {state : State} {out : Output},
    run state ops = .ok out → state.phase = .connected →
      out.state.phase = .connected := by
  induction ops with
  | nil =>
      intro state out h hc
      unfold run at h; cases h; exact hc
  | cons op rest ih =>
      intro state out h hc
      unfold run at h
      split at h
      · cases h
      · rename_i out1 hstep
        split at h
        · cases h
        · rename_i final hrun
          have h2 := ih hrun (step_connected hstep hc)
          cases h
          exact h2

/-- **Over a whole run, too**: any plaintext the caller receives comes back
alongside an established connection. -/
theorem run_plaintext_connected {ops : List Op} : ∀ {state : State} {out : Output},
    run state ops = .ok out → out.plaintext.isEmpty = false →
      out.state.phase = .connected := by
  induction ops with
  | nil =>
      intro state out h hne
      unfold run at h; cases h; cases hne
  | cons op rest ih =>
      intro state out h hne
      unfold run at h
      split at h
      · cases h
      · rename_i out1 hstep
        split at h
        · cases h
        · rename_i final hrun
          cases h
          rcases append_isEmpty_false hne with h1 | h2
          · have hc := step_plaintext_connected hstep h1
            have h3 := run_connected hrun hc
            exact h3
          · have h3 := ih hrun h2
            exact h3

/-- **HelloRetryRequest applies the RFC 8446 §4.4.1 synthetic transcript**: the
first ClientHello is replaced by `message_hash(CH1)` before the
HelloRetryRequest is appended. -/
theorem sendHelloRetryRequest_messageHash {state next : State}
    {message : Handshake.Message} {hello : Handshake.ClientHello}
    {group : Handshake.NamedGroup} {wire : ByteArray}
    (h : sendHelloRetryRequest state message hello group = .ok (next, wire)) :
    ∃ retry messageHash,
      Handshake.encodeHelloRetryRequest hello.legacySessionId group = .ok retry ∧
        Handshake.frame Handshake.messageHashType
            (HaclStar.sha256 message.encoded) = .ok messageHash ∧
        next.transcript = messageHash.encoded ++ retry.encoded ∧
        next.retryHello? = some hello := by
  unfold sendHelloRetryRequest at h
  simp only [pure_bind] at h
  obtain ⟨retry, hretry, h⟩ := except_bind_ok_inv h
  obtain ⟨messageHash, hmh, h⟩ := except_bind_ok_inv h
  obtain ⟨retryWire, _, h⟩ := except_bind_ok_inv h
  refine ⟨retry, messageHash, liftHandshake_ok hretry, liftHandshake_ok hmh, ?_, ?_⟩ <;>
    (split at h
     · obtain ⟨ccsWire, _, h⟩ := except_bind_ok_inv h
       cases h
       rfl
     · cases h
       rfl)

/-- **A KeyUpdate installs the structural §7.2 successor epoch**: the peer's
new read traffic secret is derived from the old one by the RFC update step, and
its record sequence number restarts at zero. This does not claim byte
inequality from an opaque, finite-output HKDF. -/
theorem acceptKeyUpdate_epoch {state next : State}
    {message : Handshake.Message} {wire : ByteArray}
    (h : acceptKeyUpdate state message = .ok (next, wire)) :
    ∃ keys keys', state.readKeys? = some keys ∧ next.readKeys? = some keys' ∧
      Record.updateTrafficSecret keys.secret = .ok keys'.secret ∧
      keys'.seq = 0 := by
  unfold acceptKeyUpdate at h
  obtain ⟨update, _, h⟩ := except_bind_ok_inv h
  obtain ⟨readKeys, hread, h⟩ := except_bind_ok_inv h
  obtain ⟨updated, hupd, h⟩ := except_bind_ok_inv h
  have hread' : state.readKeys? = some readKeys := by
    unfold requireReadKeys at hread
    cases hs : state.readKeys? with
    | none => rw [hs] at hread; cases hread
    | some k => rw [hs] at hread; cases hread; rfl
  have hupd' := liftRecord_ok hupd
  refine ⟨readKeys, updated, hread', ?_, Record.TrafficKeys.secret_update hupd',
    Record.TrafficKeys.seq_update hupd'⟩
  split at h
  · cases h; rfl
  · simp only [] at h
    split at h
    · cases h; rfl
    · rw [sendKeyUpdateResponse_readKeys h]

/-- A one-byte KeyUpdate carrying a request value other than 0 or 1 is an
`illegal_parameter`, rather than the `decode_error` used for framing and body
length failures. -/
theorem acceptKeyUpdate_invalid_request {state : State}
    {message : Handshake.Message}
    (htype : message.msgType = Handshake.keyUpdateType)
    (hsize : message.body.size = 1)
    (hrequest :
      Handshake.KeyUpdateRequest.ofUInt8? (message.body.get! 0) = none) :
    acceptKeyUpdate state message = .error (.illegalParameter
      s!"invalid KeyUpdate request value {message.body.get! 0}") := by
  unfold acceptKeyUpdate parseKeyUpdateForServer invalidKeyUpdateRequest
  simp [htype, hsize, hrequest]
  rfl

/-- The RFC 9846 sending-generation limit is inductive: a state at or below
`2^48 - 1` remains at or below it after accepting a KeyUpdate. -/
theorem acceptKeyUpdate_sendingKeyUpdates_le {state next : State}
    {message : Handshake.Message} {wire : ByteArray}
    (hbound : state.sendingKeyUpdates ≤ maxSendingKeyUpdates)
    (h : acceptKeyUpdate state message = .ok (next, wire)) :
    next.sendingKeyUpdates ≤ maxSendingKeyUpdates := by
  unfold acceptKeyUpdate at h
  obtain ⟨_, _, h⟩ := except_bind_ok_inv h
  obtain ⟨_, _, h⟩ := except_bind_ok_inv h
  obtain ⟨_, _, h⟩ := except_bind_ok_inv h
  split at h
  · cases h
    exact hbound
  · simp only [] at h
    split at h
    · cases h
      exact hbound
    · unfold sendKeyUpdateResponse at h
      simp only [] at h
      split at h
      · obtain ⟨_, _, h⟩ := except_bind_ok_inv h
        obtain ⟨_, _, h⟩ := except_bind_ok_inv h
        obtain ⟨sealed, _, h⟩ := except_bind_ok_inv h
        obtain ⟨_, _⟩ := sealed
        obtain ⟨_, _, h⟩ := except_bind_ok_inv h
        cases h
        change state.sendingKeyUpdates + 1 ≤ maxSendingKeyUpdates
        omega
      · cases h
        exact hbound

/-- At RFC 9846's `2^48 - 1` sending limit, a requested reciprocal KeyUpdate
is silently suppressed. The peer's read epoch has already advanced, but the
server emits no bytes and does not advance its sending counter. -/
theorem acceptKeyUpdate_at_sending_limit {state next : State}
    {message : Handshake.Message} {wire : ByteArray}
    (hlimit : maxSendingKeyUpdates ≤ state.sendingKeyUpdates)
    (h : acceptKeyUpdate state message = .ok (next, wire)) :
    next.writeKeys? = state.writeKeys? ∧
      next.sendingKeyUpdates = state.sendingKeyUpdates ∧
      wire = ByteArray.empty := by
  unfold acceptKeyUpdate at h
  obtain ⟨_, _, h⟩ := except_bind_ok_inv h
  obtain ⟨_, _, h⟩ := except_bind_ok_inv h
  obtain ⟨updatedReadKeys, _, h⟩ := except_bind_ok_inv h
  split at h
  · cases h
    exact ⟨rfl, rfl, rfl⟩
  · simp only [] at h
    split at h
    · cases h
      exact ⟨rfl, rfl, rfl⟩
    · change sendKeyUpdateResponse
        ({ state with readKeys? := some updatedReadKeys }) = .ok (next, wire) at h
      rw [sendKeyUpdateResponse_at_limit
        (state := { state with readKeys? := some updatedReadKeys }) hlimit] at h
      cases h
      exact ⟨rfl, rfl, rfl⟩

/-- Every reciprocal KeyUpdate that actually emits a record increments the
sending counter exactly once, and the resulting count remains within the RFC
9846 limit. -/
theorem acceptKeyUpdate_response_increments {state next : State}
    {message : Handshake.Message} {wire : ByteArray}
    (h : acceptKeyUpdate state message = .ok (next, wire))
    (hemitted : wire ≠ ByteArray.empty) :
    next.sendingKeyUpdates = state.sendingKeyUpdates + 1 ∧
      next.sendingKeyUpdates ≤ maxSendingKeyUpdates := by
  unfold acceptKeyUpdate at h
  obtain ⟨_, _, h⟩ := except_bind_ok_inv h
  obtain ⟨_, _, h⟩ := except_bind_ok_inv h
  obtain ⟨updatedReadKeys, _, h⟩ := except_bind_ok_inv h
  split at h
  · cases h
    exact absurd rfl hemitted
  · simp only [] at h
    split at h
    · cases h
      exact absurd rfl hemitted
    · change sendKeyUpdateResponse
        ({ state with readKeys? := some updatedReadKeys }) = .ok (next, wire) at h
      unfold sendKeyUpdateResponse at h
      split at h
      · rename_i hbelow
        obtain ⟨_, _, h⟩ := except_bind_ok_inv h
        obtain ⟨_, _, h⟩ := except_bind_ok_inv h
        obtain ⟨sealed, _, h⟩ := except_bind_ok_inv h
        obtain ⟨_, _⟩ := sealed
        obtain ⟨_, _, h⟩ := except_bind_ok_inv h
        cases h
        constructor
        · rfl
        · change state.sendingKeyUpdates + 1 ≤ maxSendingKeyUpdates
          exact Nat.succ_le_of_lt hbelow
      · cases h
        exact absurd rfl hemitted

/-- A KeyUpdate crossing the local `close_notify` still advances the peer/read
epoch, but it cannot reopen the local write direction or emit a reciprocal
update. -/
theorem acceptKeyUpdate_localClosed_suppresses_response {state next : State}
    {message : Handshake.Message} {wire : ByteArray}
    (hclosed : state.localClosed = true)
    (h : acceptKeyUpdate state message = .ok (next, wire)) :
    next.localClosed = true ∧
      next.writeKeys? = state.writeKeys? ∧
      next.sendingKeyUpdates = state.sendingKeyUpdates ∧
      wire = ByteArray.empty := by
  unfold acceptKeyUpdate at h
  obtain ⟨_, _, h⟩ := except_bind_ok_inv h
  obtain ⟨_, _, h⟩ := except_bind_ok_inv h
  obtain ⟨_, _, h⟩ := except_bind_ok_inv h
  split at h
  · cases h
    exact ⟨hclosed, rfl, rfl, rfl⟩
  · simp [hclosed] at h
    cases h
    exact ⟨rfl, rfl, rfl, rfl⟩

/-- **AEAD key--nonce non-reuse across a server connection.** For any successful
run there is an `AeadWriteRun`: the explicit list of records the engine
protected, each tagged with the concrete AEAD key that protected it. If the
concrete epoch keys in that finite trace are distinct, no `(key, nonce)` pair in
it repeats.

Sequence numbers restart at zero on every KeyUpdate, which is why the trace is
scoped by AEAD key; `aeadKeys` lists the epochs the run used, oldest first, and
the only hypothesis is that those concrete keys are distinct.

What this does *not* say: nothing constrains a caller who keeps an old `State`
and drives a second connection from it. Single-threading the state is the
caller's obligation, and finite-run key distinctness remains the explicit
`aeadKeys.Nodup` premise. -/
theorem run_nonce_nodup {ops : List Op} {state : State} {out : Output}
    (h : run state ops = .ok out) :
    ∃ (aeadKeys : List ByteArray) (keyNonces : List (ByteArray × ByteArray)),
      Record.AeadWriteRun state.writeKeys? out.state.writeKeys? aeadKeys keyNonces ∧
        (aeadKeys.Nodup → keyNonces.Nodup) := by
  obtain ⟨secrets, taggedNonces, hrun⟩ := Record.Extends.run (run_write h)
  obtain ⟨aeadKeys, keyNonces, haead, _⟩ := hrun.toAeadWriteRun
  exact ⟨aeadKeys, keyNonces, haead, fun hfresh => haead.nodup hfresh⟩

/-- `run_nonce_nodup` for a single `feed` — which for a server covers the entire
handshake flight it emits in response to a ClientHello. -/
theorem feed_nonce_nodup {state : State} {chunk : ByteArray} {out : Output}
    (h : feed state chunk = .ok out) :
    ∃ (aeadKeys : List ByteArray) (keyNonces : List (ByteArray × ByteArray)),
      Record.AeadWriteRun state.writeKeys? out.state.writeKeys? aeadKeys keyNonces ∧
        (aeadKeys.Nodup → keyNonces.Nodup) := by
  obtain ⟨secrets, taggedNonces, hrun⟩ := Record.Extends.run (feed_write h)
  obtain ⟨aeadKeys, keyNonces, haead, _⟩ := hrun.toAeadWriteRun
  exact ⟨aeadKeys, keyNonces, haead, fun hfresh => haead.nodup hfresh⟩

/-! ## The engine installs the RFC 8446 §7.1 epochs

The laws below tie the server's actual key installations to the specification in
`TLS13.KeySchedule.Spec`: at each transition, the epoch secrets the engine
stores are the specification's, derived from the right parent secret, under the
right label, over the right transcript.

As everywhere else, this is *structural* refinement. It is stated for an
arbitrary `Spec.Hkdf` the HACL\* bindings implement, so it says nothing about
what HKDF computes — only that the engine applies it in the RFC's shape. The
empirical half is `Test/HaclKat.lean`'s RFC 8448 vectors; if the two ever
disagree, the vectors are right. -/

open TLS13.KeySchedule

/-- **The Finished MAC is keyed by RFC 8446 §4.4.4's `finished_key`**:
`HKDF-Expand-Label(BaseKey, "finished", "", Hash.length)` — an *empty* context,
not a transcript hash — and the transcript hash is the HMAC message. -/
theorem finishedVerifyData_spec {H : Spec.Hkdf} (hi : Implements H)
    (trafficSecret transcriptHash : ByteArray) :
    finishedVerifyData trafficSecret transcriptHash =
      HaclStar.hmacSha256 (Spec.finishedKey H trafficSecret) transcriptHash := by
  have he : expandLabel trafficSecret (Spec.Label.finished).text ByteArray.empty
      hashLen = Spec.finishedKey H trafficSecret := by
    rw [show (hashLen : Nat) = H.hashLen from hi.hashLen_eq.symm]
    exact expandLabel_spec hi trafficSecret .finished ByteArray.empty H.hashLen
  exact congrArg (fun k => HaclStar.hmacSha256 k transcriptHash) he

/-- **Answering a ClientHello installs the RFC 8446 §7.1 epochs.** There is an
(EC)DHE shared secret of hash length and a server flight — ServerHello,
EncryptedExtensions, Certificate, CertificateVerify, Finished — such that, for
any key-schedule inputs with no PSK, that shared secret, and the transcript
hashes of exactly those two message sequences, the epochs the server installs
are the specification's:

* the read epoch is `client_handshake_traffic_secret`, over
  ClientHello…ServerHello;
* the write epoch is already `server_application_traffic_secret_0` — the server
  installs it in this same step, having just sealed its flight under the
  handshake epoch — over ClientHello…server Finished;
* the retained client application epoch is
  `client_application_traffic_secret_0`, over the same transcript;
* and the client Finished the server will demand is HMAC-keyed by §4.4.4's
  `finished_key` of the **client handshake** traffic secret, over the
  ClientHello…server Finished transcript.

Note which transcript goes where: the `"derived"` steps feeding the Handshake
and Master Secrets bind the **empty** message sequence, the handshake-traffic
secrets bind ClientHello…ServerHello, and the application-traffic secrets bind
the longer ClientHello…server Finished sequence. -/
theorem completeClientHello_keySchedule {H : Spec.Hkdf} (hi : Implements H)
    {state next : State} {hello : Handshake.ClientHello}
    {group : Handshake.NamedGroup} {transcriptPrefix wire : ByteArray}
    (h : completeClientHello state hello group transcriptPrefix = .ok (next, wire)) :
    ∃ (ecdhe : ByteArray) (serverHello encryptedExtensions certificate certVerify
        serverFinished : Handshake.Message),
      ecdhe.size = hashLen ∧
      ∀ inp : Spec.Inputs,
        inp.psk = zeros →
        inp.ecdhe = ecdhe →
        inp.hash .empty = HaclStar.sha256 ByteArray.empty →
        inp.hash .serverHello =
          HaclStar.sha256 (transcriptPrefix ++ serverHello.encoded) →
        inp.hash .serverFinished =
          HaclStar.sha256 (transcriptPrefix ++ serverHello.encoded ++
            encryptedExtensions.encoded ++ certificate.encoded ++ certVerify.encoded ++
            serverFinished.encoded) →
        (∃ rk, next.readKeys? = some rk ∧
          Record.TrafficKeys.DerivedFrom H rk (Spec.derived H inp .cHsTraffic)) ∧
        (∃ wk, next.writeKeys? = some wk ∧
          Record.TrafficKeys.DerivedFrom H wk (Spec.derived H inp .sApTraffic)) ∧
        (∃ ck, next.clientApplicationKeys? = some ck ∧
          Record.TrafficKeys.DerivedFrom H ck (Spec.derived H inp .cApTraffic)) ∧
        next.expectedClientFinished? =
          some (HaclStar.hmacSha256
            (Spec.finishedKey H (Spec.derived H inp .cHsTraffic))
            (inp.hash .serverFinished)) := by
  unfold completeClientHello at h
  simp only [pure_bind] at h
  obtain ⟨exchanged, _, h⟩ := except_bind_ok_inv h
  obtain ⟨serverPublic, sharedSecret⟩ := exchanged
  obtain ⟨hsize, h⟩ := unless_ok h
  obtain ⟨serverHello, _, h⟩ := except_bind_ok_inv h
  obtain ⟨serverWriteKeys, _, h⟩ := except_bind_ok_inv h
  obtain ⟨clientReadKeys, hcrk, h⟩ := except_bind_ok_inv h
  obtain ⟨encryptedExtensions, _, h⟩ := except_bind_ok_inv h
  obtain ⟨certificate, _, h⟩ := except_bind_ok_inv h
  split at h
  case h_2 => cases h
  obtain ⟨_, h⟩ := unless_ok h
  obtain ⟨certVerify, _, h⟩ := except_bind_ok_inv h
  obtain ⟨serverFinished, _, h⟩ := except_bind_ok_inv h
  obtain ⟨serverApplicationKeys, hsak, h⟩ := except_bind_ok_inv h
  obtain ⟨clientApplicationKeys, hcak, h⟩ := except_bind_ok_inv h
  obtain ⟨flightSealed, _, h⟩ := except_bind_ok_inv h
  obtain ⟨flightKeys, sealedFlight⟩ := flightSealed
  obtain ⟨serverHelloWire, _, h⟩ := except_bind_ok_inv h
  have hderiv : ∀ inp : Spec.Inputs,
      inp.psk = zeros → inp.ecdhe = sharedSecret →
      inp.hash .empty = HaclStar.sha256 ByteArray.empty →
      inp.hash .serverHello = HaclStar.sha256 (transcriptPrefix ++ serverHello.encoded) →
      inp.hash .serverFinished =
        HaclStar.sha256 (transcriptPrefix ++ serverHello.encoded ++
          encryptedExtensions.encoded ++ certificate.encoded ++ certVerify.encoded ++
          serverFinished.encoded) →
      Record.TrafficKeys.DerivedFrom H clientReadKeys (Spec.derived H inp .cHsTraffic) ∧
      Record.TrafficKeys.DerivedFrom H serverApplicationKeys
        (Spec.derived H inp .sApTraffic) ∧
      Record.TrafficKeys.DerivedFrom H clientApplicationKeys
        (Spec.derived H inp .cApTraffic) ∧
      finishedVerifyData
          (deriveSecret (handshakeSecret earlySecret sharedSecret
            (HaclStar.sha256 ByteArray.empty)) "c hs traffic"
            (HaclStar.sha256 (transcriptPrefix ++ serverHello.encoded)))
          (HaclStar.sha256 (transcriptPrefix ++ serverHello.encoded ++
            encryptedExtensions.encoded ++ certificate.encoded ++ certVerify.encoded ++
            serverFinished.encoded)) =
        HaclStar.hmacSha256 (Spec.finishedKey H (Spec.derived H inp .cHsTraffic))
          (inp.hash .serverFinished) := by
    intro inp hpsk hecdhe hempty hsh hfin
    have hhs := handshakeSecret_node_spec hi inp hpsk hecdhe hempty
    have hchs := deriveSecret_node_spec hi inp .cHsTraffic hhs hsh
    have hms := masterSecret_node_spec hi inp hhs hempty
    have hsap := deriveSecret_node_spec hi inp .sApTraffic hms hfin
    have hcap := deriveSecret_node_spec hi inp .cApTraffic hms hfin
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [← hchs]; exact Record.deriveTrafficKeys_spec hi (liftRecord_ok hcrk)
    · rw [← hsap]; exact Record.deriveTrafficKeys_spec hi (liftRecord_ok hsak)
    · rw [← hcap]; exact Record.deriveTrafficKeys_spec hi (liftRecord_ok hcak)
    · refine Eq.trans (finishedVerifyData_spec hi _ _) ?_
      rw [← hfin]
      exact congrArg
        (fun s => HaclStar.hmacSha256 (Spec.finishedKey H s) (inp.hash .serverFinished))
        hchs
  refine ⟨sharedSecret, serverHello, encryptedExtensions, certificate, certVerify,
    serverFinished, eq_of_beq hsize, fun inp h1 h2 h3 h4 h5 => ?_⟩
  obtain ⟨a, b, c, d⟩ := hderiv inp h1 h2 h3 h4 h5
  split at h
  · cases h
    exact ⟨⟨_, rfl, a⟩, ⟨_, rfl, b⟩, ⟨_, rfl, c⟩, congrArg some d⟩
  · obtain ⟨ccsWire, _, h⟩ := except_bind_ok_inv h
    cases h
    exact ⟨⟨_, rfl, a⟩, ⟨_, rfl, b⟩, ⟨_, rfl, c⟩, congrArg some d⟩

/-- **A KeyUpdate installs the RFC 8446 §7.2 successor epoch.** The new read
epoch's secret is `HKDF-Expand-Label(old, "traffic upd", "", Hash.length)` —
empty context, not a transcript hash — and its key, IV and sequence number are
that secret's §7.3 record-protection state. -/
theorem acceptKeyUpdate_keySchedule {H : Spec.Hkdf} (hi : Implements H)
    {state next : State} {message : Handshake.Message} {wire : ByteArray}
    (h : acceptKeyUpdate state message = .ok (next, wire)) :
    ∃ keys keys', state.readKeys? = some keys ∧ next.readKeys? = some keys' ∧
      Record.TrafficKeys.DerivedFrom H keys'
        (Spec.nextTrafficSecret H keys.secret) := by
  unfold acceptKeyUpdate at h
  obtain ⟨update, _, h⟩ := except_bind_ok_inv h
  obtain ⟨readKeys, hread, h⟩ := except_bind_ok_inv h
  obtain ⟨updated, hupd, h⟩ := except_bind_ok_inv h
  have hread' : state.readKeys? = some readKeys := by
    unfold requireReadKeys at hread
    cases hs : state.readKeys? with
    | none => rw [hs] at hread; cases hread
    | some k => rw [hs] at hread; cases hread; rfl
  refine ⟨readKeys, updated, hread', ?_,
    Record.TrafficKeys.update_spec hi (liftRecord_ok hupd)⟩
  split at h
  · cases h; rfl
  · simp only [] at h
    split at h
    · cases h; rfl
    · rw [sendKeyUpdateResponse_readKeys h]

/-! ## A finite AEAD nonce trace refined by the key schedule

`run_nonce_nodup` concludes `aeadKeys.Nodup → keyNonces.Nodup`. The laws below add
the structural fact that the server's epochs are not arbitrary:
`completeClientHello` derives `server_handshake_traffic_secret` and then
`server_application_traffic_secret_0` from the RFC 8446 §7.1 diagram, and every
KeyUpdate advances the latter under `"traffic upd"`. The epoch descriptors of a
run therefore form a strictly increasing schedule trace (`Spec.Epoch.Lt`).

`run_nonce_trace_spec` returns that schedule witness and traffic-secret
`WriteRun` alongside an `AeadWriteRun` over the actual key--nonce pairs; the two
traces have the same nonce sequence. It retains the finite-run implication
`aeadKeys.Nodup → keyNonces.Nodup`, because structurally distinct nodes may
derive the same fixed-size AEAD key. Byte-level collision freedom is a
cryptographic condition on the concrete run, not a deterministic global KDF
property. -/

/-- **Which node of the key schedule a server's write state is in.** `none`
before the first epoch is installed; otherwise the §7.1 derivation the write
traffic secret came from, plus the number of §7.2 KeyUpdates since.

Unlike the client's, the label does not depend on the phase. The server installs
its write epoch exactly once, in `completeClientHello`, and what it *stores*
there is already `server_application_traffic_secret_0`: the handshake flight is
sealed inside that same transition, under a `"s hs traffic"` epoch that no
reachable state ever carries. -/
def State.WriteEpoch (H : Spec.Hkdf) (state : State) (o : Option Spec.Epoch) : Prop :=
  Record.EpochOf H o state.writeKeys? ∧
    ∀ e, o = some e → e.label = Spec.Label.sApTraffic

theorem State.WriteEpoch.valid {H : Spec.Hkdf} {state : State}
    {o : Option Spec.Epoch} (h : state.WriteEpoch H o) :
    ∀ e, o = some e → e.Valid := by
  intro e he
  show e.label ≠ Spec.Label.trafficUpd
  rw [h.2 e he]
  intro hc
  cases hc

/-- The write side of one engine step, refined by the key schedule: it maps the
epoch the connection was in to the epoch it ends in, and the epochs it abandoned
on the way join the run's epoch list in strictly increasing order. -/
def SpecEffect (H : Spec.Hkdf) (before after : State) : Prop :=
  ∀ o, before.WriteEpoch H o →
    ∃ o', after.WriteEpoch H o' ∧
      Record.SpecExtends H o o' before.writeKeys? after.writeKeys?

theorem SpecEffect.trans {H : Spec.Hkdf} {a b c : State}
    (h1 : SpecEffect H a b) (h2 : SpecEffect H b c) : SpecEffect H a c := by
  intro o ho
  obtain ⟨o', ho', hx⟩ := h1 o ho
  obtain ⟨o'', ho'', hx'⟩ := h2 o' ho'
  exact ⟨o'', ho'', hx.trans hx'⟩

/-- A step that protects records but installs no epoch. -/
theorem SpecEffect.within {H : Spec.Hkdf} {before after : State}
    (hx : Record.WithinEpoch H before.writeKeys? after.writeKeys?) :
    SpecEffect H before after := by
  intro o ho
  obtain ⟨ha, hs⟩ := hx.apply ho.1
  exact ⟨o, ⟨ha, ho.2⟩, hs⟩

/-- Prefix a step with a state change that leaves the write keys alone. -/
theorem SpecEffect.of_eq {H : Spec.Hkdf} {a b c : State} (h : SpecEffect H b c)
    (hw : b.writeKeys? = a.writeKeys?) : SpecEffect H a c := by
  intro o ho
  have ho' : b.WriteEpoch H o := ⟨by rw [hw]; exact ho.1, ho.2⟩
  obtain ⟨o', ho'', hx⟩ := h o ho'
  rw [hw] at hx
  exact ⟨o', ho'', hx⟩

private theorem sealHandshakeFlight_epochs {H : Spec.Hkdf}
    {keys keys' : Record.TrafficKeys} {flight : ByteArray} {offset : Nat}
    {wireBytes wireOut : ByteArray}
    (h : sealHandshakeFlight keys flight offset wireBytes = .ok (keys', wireOut)) :
    Record.WithinEpoch H (some keys) (some keys') := by
  unfold sealHandshakeFlight at h
  split at h
  · cases h; exact Record.WithinEpoch.refl _
  · simp only [] at h
    split at h
    · cases h
    · rename_i nextKeys record hseal
      exact Record.WithinEpoch.trans
        (Record.WithinEpoch.of_seal (liftRecord_ok hseal)) (sealHandshakeFlight_epochs h)
  termination_by flight.size - offset
  decreasing_by
    have : 0 < Record.maxPlaintextLength := by decide
    omega

private theorem sealChunks_epochs {H : Spec.Hkdf} {keys keys' : Record.TrafficKeys}
    {plaintext : ByteArray} {offset : Nat} {records records' : Array ByteArray}
    (h : sealChunks keys plaintext offset records = .ok (keys', records')) :
    Record.WithinEpoch H (some keys) (some keys') := by
  unfold sealChunks at h
  split at h
  · cases h; exact Record.WithinEpoch.refl _
  · simp only [] at h
    split at h
    · cases h
    · rename_i nextKeys wire hpair
      exact Record.WithinEpoch.trans
        (Record.WithinEpoch.of_seal (liftRecord_ok hpair)) (sealChunks_epochs h)
  termination_by plaintext.size - offset
  decreasing_by
    have : 0 < Record.maxPlaintextLength := by decide
    omega

theorem sealApplication_epochs {H : Spec.Hkdf} {state : State} {plaintext : ByteArray}
    {out : Output} (h : sealApplication state plaintext = .ok out) :
    SpecEffect H state out.state := by
  unfold sealApplication at h
  simp only [pure_bind] at h
  split at h
  · split at h
    · cases h
    · split at h
      · cases h; exact SpecEffect.within (Record.WithinEpoch.refl _)
      · obtain ⟨keys, hk, h⟩ := except_bind_ok_inv h
        obtain ⟨sealed, hs, h⟩ := except_bind_ok_inv h
        obtain ⟨nextKeys, records⟩ := sealed
        cases h
        refine SpecEffect.within ?_
        show Record.WithinEpoch H state.writeKeys? (some nextKeys)
        rw [requireWriteKeys_ok hk]
        exact sealChunks_epochs hs
  · cases h

private theorem emitCloseNotify_epochs {H : Spec.Hkdf} {state next : State}
    {wire : ByteArray} (h : emitCloseNotify state = .ok (next, wire)) :
    SpecEffect H state next := by
  unfold emitCloseNotify at h
  split at h
  · cases h; exact SpecEffect.within (Record.WithinEpoch.refl _)
  · obtain ⟨keys, hk, h⟩ := except_bind_ok_inv h
    obtain ⟨sealed, hs, h⟩ := except_bind_ok_inv h
    obtain ⟨sealedKeys, wireBytes⟩ := sealed
    cases h
    refine SpecEffect.within ?_
    show Record.WithinEpoch H state.writeKeys? (some sealedKeys)
    rw [requireWriteKeys_ok hk]
    exact Record.WithinEpoch.of_seal (liftRecord_ok hs)

theorem closeNotify_epochs {H : Spec.Hkdf} {state : State} {out : Output}
    (h : closeNotify state = .ok out) : SpecEffect H state out.state := by
  unfold closeNotify at h
  simp only [pure_bind] at h
  split at h
  case isFalse => cases h
  obtain ⟨pair, hp, h⟩ := except_bind_ok_inv h
  obtain ⟨next, wire⟩ := pair
  cases h
  exact emitCloseNotify_epochs hp

theorem sealFatalAlert_epochs {H : Spec.Hkdf} {state : State} {description : UInt8}
    {out : Output} (h : sealFatalAlert state description = .ok out) :
    SpecEffect H state out.state := by
  unfold sealFatalAlert at h
  simp only [pure_bind] at h
  split at h
  · cases h
  · split at h
    · rename_i writeKeys hkeys
      obtain ⟨sealed, hs, h⟩ := except_bind_ok_inv h
      obtain ⟨nextKeys, wire⟩ := sealed
      cases h
      refine SpecEffect.within ?_
      show Record.WithinEpoch H state.writeKeys? (some nextKeys)
      rw [hkeys]
      exact Record.WithinEpoch.of_seal (liftRecord_ok hs)
    · rename_i hkeys
      obtain ⟨_, h⟩ := unless_ok h
      obtain ⟨wire, _, h⟩ := except_bind_ok_inv h
      cases h
      exact SpecEffect.within (Record.WithinEpoch.refl _)

private theorem processAlert_epochs {H : Spec.Hkdf} {state next : State}
    {fragment : ByteArray} {duringHandshake : Bool} {wire : ByteArray}
    (h : processAlert state fragment duringHandshake = .ok (next, wire)) :
    SpecEffect H state next := by
  unfold processAlert at h
  simp only [pure_bind] at h
  split at h
  case isFalse => cases h
  split at h
  · split at h
    · cases h
    · cases h
      exact SpecEffect.within (Record.WithinEpoch.refl _)
  · split at h
    · cases h
      exact SpecEffect.within (Record.WithinEpoch.refl _)
    · cases h

/-- **A KeyUpdate response moves the write side to the §7.2 successor epoch.**
The reciprocal KeyUpdate is sealed under the old epoch, and only then is the
traffic secret rolled forward to `HKDF-Expand-Label(old, "traffic upd", "", 32)`
— a strictly later node of the schedule. -/
private theorem sendKeyUpdateResponse_epochs {H : Spec.Hkdf} (hi : Implements H)
    {state next : State} {wire : ByteArray}
    (h : sendKeyUpdateResponse state = .ok (next, wire)) :
    SpecEffect H state next := by
  unfold sendKeyUpdateResponse at h
  split at h
  · obtain ⟨_, _, h⟩ := except_bind_ok_inv h
    obtain ⟨keys, hk, h⟩ := except_bind_ok_inv h
    obtain ⟨sealed, hs, h⟩ := except_bind_ok_inv h
    obtain ⟨advancedKeys, wireBytes⟩ := sealed
    obtain ⟨updatedKeys, hu, h⟩ := except_bind_ok_inv h
    cases h
    intro o ho
    have hw : state.writeKeys? = some keys := requireWriteKeys_ok hk
    have hE : Record.EpochOf H o (some keys) := by rw [← hw]; exact ho.1
    obtain ⟨e, rfl, hsec⟩ := Record.EpochOf.some_inv hE
    have hadv : advancedKeys.secret = e.secret H := by
      rw [Record.seal_secret_eq (liftRecord_ok hs)]; exact hsec
    have hupd := Record.TrafficKeys.update_spec hi (liftRecord_ok hu)
    refine ⟨some e.next, ⟨Record.EpochOf.intro ?_, fun e' he' => ?_⟩, ?_⟩
    · rw [hupd.secret_eq, hadv, Spec.Epoch.secret_next]
    · cases he'
      exact ho.2 e rfl
    · rw [hw]
      exact (Record.SpecExtends.of_seal (liftRecord_ok hs)).trans
        (Record.SpecExtends.rekey hadv (ho.valid e rfl) (Spec.Epoch.lt_next e))
  · cases h
    exact SpecEffect.within (Record.WithinEpoch.refl _)

private theorem acceptKeyUpdate_epochs {H : Spec.Hkdf} (hi : Implements H)
    {state next : State} {message : Handshake.Message} {wire : ByteArray}
    (h : acceptKeyUpdate state message = .ok (next, wire)) :
    SpecEffect H state next := by
  unfold acceptKeyUpdate at h
  obtain ⟨_, _, h⟩ := except_bind_ok_inv h
  obtain ⟨_, _, h⟩ := except_bind_ok_inv h
  obtain ⟨_, _, h⟩ := except_bind_ok_inv h
  split at h
  · cases h
    exact SpecEffect.within (Record.WithinEpoch.refl _)
  · simp only [] at h
    split at h
    · cases h
      exact SpecEffect.within (Record.WithinEpoch.refl _)
    · have hw := sendKeyUpdateResponse_epochs hi h
      exact SpecEffect.of_eq hw rfl

/-- **The server's flight installs the connection's first two epochs, in the
schedule's order.** The flight is protected under `"s hs traffic"`, and the
epoch the state keeps is `"s ap traffic"` — a strictly later node
(`Spec.Label.stage`). That the server held no epoch beforehand is the
`waitingClientHello` clause of `State.WellFormed`, and it is what rules out an
epoch being revisited here. -/
private theorem completeClientHello_epochs {H : Spec.Hkdf} (hi : Implements H)
    {state next : State} {hello : Handshake.ClientHello}
    {group : Handshake.NamedGroup} {transcriptPrefix wire : ByteArray}
    (h : completeClientHello state hello group transcriptPrefix = .ok (next, wire))
    (hnone : state.writeKeys? = none) : SpecEffect H state next := by
  unfold completeClientHello at h
  simp only [pure_bind] at h
  obtain ⟨exchanged, _, h⟩ := except_bind_ok_inv h
  obtain ⟨serverPublic, sharedSecret⟩ := exchanged
  obtain ⟨_, h⟩ := unless_ok h
  obtain ⟨serverHello, _, h⟩ := except_bind_ok_inv h
  obtain ⟨serverWriteKeys, hswk, h⟩ := except_bind_ok_inv h
  obtain ⟨clientReadKeys, _, h⟩ := except_bind_ok_inv h
  obtain ⟨encryptedExtensions, _, h⟩ := except_bind_ok_inv h
  obtain ⟨certificate, _, h⟩ := except_bind_ok_inv h
  split at h
  case h_2 => cases h
  obtain ⟨_, h⟩ := unless_ok h
  obtain ⟨certVerify, _, h⟩ := except_bind_ok_inv h
  obtain ⟨serverFinished, _, h⟩ := except_bind_ok_inv h
  obtain ⟨serverApplicationKeys, hsak, h⟩ := except_bind_ok_inv h
  obtain ⟨clientApplicationKeys, _, h⟩ := except_bind_ok_inv h
  obtain ⟨flightSealed, hflight, h⟩ := except_bind_ok_inv h
  obtain ⟨flightKeys, sealedFlight⟩ := flightSealed
  obtain ⟨serverHelloWire, _, h⟩ := except_bind_ok_inv h
  have hgoal : ∀ (p₁ c₁ p₂ c₂ : ByteArray) (swk sak fk : Record.TrafficKeys)
      (n : State),
      Record.deriveTrafficKeys
        (TLS13.KeySchedule.deriveSecret p₁ "s hs traffic" c₁) = .ok swk →
      Record.deriveTrafficKeys
        (TLS13.KeySchedule.deriveSecret p₂ "s ap traffic" c₂) = .ok sak →
      Record.WithinEpoch H (some swk) (some fk) →
      n.writeKeys? = some sak → SpecEffect H state n := by
    intro p₁ c₁ p₂ c₂ swk sak fk n hd₁ hd₂ hfl hwk o ho
    have ho' : o = none := Record.EpochOf.none_inv (by rw [← hnone]; exact ho.1)
    subst ho'
    have hswk' : swk.secret = (⟨p₁, .sHsTraffic, c₁, 0⟩ : Spec.Epoch).secret H :=
      (Record.deriveTrafficKeys_spec hi hd₁).secret_eq.trans
        (TLS13.KeySchedule.deriveSecret_spec hi p₁ .sHsTraffic c₁)
    have hstep := hfl.apply (Record.EpochOf.intro hswk')
    have hlt : (⟨p₁, Spec.Label.sHsTraffic, c₁, 0⟩ : Spec.Epoch).Lt
        ⟨p₂, Spec.Label.sApTraffic, c₂, 0⟩ :=
      Or.inl (by exact (by decide : (1 : Nat) < 2))
    refine ⟨some ⟨p₂, .sApTraffic, c₂, 0⟩, ⟨?_, fun e he => by cases he; rfl⟩, ?_⟩
    · rw [hwk]
      exact Record.EpochOf.intro
        ((Record.deriveTrafficKeys_spec hi hd₂).secret_eq.trans
          (TLS13.KeySchedule.deriveSecret_spec hi p₂ .sApTraffic c₂))
    · rw [hnone, hwk]
      exact Record.SpecExtends.install.trans
        (hstep.2.trans (Record.SpecExtends.rekey (Record.EpochOf.secret_eq hstep.1)
          (by intro hc; cases hc) hlt))
  split at h
  · cases h
    exact hgoal _ _ _ _ _ _ _ _ (liftRecord_ok hswk) (liftRecord_ok hsak)
      (sealHandshakeFlight_epochs hflight) rfl
  · obtain ⟨ccsWire, _, h⟩ := except_bind_ok_inv h
    cases h
    exact hgoal _ _ _ _ _ _ _ _ (liftRecord_ok hswk) (liftRecord_ok hsak)
      (sealHandshakeFlight_epochs hflight) rfl

private theorem sendHelloRetryRequest_epochs {H : Spec.Hkdf} {state next : State}
    {message : Handshake.Message} {hello : Handshake.ClientHello}
    {group : Handshake.NamedGroup} {wire : ByteArray}
    (h : sendHelloRetryRequest state message hello group = .ok (next, wire)) :
    SpecEffect H state next := by
  unfold sendHelloRetryRequest at h
  simp only [pure_bind] at h
  obtain ⟨retry, _, h⟩ := except_bind_ok_inv h
  obtain ⟨messageHash, _, h⟩ := except_bind_ok_inv h
  obtain ⟨retryWire, _, h⟩ := except_bind_ok_inv h
  split at h
  · obtain ⟨ccsWire, _, h⟩ := except_bind_ok_inv h
    cases h
    exact SpecEffect.within (Record.WithinEpoch.refl _)
  · cases h
    exact SpecEffect.within (Record.WithinEpoch.refl _)

private theorem acceptClientHello_epochs {H : Spec.Hkdf} (hi : Implements H)
    {state next : State} {message : Handshake.Message} {wire : ByteArray}
    (h : acceptClientHello state message = .ok (next, wire))
    (hnone : state.writeKeys? = none) : SpecEffect H state next := by
  unfold acceptClientHello at h
  obtain ⟨hello, _, h⟩ := except_bind_ok_inv h
  obtain ⟨_, _, h⟩ := except_bind_ok_inv h
  obtain ⟨_, _, h⟩ := except_bind_ok_inv h
  split at h <;>
    first
      | (obtain ⟨group, _, h⟩ := except_bind_ok_inv h
         split at h
         · exact completeClientHello_epochs hi h hnone
         · exact sendHelloRetryRequest_epochs h)
      | (split at h <;>
          first
            | cases h
            | (split at h <;>
                first
                  | cases h
                  | (obtain ⟨_, _, h⟩ := except_bind_ok_inv h
                     exact completeClientHello_epochs hi h hnone)))
      | cases h

private theorem acceptClientFinished_epochs {H : Spec.Hkdf} {state next : State}
    {message : Handshake.Message}
    (h : acceptClientFinished state message = .ok next) :
    SpecEffect H state next := by
  unfold acceptClientFinished at h
  simp only [pure_bind] at h
  obtain ⟨finished, _, h⟩ := except_bind_ok_inv h
  split at h <;>
    first
      | (cases h <;> exact SpecEffect.within (Record.WithinEpoch.refl _))
      | (split at h <;>
          first
            | (cases h <;> exact SpecEffect.within (Record.WithinEpoch.refl _))
            | (split at h <;>
                (cases h <;> exact SpecEffect.within (Record.WithinEpoch.refl _))))

private theorem processHandshakeBuffer_epochs {H : Spec.Hkdf} (hi : Implements H)
    {state next : State} {wire : ByteArray}
    (h : processHandshakeBuffer state = .ok (next, wire))
    (hinv : state.WellFormed) : SpecEffect H state next := by
  unfold processHandshakeBuffer at h
  split at h
  · cases h
  · cases h; exact SpecEffect.within (Record.WithinEpoch.refl _)
  · rename_i message rest htake
    simp only [pure_bind] at h
    split at h
    · rename_i hph
      obtain ⟨_, h⟩ := unless_ok h
      obtain ⟨_, h⟩ := unless_ok h
      have hw := acceptClientHello_epochs hi h (hinv.2.2 (.inl hph)).2
      exact SpecEffect.of_eq hw rfl
    · rename_i hph
      obtain ⟨_, h⟩ := unless_ok h
      obtain ⟨_, h⟩ := unless_ok h
      have hw := acceptClientHello_epochs hi h (hinv.2.2 (.inr hph)).2
      exact SpecEffect.of_eq hw rfl
    · obtain ⟨_, h⟩ := unless_ok h
      obtain ⟨_, h⟩ := unless_ok h
      obtain ⟨stateF, hfin, h⟩ := except_bind_ok_inv h
      cases h
      have hw := acceptClientFinished_epochs (H := H) hfin
      exact SpecEffect.of_eq hw rfl
    · split at h
      · obtain ⟨_, h⟩ := unless_ok h
        exact SpecEffect.of_eq (acceptKeyUpdate_epochs hi h) rfl
      · cases h

private theorem processProtectedRecord_epochs {H : Spec.Hkdf} (hi : Implements H)
    {state next : State} {record : Record.RawRecord} {plain wire : ByteArray}
    (h : processProtectedRecord state record = .ok (next, plain, wire))
    (hinv : state.WellFormed) : SpecEffect H state next := by
  unfold processProtectedRecord at h
  simp only [pure_bind] at h
  obtain ⟨readKeys, hrk, h⟩ := except_bind_ok_inv h
  obtain ⟨opened, _, h⟩ := except_bind_ok_inv h
  obtain ⟨nextReadKeys, plaintext⟩ := opened
  have hinv' : ({ state with readKeys? := some nextReadKeys } : State).WellFormed :=
    wellFormed_transfer hinv rfl
      (.inr ⟨⟨_, rfl⟩, requireReadKeys_isSome hrk⟩) rfl rfl (.inl rfl)
  refine SpecEffect.of_eq (b := { state with readKeys? := some nextReadKeys }) ?_ rfl
  split at h
  · cases h
    exact SpecEffect.within (Record.WithinEpoch.refl _)
  · split at h <;>
      first
        | (obtain ⟨_, h⟩ := unless_ok h
           obtain ⟨_, h⟩ := unless_ok h
           cases h
           exact SpecEffect.within (Record.WithinEpoch.refl _))
        | (obtain ⟨_, h⟩ := if_throw_ok h
           obtain ⟨pair, hpb, h⟩ := except_bind_ok_inv h
           obtain ⟨stateH, wireH⟩ := pair
           cases h
           have hw := processHandshakeBuffer_epochs hi hpb hinv'
           exact SpecEffect.of_eq hw rfl)
        | (obtain ⟨_, h⟩ := unless_ok h
           obtain ⟨pair, hpa, h⟩ := except_bind_ok_inv h
           obtain ⟨stateA, wireA⟩ := pair
           cases h
           have hw := processAlert_epochs (H := H) hpa
           exact hw)
        | cases h

private theorem feedPlaintextClientHello_epochs {H : Spec.Hkdf} (hi : Implements H)
    {state next : State} {fragment wire : ByteArray}
    (h : feedPlaintextClientHello state fragment = .ok (next, wire))
    (hinv : state.WellFormed) : SpecEffect H state next := by
  unfold feedPlaintextClientHello at h
  simp only [pure_bind] at h
  obtain ⟨_, h⟩ := if_throw_ok h
  have hw := processHandshakeBuffer_epochs hi h
    (wellFormed_transfer hinv rfl (.inl rfl) rfl rfl (.inl rfl))
  exact SpecEffect.of_eq hw rfl

private theorem processRecord_epochs {H : Spec.Hkdf} (hi : Implements H)
    {state next : State} {record : Record.RawRecord} {plain wire : ByteArray}
    (h : processRecord state record = .ok (next, plain, wire))
    (hinv : state.WellFormed) : SpecEffect H state next := by
  unfold processRecord at h
  simp only [pure_bind] at h
  split at h <;> split at h <;>
    first
      | (obtain ⟨pair, hfp, h⟩ := except_bind_ok_inv h
         obtain ⟨stateP, wireP⟩ := pair
         cases h
         have hw := feedPlaintextClientHello_epochs hi hfp hinv
         exact hw)
      | (obtain ⟨_, h⟩ := unless_ok h
         obtain ⟨_, h⟩ := unless_ok h
         cases h
         exact SpecEffect.within (Record.WithinEpoch.refl _))
      | (obtain ⟨_, h⟩ := unless_ok h
         obtain ⟨pair, hpa, h⟩ := except_bind_ok_inv h
         obtain ⟨stateA, wireA⟩ := pair
         cases h
         have hw := processAlert_epochs (H := H) hpa
         exact hw)
      | exact processProtectedRecord_epochs hi h hinv
      | cases h

private theorem processRecords_epochs {H : Spec.Hkdf} (hi : Implements H)
    {records : List Record.RawRecord} :
    ∀ {state : State} {plaintext wireBytes : ByteArray} {out : Output},
      processRecords state records plaintext wireBytes = .ok out →
      state.WellFormed → SpecEffect H state out.state := by
  induction records with
  | nil =>
      intro state plaintext wireBytes out h hinv
      unfold processRecords at h
      cases h
      exact SpecEffect.within (Record.WithinEpoch.refl _)
  | cons record rest ih =>
      intro state plaintext wireBytes out h hinv
      unfold processRecords at h
      split at h
      · cases h
        exact SpecEffect.within (Record.WithinEpoch.refl _)
      · split at h
        · cases h
        · rename_i stateN cleartext outbound hpr
          have h1 := processRecord_epochs hi hpr hinv
          have h2 := ih h (processRecord_wellFormed hpr hinv)
          exact SpecEffect.trans h1 h2

theorem feedWithFailure_epochs {H : Spec.Hkdf} (hi : Implements H)
    {initial : State} {chunk : ByteArray} {out : Output}
    (h : feedWithFailure initial chunk = .ok out) (hinv : initial.WellFormed) :
    SpecEffect H initial out.state := by
  unfold feedWithFailure at h
  split at h
  · cases h
    exact SpecEffect.within (Record.WithinEpoch.refl _)
  · split at h
    · cases h
    · have hw := processRecords_epochs hi h
        ⟨fun hc => hinv.1 hc, fun hp => hinv.2.1 hp, fun hp => hinv.2.2 hp⟩
      exact SpecEffect.of_eq hw rfl

theorem feed_epochs {H : Spec.Hkdf} (hi : Implements H) {state : State}
    {chunk : ByteArray} {out : Output} (h : feed state chunk = .ok out)
    (hinv : state.WellFormed) : SpecEffect H state out.state := by
  unfold feed at h
  cases hf : feedWithFailure state chunk with
  | error failure => rw [hf] at h; cases h
  | ok output =>
      rw [hf] at h
      simp only [Except.mapError] at h
      cases h
      exact feedWithFailure_epochs hi hf hinv

theorem step_epochs {H : Spec.Hkdf} (hi : Implements H) {state : State} {op : Op}
    {out : Output} (h : step state op = .ok out) (hinv : state.WellFormed) :
    SpecEffect H state out.state := by
  unfold step at h
  split at h
  · exact feed_epochs hi h hinv
  · exact sealApplication_epochs h
  · exact closeNotify_epochs h
  · exact sealFatalAlert_epochs h

/-- **Every epoch a run installs is a strictly later node of the RFC 8446 §7.1 /
§7.2 key schedule than the one it replaces.** -/
theorem run_epochs {H : Spec.Hkdf} (hi : Implements H) {ops : List Op} :
    ∀ {state : State} {out : Output}, run state ops = .ok out →
      state.WellFormed → SpecEffect H state out.state := by
  induction ops with
  | nil =>
      intro state out h hinv
      unfold run at h; cases h
      exact SpecEffect.within (Record.WithinEpoch.refl _)
  | cons op rest ih =>
      intro state out h hinv
      unfold run at h
      split at h
      · cases h
      · rename_i out1 hstep
        split at h
        · cases h
        · rename_i final hrun
          have h1 := step_epochs hi hstep hinv
          have h2 := ih hrun (step_wellFormed hstep hinv)
          cases h
          exact SpecEffect.trans h1 h2

/-- A server that has not yet answered a ClientHello is in no epoch at all. -/
private theorem writeEpoch_start {H : Spec.Hkdf} {state : State}
    (hinv : state.WellFormed)
    (hph : state.phase = .waitingClientHello ∨
      state.phase = .waitingSecondClientHello) :
    state.WriteEpoch H none :=
  ⟨by rw [hinv.noWriteKeys hph]; exact Record.EpochOf.idle, fun e he => by cases he⟩

/-- **A server's finite AEAD nonce trace, refined by the key schedule.** For any
run of a server that has not yet answered a ClientHello — in particular a server
from `start` — the traffic-secret tags form a strictly increasing RFC 8446
§7.1 / §7.2 schedule, while a parallel executable trace records the concrete
AEAD key used with every nonce. The traces have the same nonce sequence, and
the actual `(key, nonce)` pairs are duplicate-free under the explicit finite-run
condition `aeadKeys.Nodup`. -/
theorem run_nonce_trace_spec {H : Spec.Hkdf} (hi : Implements H)
    {ops : List Op} {state : State}
    {out : Output} (hinv : state.WellFormed)
    (hph : state.phase = .waitingClientHello ∨
      state.phase = .waitingSecondClientHello) (h : run state ops = .ok out) :
    ∃ secrets taggedNonces aeadKeys keyNonces,
      Record.WriteRun state.writeKeys? out.state.writeKeys? secrets taggedNonces ∧
        Record.EpochsFrom H none secrets ∧
        Record.AeadWriteRun state.writeKeys? out.state.writeKeys?
          aeadKeys keyNonces ∧
        keyNonces.map Prod.snd = taggedNonces.map Prod.snd ∧
        (aeadKeys.Nodup → keyNonces.Nodup) := by
  obtain ⟨o', ho', hx⟩ := run_epochs hi h hinv none (writeEpoch_start hinv hph)
  exact hx.finite_nonce_trace ho'.1 ho'.valid

/-- `run_nonce_trace_spec` for a single `feed` — which for a server covers the
entire handshake. -/
theorem feed_nonce_trace_spec {H : Spec.Hkdf} (hi : Implements H)
    {state : State} {chunk : ByteArray}
    {out : Output} (hinv : state.WellFormed)
    (hph : state.phase = .waitingClientHello ∨
      state.phase = .waitingSecondClientHello) (h : feed state chunk = .ok out) :
    ∃ secrets taggedNonces aeadKeys keyNonces,
      Record.WriteRun state.writeKeys? out.state.writeKeys? secrets taggedNonces ∧
        Record.EpochsFrom H none secrets ∧
        Record.AeadWriteRun state.writeKeys? out.state.writeKeys?
          aeadKeys keyNonces ∧
        keyNonces.map Prod.snd = taggedNonces.map Prod.snd ∧
        (aeadKeys.Nodup → keyNonces.Nodup) := by
  obtain ⟨o', ho', hx⟩ := feed_epochs hi h hinv none (writeEpoch_start hinv hph)
  exact hx.finite_nonce_trace ho'.1 ho'.valid

/-- The finite, schedule-refined nonce trace for a server driven from `start`. -/
theorem start_run_nonce_trace_spec {H : Spec.Hkdf} (hi : Implements H)
    {config : Config} {ops : List Op}
    {out : Output} (h : run (start config) ops = .ok out) :
    ∃ secrets taggedNonces aeadKeys keyNonces,
      Record.WriteRun (start config).writeKeys? out.state.writeKeys?
          secrets taggedNonces ∧
        Record.EpochsFrom H none secrets ∧
        Record.AeadWriteRun (start config).writeKeys? out.state.writeKeys?
          aeadKeys keyNonces ∧
        keyNonces.map Prod.snd = taggedNonces.map Prod.snd ∧
        (aeadKeys.Nodup → keyNonces.Nodup) :=
  run_nonce_trace_spec hi (start_wellFormed config) (.inl rfl) h

end Server
end Tls
