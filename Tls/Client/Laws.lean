module

public import Tls.Client
public import Tls.Record.Laws
import all Tls.Client
import all Tls.Record

public section

namespace Tls
namespace Client

/-!
Kernel-checked laws about the executable client state machine in `Tls.Client`.

The headline is **nonce non-reuse across a connection**. `Tls.Record.Laws`
proves the arithmetic — one epoch, one sequence number per record, no wrap, and
an injective nonce — but it cannot rule out a caller sealing twice with a
retained copy of a `TrafficKeys`. This module supplies the missing half: every
record the *client engine itself* protects is sealed with the write traffic
keys its own state carries, and the advanced state is stored straight back.
Composing those two facts, `run_nonce_nodup` exposes the actual
`(AEAD key, nonce)` trace of a whole run and proves it has no repeats when the
concrete AEAD keys installed in that finite run are distinct.

Scope, stated honestly:

* The theorems are about this engine's own emissions along one chain of states.
  A caller that clones a `State` and drives two connections from it is outside
  their reach — Lean values are duplicable, and no theorem about a pure function
  can forbid that. Threading one state is the caller's obligation.
* Only the *write* direction is covered. Nonce reuse is a sender property;
  read-side nonces are the peer's.
* Distinctness across traffic epochs is an `aeadKeys.Nodup` hypothesis in
  `run_nonce_nodup`. `run_nonce_trace_spec` additionally returns the parallel
  traffic-secret bookkeeping trace and proves those secrets are evaluations of
  strictly increasing RFC 8446 §7.1 / §7.2 derivation histories. It does not
  infer byte distinctness from structural order: a fixed-size KDF cannot be
  globally injective. Within one epoch nothing is assumed; across epochs,
  concrete derived-key collision freedom is the explicit finite-run condition.
-/

private theorem except_bind_ok_inv {α β : Type} {m : Except Error α}
    {f : α → Except Error β} {b : β} (h : (m >>= f) = .ok b) :
    ∃ a, m = .ok a ∧ f a = .ok b := by
  cases m with
  | error e => cases h
  | ok a => exact ⟨a, rfl, h⟩

private theorem liftRecord_ok {α : Type} {r : Except Record.Error α} {v : α}
    (h : liftRecord r = .ok v) : r = .ok v := by
  unfold liftRecord at h
  cases r with
  | error e => cases h
  | ok a => cases h; rfl

private theorem requireWriteKeys_ok {state : State} {keys : Record.TrafficKeys}
    (h : requireWriteKeys state = .ok keys) : state.writeKeys? = some keys := by
  unfold requireWriteKeys at h
  cases hw : state.writeKeys? with
  | none => rw [hw] at h; cases h
  | some k => rw [hw] at h; cases h; rfl

/-- The write side of one engine step: how the connection's own `seal` calls
advanced its write traffic state. `Tls.Record.Laws.Extends` composes these, so a
whole run's `WriteRun` — the list of records protected and nonces consumed — is
assembled from one lemma per engine operation. -/
def WriteEffect (before after : State) : Prop :=
  Record.Extends before.writeKeys? after.writeKeys?

/-- Sealing a fatal alert protects exactly one record under the current write
epoch. -/
theorem sealFatalAlert_write {state : State} {description : UInt8}
    {out : Output} (h : sealFatalAlert state description = .ok out) :
    WriteEffect state out.state := by
  unfold sealFatalAlert at h
  simp only [pure_bind] at h
  split at h
  · cases h
  · obtain ⟨keys, hk, h⟩ := except_bind_ok_inv h
    obtain ⟨sealed, hs, h⟩ := except_bind_ok_inv h
    obtain ⟨next, wire⟩ := sealed
    cases h
    show Record.Extends state.writeKeys? (some next)
    rw [requireWriteKeys_ok hk]
    exact Record.Extends.of_seal (liftRecord_ok hs)

/-- Once `close_notify` has closed the local write direction, even a fatal alert
is suppressed: RFC 9846 requires that no further records be sent. -/
theorem sealFatalAlert_localClosed {state : State} {description : UInt8}
    (hclosed : state.localClosed = true) :
    sealFatalAlert state description = .error .connectionClosed := by
  unfold sealFatalAlert
  rw [if_pos hclosed]
  rfl


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


/-- Application data is protected by a chain of seals under one epoch: one
record per 2^14-byte chunk, each with the state the previous seal returned. -/
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

/-- `close_notify` protects at most one record (a repeated close is a no-op). -/
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

/-- A KeyUpdate response seals its message under the *old* epoch, as RFC 8446
§7.2 requires, and only then rolls the write secret forward. -/
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

private theorem extends_fresh (before : Option Record.TrafficKeys)
    (keys : Record.TrafficKeys) : Record.Extends before (some keys) := by
  cases before with
  | none => exact Record.Extends.install keys
  | some k => exact Record.Extends.rekey k keys

private theorem acceptServerHello_write {state next : State}
    {message : Handshake.Message}
    (h : acceptServerHello state message = .ok next) : WriteEffect state next := by
  unfold acceptServerHello at h
  simp only [pure_bind] at h
  obtain ⟨_, h⟩ := unless_ok h
  obtain ⟨hello, _, h⟩ := except_bind_ok_inv h
  obtain ⟨_, _, h⟩ := except_bind_ok_inv h
  split at h
  · split at h
    · split at h
      · obtain ⟨writeKeys, _, h⟩ := except_bind_ok_inv h
        obtain ⟨readKeys, _, h⟩ := except_bind_ok_inv h
        cases h
        exact extends_fresh _ writeKeys
      · cases h
    · cases h
  · split at h
    · split at h
      · split at h
        · obtain ⟨writeKeys, _, h⟩ := except_bind_ok_inv h
          obtain ⟨readKeys, _, h⟩ := except_bind_ok_inv h
          cases h
          exact extends_fresh _ writeKeys
        · cases h
      · cases h
    · cases h

/-- Completing the handshake seals the client Finished under the handshake write
epoch and then installs the application epoch — both accounted for. -/
private theorem completeServerHandshake_write {state next : State}
    {message : Handshake.Message} {wire : ByteArray}
    (h : completeServerHandshake state message = .ok (next, wire)) :
    WriteEffect state next := by
  unfold completeServerHandshake at h
  simp only [pure_bind] at h
  obtain ⟨finished, _, h⟩ := except_bind_ok_inv h
  obtain ⟨serverSecret, _, h⟩ := except_bind_ok_inv h
  split at h
  case isFalse => cases h
  obtain ⟨handshakeSecret, _, h⟩ := except_bind_ok_inv h
  obtain ⟨clientApplicationKeys, _, h⟩ := except_bind_ok_inv h
  obtain ⟨serverApplicationKeys, _, h⟩ := except_bind_ok_inv h
  obtain ⟨clientHandshakeSecret, _, h⟩ := except_bind_ok_inv h
  obtain ⟨clientFinished, _, h⟩ := except_bind_ok_inv h
  obtain ⟨handshakeWriteKeys, hk, h⟩ := except_bind_ok_inv h
  obtain ⟨sealed, hs, h⟩ := except_bind_ok_inv h
  obtain ⟨advancedKeys, finishedWire⟩ := sealed
  have hgoal : Record.Extends state.writeKeys? (some clientApplicationKeys) := by
    rw [requireWriteKeys_ok hk]
    exact Record.Extends.trans (Record.Extends.of_seal (liftRecord_ok hs))
      (Record.Extends.rekey advancedKeys clientApplicationKeys)
  split at h
  · cases h; exact hgoal
  · obtain ⟨compatibilityWire, _, h⟩ := except_bind_ok_inv h
    cases h
    exact hgoal


private theorem processHandshakeBuffer_write {state next : State} {wire : ByteArray}
    (h : processHandshakeBuffer state = .ok (next, wire)) :
    WriteEffect state next := by
  unfold processHandshakeBuffer at h
  split at h
  · cases h
  · cases h; exact Record.Extends.refl _
  · rename_i message rest htake
    have hsize : rest.size < state.handshakeBuffered.size := takeHandshake?_size htake
    simp only [pure_bind] at h
    split at h
    · cases h
    · obtain ⟨_, h⟩ := unless_ok h
      obtain ⟨_, _, h⟩ := except_bind_ok_inv h
      obtain ⟨alpn, _, h⟩ := except_bind_ok_inv h
      split at h
      · obtain ⟨_, h⟩ := unless_ok h
        have hw := processHandshakeBuffer_write h
        exact hw
      · have hw := processHandshakeBuffer_write h
        exact hw
    · obtain ⟨_, h⟩ := unless_ok h
      obtain ⟨_, _, h⟩ := except_bind_ok_inv h
      obtain ⟨_, _, h⟩ := except_bind_ok_inv h
      have hw := processHandshakeBuffer_write h
      exact hw
    · obtain ⟨_, h⟩ := unless_ok h
      obtain ⟨_, _, h⟩ := except_bind_ok_inv h
      split at h
      · obtain ⟨_, _, h⟩ := except_bind_ok_inv h
        obtain ⟨_, h⟩ := unless_ok h
        obtain ⟨_, h⟩ := unless_ok h
        have hw := processHandshakeBuffer_write h
        exact hw
      · cases h
    · obtain ⟨_, h⟩ := unless_ok h
      obtain ⟨_, h⟩ := unless_ok h
      have hw := completeServerHandshake_write h
      exact hw
    · split at h
      · have hw := processHandshakeBuffer_write h
        exact hw
      · split at h
        · obtain ⟨_, h⟩ := unless_ok h
          split at h
          · cases h
          · rename_i stateK wireK hacc
            split at h
            · cases h
            · rename_i stateF moreWire hnext
              cases h
              have h1 := acceptKeyUpdate_write hacc
              have hbuf : stateK.handshakeBuffered.size <
                  state.handshakeBuffered.size := by
                rw [acceptKeyUpdate_buffered hacc]; exact hsize
              have h2 := processHandshakeBuffer_write hnext
              exact Record.Extends.trans h1 h2
        · cases h
  termination_by state.handshakeBuffered.size
  decreasing_by
    all_goals first
      | exact hsize
      | exact hbuf


private theorem feedPlaintextHandshake_write {state next : State}
    {fragment : ByteArray}
    (h : feedPlaintextHandshake state fragment = .ok next) :
    WriteEffect state next := by
  unfold feedPlaintextHandshake at h
  simp only [pure_bind] at h
  obtain ⟨_, h⟩ := if_throw_ok h
  obtain ⟨framed, _, h⟩ := except_bind_ok_inv h
  split at h
  · split at h
    · have hw := acceptServerHello_write h
      exact hw
    · cases h
  · cases h; exact Record.Extends.refl _

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
  · split at h
    · cases h
      exact Record.Extends.refl _
    · split at h
      · obtain ⟨_, h⟩ := unless_ok h
        cases h
        exact Record.Extends.refl _
      · obtain ⟨_, h⟩ := if_throw_ok h
        obtain ⟨pair, hpb, h⟩ := except_bind_ok_inv h
        obtain ⟨stateH, wireH⟩ := pair
        cases h
        have hw := processHandshakeBuffer_write hpb
        exact hw
      · obtain ⟨_, h⟩ := unless_ok h
        obtain ⟨pair, hpa, h⟩ := except_bind_ok_inv h
        obtain ⟨stateA, wireA⟩ := pair
        cases h
        have hw := processAlert_write hpa
        exact hw
      · cases h
  · split at h
    · obtain ⟨_, h⟩ := if_throw_ok h
      obtain ⟨pair, hpb, h⟩ := except_bind_ok_inv h
      obtain ⟨stateH, wireH⟩ := pair
      cases h
      have hw := processHandshakeBuffer_write hpb
      exact hw
    · obtain ⟨_, h⟩ := unless_ok h
      obtain ⟨pair, hpa, h⟩ := except_bind_ok_inv h
      obtain ⟨stateA, wireA⟩ := pair
      cases h
      have hw := processAlert_write hpa
      exact hw
    · cases h

private theorem processRecord_write {state next : State}
    {record : Record.RawRecord} {plain wire : ByteArray}
    (h : processRecord state record = .ok (next, plain, wire)) :
    WriteEffect state next := by
  unfold processRecord at h
  simp only [pure_bind] at h
  split at h <;> split at h <;>
    first
      | (obtain ⟨_, h⟩ := unless_ok h
         cases h
         exact Record.Extends.refl _)
      | (obtain ⟨stateP, hfp, h⟩ := except_bind_ok_inv h
         cases h
         have hw := feedPlaintextHandshake_write hfp
         exact hw)
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


/-- Everything a successful `feed` protects — a client Finished or reciprocal
KeyUpdate — is accounted for. Local `close_notify` is covered separately by
`closeNotify_write`. -/
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

/-- The same holds for the state a failed `feed` hands back for sealing a fatal
alert: it is reachable from the input by the engine's own seals, so the alert
does not reuse a nonce either. -/
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
  split at h
  · rename_i output hfeed
    cases h
    exact feedWithFailure_write hfeed
  · cases h

theorem step_write {state : State} {op : Op} {out : Output}
    (h : step state op = .ok out) : WriteEffect state out.state := by
  unfold step at h
  split at h
  · exact feed_write h
  · exact sealApplication_write h
  · exact closeNotify_write h
  · exact sealFatalAlert_write h

/-- **Every record a run protects is threaded through the engine's own state.**
-/
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

/-- Structural invariant of a client connection.

**An established connection carries both application traffic epochs and has
dropped every handshake secret and the handshake transcript.** Before the
connection is established that clause says nothing, which is exactly right —
the handshake states are the ones that legitimately hold those secrets.

**A client that has not yet accepted the ServerHello holds neither traffic
epoch.**
This is the state-only half of the inbound application-data rule: opening any
protected record needs a read epoch (`requireReadKeys`), so in
`waitingServerHello` the engine cannot decrypt anything at all, and *a fortiori*
cannot hand plaintext to the caller. Only `acceptServerHello` installs the first
read epoch, and it leaves `waitingServerHello` in the same step. The same holds
of the *write* epoch, which is what makes `acceptServerHello` the installation
of the connection's first epoch rather than the replacement of one — exactly
what `run_nonce_trace_spec` needs to start its structural epoch history at
`none`.
The rest of the
inbound rule is inherently about an *output* rather than a state and stays a
transition law: `feed_plaintext_connected` / `run_plaintext_connected` below say
that any feed or run which delivers plaintext delivers it with a `connected`
state.

`start_wellFormed` establishes both clauses and `feed`, `feedWithFailure`,
`sealApplication`, `closeNotify`, `sealFatalAlert` and whole `run`s preserve
them. The complementary facts about *how* the connection becomes established
(the server Finished was verified, the transcript grew by exactly the message
consumed) are transition laws below rather than conjuncts here. -/
def State.WellFormed (state : State) : Prop :=
  (state.phase = .connected →
    state.writeKeys?.isSome = true ∧ state.readKeys?.isSome = true ∧
      state.handshakeSecret? = none ∧
      state.clientHandshakeTrafficSecret? = none ∧
      state.serverHandshakeTrafficSecret? = none ∧
      state.transcript = ByteArray.empty) ∧
  (state.phase = .waitingServerHello →
    state.readKeys? = none ∧ state.writeKeys? = none)

/-- The established-connection clause, as a projection. -/
theorem State.WellFormed.connected {state : State} (h : state.WellFormed)
    (hc : state.phase = .connected) :
    state.writeKeys?.isSome = true ∧ state.readKeys?.isSome = true ∧
      state.handshakeSecret? = none ∧
      state.clientHandshakeTrafficSecret? = none ∧
      state.serverHandshakeTrafficSecret? = none ∧
      state.transcript = ByteArray.empty := h.1 hc

/-- **A client waiting for the ServerHello holds no read epoch**, so it can
decrypt nothing and therefore deliver nothing. -/
theorem State.WellFormed.noReadKeys {state : State} (h : state.WellFormed)
    (hp : state.phase = .waitingServerHello) : state.readKeys? = none := (h.2 hp).1

/-- **A client waiting for the ServerHello holds no write epoch either.** The
mirror of `noReadKeys`, and what makes the ServerHello the *first* epoch of the
connection: `acceptServerHello` cannot be replacing one (see
`run_nonce_trace_spec`, where that is exactly what anchors the schedule
trace). -/
theorem State.WellFormed.noWriteKeys {state : State} (h : state.WellFormed)
    (hp : state.phase = .waitingServerHello) : state.writeKeys? = none := (h.2 hp).2

/-- Opening a record needs a read epoch, so a successful `requireReadKeys`
witnesses that the state holds one. -/
private theorem requireReadKeys_isSome {state : State}
    {keys : Record.TrafficKeys} (h : requireReadKeys state = .ok keys) :
    state.readKeys?.isSome = true := by
  unfold requireReadKeys at h
  split at h
  · rename_i hk; rw [hk]; rfl
  · cases h

/-- Opening a record uses the read epoch the state carries. -/
private theorem requireReadKeys_ok {state : State} {keys : Record.TrafficKeys}
    (h : requireReadKeys state = .ok keys) : state.readKeys? = some keys := by
  unfold requireReadKeys at h
  cases hk : state.readKeys? with
  | none => rw [hk] at h; cases h
  | some k => rw [hk] at h; cases h; rfl

/-- Protecting a record needs a write epoch, so a successful `requireWriteKeys`
witnesses that the state holds one. -/
private theorem requireWriteKeys_isSome {state : State}
    {keys : Record.TrafficKeys} (h : requireWriteKeys state = .ok keys) :
    state.writeKeys?.isSome = true := by
  rw [requireWriteKeys_ok h]; rfl

/-- Transfer the invariant across a state update that changes no field it
mentions, except by installing traffic keys. A *new* epoch — in either
direction — is only ever derived from an existing one, so the second disjunct of
`hread` / `hwrite` carries the witness that `s` already had one, which is what
keeps the `waitingServerHello` clause true of `t`. -/
private theorem wellFormed_transfer {s t : State} (hinv : s.WellFormed)
    (hphase : t.phase = s.phase)
    (hwrite : t.writeKeys? = s.writeKeys? ∨
      (∃ k, t.writeKeys? = some k) ∧ s.writeKeys?.isSome = true)
    (hread : t.readKeys? = s.readKeys? ∨
      (∃ k, t.readKeys? = some k) ∧ s.readKeys?.isSome = true)
    (h1 : t.handshakeSecret? = s.handshakeSecret?)
    (h2 : t.clientHandshakeTrafficSecret? = s.clientHandshakeTrafficSecret?)
    (h3 : t.serverHandshakeTrafficSecret? = s.serverHandshakeTrafficSecret?)
    (h4 : t.transcript = s.transcript) : t.WellFormed := by
  refine ⟨fun hc => ?_, fun hp => ⟨?_, ?_⟩⟩
  · obtain ⟨a, b, c, d, e, f⟩ := hinv.1 (hphase ▸ hc)
    refine ⟨?_, ?_, by rw [h1]; exact c, by rw [h2]; exact d,
      by rw [h3]; exact e, by rw [h4]; exact f⟩
    · cases hwrite with
      | inl hw => rw [hw]; exact a
      | inr hw => obtain ⟨⟨k, hk⟩, -⟩ := hw; rw [hk]; rfl
    · cases hread with
      | inl hr => rw [hr]; exact b
      | inr hr => obtain ⟨⟨k, hk⟩, -⟩ := hr; rw [hk]; rfl
  · cases hread with
    | inl hr => rw [hr]; exact (hinv.2 (hphase ▸ hp)).1
    | inr hr =>
        obtain ⟨-, hs⟩ := hr
        rw [(hinv.2 (hphase ▸ hp)).1] at hs
        exact absurd hs (by decide)
  · cases hwrite with
    | inl hw => rw [hw]; exact (hinv.2 (hphase ▸ hp)).2
    | inr hw =>
        obtain ⟨-, hs⟩ := hw
        rw [(hinv.2 (hphase ▸ hp)).2] at hs
        exact absurd hs (by decide)

/-- A fresh client connection is waiting for the ServerHello and holds neither
traffic epoch. -/
private theorem start_phase_readKeys {config : Config} {out : Output}
    (h : start config = .ok out) :
    out.state.phase = .waitingServerHello ∧ out.state.readKeys? = none ∧
      out.state.writeKeys? = none := by
  unfold start at h
  simp only [pure_bind] at h
  obtain ⟨_, h⟩ := unless_ok h
  obtain ⟨_, h⟩ := unless_ok h
  split at h <;>
    first
      | (obtain ⟨_, h⟩ := unless_ok h
         split at h <;>
           first
             | cases h
             | (obtain ⟨_, h⟩ := unless_ok h
                split at h <;>
                  first
                    | (obtain ⟨hello, _, h⟩ := except_bind_ok_inv h
                       obtain ⟨wire, _, h⟩ := except_bind_ok_inv h
                       cases h
                       exact ⟨rfl, rfl, rfl⟩)
                    | (split at h <;>
                        first
                          | cases h
                          | (obtain ⟨_, h⟩ := unless_ok h
                             obtain ⟨hello, _, h⟩ := except_bind_ok_inv h
                             obtain ⟨wire, _, h⟩ := except_bind_ok_inv h
                             cases h
                             exact ⟨rfl, rfl, rfl⟩))))
      | (split at h <;>
          first
            | cases h
            | (obtain ⟨_, h⟩ := unless_ok h
               split at h <;>
                 first
                   | (obtain ⟨hello, _, h⟩ := except_bind_ok_inv h
                      obtain ⟨wire, _, h⟩ := except_bind_ok_inv h
                      cases h
                      exact ⟨rfl, rfl, rfl⟩)
                   | (split at h <;>
                       first
                         | cases h
                         | (obtain ⟨_, h⟩ := unless_ok h
                            obtain ⟨hello, _, h⟩ := except_bind_ok_inv h
                            obtain ⟨wire, _, h⟩ := except_bind_ok_inv h
                            cases h
                            exact ⟨rfl, rfl, rfl⟩))))

/-- A fresh client connection is waiting for the ServerHello. -/
theorem start_phase {config : Config} {out : Output}
    (h : start config = .ok out) :
    out.state.phase = .waitingServerHello := (start_phase_readKeys h).1

/-- `start` establishes the invariant: the connection is not yet established, so
the first clause holds vacuously — and in particular no traffic keys exist
yet, which is the second clause. -/
theorem start_wellFormed {config : Config} {out : Output}
    (h : start config = .ok out) : out.state.WellFormed := by
  refine ⟨fun hc => ?_, fun _ => (start_phase_readKeys h).2⟩
  rw [start_phase h] at hc
  cases hc

theorem sealFatalAlert_wellFormed {state : State} {description : UInt8}
    {out : Output} (h : sealFatalAlert state description = .ok out)
    (hinv : state.WellFormed) : out.state.WellFormed := by
  unfold sealFatalAlert at h
  simp only [pure_bind] at h
  split at h
  · cases h
  · obtain ⟨keys, hk, h⟩ := except_bind_ok_inv h
    obtain ⟨sealed, hs, h⟩ := except_bind_ok_inv h
    obtain ⟨next, wire⟩ := sealed
    cases h
    exact wellFormed_transfer hinv rfl
      (.inr ⟨⟨_, rfl⟩, requireWriteKeys_isSome hk⟩)
      (.inl rfl) rfl rfl rfl rfl

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
    exact wellFormed_transfer hinv rfl (.inr ⟨⟨_, rfl⟩, requireWriteKeys_isSome hk⟩)
      (.inl rfl) rfl rfl
      rfl rfl

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
        exact wellFormed_transfer hinv rfl
          (.inr ⟨⟨_, rfl⟩, requireWriteKeys_isSome hk⟩) (.inl rfl) rfl rfl rfl rfl
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
      exact wellFormed_transfer hinv rfl (.inl rfl) (.inl rfl) rfl rfl rfl rfl
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
    exact wellFormed_transfer hinv rfl
      (.inr ⟨⟨_, rfl⟩, requireWriteKeys_isSome hk⟩)
      (.inl rfl) rfl rfl rfl rfl
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
  have hsome := requireReadKeys_isSome hrk
  split at h
  · cases h
    exact wellFormed_transfer hinv rfl (.inl rfl) (.inr ⟨⟨_, rfl⟩, hsome⟩)
      rfl rfl rfl rfl
  · simp only [] at h
    split at h
    · cases h
      exact wellFormed_transfer hinv rfl (.inl rfl)
        (.inr ⟨⟨_, rfl⟩, hsome⟩) rfl rfl rfl rfl
    · exact sendKeyUpdateResponse_wellFormed h
        (wellFormed_transfer hinv rfl (.inl rfl)
          (.inr ⟨⟨_, rfl⟩, hsome⟩) rfl rfl rfl rfl)

private theorem acceptServerHello_wellFormed {state next : State}
    {message : Handshake.Message}
    (h : acceptServerHello state message = .ok next) : next.WellFormed := by
  unfold acceptServerHello at h
  simp only [pure_bind] at h
  obtain ⟨_, h⟩ := unless_ok h
  obtain ⟨hello, _, h⟩ := except_bind_ok_inv h
  obtain ⟨_, _, h⟩ := except_bind_ok_inv h
  split at h
  · split at h
    · split at h
      · obtain ⟨writeKeys, _, h⟩ := except_bind_ok_inv h
        obtain ⟨readKeys, _, h⟩ := except_bind_ok_inv h
        cases h
        exact ⟨fun hc => (by cases hc), fun hp => (by cases hp)⟩
      · cases h
    · cases h
  · split at h
    · split at h
      · split at h
        · obtain ⟨writeKeys, _, h⟩ := except_bind_ok_inv h
          obtain ⟨readKeys, _, h⟩ := except_bind_ok_inv h
          cases h
          exact ⟨fun hc => (by cases hc), fun hp => (by cases hp)⟩
        · cases h
      · cases h
    · cases h

/-- **The client reaches `connected` only by verifying the server Finished**,
and the established state carries application keys with the handshake secrets
and transcript dropped. -/
private theorem completeServerHandshake_wellFormed {state next : State}
    {message : Handshake.Message} {wire : ByteArray}
    (h : completeServerHandshake state message = .ok (next, wire)) :
    next.WellFormed := by
  unfold completeServerHandshake at h
  simp only [pure_bind] at h
  obtain ⟨finished, _, h⟩ := except_bind_ok_inv h
  obtain ⟨serverSecret, _, h⟩ := except_bind_ok_inv h
  split at h
  case isFalse => cases h
  obtain ⟨handshakeSecret, _, h⟩ := except_bind_ok_inv h
  obtain ⟨clientApplicationKeys, _, h⟩ := except_bind_ok_inv h
  obtain ⟨serverApplicationKeys, _, h⟩ := except_bind_ok_inv h
  obtain ⟨clientHandshakeSecret, _, h⟩ := except_bind_ok_inv h
  obtain ⟨clientFinished, _, h⟩ := except_bind_ok_inv h
  obtain ⟨handshakeWriteKeys, hk, h⟩ := except_bind_ok_inv h
  obtain ⟨sealed, hs, h⟩ := except_bind_ok_inv h
  obtain ⟨advancedKeys, finishedWire⟩ := sealed
  have hgoal : ∀ (st : State), st.phase = .connected →
      st.writeKeys? = some clientApplicationKeys →
      st.readKeys? = some serverApplicationKeys → st.handshakeSecret? = none →
      st.clientHandshakeTrafficSecret? = none →
      st.serverHandshakeTrafficSecret? = none →
      st.transcript = ByteArray.empty → st.WellFormed := by
    intro st hph a b c d e f
    exact ⟨fun _ => ⟨by rw [a]; rfl, by rw [b]; rfl, c, d, e, f⟩,
      fun hp => absurd (hph.symm.trans hp) (by decide)⟩
  split at h
  · cases h
    exact hgoal _ rfl rfl rfl rfl rfl rfl rfl
  · obtain ⟨compatibilityWire, _, h⟩ := except_bind_ok_inv h
    cases h
    exact hgoal _ rfl rfl rfl rfl rfl rfl rfl

private theorem feedPlaintextHandshake_wellFormed {state next : State}
    {fragment : ByteArray}
    (h : feedPlaintextHandshake state fragment = .ok next)
    (hinv : state.WellFormed) : next.WellFormed := by
  unfold feedPlaintextHandshake at h
  simp only [pure_bind] at h
  obtain ⟨_, h⟩ := if_throw_ok h
  obtain ⟨framed, _, h⟩ := except_bind_ok_inv h
  split at h
  · split at h
    · exact acceptServerHello_wellFormed h
    · cases h
  · cases h
    exact hinv

private theorem processHandshakeBuffer_wellFormed {state next : State}
    {wire : ByteArray} (h : processHandshakeBuffer state = .ok (next, wire))
    (hinv : state.WellFormed) : next.WellFormed := by
  unfold processHandshakeBuffer at h
  split at h
  · cases h
  · cases h; exact hinv
  · rename_i message rest htake
    have hsize : rest.size < state.handshakeBuffered.size := takeHandshake?_size htake
    simp only [pure_bind] at h
    split at h
    · cases h
    · obtain ⟨_, h⟩ := unless_ok h
      obtain ⟨_, _, h⟩ := except_bind_ok_inv h
      obtain ⟨alpn, _, h⟩ := except_bind_ok_inv h
      split at h
      · obtain ⟨_, h⟩ := unless_ok h
        exact processHandshakeBuffer_wellFormed h ⟨fun hc => (by cases hc), fun hp => (by cases hp)⟩
      · exact processHandshakeBuffer_wellFormed h ⟨fun hc => (by cases hc), fun hp => (by cases hp)⟩
    · obtain ⟨_, h⟩ := unless_ok h
      obtain ⟨_, _, h⟩ := except_bind_ok_inv h
      obtain ⟨_, _, h⟩ := except_bind_ok_inv h
      exact processHandshakeBuffer_wellFormed h ⟨fun hc => (by cases hc), fun hp => (by cases hp)⟩
    · obtain ⟨_, h⟩ := unless_ok h
      obtain ⟨_, _, h⟩ := except_bind_ok_inv h
      split at h
      · obtain ⟨_, _, h⟩ := except_bind_ok_inv h
        obtain ⟨_, h⟩ := unless_ok h
        obtain ⟨_, h⟩ := unless_ok h
        exact processHandshakeBuffer_wellFormed h ⟨fun hc => (by cases hc), fun hp => (by cases hp)⟩
      · cases h
    · obtain ⟨_, h⟩ := unless_ok h
      obtain ⟨_, h⟩ := unless_ok h
      exact completeServerHandshake_wellFormed h
    · split at h
      · exact processHandshakeBuffer_wellFormed h hinv
      · split at h
        · obtain ⟨_, h⟩ := unless_ok h
          split at h
          · cases h
          · rename_i stateK wireK hacc
            split at h
            · cases h
            · rename_i stateF moreWire hnext
              have hbuf : stateK.handshakeBuffered.size <
                  state.handshakeBuffered.size := by
                rw [acceptKeyUpdate_buffered hacc]; exact hsize
              have h2 := processHandshakeBuffer_wellFormed hnext
                (acceptKeyUpdate_wellFormed hacc hinv)
              cases h
              exact h2
        · cases h
  termination_by state.handshakeBuffered.size
  decreasing_by
    all_goals first
      | exact hsize
      | exact hbuf

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
    wellFormed_transfer hinv rfl (.inl rfl)
      (.inr ⟨⟨_, rfl⟩, requireReadKeys_isSome hrk⟩) rfl rfl rfl rfl
  split at h
  · split at h
    · cases h
      exact hinv'
    · split at h
      · obtain ⟨_, h⟩ := unless_ok h
        cases h
        exact hinv'
      · obtain ⟨_, h⟩ := if_throw_ok h
        obtain ⟨pair, hpb, h⟩ := except_bind_ok_inv h
        obtain ⟨stateH, wireH⟩ := pair
        cases h
        exact processHandshakeBuffer_wellFormed hpb hinv'
      · obtain ⟨_, h⟩ := unless_ok h
        obtain ⟨pair, hpa, h⟩ := except_bind_ok_inv h
        obtain ⟨stateA, wireA⟩ := pair
        cases h
        exact processAlert_wellFormed hpa hinv'
      · cases h
  · split at h
    · obtain ⟨_, h⟩ := if_throw_ok h
      obtain ⟨pair, hpb, h⟩ := except_bind_ok_inv h
      obtain ⟨stateH, wireH⟩ := pair
      cases h
      exact processHandshakeBuffer_wellFormed hpb
        hinv'
    · obtain ⟨_, h⟩ := unless_ok h
      obtain ⟨pair, hpa, h⟩ := except_bind_ok_inv h
      obtain ⟨stateA, wireA⟩ := pair
      cases h
      exact processAlert_wellFormed hpa hinv'
    · cases h

private theorem processRecord_wellFormed {state next : State}
    {record : Record.RawRecord} {plain wire : ByteArray}
    (h : processRecord state record = .ok (next, plain, wire))
    (hinv : state.WellFormed) : next.WellFormed := by
  unfold processRecord at h
  simp only [pure_bind] at h
  split at h <;> split at h <;>
    first
      | (obtain ⟨_, h⟩ := unless_ok h
         cases h
         exact hinv)
      | (obtain ⟨stateP, hfp, h⟩ := except_bind_ok_inv h
         cases h
         exact feedPlaintextHandshake_wellFormed hfp hinv)
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
    · exact processRecords_wellFormed h hinv

theorem feed_wellFormed {state : State} {chunk : ByteArray} {out : Output}
    (h : feed state chunk = .ok out) (hinv : state.WellFormed) :
    out.state.WellFormed := by
  unfold feed at h
  split at h
  · rename_i output hfeed
    cases h
    exact feedWithFailure_wellFormed hfeed hinv
  · cases h

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

/-! ## Transition laws

The conjuncts of `State.WellFormed` are the facts that survive every step. These
are the facts about *individual* transitions: what must have been checked for a
step to be taken at all. -/

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

The mirror of `sealApplication_connected`: outbound, the engine refuses to
protect application data unless the connection is established; inbound, this is
the statement that the caller never *receives* application-data plaintext from
any other state. One lemma per level, each in the combined form "either we were
already connected, or this level produced plaintext — then the successor state
is connected", which is what lets a single induction cover a whole feed, since
`processRecords` accumulates plaintext across records. -/

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

/-- Post-handshake messages do not leave `connected`: the only ones the engine
accepts there are NewSessionTicket (discarded) and KeyUpdate (an epoch change,
not a phase change). -/
private theorem processHandshakeBuffer_connected {state next : State}
    {wire : ByteArray} (h : processHandshakeBuffer state = .ok (next, wire))
    (hc : state.phase = .connected) : next.phase = .connected := by
  unfold processHandshakeBuffer at h
  split at h
  · cases h
  · cases h; exact hc
  · rename_i message rest htake
    have hsize : rest.size < state.handshakeBuffered.size := takeHandshake?_size htake
    simp only [pure_bind] at h
    split at h
    · cases h
    · rename_i hph
      have hph' : state.phase = Phase.waitingEncryptedExtensions := hph
      rw [hc] at hph'; cases hph'
    · rename_i hph
      have hph' : state.phase = Phase.waitingCertificate := hph
      rw [hc] at hph'; cases hph'
    · rename_i hph
      have hph' : state.phase = Phase.waitingCertificateVerify := hph
      rw [hc] at hph'; cases hph'
    · rename_i hph
      have hph' : state.phase = Phase.waitingServerFinished := hph
      rw [hc] at hph'; cases hph'
    · split at h
      · have h2 := processHandshakeBuffer_connected h hc
        exact h2
      · split at h
        · obtain ⟨_, h⟩ := unless_ok h
          split at h
          · cases h
          · rename_i stateK wireK hacc
            split at h
            · cases h
            · rename_i stateF moreWire hnext
              have hbuf : stateK.handshakeBuffered.size <
                  state.handshakeBuffered.size := by
                rw [acceptKeyUpdate_buffered hacc]; exact hsize
              have hck : stateK.phase = Phase.connected := by
                rw [acceptKeyUpdate_phase hacc]; exact hc
              have h2 := processHandshakeBuffer_connected hnext hck
              cases h
              exact h2
        · cases h
  termination_by state.handshakeBuffered.size
  decreasing_by
    all_goals first
      | exact hsize
      | exact hbuf

/-- The delivery point: a protected record hands plaintext up only from the
`applicationData` arm of the `connected` branch. -/
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
  · rename_i hph
    have hc : state.phase = Phase.connected := phase_eq_of_beq hph
    split at h
    · cases h
      exact hc
    · split at h
      · obtain ⟨_, h⟩ := unless_ok h
        cases h
        exact hc
      · obtain ⟨_, h⟩ := if_throw_ok h
        obtain ⟨pair, hpb, h⟩ := except_bind_ok_inv h
        obtain ⟨stateH, wireH⟩ := pair
        cases h
        have h2 := processHandshakeBuffer_connected hpb hc
        exact h2
      · obtain ⟨_, h⟩ := unless_ok h
        obtain ⟨pair, hpa, h⟩ := except_bind_ok_inv h
        obtain ⟨stateA, wireA⟩ := pair
        cases h
        have h2 := processAlert_phase hpa
        exact h2.trans hc
      · cases h
  · rename_i hph
    have hph' : (state.phase == Phase.connected) = false :=
      Bool.eq_false_iff.mpr hph
    split at h
    · obtain ⟨_, h⟩ := if_throw_ok h
      obtain ⟨pair, _, h⟩ := except_bind_ok_inv h
      obtain ⟨stateH, wireH⟩ := pair
      cases h
      rcases hp with hc | hne
      · rw [hc] at hph'; exact absurd hph' (by decide)
      · exact absurd hne (by decide)
    · obtain ⟨_, h⟩ := unless_ok h
      obtain ⟨pair, _, h⟩ := except_bind_ok_inv h
      obtain ⟨stateA, wireA⟩ := pair
      cases h
      rcases hp with hc | hne
      · rw [hc] at hph'; exact absurd hph' (by decide)
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
  · rename_i hph
    have hph' : state.phase = Phase.waitingServerHello := hph
    split at h <;>
      first
        | (obtain ⟨stateP, _, h⟩ := except_bind_ok_inv h
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
        | (obtain ⟨_, h⟩ := unless_ok h
           cases h
           rcases hp with hc | hne
           · rw [hc] at hph'; cases hph'
           · exact absurd hne (by decide))
        | cases h
  all_goals
    first
      | (rename_i hph
         have hph' : state.phase = Phase.connected := hph
         split at h <;>
           first
             | (have h2 := processProtectedRecord_plaintext h (.inl hph')
                exact h2)
             | cases h)
      | (rename_i hph
         split at h <;>
           first
             | (obtain ⟨_, h⟩ := unless_ok h
                cases h
                rcases hp with hc | hne
                · rw [hc] at hph; cases hph
                · exact absurd hne (by decide))
             | (have h2 := processProtectedRecord_plaintext h hp
                exact h2)
             | cases h)

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

private theorem sealFatalAlert_phase {state : State} {description : UInt8}
    {out : Output} (h : sealFatalAlert state description = .ok out) :
    out.state.phase = state.phase := by
  unfold sealFatalAlert at h
  simp only [pure_bind] at h
  split at h
  · cases h
  · obtain ⟨keys, hk, h⟩ := except_bind_ok_inv h
    obtain ⟨sealed, hs, h⟩ := except_bind_ok_inv h
    obtain ⟨next, wire⟩ := sealed
    cases h
    rfl

private theorem sealFatalAlert_plaintext {state : State} {description : UInt8}
    {out : Output} (h : sealFatalAlert state description = .ok out) :
    out.plaintext = ByteArray.empty := by
  unfold sealFatalAlert at h
  simp only [pure_bind] at h
  split at h
  · cases h
  · obtain ⟨keys, hk, h⟩ := except_bind_ok_inv h
    obtain ⟨sealed, hs, h⟩ := except_bind_ok_inv h
    obtain ⟨next, wire⟩ := sealed
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

/-- **The client becomes connected only by verifying the server Finished**
against the transcript through the server's last handshake message, under the
server handshake traffic secret. This is the only transition into
`Phase.connected`. -/
theorem completeServerHandshake_verified {state next : State}
    {message : Handshake.Message} {wire : ByteArray}
    (h : completeServerHandshake state message = .ok (next, wire)) :
    ∃ finished secret,
      Handshake.parseFinished message = .ok finished ∧
        state.serverHandshakeTrafficSecret? = some secret ∧
        constantTimeEq (finishedVerifyData secret (HaclStar.sha256 state.transcript))
            finished.verifyData = true := by
  unfold completeServerHandshake at h
  simp only [pure_bind] at h
  obtain ⟨finished, hfin, h⟩ := except_bind_ok_inv h
  obtain ⟨serverSecret, hsec, h⟩ := except_bind_ok_inv h
  obtain ⟨hverify, h⟩ := unless_ok h
  refine ⟨finished, serverSecret, liftHandshake_ok hfin, ?_, hverify⟩
  unfold requireServerHandshakeTrafficSecret at hsec
  cases hs : state.serverHandshakeTrafficSecret? with
  | none => rw [hs] at hsec; cases hsec
  | some s => rw [hs] at hsec; cases hsec; rfl

/-- **A KeyUpdate installs the structural §7.2 successor epoch**: the peer's
new read traffic secret is derived from the old one by `"traffic upd"`, and its
record sequence number restarts at zero. This does not claim byte inequality
under a hypothetical HKDF collision. -/
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

/-- **The RFC 9846 sending-generation limit is inductive.** Starting at or
below the `2^48 - 1` cap, accepting a KeyUpdate cannot move the client above
it: a requested reciprocal update increments below the cap, and is suppressed
at the cap. The peer's read-side update is independent (see
`acceptKeyUpdate_epoch`). -/
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

/-- **Reciprocal KeyUpdate is suppressed at the RFC 9846 cap.** Once the
client has installed `2^48 - 1` sending generations, accepting any valid
KeyUpdate leaves the write keys and counter untouched and emits no response.
The read epoch still advances, as `acceptKeyUpdate_epoch` proves. -/
theorem acceptKeyUpdate_response_suppressed_at_limit {state next : State}
    {message : Handshake.Message} {wire : ByteArray}
    (hlimit : maxSendingKeyUpdates ≤ state.sendingKeyUpdates)
    (h : acceptKeyUpdate state message = .ok (next, wire)) :
    next.writeKeys? = state.writeKeys? ∧
      next.sendingKeyUpdates = state.sendingKeyUpdates ∧
      wire = ByteArray.empty := by
  unfold acceptKeyUpdate at h
  obtain ⟨_, _, h⟩ := except_bind_ok_inv h
  obtain ⟨_, _, h⟩ := except_bind_ok_inv h
  obtain ⟨_, _, h⟩ := except_bind_ok_inv h
  split at h
  · cases h
    exact ⟨rfl, rfl, rfl⟩
  · simp only [] at h
    split at h
    · cases h
      exact ⟨rfl, rfl, rfl⟩
    · unfold sendKeyUpdateResponse at h
      simp only [] at h
      split at h
      · omega
      · cases h
        exact ⟨rfl, rfl, rfl⟩

/-- Every reciprocal KeyUpdate that actually emits a record increments the
client's sending counter exactly once, and the resulting count remains within
the RFC 9846 limit. -/
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

/-- A syntactically well-framed KeyUpdate whose request byte is neither zero
nor one is an RFC 9846 `illegal_parameter`, not a generic decode error. -/
theorem acceptKeyUpdate_invalid_request_illegalParameter (state : State)
    (message : Handshake.Message)
    (htype : message.msgType = Handshake.keyUpdateType)
    (hsize : message.body.size = 1)
    (hvalue : Handshake.KeyUpdateRequest.ofUInt8? (message.body.get! 0) = none) :
    acceptKeyUpdate state message = .error (.illegalParameter
      s!"invalid KeyUpdate request value {message.body.get! 0}") := by
  have hp : parseKeyUpdateForClient message = .error (.illegalParameter
      s!"invalid KeyUpdate request value {message.body.get! 0}") := by
    unfold parseKeyUpdateForClient
    simp [htype, hsize, hvalue]
  unfold acceptKeyUpdate
  rw [hp]
  rfl

/-- **Accepting the ServerHello extends the transcript by exactly that
message.** -/
theorem acceptServerHello_transcript {state next : State}
    {message : Handshake.Message}
    (h : acceptServerHello state message = .ok next) :
    next.transcript = state.transcript ++ message.encoded := by
  unfold acceptServerHello at h
  simp only [pure_bind] at h
  obtain ⟨_, h⟩ := unless_ok h
  obtain ⟨hello, _, h⟩ := except_bind_ok_inv h
  obtain ⟨_, _, h⟩ := except_bind_ok_inv h
  split at h
  · split at h
    · split at h
      · obtain ⟨writeKeys, _, h⟩ := except_bind_ok_inv h
        obtain ⟨readKeys, _, h⟩ := except_bind_ok_inv h
        cases h
        rfl
      · cases h
    · cases h
  · split at h
    · split at h
      · split at h
        · obtain ⟨writeKeys, _, h⟩ := except_bind_ok_inv h
          obtain ⟨readKeys, _, h⟩ := except_bind_ok_inv h
          cases h
          rfl
        · cases h
      · cases h
    · cases h

/-- **AEAD key--nonce non-reuse across a client connection.** For any successful
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

/-- `run_nonce_nodup` for a single `feed`. -/
theorem feed_nonce_nodup {state : State} {chunk : ByteArray} {out : Output}
    (h : feed state chunk = .ok out) :
    ∃ (aeadKeys : List ByteArray) (keyNonces : List (ByteArray × ByteArray)),
      Record.AeadWriteRun state.writeKeys? out.state.writeKeys? aeadKeys keyNonces ∧
        (aeadKeys.Nodup → keyNonces.Nodup) := by
  obtain ⟨secrets, taggedNonces, hrun⟩ := Record.Extends.run (feed_write h)
  obtain ⟨aeadKeys, keyNonces, haead, _⟩ := hrun.toAeadWriteRun
  exact ⟨aeadKeys, keyNonces, haead, fun hfresh => haead.nodup hfresh⟩

/-! ## The engine installs the RFC 8446 §7.1 epochs

The laws below tie the client's actual key installations to the specification in
`TLS13.KeySchedule.Spec`: at each transition, the epoch secrets the engine
stores are the specification's, derived from the right parent secret, under the
right label, over the right transcript.

As everywhere else, this is *structural* refinement. It is stated for an
arbitrary `Spec.Hkdf` the HACL\* bindings implement, so it says nothing about
what HKDF computes — only that the engine applies it in the RFC's shape. The
empirical half is `Test/HaclKat.lean`'s RFC 8448 vectors; if the two ever
disagree, the vectors are right. -/

open TLS13.KeySchedule

private theorem requireHandshakeSecret_ok {state : State} {secret : ByteArray}
    (h : requireHandshakeSecret state = .ok secret) :
    state.handshakeSecret? = some secret := by
  unfold requireHandshakeSecret at h
  cases hs : state.handshakeSecret? with
  | none => rw [hs] at h; cases h
  | some s => rw [hs] at h; cases h; rfl

/-- The handshake-traffic branch of the diagram, for the values the engine
holds at `acceptServerHello`. -/
private theorem hsEpoch_spec {H : Spec.Hkdf} (hi : Implements H) (inp : Spec.Inputs)
    (shared transcriptHash : ByteArray)
    (hpsk : inp.psk = zeros) (hecdhe : inp.ecdhe = shared)
    (hempty : inp.hash .empty = HaclStar.sha256 ByteArray.empty)
    (hsh : inp.hash .serverHello = transcriptHash) :
    handshakeSecret earlySecret shared (HaclStar.sha256 ByteArray.empty)
        = Spec.secret H inp .handshake ∧
    deriveSecret (handshakeSecret earlySecret shared (HaclStar.sha256 ByteArray.empty))
        "c hs traffic" transcriptHash = Spec.derived H inp .cHsTraffic ∧
    deriveSecret (handshakeSecret earlySecret shared (HaclStar.sha256 ByteArray.empty))
        "s hs traffic" transcriptHash = Spec.derived H inp .sHsTraffic :=
  have hhs := handshakeSecret_node_spec hi inp hpsk hecdhe hempty
  ⟨hhs, deriveSecret_node_spec hi inp .cHsTraffic hhs hsh,
    deriveSecret_node_spec hi inp .sHsTraffic hhs hsh⟩

/-- The application-traffic branch, for the values the engine holds at
`completeServerHandshake`. -/
private theorem apEpoch_spec {H : Spec.Hkdf} (hi : Implements H) (inp : Spec.Inputs)
    (handshake transcriptHash : ByteArray)
    (hhandshake : handshake = Spec.secret H inp .handshake)
    (hempty : inp.hash .empty = HaclStar.sha256 ByteArray.empty)
    (hfin : inp.hash .serverFinished = transcriptHash) :
    deriveSecret (masterSecret handshake (HaclStar.sha256 ByteArray.empty))
        "c ap traffic" transcriptHash = Spec.derived H inp .cApTraffic ∧
    deriveSecret (masterSecret handshake (HaclStar.sha256 ByteArray.empty))
        "s ap traffic" transcriptHash = Spec.derived H inp .sApTraffic :=
  have hms := masterSecret_node_spec hi inp hhandshake hempty
  ⟨deriveSecret_node_spec hi inp .cApTraffic hms hfin,
    deriveSecret_node_spec hi inp .sApTraffic hms hfin⟩

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

/-- **Accepting the ServerHello installs the RFC 8446 §7.1 handshake-traffic
epochs.** There is an (EC)DHE shared secret of hash length such that, for any
key-schedule inputs with no PSK, that shared secret, and these transcript
hashes, the three secrets the client stores are exactly the specification's
`Handshake Secret`, `client_handshake_traffic_secret` and
`server_handshake_traffic_secret`, and the write and read epochs are their §7.3
record-protection states.

Note which transcript goes where: the `"derived"` step feeding the Handshake
Secret binds the **empty** message sequence, while `"c hs traffic"` and
`"s hs traffic"` bind ClientHello…ServerHello — which
`acceptServerHello_transcript` independently identifies as
`state.transcript ++ message.encoded`. -/
theorem acceptServerHello_keySchedule {H : Spec.Hkdf} (hi : Implements H)
    {state next : State} {message : Handshake.Message}
    (h : acceptServerHello state message = .ok next) :
    ∃ ecdhe : ByteArray, ecdhe.size = hashLen ∧
      ∀ inp : Spec.Inputs,
        inp.psk = zeros →
        inp.ecdhe = ecdhe →
        inp.hash .empty = HaclStar.sha256 ByteArray.empty →
        inp.hash .serverHello = HaclStar.sha256 (state.transcript ++ message.encoded) →
        next.handshakeSecret? = some (Spec.secret H inp .handshake) ∧
        next.clientHandshakeTrafficSecret? = some (Spec.derived H inp .cHsTraffic) ∧
        next.serverHandshakeTrafficSecret? = some (Spec.derived H inp .sHsTraffic) ∧
        (∃ wk, next.writeKeys? = some wk ∧
          Record.TrafficKeys.DerivedFrom H wk (Spec.derived H inp .cHsTraffic)) ∧
        (∃ rk, next.readKeys? = some rk ∧
          Record.TrafficKeys.DerivedFrom H rk (Spec.derived H inp .sHsTraffic)) := by
  unfold acceptServerHello at h
  simp only [pure_bind] at h
  obtain ⟨_, h⟩ := unless_ok h
  obtain ⟨hello, _, h⟩ := except_bind_ok_inv h
  obtain ⟨_, _, h⟩ := except_bind_ok_inv h
  split at h
  · split at h
    · rename_i shared _
      split at h
      · rename_i hsize
        obtain ⟨writeKeys, hw, h⟩ := except_bind_ok_inv h
        obtain ⟨readKeys, hr, h⟩ := except_bind_ok_inv h
        cases h
        refine ⟨shared, eq_of_beq hsize, fun inp hpsk hecdhe hempty hsh => ?_⟩
        obtain ⟨h1, h2, h3⟩ := hsEpoch_spec hi inp shared _ hpsk hecdhe hempty hsh
        refine ⟨congrArg some h1, congrArg some h2, congrArg some h3,
          ⟨writeKeys, rfl, ?_⟩, ⟨readKeys, rfl, ?_⟩⟩
        · rw [← h2]; exact Record.deriveTrafficKeys_spec hi (liftRecord_ok hw)
        · rw [← h3]; exact Record.deriveTrafficKeys_spec hi (liftRecord_ok hr)
      · cases h
    · cases h
  · split at h
    · split at h
      · rename_i shared _
        split at h
        · rename_i hsize
          obtain ⟨writeKeys, hw, h⟩ := except_bind_ok_inv h
          obtain ⟨readKeys, hr, h⟩ := except_bind_ok_inv h
          cases h
          refine ⟨shared, eq_of_beq hsize, fun inp hpsk hecdhe hempty hsh => ?_⟩
          obtain ⟨h1, h2, h3⟩ := hsEpoch_spec hi inp shared _ hpsk hecdhe hempty hsh
          refine ⟨congrArg some h1, congrArg some h2, congrArg some h3,
            ⟨writeKeys, rfl, ?_⟩, ⟨readKeys, rfl, ?_⟩⟩
          · rw [← h2]; exact Record.deriveTrafficKeys_spec hi (liftRecord_ok hw)
          · rw [← h3]; exact Record.deriveTrafficKeys_spec hi (liftRecord_ok hr)
        · cases h
      · cases h
    · cases h

/-- **Becoming `connected` installs the RFC 8446 §7.1 application-traffic
epochs.** `completeServerHandshake` is the only transition into
`Phase.connected` (`completeServerHandshake_verified`), so this says: at the
moment the client is established, its write epoch is
`client_application_traffic_secret_0` and its read epoch is
`server_application_traffic_secret_0` — each `Derive-Secret` of the **Master**
Secret (not the Handshake Secret) over the ClientHello…server Finished
transcript, with their §7.3 key/IV/sequence state.

The hypotheses pin the inputs: `hhs` is the handshake secret the engine stored,
which `acceptServerHello_keySchedule` identifies as the specification's, so the
two laws compose into a statement about the whole handshake. -/
theorem completeServerHandshake_keySchedule {H : Spec.Hkdf} (hi : Implements H)
    {state next : State} {message : Handshake.Message} {wire : ByteArray}
    (inp : Spec.Inputs)
    (hempty : inp.hash .empty = HaclStar.sha256 ByteArray.empty)
    (hfin : inp.hash .serverFinished =
      HaclStar.sha256 (state.transcript ++ message.encoded))
    (hhs : state.handshakeSecret? = some (Spec.secret H inp .handshake))
    (h : completeServerHandshake state message = .ok (next, wire)) :
    (∃ wk, next.writeKeys? = some wk ∧
      Record.TrafficKeys.DerivedFrom H wk (Spec.derived H inp .cApTraffic)) ∧
    (∃ rk, next.readKeys? = some rk ∧
      Record.TrafficKeys.DerivedFrom H rk (Spec.derived H inp .sApTraffic)) := by
  unfold completeServerHandshake at h
  simp only [pure_bind] at h
  obtain ⟨finished, _, h⟩ := except_bind_ok_inv h
  obtain ⟨serverSecret, _, h⟩ := except_bind_ok_inv h
  split at h
  case isFalse => cases h
  obtain ⟨handshake, hhsec, h⟩ := except_bind_ok_inv h
  obtain ⟨clientApplicationKeys, hcak, h⟩ := except_bind_ok_inv h
  obtain ⟨serverApplicationKeys, hsak, h⟩ := except_bind_ok_inv h
  obtain ⟨clientHandshakeSecret, _, h⟩ := except_bind_ok_inv h
  obtain ⟨clientFinished, _, h⟩ := except_bind_ok_inv h
  obtain ⟨handshakeWriteKeys, hk, h⟩ := except_bind_ok_inv h
  obtain ⟨sealed, hs, h⟩ := except_bind_ok_inv h
  obtain ⟨advancedKeys, finishedWire⟩ := sealed
  have hhandshake : handshake = Spec.secret H inp .handshake := by
    rw [requireHandshakeSecret_ok hhsec] at hhs
    exact Option.some.inj hhs
  obtain ⟨hc, hsv⟩ := apEpoch_spec hi inp handshake _ hhandshake hempty hfin
  have hgoal : ∀ n : State, n.writeKeys? = some clientApplicationKeys →
      n.readKeys? = some serverApplicationKeys →
      (∃ wk, n.writeKeys? = some wk ∧
        Record.TrafficKeys.DerivedFrom H wk (Spec.derived H inp .cApTraffic)) ∧
      (∃ rk, n.readKeys? = some rk ∧
        Record.TrafficKeys.DerivedFrom H rk (Spec.derived H inp .sApTraffic)) := by
    refine fun n hw hr => ⟨⟨clientApplicationKeys, hw, ?_⟩, ⟨serverApplicationKeys, hr, ?_⟩⟩
    · rw [← hc]; exact Record.deriveTrafficKeys_spec hi (liftRecord_ok hcak)
    · rw [← hsv]; exact Record.deriveTrafficKeys_spec hi (liftRecord_ok hsak)
  split at h
  · cases h; exact hgoal _ rfl rfl
  · obtain ⟨compatibilityWire, _, h⟩ := except_bind_ok_inv h
    cases h
    exact hgoal _ rfl rfl

private theorem sendKeyUpdateResponse_handshakeSecret {state next : State}
    {wire : ByteArray} (h : sendKeyUpdateResponse state = .ok (next, wire)) :
    next.handshakeSecret? = state.handshakeSecret? := by
  unfold sendKeyUpdateResponse at h
  split at h
  · obtain ⟨_, _, h⟩ := except_bind_ok_inv h
    obtain ⟨keys, _, h⟩ := except_bind_ok_inv h
    obtain ⟨sealed, _, h⟩ := except_bind_ok_inv h
    obtain ⟨advancedKeys, wireBytes⟩ := sealed
    obtain ⟨updatedKeys, _, h⟩ := except_bind_ok_inv h
    cases h
    rfl
  · cases h
    rfl

private theorem acceptKeyUpdate_handshakeSecret {state next : State}
    {message : Handshake.Message} {wire : ByteArray}
    (h : acceptKeyUpdate state message = .ok (next, wire)) :
    next.handshakeSecret? = state.handshakeSecret? := by
  unfold acceptKeyUpdate at h
  obtain ⟨_, _, h⟩ := except_bind_ok_inv h
  obtain ⟨_, _, h⟩ := except_bind_ok_inv h
  obtain ⟨_, _, h⟩ := except_bind_ok_inv h
  split at h
  · cases h; rfl
  · simp only [] at h
    split at h
    · cases h; rfl
    · rw [sendKeyUpdateResponse_handshakeSecret h]

/-- **The client's whole encrypted server flight installs the RFC 8446 §7.1
application epochs.** `processHandshakeBuffer` consumes EncryptedExtensions,
Certificate, CertificateVerify and the server Finished in one call. Either it
did not reach the Finished — and the handshake secret is untouched, so the
epochs are unchanged — or it did, and there is a definite transcript (the
ClientHello…server Finished sequence the engine accumulated) such that for any
key-schedule inputs agreeing with the engine on the empty and
ClientHello…server Finished transcript hashes and on the handshake secret the
state carried, the installed write and read epochs are
`client_application_traffic_secret_0` and
`server_application_traffic_secret_0`.

Composed with `acceptServerHello_keySchedule` — which supplies exactly that
handshake secret, as the specification's — this links a real run of the client
from ServerHello to established connection to the RFC's derivation tree. What
is still not mechanised is the transport plumbing between `feed` and this
function (record framing, decryption and dispatch), which moves bytes and
touches no key state. -/
theorem processHandshakeBuffer_keySchedule {H : Spec.Hkdf} (hi : Implements H)
    {state next : State} {wire : ByteArray}
    (h : processHandshakeBuffer state = .ok (next, wire)) :
    next.handshakeSecret? = state.handshakeSecret? ∨
    ∃ transcript : ByteArray, ∀ inp : Spec.Inputs,
      inp.hash .empty = HaclStar.sha256 ByteArray.empty →
      inp.hash .serverFinished = HaclStar.sha256 transcript →
      state.handshakeSecret? = some (Spec.secret H inp .handshake) →
      (∃ wk, next.writeKeys? = some wk ∧
        Record.TrafficKeys.DerivedFrom H wk (Spec.derived H inp .cApTraffic)) ∧
      (∃ rk, next.readKeys? = some rk ∧
        Record.TrafficKeys.DerivedFrom H rk (Spec.derived H inp .sApTraffic)) := by
  unfold processHandshakeBuffer at h
  split at h
  · cases h
  · cases h; exact Or.inl rfl
  · rename_i message rest htake
    have hsize : rest.size < state.handshakeBuffered.size := takeHandshake?_size htake
    simp only [pure_bind] at h
    split at h
    · cases h
    · obtain ⟨_, h⟩ := unless_ok h
      obtain ⟨_, _, h⟩ := except_bind_ok_inv h
      obtain ⟨alpn, _, h⟩ := except_bind_ok_inv h
      split at h
      · obtain ⟨_, h⟩ := unless_ok h
        have hw := processHandshakeBuffer_keySchedule hi h
        exact hw
      · have hw := processHandshakeBuffer_keySchedule hi h
        exact hw
    · obtain ⟨_, h⟩ := unless_ok h
      obtain ⟨_, _, h⟩ := except_bind_ok_inv h
      obtain ⟨_, _, h⟩ := except_bind_ok_inv h
      have hw := processHandshakeBuffer_keySchedule hi h
      exact hw
    · obtain ⟨_, h⟩ := unless_ok h
      obtain ⟨_, _, h⟩ := except_bind_ok_inv h
      split at h
      · obtain ⟨_, _, h⟩ := except_bind_ok_inv h
        obtain ⟨_, h⟩ := unless_ok h
        obtain ⟨_, h⟩ := unless_ok h
        have hw := processHandshakeBuffer_keySchedule hi h
        exact hw
      · cases h
    · obtain ⟨_, h⟩ := unless_ok h
      obtain ⟨_, h⟩ := unless_ok h
      exact Or.inr ⟨state.transcript ++ message.encoded, fun inp h1 h2 h3 =>
        completeServerHandshake_keySchedule hi inp h1 h2 h3 h⟩
    · split at h
      · have hw := processHandshakeBuffer_keySchedule hi h
        exact hw
      · split at h
        · obtain ⟨_, h⟩ := unless_ok h
          split at h
          · cases h
          · rename_i stateK wireK hacc
            split at h
            · cases h
            · rename_i stateF moreWire hnext
              cases h
              have hbuf : stateK.handshakeBuffered.size <
                  state.handshakeBuffered.size := by
                rw [acceptKeyUpdate_buffered hacc]; exact hsize
              have hk := acceptKeyUpdate_handshakeSecret hacc
              rcases processHandshakeBuffer_keySchedule hi hnext with hl | ⟨t, ht⟩
              · exact Or.inl (by rw [hl, hk])
              · exact Or.inr ⟨t, fun inp h1 h2 h3 => ht inp h1 h2 (by rw [hk]; exact h3)⟩
        · cases h
  termination_by state.handshakeBuffered.size
  decreasing_by
    all_goals first
      | exact hsize
      | exact hbuf

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
  obtain ⟨_, _, h⟩ := except_bind_ok_inv h
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
the structural fact that the engine does not choose those epochs freely:
`acceptServerHello` installs `client_handshake_traffic_secret`,
`completeServerHandshake` replaces it with
`client_application_traffic_secret_0`, and every KeyUpdate advances that node
under `"traffic upd"`. Thus the epoch descriptors of a run are strictly
increasing nodes of the RFC 8446 §7.1 / §7.2 schedule (`Spec.Epoch.Lt`).

`run_nonce_trace_spec` returns that schedule witness and traffic-secret
`WriteRun` alongside an `AeadWriteRun` over the actual key--nonce pairs; the two
traces have the same nonce sequence. It retains the finite-run implication
`aeadKeys.Nodup → keyNonces.Nodup`: structural nodes can be distinct while
their fixed-size derived keys collide, so byte distinctness is a cryptographic
condition, not a deterministic consequence of the schedule. A caller who
clones a `State` is still outside the theorem; single-threading remains the
caller's obligation. -/

/-- The label a client's write epoch is derived under in a given phase: RFC 8446
§7.1's `"c hs traffic"` while the handshake runs, `"c ap traffic"` once the
connection is established. -/
def writeEpochLabel : Phase → Spec.Label
  | .connected => .cApTraffic
  | _ => .cHsTraffic

theorem writeEpochLabel_valid (p : Phase) :
    writeEpochLabel p ≠ Spec.Label.trafficUpd := by
  cases p <;> (intro hc; cases hc)

theorem writeEpochLabel_of_ne_connected {p : Phase} (h : p ≠ .connected) :
    writeEpochLabel p = Spec.Label.cHsTraffic := by
  cases p <;> first | rfl | exact absurd rfl h

/-- **Which node of the key schedule a client's write state is in.** `none`
before the first epoch is installed; otherwise the §7.1 derivation the write
traffic secret came from, plus the number of §7.2 KeyUpdates since. The phase
fixes the label: a handshake-phase client writes under `"c hs traffic"`, an
established one under `"c ap traffic"`. -/
def State.WriteEpoch (H : Spec.Hkdf) (state : State) (o : Option Spec.Epoch) : Prop :=
  Record.EpochOf H o state.writeKeys? ∧
    ∀ e, o = some e → e.label = writeEpochLabel state.phase

theorem State.WriteEpoch.valid {H : Spec.Hkdf} {state : State}
    {o : Option Spec.Epoch} (h : state.WriteEpoch H o) :
    ∀ e, o = some e → e.Valid := by
  intro e he
  show e.label ≠ Spec.Label.trafficUpd
  rw [h.2 e he]
  exact writeEpochLabel_valid _

/-- The write side of one engine step, refined by the key schedule: it maps the
epoch the connection was in to the epoch it ends in, and the epochs it abandoned
on the way join the run's epoch list in strictly increasing order. `SpecEffect`
composes exactly as `WriteEffect` does. -/
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
    (hp : writeEpochLabel after.phase = writeEpochLabel before.phase)
    (hx : Record.WithinEpoch H before.writeKeys? after.writeKeys?) :
    SpecEffect H before after := by
  intro o ho
  obtain ⟨ha, hs⟩ := hx.apply ho.1
  exact ⟨o, ⟨ha, fun e he => by rw [hp]; exact ho.2 e he⟩, hs⟩

/-- Prefix a step with a state change that touches neither the write keys nor
the phase's epoch label — which is what every field the engine updates between
epochs (buffers, transcript, read keys, flags) amounts to. -/
theorem SpecEffect.of_eq {H : Spec.Hkdf} {a b c : State} (h : SpecEffect H b c)
    (hw : b.writeKeys? = a.writeKeys?)
    (hp : writeEpochLabel b.phase = writeEpochLabel a.phase) :
    SpecEffect H a c := by
  intro o ho
  have ho' : b.WriteEpoch H o :=
    ⟨by rw [hw]; exact ho.1, fun e he => by rw [hp]; exact ho.2 e he⟩
  obtain ⟨o', ho'', hx⟩ := h o ho'
  rw [hw] at hx
  exact ⟨o', ho'', hx⟩

theorem sealFatalAlert_epochs {H : Spec.Hkdf} {state : State} {description : UInt8}
    {out : Output} (h : sealFatalAlert state description = .ok out) :
    SpecEffect H state out.state := by
  unfold sealFatalAlert at h
  simp only [pure_bind] at h
  split at h
  · cases h
  · obtain ⟨keys, hk, h⟩ := except_bind_ok_inv h
    obtain ⟨sealed, hs, h⟩ := except_bind_ok_inv h
    obtain ⟨next, wire⟩ := sealed
    cases h
    refine SpecEffect.within rfl ?_
    show Record.WithinEpoch H state.writeKeys? (some next)
    rw [requireWriteKeys_ok hk]
    exact Record.WithinEpoch.of_seal (liftRecord_ok hs)

private theorem emitCloseNotify_epochs {H : Spec.Hkdf} {state next : State}
    {wire : ByteArray} (h : emitCloseNotify state = .ok (next, wire)) :
    SpecEffect H state next := by
  unfold emitCloseNotify at h
  split at h
  · cases h; exact SpecEffect.within rfl (Record.WithinEpoch.refl _)
  · obtain ⟨keys, hk, h⟩ := except_bind_ok_inv h
    obtain ⟨sealed, hs, h⟩ := except_bind_ok_inv h
    obtain ⟨sealedKeys, wireBytes⟩ := sealed
    cases h
    refine SpecEffect.within rfl ?_
    show Record.WithinEpoch H state.writeKeys? (some sealedKeys)
    rw [requireWriteKeys_ok hk]
    exact Record.WithinEpoch.of_seal (liftRecord_ok hs)

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
      · cases h; exact SpecEffect.within rfl (Record.WithinEpoch.refl _)
      · obtain ⟨keys, hk, h⟩ := except_bind_ok_inv h
        obtain ⟨sealed, hs, h⟩ := except_bind_ok_inv h
        obtain ⟨nextKeys, records⟩ := sealed
        cases h
        refine SpecEffect.within rfl ?_
        show Record.WithinEpoch H state.writeKeys? (some nextKeys)
        rw [requireWriteKeys_ok hk]
        exact sealChunks_epochs hs
  · cases h

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
      exact SpecEffect.within rfl (Record.WithinEpoch.refl _)
  · split at h
    · cases h
      exact SpecEffect.within rfl (Record.WithinEpoch.refl _)
    · cases h

/-- **A KeyUpdate response moves the write side to the §7.2 successor epoch.**
The reciprocal KeyUpdate is sealed under the old epoch — so that record is
accounted for in the old epoch's nonce budget — and only then is the traffic
secret rolled forward, to `HKDF-Expand-Label(old, "traffic upd", "", 32)`, which
is a strictly later node of the schedule. -/
private theorem sendKeyUpdateResponse_epochs {H : Spec.Hkdf} (hi : Implements H)
    {state next : State} {wire : ByteArray}
    (h : sendKeyUpdateResponse state = .ok (next, wire)) : SpecEffect H state next := by
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
    exact SpecEffect.within rfl (Record.WithinEpoch.refl _)

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
    exact SpecEffect.within rfl (Record.WithinEpoch.refl _)
  · simp only [] at h
    split at h
    · cases h
      exact SpecEffect.within rfl (Record.WithinEpoch.refl _)
    · have hw := sendKeyUpdateResponse_epochs hi h
      exact SpecEffect.of_eq hw rfl rfl

/-- **Accepting the ServerHello installs the connection's first write epoch.**
The `waitingServerHello` clause of `State.WellFormed` is what makes this an
installation rather than a replacement: there was no epoch to abandon, so no
epoch can be revisited here. -/
private theorem acceptServerHello_epochs {H : Spec.Hkdf} (hi : Implements H)
    {state next : State} {message : Handshake.Message}
    (h : acceptServerHello state message = .ok next) (hinv : state.WellFormed) :
    SpecEffect H state next := by
  unfold acceptServerHello at h
  simp only [pure_bind] at h
  obtain ⟨hph, h⟩ := unless_ok h
  have hnone : state.writeKeys? = none := hinv.noWriteKeys (phase_eq_of_beq hph)
  have hgoal : ∀ (parent ctx : ByteArray) (wk : Record.TrafficKeys) (n : State),
      Record.deriveTrafficKeys
          (TLS13.KeySchedule.deriveSecret parent "c hs traffic" ctx) = .ok wk →
      n.writeKeys? = some wk →
      writeEpochLabel n.phase = Spec.Label.cHsTraffic →
      SpecEffect H state n := by
    intro parent ctx wk n hd hwk hlab o ho
    have ho' : o = none := Record.EpochOf.none_inv (by rw [← hnone]; exact ho.1)
    subst ho'
    refine ⟨some ⟨parent, .cHsTraffic, ctx, 0⟩, ⟨?_, fun e he => ?_⟩, ?_⟩
    · rw [hwk]
      exact Record.EpochOf.intro
        ((Record.deriveTrafficKeys_spec hi hd).secret_eq.trans
          (TLS13.KeySchedule.deriveSecret_spec hi parent .cHsTraffic ctx))
    · cases he
      exact hlab.symm
    · rw [hnone, hwk]
      exact Record.SpecExtends.install
  obtain ⟨hello, _, h⟩ := except_bind_ok_inv h
  obtain ⟨_, _, h⟩ := except_bind_ok_inv h
  split at h
  · split at h
    · split at h
      · obtain ⟨writeKeys, hw, h⟩ := except_bind_ok_inv h
        obtain ⟨readKeys, hr, h⟩ := except_bind_ok_inv h
        cases h
        exact hgoal _ _ _ _ (liftRecord_ok hw) rfl rfl
      · cases h
    · cases h
  · split at h
    · split at h
      · split at h
        · obtain ⟨writeKeys, hw, h⟩ := except_bind_ok_inv h
          obtain ⟨readKeys, hr, h⟩ := except_bind_ok_inv h
          cases h
          exact hgoal _ _ _ _ (liftRecord_ok hw) rfl rfl
        · cases h
      · cases h
    · cases h

/-- **Becoming established moves the write side from the handshake epoch to the
application epoch.** `"c ap traffic"` sits at a later stage of the schedule than
`"c hs traffic"` (`Spec.Label.stage`), so the new epoch is strictly later than
the old one however many records the handshake epoch protected. The state
invariant supplies the missing half: a client holding a handshake secret is not
already established, so the epoch it is leaving really is a handshake epoch. -/
private theorem completeServerHandshake_epochs {H : Spec.Hkdf} (hi : Implements H)
    {state next : State} {message : Handshake.Message} {wire : ByteArray}
    (h : completeServerHandshake state message = .ok (next, wire))
    (hinv : state.WellFormed) : SpecEffect H state next := by
  unfold completeServerHandshake at h
  simp only [pure_bind] at h
  obtain ⟨finished, _, h⟩ := except_bind_ok_inv h
  obtain ⟨serverSecret, _, h⟩ := except_bind_ok_inv h
  split at h
  case isFalse => cases h
  obtain ⟨handshake, hhsec, h⟩ := except_bind_ok_inv h
  obtain ⟨clientApplicationKeys, hcak, h⟩ := except_bind_ok_inv h
  obtain ⟨serverApplicationKeys, hsak, h⟩ := except_bind_ok_inv h
  obtain ⟨clientHandshakeSecret, _, h⟩ := except_bind_ok_inv h
  obtain ⟨clientFinished, _, h⟩ := except_bind_ok_inv h
  obtain ⟨handshakeWriteKeys, hk, h⟩ := except_bind_ok_inv h
  obtain ⟨sealed, hs, h⟩ := except_bind_ok_inv h
  obtain ⟨advancedKeys, finishedWire⟩ := sealed
  have hnc : state.phase ≠ .connected := by
    intro hc
    have hnone := (hinv.connected hc).2.2.1
    rw [requireHandshakeSecret_ok hhsec] at hnone
    cases hnone
  have hgoal : ∀ (parent ctx : ByteArray) (wk : Record.TrafficKeys) (n : State),
      Record.deriveTrafficKeys
          (TLS13.KeySchedule.deriveSecret parent "c ap traffic" ctx) = .ok wk →
      n.writeKeys? = some wk →
      writeEpochLabel n.phase = Spec.Label.cApTraffic → SpecEffect H state n := by
    intro parent ctx wk n hd hwk hlab o ho
    have hw : state.writeKeys? = some handshakeWriteKeys := requireWriteKeys_ok hk
    have hE : Record.EpochOf H o (some handshakeWriteKeys) := by rw [← hw]; exact ho.1
    obtain ⟨e, rfl, hsec⟩ := Record.EpochOf.some_inv hE
    have hadv : advancedKeys.secret = e.secret H := by
      rw [Record.seal_secret_eq (liftRecord_ok hs)]; exact hsec
    have hlt : e.Lt ⟨parent, Spec.Label.cApTraffic, ctx, 0⟩ := by
      refine Or.inl ?_
      rw [show e.label = Spec.Label.cHsTraffic from
        (ho.2 e rfl).trans (writeEpochLabel_of_ne_connected hnc)]
      exact (by decide : (1 : Nat) < 2)
    refine ⟨some ⟨parent, .cApTraffic, ctx, 0⟩, ⟨?_, fun e' he' => ?_⟩, ?_⟩
    · rw [hwk]
      exact Record.EpochOf.intro
        ((Record.deriveTrafficKeys_spec hi hd).secret_eq.trans
          (TLS13.KeySchedule.deriveSecret_spec hi parent .cApTraffic ctx))
    · cases he'
      exact hlab.symm
    · rw [hw, hwk]
      exact (Record.SpecExtends.of_seal (liftRecord_ok hs)).trans
        (Record.SpecExtends.rekey hadv (ho.valid e rfl) hlt)
  split at h
  · cases h; exact hgoal _ _ _ _ (liftRecord_ok hcak) rfl rfl
  · obtain ⟨compatibilityWire, _, h⟩ := except_bind_ok_inv h
    cases h
    exact hgoal _ _ _ _ (liftRecord_ok hcak) rfl rfl

private theorem processHandshakeBuffer_epochs {H : Spec.Hkdf} (hi : Implements H)
    {state next : State} {wire : ByteArray}
    (h : processHandshakeBuffer state = .ok (next, wire))
    (hinv : state.WellFormed) : SpecEffect H state next := by
  unfold processHandshakeBuffer at h
  split at h
  · cases h
  · cases h; exact SpecEffect.within rfl (Record.WithinEpoch.refl _)
  · rename_i message rest htake
    have hsize : rest.size < state.handshakeBuffered.size := takeHandshake?_size htake
    simp only [pure_bind] at h
    split at h
    · cases h
    · rename_i hph
      have hph' : writeEpochLabel state.phase = Spec.Label.cHsTraffic := by
        rw [show state.phase = Phase.waitingEncryptedExtensions from hph]; rfl
      obtain ⟨_, h⟩ := unless_ok h
      obtain ⟨_, _, h⟩ := except_bind_ok_inv h
      obtain ⟨alpn, _, h⟩ := except_bind_ok_inv h
      split at h
      · obtain ⟨_, h⟩ := unless_ok h
        have hw := processHandshakeBuffer_epochs hi h
          ⟨fun hc => (by cases hc), fun hp => (by cases hp)⟩
        exact SpecEffect.of_eq hw rfl hph'.symm
      · have hw := processHandshakeBuffer_epochs hi h
          ⟨fun hc => (by cases hc), fun hp => (by cases hp)⟩
        exact SpecEffect.of_eq hw rfl hph'.symm
    · rename_i hph
      have hph' : writeEpochLabel state.phase = Spec.Label.cHsTraffic := by
        rw [show state.phase = Phase.waitingCertificate from hph]; rfl
      obtain ⟨_, h⟩ := unless_ok h
      obtain ⟨_, _, h⟩ := except_bind_ok_inv h
      obtain ⟨_, _, h⟩ := except_bind_ok_inv h
      have hw := processHandshakeBuffer_epochs hi h
        ⟨fun hc => (by cases hc), fun hp => (by cases hp)⟩
      exact SpecEffect.of_eq hw rfl hph'.symm
    · rename_i hph
      have hph' : writeEpochLabel state.phase = Spec.Label.cHsTraffic := by
        rw [show state.phase = Phase.waitingCertificateVerify from hph]; rfl
      obtain ⟨_, h⟩ := unless_ok h
      obtain ⟨_, _, h⟩ := except_bind_ok_inv h
      split at h
      · obtain ⟨_, _, h⟩ := except_bind_ok_inv h
        obtain ⟨_, h⟩ := unless_ok h
        obtain ⟨_, h⟩ := unless_ok h
        have hw := processHandshakeBuffer_epochs hi h
          ⟨fun hc => (by cases hc), fun hp => (by cases hp)⟩
        exact SpecEffect.of_eq hw rfl hph'.symm
      · cases h
    · obtain ⟨_, h⟩ := unless_ok h
      obtain ⟨_, h⟩ := unless_ok h
      have hw := completeServerHandshake_epochs hi h
        (wellFormed_transfer hinv rfl (.inl rfl) (.inl rfl) rfl rfl rfl rfl)
      exact SpecEffect.of_eq hw rfl rfl
    · split at h
      · have hw := processHandshakeBuffer_epochs hi h
          (wellFormed_transfer hinv rfl (.inl rfl) (.inl rfl) rfl rfl rfl rfl)
        exact SpecEffect.of_eq hw rfl rfl
      · split at h
        · obtain ⟨_, h⟩ := unless_ok h
          split at h
          · cases h
          · rename_i stateK wireK hacc
            split at h
            · cases h
            · rename_i stateF moreWire hnext
              cases h
              have hbuf : stateK.handshakeBuffered.size <
                  state.handshakeBuffered.size := by
                rw [acceptKeyUpdate_buffered hacc]; exact hsize
              have hinvK := acceptKeyUpdate_wellFormed hacc
                (wellFormed_transfer hinv rfl (.inl rfl) (.inl rfl) rfl rfl rfl rfl)
              have h1 := acceptKeyUpdate_epochs hi hacc
              have h2 := processHandshakeBuffer_epochs hi hnext hinvK
              exact SpecEffect.of_eq (SpecEffect.trans h1 h2) rfl rfl
        · cases h
  termination_by state.handshakeBuffered.size
  decreasing_by
    all_goals first
      | exact hsize
      | exact hbuf

private theorem feedPlaintextHandshake_epochs {H : Spec.Hkdf} (hi : Implements H)
    {state next : State} {fragment : ByteArray}
    (h : feedPlaintextHandshake state fragment = .ok next)
    (hinv : state.WellFormed) : SpecEffect H state next := by
  unfold feedPlaintextHandshake at h
  simp only [pure_bind] at h
  obtain ⟨_, h⟩ := if_throw_ok h
  obtain ⟨framed, _, h⟩ := except_bind_ok_inv h
  split at h
  · split at h
    · have hw := acceptServerHello_epochs hi h
        (wellFormed_transfer hinv rfl (.inl rfl) (.inl rfl) rfl rfl rfl rfl)
      exact SpecEffect.of_eq hw rfl rfl
    · cases h
  · cases h; exact SpecEffect.within rfl (Record.WithinEpoch.refl _)

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
    wellFormed_transfer hinv rfl (.inl rfl)
      (.inr ⟨⟨_, rfl⟩, requireReadKeys_isSome hrk⟩) rfl rfl rfl rfl
  refine SpecEffect.of_eq (b := { state with readKeys? := some nextReadKeys }) ?_ rfl rfl
  split at h
  · split at h
    · cases h
      exact SpecEffect.within rfl (Record.WithinEpoch.refl _)
    · split at h
      · obtain ⟨_, h⟩ := unless_ok h
        cases h
        exact SpecEffect.within rfl (Record.WithinEpoch.refl _)
      · obtain ⟨_, h⟩ := if_throw_ok h
        obtain ⟨pair, hpb, h⟩ := except_bind_ok_inv h
        obtain ⟨stateH, wireH⟩ := pair
        cases h
        have hw := processHandshakeBuffer_epochs hi hpb
          (wellFormed_transfer hinv' rfl (.inl rfl) (.inl rfl) rfl rfl rfl rfl)
        exact SpecEffect.of_eq hw rfl rfl
      · obtain ⟨_, h⟩ := unless_ok h
        obtain ⟨pair, hpa, h⟩ := except_bind_ok_inv h
        obtain ⟨stateA, wireA⟩ := pair
        cases h
        have hw := processAlert_epochs (H := H) hpa
        exact hw
      · cases h
  · split at h
    · obtain ⟨_, h⟩ := if_throw_ok h
      obtain ⟨pair, hpb, h⟩ := except_bind_ok_inv h
      obtain ⟨stateH, wireH⟩ := pair
      cases h
      have hw := processHandshakeBuffer_epochs hi hpb
        (wellFormed_transfer hinv' rfl (.inl rfl) (.inl rfl) rfl rfl rfl rfl)
      exact SpecEffect.of_eq hw rfl rfl
    · obtain ⟨_, h⟩ := unless_ok h
      obtain ⟨pair, hpa, h⟩ := except_bind_ok_inv h
      obtain ⟨stateA, wireA⟩ := pair
      cases h
      have hw := processAlert_epochs (H := H) hpa
      exact hw
    · cases h

private theorem processRecord_epochs {H : Spec.Hkdf} (hi : Implements H)
    {state next : State} {record : Record.RawRecord} {plain wire : ByteArray}
    (h : processRecord state record = .ok (next, plain, wire))
    (hinv : state.WellFormed) : SpecEffect H state next := by
  unfold processRecord at h
  simp only [pure_bind] at h
  split at h <;> split at h <;>
    first
      | (obtain ⟨_, h⟩ := unless_ok h
         cases h
         exact SpecEffect.within rfl (Record.WithinEpoch.refl _))
      | (obtain ⟨stateP, hfp, h⟩ := except_bind_ok_inv h
         cases h
         have hw := feedPlaintextHandshake_epochs hi hfp hinv
         exact hw)
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
      exact SpecEffect.within rfl (Record.WithinEpoch.refl _)
  | cons record rest ih =>
      intro state plaintext wireBytes out h hinv
      unfold processRecords at h
      split at h
      · cases h
        exact SpecEffect.within rfl (Record.WithinEpoch.refl _)
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
    exact SpecEffect.within rfl (Record.WithinEpoch.refl _)
  · split at h
    · cases h
    · have hw := processRecords_epochs hi h hinv
      exact hw

theorem feed_epochs {H : Spec.Hkdf} (hi : Implements H) {state : State}
    {chunk : ByteArray} {out : Output} (h : feed state chunk = .ok out)
    (hinv : state.WellFormed) : SpecEffect H state out.state := by
  unfold feed at h
  split at h
  · rename_i output hfeed
    cases h
    exact feedWithFailure_epochs hi hfeed hinv
  · cases h

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
      exact SpecEffect.within rfl (Record.WithinEpoch.refl _)
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

/-- A client that has not yet accepted the ServerHello is in no epoch at all. -/
private theorem writeEpoch_start {H : Spec.Hkdf} {state : State}
    (hinv : state.WellFormed) (hph : state.phase = .waitingServerHello) :
    state.WriteEpoch H none :=
  ⟨by rw [hinv.noWriteKeys hph]; exact Record.EpochOf.idle, fun e he => by cases he⟩

/-- **A client's finite AEAD nonce trace, refined by the key schedule.** For any
run of a client that has not yet accepted the ServerHello — in particular a
client from `start` — the traffic-secret tags form a strictly increasing RFC
8446 §7.1 / §7.2 schedule, while a parallel executable trace records the
concrete AEAD key used with every nonce. The traces have the same nonce sequence,
and the actual `(key, nonce)` pairs are duplicate-free under the explicit
finite-run condition `aeadKeys.Nodup`. -/
theorem run_nonce_trace_spec {H : Spec.Hkdf} (hi : Implements H)
    {ops : List Op} {state : State}
    {out : Output} (hinv : state.WellFormed)
    (hph : state.phase = .waitingServerHello) (h : run state ops = .ok out) :
    ∃ secrets taggedNonces aeadKeys keyNonces,
      Record.WriteRun state.writeKeys? out.state.writeKeys? secrets taggedNonces ∧
        Record.EpochsFrom H none secrets ∧
        Record.AeadWriteRun state.writeKeys? out.state.writeKeys?
          aeadKeys keyNonces ∧
        keyNonces.map Prod.snd = taggedNonces.map Prod.snd ∧
        (aeadKeys.Nodup → keyNonces.Nodup) := by
  obtain ⟨o', ho', hx⟩ := run_epochs hi h hinv none (writeEpoch_start hinv hph)
  exact hx.finite_nonce_trace ho'.1 ho'.valid

/-- `run_nonce_trace_spec` for a single `feed`. -/
theorem feed_nonce_trace_spec {H : Spec.Hkdf} (hi : Implements H)
    {state : State} {chunk : ByteArray}
    {out : Output} (hinv : state.WellFormed)
    (hph : state.phase = .waitingServerHello) (h : feed state chunk = .ok out) :
    ∃ secrets taggedNonces aeadKeys keyNonces,
      Record.WriteRun state.writeKeys? out.state.writeKeys? secrets taggedNonces ∧
        Record.EpochsFrom H none secrets ∧
        Record.AeadWriteRun state.writeKeys? out.state.writeKeys?
          aeadKeys keyNonces ∧
        keyNonces.map Prod.snd = taggedNonces.map Prod.snd ∧
        (aeadKeys.Nodup → keyNonces.Nodup) := by
  obtain ⟨o', ho', hx⟩ := feed_epochs hi h hinv none (writeEpoch_start hinv hph)
  exact hx.finite_nonce_trace ho'.1 ho'.valid

/-- The finite, schedule-refined nonce trace for a client driven from `start`. -/
theorem start_run_nonce_trace_spec {H : Spec.Hkdf} (hi : Implements H)
    {config : Config} {ops : List Op}
    {started out : Output} (hstart : start config = .ok started)
    (h : run started.state ops = .ok out) :
    ∃ secrets taggedNonces aeadKeys keyNonces,
      Record.WriteRun started.state.writeKeys? out.state.writeKeys?
          secrets taggedNonces ∧
        Record.EpochsFrom H none secrets ∧
        Record.AeadWriteRun started.state.writeKeys? out.state.writeKeys?
          aeadKeys keyNonces ∧
        keyNonces.map Prod.snd = taggedNonces.map Prod.snd ∧
        (aeadKeys.Nodup → keyNonces.Nodup) :=
  run_nonce_trace_spec hi (start_wellFormed hstart) (start_phase hstart) h

/-! ## Threading the key-schedule linkage out to `feed`

`processHandshakeBuffer_keySchedule` links the *whole encrypted server flight* to
the RFC 8446 §7.1 application epochs, but `processHandshakeBuffer` is an internal
function. `feed_keySchedule` below states the same guarantee at the API boundary
a caller actually uses, by threading the link out through `processRecords`,
`processRecord` and `processProtectedRecord` — the transport plumbing, which
moves bytes and touches no key state.

One thing genuinely changes on the way out. A single `feed` may carry the server
Finished *and* a post-handshake KeyUpdate, in separate records; by the time the
feed returns, the epochs installed at establishment may already have been rolled
forward under `"traffic upd"`. The statement therefore concludes that the final
epochs are `Spec.trafficIter H (…) n` — the §7.1 application secrets after `n`
§7.2 updates, with `n = 0` exactly when no KeyUpdate followed in the same
chunk — and keeps the §7.3 key/IV content via `TrafficKeys.ProtectsWith`, which
is `DerivedFrom` minus the "sequence number is zero" clause that protecting a
record legitimately breaks. -/

/-- The read and write epochs both moved forward within the schedule: records
protected or opened, and possibly some §7.2 KeyUpdates. -/
def RolledEpochs (H : Spec.Hkdf) (before after : State) : Prop :=
  Record.Rolled H before.readKeys? after.readKeys? ∧
    Record.Rolled H before.writeKeys? after.writeKeys?

theorem RolledEpochs.refl {H : Spec.Hkdf} (s : State) : RolledEpochs H s s :=
  ⟨Record.Rolled.refl _, Record.Rolled.refl _⟩

theorem RolledEpochs.trans {H : Spec.Hkdf} {a b c : State}
    (h1 : RolledEpochs H a b) (h2 : RolledEpochs H b c) : RolledEpochs H a c :=
  ⟨h1.1.trans h2.1, h1.2.trans h2.2⟩

theorem RolledEpochs.of_eq {H : Spec.Hkdf} {a b : State}
    (hr : b.readKeys? = a.readKeys?) (hw : b.writeKeys? = a.writeKeys?) :
    RolledEpochs H a b :=
  ⟨Record.Rolled.of_eq hr, Record.Rolled.of_eq hw⟩

private theorem emitCloseNotify_rolled {H : Spec.Hkdf} {state next : State}
    {wire : ByteArray} (h : emitCloseNotify state = .ok (next, wire)) :
    RolledEpochs H state next := by
  unfold emitCloseNotify at h
  split at h
  · cases h; exact RolledEpochs.refl _
  · obtain ⟨keys, hk, h⟩ := except_bind_ok_inv h
    obtain ⟨sealed, hs, h⟩ := except_bind_ok_inv h
    obtain ⟨sealedKeys, wireBytes⟩ := sealed
    cases h
    refine ⟨Record.Rolled.refl _, ?_⟩
    show Record.Rolled H state.writeKeys? (some sealedKeys)
    rw [requireWriteKeys_ok hk]
    exact Record.Rolled.of_seal (liftRecord_ok hs)

private theorem processAlert_rolled {H : Spec.Hkdf} {state next : State}
    {fragment : ByteArray} {duringHandshake : Bool} {wire : ByteArray}
    (h : processAlert state fragment duringHandshake = .ok (next, wire)) :
    RolledEpochs H state next := by
  unfold processAlert at h
  simp only [pure_bind] at h
  split at h
  case isFalse => cases h
  split at h
  · split at h
    · cases h
    · cases h
      exact RolledEpochs.of_eq rfl rfl
  · split at h
    · cases h
      exact RolledEpochs.refl _
    · cases h

private theorem sendKeyUpdateResponse_rolled {H : Spec.Hkdf} (hi : Implements H)
    {state next : State} {wire : ByteArray}
    (h : sendKeyUpdateResponse state = .ok (next, wire)) :
    RolledEpochs H state next := by
  have hread := sendKeyUpdateResponse_readKeys h
  unfold sendKeyUpdateResponse at h
  split at h
  · obtain ⟨_, _, h⟩ := except_bind_ok_inv h
    obtain ⟨keys, hk, h⟩ := except_bind_ok_inv h
    obtain ⟨sealed, hs, h⟩ := except_bind_ok_inv h
    obtain ⟨advancedKeys, wireBytes⟩ := sealed
    obtain ⟨updatedKeys, hu, h⟩ := except_bind_ok_inv h
    cases h
    refine ⟨Record.Rolled.of_eq hread, ?_⟩
    show Record.Rolled H state.writeKeys? (some updatedKeys)
    rw [requireWriteKeys_ok hk]
    exact (Record.Rolled.of_seal (liftRecord_ok hs)).trans
      (Record.Rolled.of_update hi (liftRecord_ok hu))
  · cases h
    exact RolledEpochs.refl _

private theorem acceptKeyUpdate_rolled {H : Spec.Hkdf} (hi : Implements H)
    {state next : State} {message : Handshake.Message} {wire : ByteArray}
    (h : acceptKeyUpdate state message = .ok (next, wire)) :
    RolledEpochs H state next := by
  unfold acceptKeyUpdate at h
  obtain ⟨_, _, h⟩ := except_bind_ok_inv h
  obtain ⟨readKeys, hrk, h⟩ := except_bind_ok_inv h
  obtain ⟨updatedReadKeys, hu, h⟩ := except_bind_ok_inv h
  have hstep : RolledEpochs H state
      { state with readKeys? := some updatedReadKeys } := by
    refine ⟨?_, Record.Rolled.refl _⟩
    show Record.Rolled H state.readKeys? (some updatedReadKeys)
    rw [requireReadKeys_ok hrk]
    exact Record.Rolled.of_update hi (liftRecord_ok hu)
  split at h
  · cases h; exact hstep
  · simp only [] at h
    split at h
    · cases h; exact hstep
    · exact hstep.trans (sendKeyUpdateResponse_rolled hi h)

/-- In `connected` the only post-handshake messages the engine accepts are
NewSessionTicket, which touches no key state, and KeyUpdate, which rolls the
epochs forward. -/
private theorem processHandshakeBuffer_rolled {H : Spec.Hkdf} (hi : Implements H)
    {state next : State} {wire : ByteArray}
    (h : processHandshakeBuffer state = .ok (next, wire))
    (hc : state.phase = .connected) : RolledEpochs H state next := by
  unfold processHandshakeBuffer at h
  split at h
  · cases h
  · cases h; exact RolledEpochs.refl _
  · rename_i message rest htake
    have hsize : rest.size < state.handshakeBuffered.size := takeHandshake?_size htake
    simp only [pure_bind] at h
    split at h
    · cases h
    · rename_i hph
      have hph' : state.phase = Phase.waitingEncryptedExtensions := hph
      rw [hc] at hph'; cases hph'
    · rename_i hph
      have hph' : state.phase = Phase.waitingCertificate := hph
      rw [hc] at hph'; cases hph'
    · rename_i hph
      have hph' : state.phase = Phase.waitingCertificateVerify := hph
      rw [hc] at hph'; cases hph'
    · rename_i hph
      have hph' : state.phase = Phase.waitingServerFinished := hph
      rw [hc] at hph'; cases hph'
    · split at h
      · have hw := processHandshakeBuffer_rolled hi h hc
        exact hw
      · split at h
        · obtain ⟨_, h⟩ := unless_ok h
          split at h
          · cases h
          · rename_i stateK wireK hacc
            split at h
            · cases h
            · rename_i stateF moreWire hnext
              have hbuf : stateK.handshakeBuffered.size <
                  state.handshakeBuffered.size := by
                rw [acceptKeyUpdate_buffered hacc]; exact hsize
              have hck : stateK.phase = Phase.connected := by
                rw [acceptKeyUpdate_phase hacc]; exact hc
              have h1 := acceptKeyUpdate_rolled hi hacc
              have h2 := processHandshakeBuffer_rolled hi hnext hck
              cases h
              exact h1.trans h2
        · cases h
  termination_by state.handshakeBuffered.size
  decreasing_by
    all_goals first
      | exact hsize
      | exact hbuf

private theorem processProtectedRecord_rolled {H : Spec.Hkdf} (hi : Implements H)
    {state next : State} {record : Record.RawRecord} {plain wire : ByteArray}
    (h : processProtectedRecord state record = .ok (next, plain, wire))
    (hc : state.phase = .connected) : RolledEpochs H state next := by
  unfold processProtectedRecord at h
  simp only [pure_bind] at h
  obtain ⟨readKeys, hrk, h⟩ := except_bind_ok_inv h
  obtain ⟨opened, hop, h⟩ := except_bind_ok_inv h
  obtain ⟨nextReadKeys, plaintext⟩ := opened
  have hstep : RolledEpochs H state
      { state with readKeys? := some nextReadKeys } := by
    refine ⟨?_, Record.Rolled.refl _⟩
    show Record.Rolled H state.readKeys? (some nextReadKeys)
    rw [requireReadKeys_ok hrk]
    exact Record.Rolled.of_open (liftRecord_ok hop)
  refine hstep.trans ?_
  split at h
  · split at h
    · cases h
      exact RolledEpochs.refl _
    · split at h
      · obtain ⟨_, h⟩ := unless_ok h
        cases h
        exact RolledEpochs.refl _
      · obtain ⟨_, h⟩ := if_throw_ok h
        obtain ⟨pair, hpb, h⟩ := except_bind_ok_inv h
        obtain ⟨stateH, wireH⟩ := pair
        cases h
        have hw := processHandshakeBuffer_rolled hi hpb hc
        exact hw
      · obtain ⟨_, h⟩ := unless_ok h
        obtain ⟨pair, hpa, h⟩ := except_bind_ok_inv h
        obtain ⟨stateA, wireA⟩ := pair
        cases h
        have hw := processAlert_rolled (H := H) hpa
        exact hw
      · cases h
  · rename_i hph
    have hph' : ((({ state with readKeys? := some nextReadKeys } : State).phase
        == Phase.connected)) = false := Bool.eq_false_iff.mpr hph
    have : (state.phase == Phase.connected) = false := hph'
    rw [hc] at this
    exact absurd this (by decide)

private theorem processRecord_rolled {H : Spec.Hkdf} (hi : Implements H)
    {state next : State} {record : Record.RawRecord} {plain wire : ByteArray}
    (h : processRecord state record = .ok (next, plain, wire))
    (hc : state.phase = .connected) : RolledEpochs H state next := by
  unfold processRecord at h
  simp only [pure_bind] at h
  split at h
  · rename_i hph
    have hph' : state.phase = Phase.waitingServerHello := hph
    rw [hc] at hph'; cases hph'
  · rename_i hph
    have hph' : state.phase = Phase.waitingEncryptedExtensions := hph
    rw [hc] at hph'; cases hph'
  · rename_i hph
    have hph' : state.phase = Phase.waitingCertificate := hph
    rw [hc] at hph'; cases hph'
  · rename_i hph
    have hph' : state.phase = Phase.waitingCertificateVerify := hph
    rw [hc] at hph'; cases hph'
  · rename_i hph
    have hph' : state.phase = Phase.waitingServerFinished := hph
    rw [hc] at hph'; cases hph'
  · split at h
    · exact processProtectedRecord_rolled hi h hc
    · cases h

private theorem completeServerHandshake_phase {state next : State}
    {message : Handshake.Message} {wire : ByteArray}
    (h : completeServerHandshake state message = .ok (next, wire)) :
    next.phase = .connected := by
  unfold completeServerHandshake at h
  simp only [pure_bind] at h
  obtain ⟨finished, _, h⟩ := except_bind_ok_inv h
  obtain ⟨serverSecret, _, h⟩ := except_bind_ok_inv h
  split at h
  case isFalse => cases h
  obtain ⟨handshake, _, h⟩ := except_bind_ok_inv h
  obtain ⟨clientApplicationKeys, _, h⟩ := except_bind_ok_inv h
  obtain ⟨serverApplicationKeys, _, h⟩ := except_bind_ok_inv h
  obtain ⟨clientHandshakeSecret, _, h⟩ := except_bind_ok_inv h
  obtain ⟨clientFinished, _, h⟩ := except_bind_ok_inv h
  obtain ⟨handshakeWriteKeys, _, h⟩ := except_bind_ok_inv h
  obtain ⟨sealed, _, h⟩ := except_bind_ok_inv h
  obtain ⟨advancedKeys, finishedWire⟩ := sealed
  split at h
  · cases h; rfl
  · obtain ⟨compatibilityWire, _, h⟩ := except_bind_ok_inv h
    cases h
    rfl

private theorem emitCloseNotify_handshakeSecret {state next : State} {wire : ByteArray}
    (h : emitCloseNotify state = .ok (next, wire)) :
    next.handshakeSecret? = state.handshakeSecret? ∧ next.phase = state.phase := by
  unfold emitCloseNotify at h
  split at h
  · cases h; exact ⟨rfl, rfl⟩
  · obtain ⟨keys, hk, h⟩ := except_bind_ok_inv h
    obtain ⟨sealed, hs, h⟩ := except_bind_ok_inv h
    obtain ⟨sealedKeys, wireBytes⟩ := sealed
    cases h
    exact ⟨rfl, rfl⟩

private theorem processAlert_handshakeSecret {state next : State}
    {fragment : ByteArray} {duringHandshake : Bool} {wire : ByteArray}
    (h : processAlert state fragment duringHandshake = .ok (next, wire)) :
    next.handshakeSecret? = state.handshakeSecret? := by
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

/-- No transition ever returns to `waitingServerHello`: the phase only moves
forward. -/
private theorem processHandshakeBuffer_phase_ne {state next : State}
    {wire : ByteArray} (h : processHandshakeBuffer state = .ok (next, wire))
    (hph : state.phase ≠ .waitingServerHello) :
    next.phase ≠ .waitingServerHello := by
  unfold processHandshakeBuffer at h
  split at h
  · cases h
  · cases h; exact hph
  · rename_i message rest htake
    have hsize : rest.size < state.handshakeBuffered.size := takeHandshake?_size htake
    simp only [pure_bind] at h
    split at h
    · cases h
    · obtain ⟨_, h⟩ := unless_ok h
      obtain ⟨_, _, h⟩ := except_bind_ok_inv h
      obtain ⟨alpn, _, h⟩ := except_bind_ok_inv h
      split at h
      · obtain ⟨_, h⟩ := unless_ok h
        exact processHandshakeBuffer_phase_ne h (by intro hc; cases hc)
      · exact processHandshakeBuffer_phase_ne h (by intro hc; cases hc)
    · obtain ⟨_, h⟩ := unless_ok h
      obtain ⟨_, _, h⟩ := except_bind_ok_inv h
      obtain ⟨_, _, h⟩ := except_bind_ok_inv h
      exact processHandshakeBuffer_phase_ne h (by intro hc; cases hc)
    · obtain ⟨_, h⟩ := unless_ok h
      obtain ⟨_, _, h⟩ := except_bind_ok_inv h
      split at h
      · obtain ⟨_, _, h⟩ := except_bind_ok_inv h
        obtain ⟨_, h⟩ := unless_ok h
        obtain ⟨_, h⟩ := unless_ok h
        exact processHandshakeBuffer_phase_ne h (by intro hc; cases hc)
      · cases h
    · obtain ⟨_, h⟩ := unless_ok h
      obtain ⟨_, h⟩ := unless_ok h
      rw [completeServerHandshake_phase h]
      intro hc; cases hc
    · rename_i hph'
      have hc : state.phase = Phase.connected := hph'
      split at h
      · exact processHandshakeBuffer_phase_ne h hph
      · split at h
        · obtain ⟨_, h⟩ := unless_ok h
          split at h
          · cases h
          · rename_i stateK wireK hacc
            split at h
            · cases h
            · rename_i stateF moreWire hnext
              have hbuf : stateK.handshakeBuffered.size <
                  state.handshakeBuffered.size := by
                rw [acceptKeyUpdate_buffered hacc]; exact hsize
              have hck : stateK.phase ≠ Phase.waitingServerHello := by
                rw [acceptKeyUpdate_phase hacc, hc]; intro hx; cases hx
              have h2 := processHandshakeBuffer_phase_ne hnext hck
              cases h
              exact h2
        · cases h
  termination_by state.handshakeBuffered.size
  decreasing_by
    all_goals first
      | exact hsize
      | exact hbuf

private theorem processProtectedRecord_phase_ne {state next : State}
    {record : Record.RawRecord} {plain wire : ByteArray}
    (h : processProtectedRecord state record = .ok (next, plain, wire))
    (hph : state.phase ≠ .waitingServerHello) :
    next.phase ≠ .waitingServerHello := by
  unfold processProtectedRecord at h
  simp only [pure_bind] at h
  obtain ⟨readKeys, hrk, h⟩ := except_bind_ok_inv h
  obtain ⟨opened, hop, h⟩ := except_bind_ok_inv h
  obtain ⟨nextReadKeys, plaintext⟩ := opened
  split at h
  · split at h
    · cases h
      exact hph
    · split at h
      · obtain ⟨_, h⟩ := unless_ok h
        cases h
        exact hph
      · obtain ⟨_, h⟩ := if_throw_ok h
        obtain ⟨pair, hpb, h⟩ := except_bind_ok_inv h
        obtain ⟨stateH, wireH⟩ := pair
        cases h
        exact processHandshakeBuffer_phase_ne hpb hph
      · obtain ⟨_, h⟩ := unless_ok h
        obtain ⟨pair, hpa, h⟩ := except_bind_ok_inv h
        obtain ⟨stateA, wireA⟩ := pair
        cases h
        rw [processAlert_phase hpa]
        exact hph
      · cases h
  · split at h
    · obtain ⟨_, h⟩ := if_throw_ok h
      obtain ⟨pair, hpb, h⟩ := except_bind_ok_inv h
      obtain ⟨stateH, wireH⟩ := pair
      cases h
      exact processHandshakeBuffer_phase_ne hpb hph
    · obtain ⟨_, h⟩ := unless_ok h
      obtain ⟨pair, hpa, h⟩ := except_bind_ok_inv h
      obtain ⟨stateA, wireA⟩ := pair
      cases h
      rw [processAlert_phase hpa]
      exact hph
    · cases h

private theorem processRecord_phase_ne {state next : State}
    {record : Record.RawRecord} {plain wire : ByteArray}
    (h : processRecord state record = .ok (next, plain, wire))
    (hph : state.phase ≠ .waitingServerHello) :
    next.phase ≠ .waitingServerHello := by
  unfold processRecord at h
  simp only [pure_bind] at h
  split at h <;>
    first
      | (rename_i hph'
         exact absurd (show state.phase = Phase.waitingServerHello from hph') hph)
      | (split at h <;>
          first
            | (obtain ⟨_, h⟩ := unless_ok h
               cases h
               exact hph)
            | (obtain ⟨_, h⟩ := unless_ok h
               obtain ⟨pair, hpa, h⟩ := except_bind_ok_inv h
               obtain ⟨stateA, wireA⟩ := pair
               cases h
               rw [processAlert_phase hpa]
               exact hph)
            | exact processProtectedRecord_phase_ne h hph
            | cases h)


/-- The conclusion the key-schedule link carries out to `feed`: the connection is
established, and its epochs are the RFC 8446 §7.1 application secrets over a
definite transcript, rolled forward by however many §7.2 KeyUpdates arrived in
the same chunk. -/
def EstablishedEpochs (H : Spec.Hkdf) (before after : State) : Prop :=
  after.phase = .connected ∧
  ∃ transcript : ByteArray, ∀ inp : Spec.Inputs,
    inp.hash .empty = HaclStar.sha256 ByteArray.empty →
    inp.hash .serverFinished = HaclStar.sha256 transcript →
    before.handshakeSecret? = some (Spec.secret H inp .handshake) →
    (∃ (wk : Record.TrafficKeys) (n : Nat), after.writeKeys? = some wk ∧
      wk.ProtectsWith H (Spec.trafficIter H (Spec.derived H inp .cApTraffic) n)) ∧
    (∃ (rk : Record.TrafficKeys) (n : Nat), after.readKeys? = some rk ∧
      rk.ProtectsWith H (Spec.trafficIter H (Spec.derived H inp .sApTraffic) n))

private theorem rolled_epoch {H : Spec.Hkdf}
    {before after : Option Record.TrafficKeys} (hr : Record.Rolled H before after)
    {k : Record.TrafficKeys} {s : ByteArray} {n : Nat} (hk : before = some k)
    (hp : k.ProtectsWith H (Spec.trafficIter H s n)) :
    ∃ (k' : Record.TrafficKeys) (m : Nat), after = some k' ∧
      k'.ProtectsWith H (Spec.trafficIter H s m) := by
  obtain ⟨k', m, hk', hp'⟩ := hr.apply hk hp
  exact ⟨k', n + m, hk', by rw [← Record.trafficIter_add]; exact hp'⟩

/-- An established link survives whatever the rest of the same feed does to the
epochs: records protected or opened, and KeyUpdates, only roll them forward. -/
private theorem EstablishedEpochs.roll {H : Spec.Hkdf} {a b c : State}
    (h : EstablishedEpochs H a b) (hr : RolledEpochs H b c)
    (hc : c.phase = .connected) : EstablishedEpochs H a c := by
  obtain ⟨-, transcript, ht⟩ := h
  refine ⟨hc, transcript, fun inp h1 h2 h3 => ?_⟩
  obtain ⟨⟨wk, n, hwk, hpw⟩, ⟨rk, m, hrk, hpr⟩⟩ := ht inp h1 h2 h3
  exact ⟨rolled_epoch hr.2 hwk hpw, rolled_epoch hr.1 hrk hpr⟩

/-- **The client's whole encrypted server flight, with the phase it lands in.**
`processHandshakeBuffer_keySchedule` with the extra fact that the second case is
exactly the transition into `connected` — which is what lets the link be carried
past the records that follow in the same feed. -/
private theorem processHandshakeBuffer_established {H : Spec.Hkdf} (hi : Implements H)
    {state next : State} {wire : ByteArray}
    (h : processHandshakeBuffer state = .ok (next, wire)) :
    next.handshakeSecret? = state.handshakeSecret? ∨ EstablishedEpochs H state next := by
  unfold processHandshakeBuffer at h
  split at h
  · cases h
  · cases h; exact Or.inl rfl
  · rename_i message rest htake
    have hsize : rest.size < state.handshakeBuffered.size := takeHandshake?_size htake
    simp only [pure_bind] at h
    split at h
    · cases h
    · obtain ⟨_, h⟩ := unless_ok h
      obtain ⟨_, _, h⟩ := except_bind_ok_inv h
      obtain ⟨alpn, _, h⟩ := except_bind_ok_inv h
      split at h
      · obtain ⟨_, h⟩ := unless_ok h
        have hw := processHandshakeBuffer_established hi h
        exact hw
      · have hw := processHandshakeBuffer_established hi h
        exact hw
    · obtain ⟨_, h⟩ := unless_ok h
      obtain ⟨_, _, h⟩ := except_bind_ok_inv h
      obtain ⟨_, _, h⟩ := except_bind_ok_inv h
      have hw := processHandshakeBuffer_established hi h
      exact hw
    · obtain ⟨_, h⟩ := unless_ok h
      obtain ⟨_, _, h⟩ := except_bind_ok_inv h
      split at h
      · obtain ⟨_, _, h⟩ := except_bind_ok_inv h
        obtain ⟨_, h⟩ := unless_ok h
        obtain ⟨_, h⟩ := unless_ok h
        have hw := processHandshakeBuffer_established hi h
        exact hw
      · cases h
    · obtain ⟨_, h⟩ := unless_ok h
      obtain ⟨_, h⟩ := unless_ok h
      refine Or.inr ⟨completeServerHandshake_phase h,
        state.transcript ++ message.encoded, fun inp h1 h2 h3 => ?_⟩
      obtain ⟨⟨wk, hwk, hdw⟩, ⟨rk, hrk, hdr⟩⟩ :=
        completeServerHandshake_keySchedule hi inp h1 h2 h3 h
      exact ⟨⟨wk, 0, hwk, hdw.protectsWith⟩, ⟨rk, 0, hrk, hdr.protectsWith⟩⟩
    · split at h
      · have hw := processHandshakeBuffer_established hi h
        exact hw
      · split at h
        · obtain ⟨_, h⟩ := unless_ok h
          split at h
          · cases h
          · rename_i stateK wireK hacc
            split at h
            · cases h
            · rename_i stateF moreWire hnext
              cases h
              have hbuf : stateK.handshakeBuffered.size <
                  state.handshakeBuffered.size := by
                rw [acceptKeyUpdate_buffered hacc]; exact hsize
              have hk := acceptKeyUpdate_handshakeSecret hacc
              rcases processHandshakeBuffer_established hi hnext with hl | ⟨hcon, t, ht⟩
              · exact Or.inl (by rw [hl, hk])
              · exact Or.inr ⟨hcon, t, fun inp h1 h2 h3 => ht inp h1 h2 (by rw [hk]; exact h3)⟩
        · cases h
  termination_by state.handshakeBuffered.size
  decreasing_by
    all_goals first
      | exact hsize
      | exact hbuf

private theorem processProtectedRecord_established {H : Spec.Hkdf} (hi : Implements H)
    {state next : State} {record : Record.RawRecord} {plain wire : ByteArray}
    (h : processProtectedRecord state record = .ok (next, plain, wire)) :
    next.handshakeSecret? = state.handshakeSecret? ∨ EstablishedEpochs H state next := by
  unfold processProtectedRecord at h
  simp only [pure_bind] at h
  obtain ⟨readKeys, hrk, h⟩ := except_bind_ok_inv h
  obtain ⟨opened, hop, h⟩ := except_bind_ok_inv h
  obtain ⟨nextReadKeys, plaintext⟩ := opened
  split at h
  · split at h
    · cases h
      exact Or.inl rfl
    · split at h
      · obtain ⟨_, h⟩ := unless_ok h
        cases h
        exact Or.inl rfl
      · obtain ⟨_, h⟩ := if_throw_ok h
        obtain ⟨pair, hpb, h⟩ := except_bind_ok_inv h
        obtain ⟨stateH, wireH⟩ := pair
        cases h
        have hw := processHandshakeBuffer_established hi hpb
        exact hw
      · obtain ⟨_, h⟩ := unless_ok h
        obtain ⟨pair, hpa, h⟩ := except_bind_ok_inv h
        obtain ⟨stateA, wireA⟩ := pair
        cases h
        have hw := processAlert_handshakeSecret hpa
        exact Or.inl hw
      · cases h
  · split at h
    · obtain ⟨_, h⟩ := if_throw_ok h
      obtain ⟨pair, hpb, h⟩ := except_bind_ok_inv h
      obtain ⟨stateH, wireH⟩ := pair
      cases h
      have hw := processHandshakeBuffer_established hi hpb
      exact hw
    · obtain ⟨_, h⟩ := unless_ok h
      obtain ⟨pair, hpa, h⟩ := except_bind_ok_inv h
      obtain ⟨stateA, wireA⟩ := pair
      cases h
      have hw := processAlert_handshakeSecret hpa
      exact Or.inl hw
    · cases h

private theorem processRecord_established {H : Spec.Hkdf} (hi : Implements H)
    {state next : State} {record : Record.RawRecord} {plain wire : ByteArray}
    (h : processRecord state record = .ok (next, plain, wire))
    (hph : state.phase ≠ .waitingServerHello) :
    next.handshakeSecret? = state.handshakeSecret? ∨ EstablishedEpochs H state next := by
  unfold processRecord at h
  simp only [pure_bind] at h
  split at h <;>
    first
      | (rename_i hph'
         exact absurd (show state.phase = Phase.waitingServerHello from hph') hph)
      | (split at h <;>
          first
            | (obtain ⟨_, h⟩ := unless_ok h
               cases h
               exact Or.inl rfl)
            | (obtain ⟨_, h⟩ := unless_ok h
               obtain ⟨pair, hpa, h⟩ := except_bind_ok_inv h
               obtain ⟨stateA, wireA⟩ := pair
               cases h
               have hw := processAlert_handshakeSecret hpa
               exact Or.inl hw)
            | exact processProtectedRecord_established hi h
            | cases h)

private theorem processRecords_rolled {H : Spec.Hkdf} (hi : Implements H)
    {records : List Record.RawRecord} :
    ∀ {state : State} {plaintext wireBytes : ByteArray} {out : Output},
      processRecords state records plaintext wireBytes = .ok out →
      state.phase = .connected → RolledEpochs H state out.state := by
  induction records with
  | nil =>
      intro state plaintext wireBytes out h hc
      unfold processRecords at h
      cases h
      exact RolledEpochs.refl _
  | cons record rest ih =>
      intro state plaintext wireBytes out h hc
      unfold processRecords at h
      split at h
      · cases h
        exact RolledEpochs.refl _
      · split at h
        · cases h
        · rename_i stateN cleartext outbound hpr
          exact (processRecord_rolled hi hpr hc).trans
            (ih h (processRecord_plaintext hpr (.inl hc)))

private theorem processRecords_established {H : Spec.Hkdf} (hi : Implements H)
    {records : List Record.RawRecord} :
    ∀ {state : State} {plaintext wireBytes : ByteArray} {out : Output},
      processRecords state records plaintext wireBytes = .ok out →
      state.phase ≠ .waitingServerHello →
      out.state.handshakeSecret? = state.handshakeSecret? ∨
        EstablishedEpochs H state out.state := by
  induction records with
  | nil =>
      intro state plaintext wireBytes out h hph
      unfold processRecords at h
      cases h
      exact Or.inl rfl
  | cons record rest ih =>
      intro state plaintext wireBytes out h hph
      unfold processRecords at h
      split at h
      · cases h
        exact Or.inl rfl
      · split at h
        · cases h
        · rename_i stateN cleartext outbound hpr
          rcases processRecord_established hi hpr hph with hl | hcon
          · rcases ih h (processRecord_phase_ne hpr hph) with hl' | ⟨hc, t, ht⟩
            · exact Or.inl (hl'.trans hl)
            · exact Or.inr ⟨hc, t, fun inp h1 h2 h3 => ht inp h1 h2 (by rw [hl]; exact h3)⟩
          · refine Or.inr (hcon.roll ?_ ?_)
            · exact processRecords_rolled hi h hcon.1
            · exact processRecords_connected h hcon.1

/-- **`feed` installs the RFC 8446 §7.1 application epochs.** Either the feed did
not complete the handshake — and the handshake secret is untouched — or it did,
and there is a definite transcript (the ClientHello…server Finished sequence the
engine accumulated) such that, for any key-schedule inputs agreeing with the
engine on the empty and ClientHello…server Finished transcript hashes and on the
handshake secret the state carried, the connection is `connected` and its write
and read epochs are `client_application_traffic_secret_0` and
`server_application_traffic_secret_0` — rolled forward by however many §7.2
KeyUpdates arrived in the same chunk, which is none in the usual case.

This is the `feed`-level form of `processHandshakeBuffer_keySchedule`: the
statement carries the relation through transport framing, decryption, and
dispatch, which move bytes without touching key state. As everywhere, the
statement is parametric in the HKDF the HACL\* bindings
implement, so it constrains the derivation structure and assumes nothing about
what the primitive computes.

Scope: `hph` excludes a feed that itself accepts the ServerHello, because such a
feed *replaces* the handshake secret the conclusion is stated against —
`acceptServerHello_keySchedule` is the law for that step. A feed that carries
the ServerHello and the encrypted flight in one chunk is therefore not covered
by this statement; linking the two into one whole-handshake law is left open. -/
theorem feed_keySchedule {H : Spec.Hkdf} (hi : Implements H) {state : State}
    {chunk : ByteArray} {out : Output} (h : feed state chunk = .ok out)
    (hph : state.phase ≠ .waitingServerHello) :
    out.state.handshakeSecret? = state.handshakeSecret? ∨
      EstablishedEpochs H state out.state := by
  unfold feed at h
  split at h
  · rename_i output hfeed
    cases h
    unfold feedWithFailure at hfeed
    split at hfeed
    · cases hfeed
      exact Or.inl rfl
    · split at hfeed
      · cases hfeed
      · have hw := processRecords_established hi hfeed hph
        exact hw
  · cases h

end Client
end Tls
