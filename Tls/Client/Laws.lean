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
Composing those two facts, `run_nonce_nodup` states that a whole run of the
engine never repeats a (traffic secret, nonce) pair.

Scope, stated honestly:

* The theorems are about this engine's own emissions along one chain of states.
  A caller that clones a `State` and drives two connections from it is outside
  their reach — Lean values are duplicable, and no theorem about a pure function
  can forbid that. Threading one state is the caller's obligation.
* Only the *write* direction is covered. Nonce reuse is a sender property;
  read-side nonces are the peer's.
* Distinctness across traffic epochs is the `secrets.Nodup` hypothesis, not a
  theorem: TLS derives each new epoch with HKDF-Expand-Label, which is an opaque
  HACL\* binding here (`Tls.Record.Laws.WriteRun.nodup` documents the same
  boundary). Within one epoch nothing is assumed.
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
  obtain ⟨keys, hk, h⟩ := except_bind_ok_inv h
  obtain ⟨sealed, hs, h⟩ := except_bind_ok_inv h
  obtain ⟨next, wire⟩ := sealed
  cases h
  show Record.Extends state.writeKeys? (some next)
  rw [requireWriteKeys_ok hk]
  exact Record.Extends.of_seal (liftRecord_ok hs)


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
  case isFalse => cases h
  split at h
  · split at h
    · cases h
    · have hw := emitCloseNotify_write h
      exact hw
  · cases h

/-- A KeyUpdate response seals its message under the *old* epoch, as RFC 8446
§7.2 requires, and only then rolls the write secret forward. -/
private theorem sendKeyUpdateResponse_write {state next : State} {wire : ByteArray}
    (h : sendKeyUpdateResponse state = .ok (next, wire)) :
    WriteEffect state next := by
  unfold sendKeyUpdateResponse at h
  obtain ⟨_, _, h⟩ := except_bind_ok_inv h
  obtain ⟨keys, hk, h⟩ := except_bind_ok_inv h
  obtain ⟨sealed, hs, h⟩ := except_bind_ok_inv h
  obtain ⟨advancedKeys, wireBytes⟩ := sealed
  obtain ⟨updatedKeys, hu, h⟩ := except_bind_ok_inv h
  cases h
  show Record.Extends state.writeKeys? (some updatedKeys)
  rw [requireWriteKeys_ok hk]
  exact Record.Extends.trans (Record.Extends.of_seal (liftRecord_ok hs))
    (Record.Extends.rekey advancedKeys updatedKeys)

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
      · obtain ⟨_, _, h⟩ := except_bind_ok_inv h
        have hw := processHandshakeBuffer_write h
        exact hw
      · split at h
        · split at h
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
  · obtain ⟨_, h⟩ := if_throw_ok h
    split at h
    · obtain ⟨_, h⟩ := unless_ok h
      cases h
      exact Record.Extends.refl _
    · obtain ⟨pair, hpb, h⟩ := except_bind_ok_inv h
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
    · obtain ⟨pair, hpb, h⟩ := except_bind_ok_inv h
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
        exact Record.Extends.refl _
      · rename_i stateN cleartext outbound hpr
        have h1 := processRecord_write hpr
        have h2 := ih h
        exact Record.Extends.trans h1 h2


/-- Everything a successful `feed` protects — a client Finished, a reciprocal
KeyUpdate, a `close_notify` echo — is accounted for. -/
theorem feedWithFailure_write {initial : State} {chunk : ByteArray} {out : Output}
    (h : feedWithFailure initial chunk = .ok out) :
    WriteEffect initial out.state := by
  unfold feedWithFailure at h
  split at h
  · cases h
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
  · cases h; exact Record.Extends.refl _
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

/-- **Nonce non-reuse across a client connection.** For any successful run of
the engine there is a `Tls.Record.Laws.WriteRun` — the explicit list of records
the run protected, each tagged with the traffic secret of the epoch that
protected it — leading from the connection's initial write state to its final
one, and no (secret, nonce) pair in it repeats.

Sequence numbers restart at zero on every KeyUpdate, which is why the trace is
scoped by epoch secret; `secrets` lists the epochs the run used, oldest first,
and the only hypothesis is that they are distinct.

What this does *not* say: nothing constrains a caller who keeps an old `State`
and drives a second connection from it. Single-threading the state is the
caller's obligation; given that, the engine never repeats a nonce. -/
theorem run_nonce_nodup {ops : List Op} {state : State} {out : Output}
    (h : run state ops = .ok out) :
    ∃ (secrets : List ByteArray) (nonces : List (ByteArray × ByteArray)),
      Record.WriteRun state.writeKeys? out.state.writeKeys? secrets nonces ∧
        (secrets.Nodup → nonces.Nodup) := by
  obtain ⟨secrets, nonces, hrun⟩ := Record.Extends.run (run_write h)
  exact ⟨secrets, nonces, hrun, fun hfresh => hrun.nodup hfresh⟩

/-- `run_nonce_nodup` for a single `feed`. -/
theorem feed_nonce_nodup {state : State} {chunk : ByteArray} {out : Output}
    (h : feed state chunk = .ok out) :
    ∃ (secrets : List ByteArray) (nonces : List (ByteArray × ByteArray)),
      Record.WriteRun state.writeKeys? out.state.writeKeys? secrets nonces ∧
        (secrets.Nodup → nonces.Nodup) := by
  obtain ⟨secrets, nonces, hrun⟩ := Record.Extends.run (feed_write h)
  exact ⟨secrets, nonces, hrun, fun hfresh => hrun.nodup hfresh⟩

end Client
end Tls
