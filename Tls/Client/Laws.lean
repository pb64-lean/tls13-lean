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

private theorem sendKeyUpdateResponse_readKeys {state next : State}
    {wire : ByteArray} (h : sendKeyUpdateResponse state = .ok (next, wire)) :
    next.readKeys? = state.readKeys? := by
  unfold sendKeyUpdateResponse at h
  obtain ⟨_, _, h⟩ := except_bind_ok_inv h
  obtain ⟨keys, hk, h⟩ := except_bind_ok_inv h
  obtain ⟨sealed, hs, h⟩ := except_bind_ok_inv h
  obtain ⟨advancedKeys, wireBytes⟩ := sealed
  obtain ⟨updatedKeys, hu, h⟩ := except_bind_ok_inv h
  cases h
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

/-! ## Handshake state invariants -/

/-- Structural invariant of a client connection: **an established connection
carries both application traffic epochs and has dropped every handshake
secret and the handshake transcript**. Before the connection is established the
predicate says nothing, which is exactly right — the handshake states are the
ones that legitimately hold those secrets.

`start_wellFormed` establishes it and `feed`, `feedWithFailure`,
`sealApplication`, `closeNotify`, `sealFatalAlert` and whole `run`s preserve it.
The complementary facts about *how* the connection becomes established (the
server Finished was verified, the transcript grew by exactly the message
consumed) are transition laws below rather than conjuncts here. -/
def State.WellFormed (state : State) : Prop :=
  state.phase = .connected →
    state.writeKeys?.isSome = true ∧ state.readKeys?.isSome = true ∧
      state.handshakeSecret? = none ∧
      state.clientHandshakeTrafficSecret? = none ∧
      state.serverHandshakeTrafficSecret? = none ∧
      state.transcript = ByteArray.empty

/-- Transfer the invariant across a state update that changes no field it
mentions, except by installing traffic keys. -/
private theorem wellFormed_transfer {s t : State} (hinv : s.WellFormed)
    (hphase : t.phase = s.phase)
    (hwrite : t.writeKeys? = s.writeKeys? ∨ ∃ k, t.writeKeys? = some k)
    (hread : t.readKeys? = s.readKeys? ∨ ∃ k, t.readKeys? = some k)
    (h1 : t.handshakeSecret? = s.handshakeSecret?)
    (h2 : t.clientHandshakeTrafficSecret? = s.clientHandshakeTrafficSecret?)
    (h3 : t.serverHandshakeTrafficSecret? = s.serverHandshakeTrafficSecret?)
    (h4 : t.transcript = s.transcript) : t.WellFormed := by
  intro hc
  obtain ⟨a, b, c, d, e, f⟩ := hinv (hphase ▸ hc)
  refine ⟨?_, ?_, by rw [h1]; exact c, by rw [h2]; exact d,
    by rw [h3]; exact e, by rw [h4]; exact f⟩
  · cases hwrite with
    | inl hw => rw [hw]; exact a
    | inr hw => obtain ⟨k, hk⟩ := hw; rw [hk]; rfl
  · cases hread with
    | inl hr => rw [hr]; exact b
    | inr hr => obtain ⟨k, hk⟩ := hr; rw [hk]; rfl

/-- A fresh client connection is waiting for the ServerHello. -/
theorem start_phase {config : Config} {out : Output}
    (h : start config = .ok out) :
    out.state.phase = .waitingServerHello := by
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
                       rfl)
                    | (split at h <;>
                        first
                          | cases h
                          | (obtain ⟨_, h⟩ := unless_ok h
                             obtain ⟨hello, _, h⟩ := except_bind_ok_inv h
                             obtain ⟨wire, _, h⟩ := except_bind_ok_inv h
                             cases h
                             rfl))))
      | (split at h <;>
          first
            | cases h
            | (obtain ⟨_, h⟩ := unless_ok h
               split at h <;>
                 first
                   | (obtain ⟨hello, _, h⟩ := except_bind_ok_inv h
                      obtain ⟨wire, _, h⟩ := except_bind_ok_inv h
                      cases h
                      rfl)
                   | (split at h <;>
                       first
                         | cases h
                         | (obtain ⟨_, h⟩ := unless_ok h
                            obtain ⟨hello, _, h⟩ := except_bind_ok_inv h
                            obtain ⟨wire, _, h⟩ := except_bind_ok_inv h
                            cases h
                            rfl))))

/-- `start` establishes the invariant: the connection is not yet established, so
it holds vacuously — and in particular no traffic keys exist yet. -/
theorem start_wellFormed {config : Config} {out : Output}
    (h : start config = .ok out) : out.state.WellFormed := by
  intro hc
  rw [start_phase h] at hc
  cases hc

theorem sealFatalAlert_wellFormed {state : State} {description : UInt8}
    {out : Output} (h : sealFatalAlert state description = .ok out)
    (hinv : state.WellFormed) : out.state.WellFormed := by
  unfold sealFatalAlert at h
  obtain ⟨keys, hk, h⟩ := except_bind_ok_inv h
  obtain ⟨sealed, hs, h⟩ := except_bind_ok_inv h
  obtain ⟨next, wire⟩ := sealed
  cases h
  exact wellFormed_transfer hinv rfl (.inr ⟨_, rfl⟩) (.inl rfl) rfl rfl
    rfl rfl

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
    exact wellFormed_transfer hinv rfl (.inr ⟨_, rfl⟩) (.inl rfl) rfl rfl
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
        exact wellFormed_transfer hinv rfl (.inr ⟨_, rfl⟩) (.inl rfl) rfl rfl
          rfl rfl
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
  case isFalse => cases h
  split at h
  · split at h
    · cases h
    · exact emitCloseNotify_wellFormed h (fun hc => hinv hc)
  · cases h

private theorem sendKeyUpdateResponse_wellFormed {state next : State}
    {wire : ByteArray} (h : sendKeyUpdateResponse state = .ok (next, wire))
    (hinv : state.WellFormed) : next.WellFormed := by
  unfold sendKeyUpdateResponse at h
  obtain ⟨_, _, h⟩ := except_bind_ok_inv h
  obtain ⟨keys, hk, h⟩ := except_bind_ok_inv h
  obtain ⟨sealed, hs, h⟩ := except_bind_ok_inv h
  obtain ⟨advancedKeys, wireBytes⟩ := sealed
  obtain ⟨updatedKeys, hu, h⟩ := except_bind_ok_inv h
  cases h
  exact wellFormed_transfer hinv rfl (.inr ⟨_, rfl⟩) (.inl rfl) rfl rfl
    rfl rfl

private theorem acceptKeyUpdate_wellFormed {state next : State}
    {message : Handshake.Message} {wire : ByteArray}
    (h : acceptKeyUpdate state message = .ok (next, wire))
    (hinv : state.WellFormed) : next.WellFormed := by
  unfold acceptKeyUpdate at h
  obtain ⟨_, _, h⟩ := except_bind_ok_inv h
  obtain ⟨_, _, h⟩ := except_bind_ok_inv h
  obtain ⟨_, _, h⟩ := except_bind_ok_inv h
  split at h
  · cases h
    exact wellFormed_transfer hinv rfl (.inl rfl) (.inr ⟨_, rfl⟩) rfl rfl rfl rfl
  · exact sendKeyUpdateResponse_wellFormed h
      (wellFormed_transfer hinv rfl (.inl rfl) (.inr ⟨_, rfl⟩) rfl rfl rfl rfl)

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
        intro hc
        cases hc
      · cases h
    · cases h
  · split at h
    · split at h
      · split at h
        · obtain ⟨writeKeys, _, h⟩ := except_bind_ok_inv h
          obtain ⟨readKeys, _, h⟩ := except_bind_ok_inv h
          cases h
          intro hc
          cases hc
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
  have hgoal : ∀ (st : State), st.writeKeys? = some clientApplicationKeys →
      st.readKeys? = some serverApplicationKeys → st.handshakeSecret? = none →
      st.clientHandshakeTrafficSecret? = none →
      st.serverHandshakeTrafficSecret? = none →
      st.transcript = ByteArray.empty → st.WellFormed := by
    intro st a b c d e f _
    exact ⟨by rw [a]; rfl, by rw [b]; rfl, c, d, e, f⟩
  split at h
  · cases h
    exact hgoal _ rfl rfl rfl rfl rfl rfl
  · obtain ⟨compatibilityWire, _, h⟩ := except_bind_ok_inv h
    cases h
    exact hgoal _ rfl rfl rfl rfl rfl rfl

private theorem feedPlaintextHandshake_wellFormed {state next : State}
    {fragment : ByteArray}
    (h : feedPlaintextHandshake state fragment = .ok next)
    (hinv : state.WellFormed) : next.WellFormed := by
  unfold feedPlaintextHandshake at h
  simp only [pure_bind] at h
  obtain ⟨framed, _, h⟩ := except_bind_ok_inv h
  split at h
  · split at h
    · exact acceptServerHello_wellFormed h
    · cases h
  · cases h
    exact fun hc => hinv hc

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
        exact processHandshakeBuffer_wellFormed h (by intro hc; cases hc)
      · exact processHandshakeBuffer_wellFormed h (by intro hc; cases hc)
    · obtain ⟨_, h⟩ := unless_ok h
      obtain ⟨_, _, h⟩ := except_bind_ok_inv h
      obtain ⟨_, _, h⟩ := except_bind_ok_inv h
      exact processHandshakeBuffer_wellFormed h (by intro hc; cases hc)
    · obtain ⟨_, h⟩ := unless_ok h
      obtain ⟨_, _, h⟩ := except_bind_ok_inv h
      split at h
      · obtain ⟨_, _, h⟩ := except_bind_ok_inv h
        obtain ⟨_, h⟩ := unless_ok h
        obtain ⟨_, h⟩ := unless_ok h
        exact processHandshakeBuffer_wellFormed h (by intro hc; cases hc)
      · cases h
    · obtain ⟨_, h⟩ := unless_ok h
      obtain ⟨_, h⟩ := unless_ok h
      exact completeServerHandshake_wellFormed h
    · split at h
      · obtain ⟨_, _, h⟩ := except_bind_ok_inv h
        exact processHandshakeBuffer_wellFormed h (fun hc => hinv hc)
      · split at h
        · split at h
          · cases h
          · rename_i stateK wireK hacc
            split at h
            · cases h
            · rename_i stateF moreWire hnext
              have hbuf : stateK.handshakeBuffered.size <
                  state.handshakeBuffered.size := by
                rw [acceptKeyUpdate_buffered hacc]; exact hsize
              have h2 := processHandshakeBuffer_wellFormed hnext
                (acceptKeyUpdate_wellFormed hacc (fun hc => hinv hc))
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
  obtain ⟨readKeys, _, h⟩ := except_bind_ok_inv h
  obtain ⟨opened, _, h⟩ := except_bind_ok_inv h
  obtain ⟨nextReadKeys, plaintext⟩ := opened
  have hinv' : ({ state with readKeys? := some nextReadKeys } : State).WellFormed :=
    wellFormed_transfer hinv rfl (.inl rfl) (.inr ⟨_, rfl⟩) rfl rfl rfl rfl
  split at h
  · obtain ⟨_, h⟩ := if_throw_ok h
    split at h
    · obtain ⟨_, h⟩ := unless_ok h
      cases h
      exact hinv'
    · obtain ⟨pair, hpb, h⟩ := except_bind_ok_inv h
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
  · split at h
    · obtain ⟨pair, hpb, h⟩ := except_bind_ok_inv h
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
      · rename_i stateN cleartext outbound hpr
        exact ih h (processRecord_wellFormed hpr hinv)

theorem feedWithFailure_wellFormed {initial : State} {chunk : ByteArray}
    {out : Output} (h : feedWithFailure initial chunk = .ok out)
    (hinv : initial.WellFormed) : out.state.WellFormed := by
  unfold feedWithFailure at h
  split at h
  · cases h
  · split at h
    · cases h
    · exact processRecords_wellFormed h (fun hc => hinv hc)

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

/-- **Application data is protected only by an established, open connection.**
-/
theorem sealApplication_connected {state : State} {plaintext : ByteArray}
    {out : Output} (h : sealApplication state plaintext = .ok out) :
    state.phase = .connected ∧ state.localClosed = false ∧
      state.peerClosed = false := by
  unfold sealApplication at h
  simp only [pure_bind] at h
  obtain ⟨hp, h⟩ := unless_ok h
  obtain ⟨hcl, h⟩ := if_throw_ok h
  refine ⟨phase_eq_of_beq hp, ?_, ?_⟩ <;> simp_all

/-- **`close_notify` is sent only by an established connection.** -/
theorem closeNotify_connected {state : State} {out : Output}
    (h : closeNotify state = .ok out) : state.phase = .connected := by
  unfold closeNotify at h
  simp only [pure_bind] at h
  obtain ⟨hp, h⟩ := unless_ok h
  exact phase_eq_of_beq hp

/-- **A closed connection is terminal.** Once both directions have sent
`close_notify`, feeding further transport bytes fails without advancing the
state; and since every failure is reported as an `Except` error carrying no
successor state, there is no transition out of a failed step at all. -/
theorem feedWithFailure_closed {state : State} {chunk : ByteArray}
    (hclosed : state.closed = true) (hchunk : chunk.isEmpty = false) :
    feedWithFailure state chunk =
      .error { state, error := .connectionClosed } := by
  unfold feedWithFailure
  rw [if_pos (by rw [hclosed, hchunk]; rfl)]

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
  case isFalse => cases h
  split at h
  · split at h
    · cases h
    · have hp := emitCloseNotify_phase h
      exact hp
  · cases h

private theorem sendKeyUpdateResponse_phase {state next : State} {wire : ByteArray}
    (h : sendKeyUpdateResponse state = .ok (next, wire)) :
    next.phase = state.phase := by
  unfold sendKeyUpdateResponse at h
  obtain ⟨_, _, h⟩ := except_bind_ok_inv h
  obtain ⟨keys, hk, h⟩ := except_bind_ok_inv h
  obtain ⟨sealed, hs, h⟩ := except_bind_ok_inv h
  obtain ⟨advancedKeys, wireBytes⟩ := sealed
  obtain ⟨updatedKeys, hu, h⟩ := except_bind_ok_inv h
  cases h
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
      · obtain ⟨_, _, h⟩ := except_bind_ok_inv h
        have h2 := processHandshakeBuffer_connected h hc
        exact h2
      · split at h
        · split at h
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
    case isTrue => cases h
    split at h
    · obtain ⟨_, h⟩ := unless_ok h
      cases h
      exact hc
    · obtain ⟨pair, hpb, h⟩ := except_bind_ok_inv h
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
    · obtain ⟨pair, _, h⟩ := except_bind_ok_inv h
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
  obtain ⟨keys, hk, h⟩ := except_bind_ok_inv h
  obtain ⟨sealed, hs, h⟩ := except_bind_ok_inv h
  obtain ⟨next, wire⟩ := sealed
  cases h
  rfl

private theorem sealFatalAlert_plaintext {state : State} {description : UInt8}
    {out : Output} (h : sealFatalAlert state description = .ok out) :
    out.plaintext = ByteArray.empty := by
  unfold sealFatalAlert at h
  obtain ⟨keys, hk, h⟩ := except_bind_ok_inv h
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

/-- **A KeyUpdate really changes the epoch**: the peer's new read traffic secret
is the RFC 8446 §7.2 successor of the old one, and its record sequence number
restarts at zero. -/
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
  · rw [sendKeyUpdateResponse_readKeys h]

/-- **Accepting the ServerHello extends the transcript by exactly that
message.** -/
private theorem acceptServerHello_transcript {state next : State}
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
