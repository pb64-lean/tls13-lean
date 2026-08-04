module

public import Tls.Server
public import Tls.Record.Laws
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
threaded single-threadedly through its own state. `run_nonce_nodup` composes
that into the statement that one run of the engine never repeats a (traffic
secret, nonce) pair. The same honesty notes as `Tls.Client.Laws` apply: the
theorem is about this engine's own emissions along one chain of states, not
about a caller who clones a `State`; it covers the write direction only; and
distinctness across epochs is the `secrets.Nodup` hypothesis, since HKDF is an
opaque HACL\* binding here.

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
    have hsize : rest.size < state.handshakeBuffered.size := takeHandshake?_size htake
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
      · split at h
        · cases h
        · rename_i stateK wireK hacc
          split at h
          · cases h
          · rename_i stateF moreWire hnext
            have h1 := acceptKeyUpdate_write hacc
            have hbuf : stateK.handshakeBuffered.size <
                state.handshakeBuffered.size := by
              rw [acceptKeyUpdate_buffered hacc]; exact hsize
            have h2 := processHandshakeBuffer_write hnext
            cases h
            exact Record.Extends.trans h1 h2
      · cases h
  termination_by state.handshakeBuffered.size
  decreasing_by exact hbuf

private theorem processProtectedRecord_write {state next : State}
    {record : Record.RawRecord} {plain wire : ByteArray}
    (h : processProtectedRecord state record = .ok (next, plain, wire)) :
    WriteEffect state next := by
  unfold processProtectedRecord at h
  simp only [pure_bind] at h
  obtain ⟨readKeys, _, h⟩ := except_bind_ok_inv h
  obtain ⟨opened, _, h⟩ := except_bind_ok_inv h
  obtain ⟨nextReadKeys, plaintext⟩ := opened
  split at h <;>
    first
      | (obtain ⟨_, h⟩ := unless_ok h
         obtain ⟨_, h⟩ := if_throw_ok h
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

/-- **Nonce non-reuse across a server connection.** For any successful run of
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

/-- `run_nonce_nodup` for a single `feed` — which for a server covers the entire
handshake flight it emits in response to a ClientHello. -/
theorem feed_nonce_nodup {state : State} {chunk : ByteArray} {out : Output}
    (h : feed state chunk = .ok out) :
    ∃ (secrets : List ByteArray) (nonces : List (ByteArray × ByteArray)),
      Record.WriteRun state.writeKeys? out.state.writeKeys? secrets nonces ∧
        (secrets.Nodup → nonces.Nodup) := by
  obtain ⟨secrets, nonces, hrun⟩ := Record.Extends.run (feed_write h)
  exact ⟨secrets, nonces, hrun, fun hfresh => hrun.nodup hfresh⟩

end Server
end Tls
