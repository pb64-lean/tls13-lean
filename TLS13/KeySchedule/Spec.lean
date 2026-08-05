module

public section

/-!
# RFC 8446 §7.1 key schedule, as a specification

This module is a *declarative* transcription of the TLS 1.3 key schedule: the
`HkdfLabel` wire structure, `HKDF-Expand-Label`, `Derive-Secret`, and the whole
derivation diagram of RFC 8446 §7.1 encoded **as data** — for every named
secret, which secret it is derived from, under which label, and over which
transcript.

Nothing here calls a cryptographic primitive. The schedule is defined over an
abstract `Hkdf` interface (`extract` / `expand` / `hashLen`), so the definitions
are meaningful for *any* HKDF, and the refinement theorems in
`TLS13.KeySchedule.Refinement` — and, for the engines, `Tls.Client.Laws` and
`Tls.Server.Laws` — hold for any implementation of that interface, exactly as
`Tls.Record.open_seal` is stated for any AEAD satisfying its round trip.

**What a refinement against this specification does and does not say.** It says
the implementation's derivation *structure* is the RFC's: the right labels, the
right context (transcript hash versus the empty-string hash), the right parent
secret, the right output lengths, and the right order. Historically that is
where TLS key-schedule bugs live — a mistyped label, the wrong transcript at a
`Derive-Secret`, the handshake secret used where the master secret belongs, a
missing derivation step. It says *nothing* about whether HKDF-Extract and
HKDF-Expand compute the right bytes: those are opaque `@[extern]` HACL\*
bindings here, and modelling them is out of scope. It is not a security proof.

The empirical anchor is separate and complementary: `Test/HaclKat.lean` checks
the schedule against RFC 8448's published values. If a theorem here and a
known-answer test ever disagree, **the known-answer test wins** — the RFC's
numbers are ground truth and this transcription is what is wrong.
-/

namespace TLS13
namespace KeySchedule
namespace Spec

/-! ## The primitive interface

The key schedule is parametric over HKDF. `extract salt ikm` is
`HKDF-Extract(salt, IKM)`, `expand prk info len` is `HKDF-Expand(PRK, info,
len)`, and `hashLen` is `Hash.length` — the output size of the cipher suite's
hash, which is also the size of every secret in the diagram. -/

/-- The HKDF interface RFC 8446 §7.1 is written against. -/
structure Hkdf where
  /-- `Hash.length`: the size in bytes of the suite hash's output. -/
  hashLen : Nat
  /-- `HKDF-Extract(salt, IKM)`. -/
  extract : ByteArray → ByteArray → ByteArray
  /-- `HKDF-Expand(PRK, info, L)`. -/
  expand : ByteArray → ByteArray → Nat → ByteArray

/-- TLS 1.3's `0` for a secret-sized value: `n` zero bytes. Used as the default
salt of the Early Secret extraction, as the IKM when there is no PSK, and as the
IKM of the Master Secret extraction. -/
@[expose] def zeros (n : Nat) : ByteArray :=
  ByteArray.mk ((List.replicate n (0 : UInt8)).toArray)

/-! ## Labels

Every label RFC 8446 uses with `HKDF-Expand-Label`, as data. `Label.text` is the
`Label` field of the `HkdfLabel` structure, *before* the mandatory `"tls13 "`
prefix is prepended. -/

/-- The RFC 8446 `HKDF-Expand-Label` labels. -/
inductive Label where
  /-- §7.1, between extraction stages: `Derive-Secret(., "derived", "")`. -/
  | derived
  /-- §7.1, `binder_key` for an external PSK. -/
  | extBinder
  /-- §7.1, `binder_key` for a resumption PSK. -/
  | resBinder
  /-- §7.1, `client_early_traffic_secret`. -/
  | ceTraffic
  /-- §7.1, `early_exporter_master_secret`. -/
  | eExpMaster
  /-- §7.1, `client_handshake_traffic_secret`. -/
  | cHsTraffic
  /-- §7.1, `server_handshake_traffic_secret`. -/
  | sHsTraffic
  /-- §7.1, `client_application_traffic_secret_0`. -/
  | cApTraffic
  /-- §7.1, `server_application_traffic_secret_0`. -/
  | sApTraffic
  /-- §7.1, `exporter_master_secret`. -/
  | expMaster
  /-- §7.1, `resumption_master_secret`. -/
  | resMaster
  /-- §7.3, the record-protection key. -/
  | key
  /-- §7.3, the record-protection static IV. -/
  | iv
  /-- §4.4.4, the `finished_key` an endpoint's Finished MAC is keyed with. -/
  | finished
  /-- §7.2, the successor of an application traffic secret. -/
  | trafficUpd
  deriving Repr, BEq, DecidableEq, Inhabited

/-- The exact label strings of RFC 8446. -/
@[expose] def Label.text : Label → String
  | .derived => "derived"
  | .extBinder => "ext binder"
  | .resBinder => "res binder"
  | .ceTraffic => "c e traffic"
  | .eExpMaster => "e exp master"
  | .cHsTraffic => "c hs traffic"
  | .sHsTraffic => "s hs traffic"
  | .cApTraffic => "c ap traffic"
  | .sApTraffic => "s ap traffic"
  | .expMaster => "exp master"
  | .resMaster => "res master"
  | .key => "key"
  | .iv => "iv"
  | .finished => "finished"
  | .trafficUpd => "traffic upd"

/-- **The labels are RFC 8446's, spelled out.** A typo anywhere in `Label.text`
fails this theorem, and every derivation below names a `Label` rather than a
string, so a typo cannot hide in a call site either. -/
theorem Label.text_rfc8446 :
    Label.text .derived = "derived" ∧
    Label.text .extBinder = "ext binder" ∧
    Label.text .resBinder = "res binder" ∧
    Label.text .ceTraffic = "c e traffic" ∧
    Label.text .eExpMaster = "e exp master" ∧
    Label.text .cHsTraffic = "c hs traffic" ∧
    Label.text .sHsTraffic = "s hs traffic" ∧
    Label.text .cApTraffic = "c ap traffic" ∧
    Label.text .sApTraffic = "s ap traffic" ∧
    Label.text .expMaster = "exp master" ∧
    Label.text .resMaster = "res master" ∧
    Label.text .key = "key" ∧
    Label.text .iv = "iv" ∧
    Label.text .finished = "finished" ∧
    Label.text .trafficUpd = "traffic upd" :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ## The `HkdfLabel` wire structure

```
struct {
    uint16 length = Length;
    opaque label<7..255> = "tls13 " + Label;
    opaque context<0..255> = Context;
} HkdfLabel;
```
-/

/-- RFC 8446 §7.1's `HkdfLabel`. `label` is the bare `Label`; `encode` prepends
the mandatory `"tls13 "`. -/
structure HkdfLabel where
  /-- The requested output length, in bytes. -/
  length : Nat
  /-- `Label`, without the `"tls13 "` prefix. -/
  label : ByteArray
  /-- `Context`. -/
  context : ByteArray

/-- A big-endian `uint16`. -/
@[expose] def uint16 (n : Nat) : ByteArray :=
  ByteArray.mk #[UInt8.ofNat (n >>> 8), UInt8.ofNat n]

/-- A TLS `opaque x<0..255>` vector: a one-byte length followed by the bytes. -/
@[expose] def opaque8 (value : ByteArray) : ByteArray :=
  ByteArray.mk #[UInt8.ofNat value.size] ++ value

/-- `"tls13 "`, as the six ASCII bytes it is. -/
@[expose] def labelPrefix : ByteArray :=
  ByteArray.mk #[0x74, 0x6c, 0x73, 0x31, 0x33, 0x20]

/-- The wire encoding of an `HkdfLabel`. -/
@[expose] def HkdfLabel.encode (l : HkdfLabel) : ByteArray :=
  uint16 l.length ++ opaque8 (labelPrefix ++ l.label) ++ opaque8 l.context

/-- **`labelPrefix` is `"tls13 "`.** -/
theorem labelPrefix_eq : "tls13 ".toUTF8 = labelPrefix := by
  rw [String.toUTF8_eq_toByteArray]; rfl

/-- **The `HkdfLabel` encoding, byte for byte**: two big-endian length bytes,
the one-byte length of `"tls13 " + Label`, the six bytes of `"tls13 "`, the
label, the one-byte context length, and the context. Nothing else, in no other
order. -/
theorem HkdfLabel.encode_bytes (l : HkdfLabel) :
    l.encode =
      ByteArray.mk #[UInt8.ofNat (l.length >>> 8), UInt8.ofNat l.length,
          UInt8.ofNat (6 + l.label.size), 0x74, 0x6c, 0x73, 0x31, 0x33, 0x20] ++
        l.label ++ ByteArray.mk #[UInt8.ofNat l.context.size] ++ l.context := by
  unfold HkdfLabel.encode opaque8 uint16
  rw [show (labelPrefix ++ l.label).size = 6 + l.label.size from by
    rw [ByteArray.size_append]; rfl]
  simp only [ByteArray.append_assoc]
  rfl

/-! ## `HKDF-Expand-Label` and `Derive-Secret` -/

/--
```
HKDF-Expand-Label(Secret, Label, Context, Length) =
     HKDF-Expand(Secret, HkdfLabel, Length)
```
-/
@[expose] def expandLabel (H : Hkdf) (secret : ByteArray) (label : Label)
    (context : ByteArray) (length : Nat) : ByteArray :=
  H.expand secret (HkdfLabel.encode ⟨length, label.text.toUTF8, context⟩) length

/--
```
Derive-Secret(Secret, Label, Messages) =
     HKDF-Expand-Label(Secret, Label, Transcript-Hash(Messages), Hash.length)
```
The transcript hash is passed in; computing it is the state machine's job. -/
@[expose] def deriveSecret (H : Hkdf) (secret : ByteArray) (label : Label)
    (transcriptHash : ByteArray) : ByteArray :=
  expandLabel H secret label transcriptHash H.hashLen

/-! ## The §7.1 diagram, as data -/

/-- The message sequences §7.1's diagram feeds to `Transcript-Hash` in the
`Messages` column of a `Derive-Secret`. -/
inductive Transcript where
  /-- `""` — the empty message sequence, whose hash is `Hash("")`. -/
  | empty
  /-- ClientHello. -/
  | clientHello
  /-- ClientHello … ServerHello. -/
  | serverHello
  /-- ClientHello … server Finished. -/
  | serverFinished
  /-- ClientHello … client Finished. -/
  | clientFinished
  deriving Repr, BEq, DecidableEq, Inhabited

/-- The three secrets of §7.1's `HKDF-Extract` chain, in order. -/
inductive Secret where
  /-- `HKDF-Extract(0, PSK)`. -/
  | early
  /-- `HKDF-Extract(Derive-Secret(Early, "derived", ""), (EC)DHE)`. -/
  | handshake
  /-- `HKDF-Extract(Derive-Secret(Handshake, "derived", ""), 0)`. -/
  | master
  deriving Repr, BEq, DecidableEq, Inhabited

/-- Every named output §7.1 produces with a `Derive-Secret` off the extract
chain. The tables below give each one's parent, label and transcript: together
they *are* the diagram. -/
inductive Derived where
  /-- `binder_key`, external PSK. -/
  | extBinder
  /-- `binder_key`, resumption PSK. -/
  | resBinder
  /-- `client_early_traffic_secret`. -/
  | ceTraffic
  /-- `early_exporter_master_secret`. -/
  | eExpMaster
  /-- `client_handshake_traffic_secret`. -/
  | cHsTraffic
  /-- `server_handshake_traffic_secret`. -/
  | sHsTraffic
  /-- `client_application_traffic_secret_0`. -/
  | cApTraffic
  /-- `server_application_traffic_secret_0`. -/
  | sApTraffic
  /-- `exporter_master_secret`. -/
  | expMaster
  /-- `resumption_master_secret`. -/
  | resMaster
  deriving Repr, BEq, DecidableEq, Inhabited

/-- Which extract-chain secret each output hangs off. -/
@[expose] def Derived.parent : Derived → Secret
  | .extBinder | .resBinder | .ceTraffic | .eExpMaster => .early
  | .cHsTraffic | .sHsTraffic => .handshake
  | .cApTraffic | .sApTraffic | .expMaster | .resMaster => .master

/-- The `Derive-Secret` label of each output. -/
@[expose] def Derived.label : Derived → Label
  | .extBinder => .extBinder
  | .resBinder => .resBinder
  | .ceTraffic => .ceTraffic
  | .eExpMaster => .eExpMaster
  | .cHsTraffic => .cHsTraffic
  | .sHsTraffic => .sHsTraffic
  | .cApTraffic => .cApTraffic
  | .sApTraffic => .sApTraffic
  | .expMaster => .expMaster
  | .resMaster => .resMaster

/-- The transcript each output binds. Note that the two binder keys bind the
*empty* message sequence: the truncated ClientHello of §4.2.11.2 is an input to
the binder value, not to `binder_key`. -/
@[expose] def Derived.context : Derived → Transcript
  | .extBinder | .resBinder => .empty
  | .ceTraffic | .eExpMaster => .clientHello
  | .cHsTraffic | .sHsTraffic => .serverHello
  | .cApTraffic | .sApTraffic | .expMaster => .serverFinished
  | .resMaster => .clientFinished

/-- **The RFC 8446 §7.1 diagram, tabulated.** For every named secret: the
secret it is derived from, the exact label string, and the message sequence
whose transcript hash is its context. This single theorem is the specification's
statement of the derivation tree's shape. -/
theorem Derived.tree_rfc8446 :
    (Derived.extBinder.parent, Derived.extBinder.label.text,
        Derived.extBinder.context) = (Secret.early, "ext binder", Transcript.empty) ∧
    (Derived.resBinder.parent, Derived.resBinder.label.text,
        Derived.resBinder.context) = (Secret.early, "res binder", Transcript.empty) ∧
    (Derived.ceTraffic.parent, Derived.ceTraffic.label.text,
        Derived.ceTraffic.context) = (Secret.early, "c e traffic", Transcript.clientHello) ∧
    (Derived.eExpMaster.parent, Derived.eExpMaster.label.text,
        Derived.eExpMaster.context) = (Secret.early, "e exp master", Transcript.clientHello) ∧
    (Derived.cHsTraffic.parent, Derived.cHsTraffic.label.text,
        Derived.cHsTraffic.context) = (Secret.handshake, "c hs traffic", Transcript.serverHello) ∧
    (Derived.sHsTraffic.parent, Derived.sHsTraffic.label.text,
        Derived.sHsTraffic.context) = (Secret.handshake, "s hs traffic", Transcript.serverHello) ∧
    (Derived.cApTraffic.parent, Derived.cApTraffic.label.text,
        Derived.cApTraffic.context) =
      (Secret.master, "c ap traffic", Transcript.serverFinished) ∧
    (Derived.sApTraffic.parent, Derived.sApTraffic.label.text,
        Derived.sApTraffic.context) =
      (Secret.master, "s ap traffic", Transcript.serverFinished) ∧
    (Derived.expMaster.parent, Derived.expMaster.label.text,
        Derived.expMaster.context) = (Secret.master, "exp master", Transcript.serverFinished) ∧
    (Derived.resMaster.parent, Derived.resMaster.label.text,
        Derived.resMaster.context) =
      (Secret.master, "res master", Transcript.clientFinished) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ## Evaluating the diagram -/

/-- The non-derived inputs of one handshake's key schedule: the PSK, the (EC)DHE
shared secret, and the transcript hashes. -/
structure Inputs where
  /-- The pre-shared key; `zeros H.hashLen` when there is none. -/
  psk : ByteArray
  /-- The (EC)DHE shared secret; `zeros H.hashLen` when there is none. -/
  ecdhe : ByteArray
  /-- `Transcript-Hash` of each message sequence the diagram binds. -/
  hash : Transcript → ByteArray

/-- The inputs of a full handshake with no pre-shared key: `PSK = 0`. -/
@[expose] def fullHandshakeInputs (H : Hkdf) (ecdhe : ByteArray)
    (hash : Transcript → ByteArray) : Inputs :=
  { psk := zeros H.hashLen, ecdhe, hash }

/-- `Early Secret = HKDF-Extract(0, PSK)`. -/
@[expose] def earlySecret (H : Hkdf) (inp : Inputs) : ByteArray :=
  H.extract (zeros H.hashLen) inp.psk

/-- `Handshake Secret = HKDF-Extract(Derive-Secret(Early, "derived", ""), (EC)DHE)`. -/
@[expose] def handshakeSecret (H : Hkdf) (inp : Inputs) : ByteArray :=
  H.extract (deriveSecret H (earlySecret H inp) .derived (inp.hash .empty)) inp.ecdhe

/-- `Master Secret = HKDF-Extract(Derive-Secret(Handshake, "derived", ""), 0)`. -/
@[expose] def masterSecret (H : Hkdf) (inp : Inputs) : ByteArray :=
  H.extract (deriveSecret H (handshakeSecret H inp) .derived (inp.hash .empty))
    (zeros H.hashLen)

/-- The extract chain, evaluated. -/
@[expose] def secret (H : Hkdf) (inp : Inputs) : Secret → ByteArray
  | .early => earlySecret H inp
  | .handshake => handshakeSecret H inp
  | .master => masterSecret H inp

/-- A named §7.1 secret, evaluated: `Derive-Secret` of its parent, under its
label, over the hash of the transcript it binds. -/
@[expose] def derived (H : Hkdf) (inp : Inputs) (d : Derived) : ByteArray :=
  deriveSecret H (secret H inp d.parent) d.label (inp.hash d.context)

/-! ## The expansions with an empty context

RFC 8446 §7.3 (`key`, `iv`), §4.4.4 (`finished`) and §7.2 (`traffic upd`) expand
a traffic secret with the **empty byte string** as context — not the hash of an
empty transcript. Confusing the two is a classic implementation bug, so they are
separate definitions here. -/

/-- §7.3: `[sender]_write_key = HKDF-Expand-Label(Secret, "key", "", key_length)`. -/
@[expose] def trafficKey (H : Hkdf) (secret : ByteArray) (keyLength : Nat) : ByteArray :=
  expandLabel H secret .key ByteArray.empty keyLength

/-- §7.3: `[sender]_write_iv = HKDF-Expand-Label(Secret, "iv", "", iv_length)`. -/
@[expose] def trafficIv (H : Hkdf) (secret : ByteArray) (ivLength : Nat) : ByteArray :=
  expandLabel H secret .iv ByteArray.empty ivLength

/-- §4.4.4:
`finished_key = HKDF-Expand-Label(BaseKey, "finished", "", Hash.length)`. -/
@[expose] def finishedKey (H : Hkdf) (secret : ByteArray) : ByteArray :=
  expandLabel H secret .finished ByteArray.empty H.hashLen

/-- §7.2:
`application_traffic_secret_N+1 =
   HKDF-Expand-Label(application_traffic_secret_N, "traffic upd", "", Hash.length)`. -/
@[expose] def nextTrafficSecret (H : Hkdf) (secret : ByteArray) : ByteArray :=
  expandLabel H secret .trafficUpd ByteArray.empty H.hashLen

/-- **The empty-context expansions really use the empty byte string.** Stated
against `expandLabel` so the context argument is visible; contrast `derived`,
every one of whose contexts is a transcript hash. -/
theorem emptyContext_rfc8446 (H : Hkdf) (s : ByteArray) (keyLength ivLength : Nat) :
    trafficKey H s keyLength = expandLabel H s .key ByteArray.empty keyLength ∧
    trafficIv H s ivLength = expandLabel H s .iv ByteArray.empty ivLength ∧
    finishedKey H s = expandLabel H s .finished ByteArray.empty H.hashLen ∧
    nextTrafficSecret H s = expandLabel H s .trafficUpd ByteArray.empty H.hashLen :=
  ⟨rfl, rfl, rfl, rfl⟩

/-! ## Describing traffic epochs

A record-layer nonce is unique only within one traffic epoch: sequence numbers
restart at zero whenever a new traffic secret is installed. The definitions
below therefore name an epoch by the derivation history that produced it and
record the order in which an engine uses those histories.

This is deliberately a *structural* account. It does not claim that distinct
derivations produce distinct byte strings. `HKDF-Expand-Label` has a finite
output, so global injectivity over arbitrary secrets and contexts is impossible;
an unbounded chain of fixed-size traffic secrets must eventually collide as
well. Byte-level collision freedom can only be a condition on the particular
finite trace under consideration (or a probabilistic cryptographic claim), not
a deterministic property of HKDF. -/

/-- `n` applications of the §7.2 traffic-secret update: the traffic secret in
force after `n` KeyUpdates of an epoch that started from `secret`. -/
@[expose] def trafficIter (H : Hkdf) (secret : ByteArray) : Nat → ByteArray
  | 0 => secret
  | n + 1 => nextTrafficSecret H (trafficIter H secret n)

/-- **An epoch of a connection, named by the derivation that produced it.** A
traffic epoch is a §7.1 `HKDF-Expand-Label` node — a parent secret, a label and
a context — followed by some number of §7.2 `"traffic upd"` steps. Epoch
descriptors are equal exactly when these four structural components agree; two
different descriptors may still evaluate to the same finite byte string.

`updates` is unbounded, so this names every epoch a connection can reach no
matter how many KeyUpdates it performs. -/
structure Epoch where
  /-- The secret `HKDF-Expand-Label` was applied to. -/
  parent : ByteArray
  /-- The label the epoch's base secret was derived under. -/
  label : Label
  /-- The context of that derivation — a transcript hash, for a §7.1 node. -/
  context : ByteArray
  /-- The number of §7.2 KeyUpdates performed since. -/
  updates : Nat

/-- The §7.1 traffic secret an epoch starts from, before any KeyUpdate. -/
@[expose] def Epoch.base (H : Hkdf) (e : Epoch) : ByteArray :=
  expandLabel H e.parent e.label e.context H.hashLen

/-- The traffic secret an epoch is protecting records under. -/
@[expose] def Epoch.secret (H : Hkdf) (e : Epoch) : ByteArray :=
  trafficIter H (e.base H) e.updates

/-- An epoch descriptor names a real epoch only when its base secret is a §7.1
derivation rather than itself a §7.2 update — otherwise `updates` would not
count the KeyUpdates. Every label a TLS 1.3 traffic epoch is derived under
(`"c hs traffic"`, `"s hs traffic"`, `"c ap traffic"`, `"s ap traffic"`,
`"c e traffic"`) satisfies this. -/
@[expose] def Epoch.Valid (e : Epoch) : Prop := e.label ≠ Label.trafficUpd

/-- The successor epoch a KeyUpdate installs. -/
@[expose] def Epoch.next (e : Epoch) : Epoch := { e with updates := e.updates + 1 }

theorem Epoch.secret_next (H : Hkdf) (e : Epoch) :
    e.next.secret H = nextTrafficSecret H (e.secret H) := rfl

theorem Epoch.next_valid {e : Epoch} (h : e.Valid) : e.next.Valid := h

/-! ### The order the epochs of a connection are used in

A connection moves through its epochs in one direction: it may install a new
§7.1 traffic secret at a later stage of the handshake, or roll the current one
forward with a KeyUpdate, but it never goes back. `Epoch.Lt` is that order, and
`Tls.Record.EpochsFrom` uses it to state that a run's derivation-history list is
strictly increasing. This order is independent of whether two evaluated secret
byte strings happen to collide. -/

/-- The stage of a connection at which an epoch derived under this label becomes
current: early data, then the handshake, then the application data. Labels that
never name a traffic epoch share the last stage; nothing below depends on their
value. -/
@[expose] def Label.stage : Label → Nat
  | .ceTraffic => 0
  | .cHsTraffic | .sHsTraffic => 1
  | .cApTraffic | .sApTraffic => 2
  | _ => 3

/-- `e` is used strictly before `e'`: either `e'`'s base secret belongs to a
later stage of the handshake, or the two are the same §7.1 node and `e'` has had
strictly more KeyUpdates. -/
@[expose] def Epoch.Lt (e e' : Epoch) : Prop :=
  e.label.stage < e'.label.stage ∨
    (e.parent = e'.parent ∧ e.label = e'.label ∧ e.context = e'.context ∧
      e.updates < e'.updates)

/-- `Epoch.Lt`, reflexively closed. -/
@[expose] def Epoch.Le (e e' : Epoch) : Prop := e = e' ∨ e.Lt e'

theorem Epoch.Le.refl (e : Epoch) : e.Le e := Or.inl rfl

theorem Epoch.lt_next (e : Epoch) : e.Lt e.next :=
  Or.inr ⟨rfl, rfl, rfl, Nat.lt_succ_self _⟩

theorem Epoch.Lt.trans {a b c : Epoch} (h1 : a.Lt b) (h2 : b.Lt c) : a.Lt c := by
  rcases h1 with h1 | ⟨p1, l1, c1, u1⟩ <;> rcases h2 with h2 | ⟨p2, l2, c2, u2⟩
  · exact Or.inl (Nat.lt_trans h1 h2)
  · exact Or.inl (l2 ▸ h1)
  · exact Or.inl (l1 ▸ h2)
  · exact Or.inr ⟨p1.trans p2, l1.trans l2, c1.trans c2, Nat.lt_trans u1 u2⟩

theorem Epoch.lt_of_lt_of_le {a b c : Epoch} (h1 : a.Lt b) (h2 : b.Le c) : a.Lt c := by
  rcases h2 with rfl | h2
  · exact h1
  · exact h1.trans h2

theorem Epoch.Lt.ne {a b : Epoch} (h : a.Lt b) : a ≠ b := by
  intro heq
  subst heq
  rcases h with h | ⟨-, -, -, h⟩ <;> omega

/-- `e` is at or after the epoch `o`, where `none` means "no epoch has been
installed yet" and so precedes every epoch. -/
@[expose] def Epoch.LeOpt : Option Epoch → Epoch → Prop
  | none, _ => True
  | some e, e' => e.Le e'

theorem Epoch.LeOpt.none_le (e : Epoch) : Epoch.LeOpt none e := trivial

end Spec
end KeySchedule
end TLS13
