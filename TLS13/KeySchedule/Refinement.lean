module

public import TLS13.KeySchedule
public import TLS13.KeySchedule.Spec
import all TLS13.KeySchedule

public section

/-!
# `TLS13.KeySchedule` refines RFC 8446 §7.1

Kernel-checked laws tying the executable key schedule in `TLS13.KeySchedule` to
the declarative specification in `TLS13.KeySchedule.Spec`.

Every theorem is stated for an **arbitrary** `Spec.Hkdf` that the HACL\*
bindings implement (`Implements`), never for one fixed model of HKDF. So none of
them depends on what HKDF-Extract and HKDF-Expand compute: what is proved is
that the implementation applies them in the RFC's *shape* — the RFC's labels,
the RFC's contexts, the RFC's parent secrets, the RFC's output lengths. This is
the same device `Tls.Record.open_seal` uses for the opaque AEAD.

The one theorem here that is unconditionally about bytes is
`hkdfLabel_encode` / `Spec.HkdfLabel.encode_bytes`: the `HkdfLabel`
serialization is pure Lean, so its wire image is proved outright.
-/

namespace TLS13
namespace KeySchedule

/-- `H` is an HKDF interface implemented by this repository's HACL\* SHA-256
bindings. Refinement theorems take this as a hypothesis rather than fixing `H`,
so they say something about the derivation structure and nothing about the
primitive. -/
structure Implements (H : Spec.Hkdf) : Prop where
  /-- The interface's hash length is the suite's. -/
  hashLen_eq : H.hashLen = hashLen
  /-- `extract` is HKDF-Extract-SHA256. -/
  extract_eq : ∀ salt ikm, H.extract salt ikm = HaclStar.Hkdf.extractSha256 salt ikm
  /-- `expand` is HKDF-Expand-SHA256. -/
  expand_eq : ∀ prk info len,
    H.expand prk info len = HaclStar.Hkdf.expandSha256 prk info (UInt32.ofNat len)

/-- The HACL\* SHA-256 instance of the interface. Nothing below needs it — the
theorems are parametric — but it witnesses that `Implements` is inhabited, so
none of them is vacuous. -/
@[expose] def hacl : Spec.Hkdf where
  hashLen := hashLen
  extract := HaclStar.Hkdf.extractSha256
  expand := fun prk info len => HaclStar.Hkdf.expandSha256 prk info (UInt32.ofNat len)

/-- `Implements` is not vacuous. -/
theorem hacl_implements : Implements hacl :=
  ⟨rfl, fun _ _ => rfl, fun _ _ _ => rfl⟩

/-- The all-zero secret-sized string is the specification's. -/
theorem zeros_eq : zeros = Spec.zeros hashLen := by rfl

/-- **`hkdfLabel` serializes RFC 8446 §7.1's `HkdfLabel` structure.** Pure
serialization, so this holds outright — no hypothesis about HKDF. Combined with
`Spec.HkdfLabel.encode_bytes` it pins the wire image byte for byte, including
the six bytes of the `"tls13 "` prefix and the length that counts them. -/
theorem hkdfLabel_encode (length : Nat) (label context : ByteArray) :
    hkdfLabel length label context =
      Spec.HkdfLabel.encode ⟨length, label, context⟩ := by
  unfold hkdfLabel Spec.HkdfLabel.encode Spec.opaque8 Spec.uint16 u16be
  rw [← Spec.labelPrefix_eq]
  simp only [ByteArray.append_assoc]

/-- **`hkdfLabel`, byte for byte.** -/
theorem hkdfLabel_bytes (length : Nat) (label context : ByteArray) :
    hkdfLabel length label context =
      ByteArray.mk #[UInt8.ofNat (length >>> 8), UInt8.ofNat length,
          UInt8.ofNat (6 + label.size), 0x74, 0x6c, 0x73, 0x31, 0x33, 0x20] ++
        label ++ ByteArray.mk #[UInt8.ofNat context.size] ++ context := by
  rw [hkdfLabel_encode]
  exact Spec.HkdfLabel.encode_bytes _

/-- **`expandLabel` is `HKDF-Expand-Label`**: the implementation expands the
secret with the specification's `HkdfLabel` for that label, context and length,
and asks for exactly that many bytes. -/
theorem expandLabel_spec {H : Spec.Hkdf} (hi : Implements H) (secret : ByteArray)
    (label : Spec.Label) (context : ByteArray) (length : Nat) :
    expandLabel secret label.text context length =
      Spec.expandLabel H secret label context length := by
  unfold expandLabel Spec.expandLabel
  rw [hi.expand_eq, hkdfLabel_encode]

/-- **`deriveSecret` is `Derive-Secret`**: `HKDF-Expand-Label` with the
transcript hash as context and `Hash.length` as the output length. -/
theorem deriveSecret_spec {H : Spec.Hkdf} (hi : Implements H) (secret : ByteArray)
    (label : Spec.Label) (transcriptHash : ByteArray) :
    deriveSecret secret label.text transcriptHash =
      Spec.deriveSecret H secret label transcriptHash := by
  unfold deriveSecret Spec.deriveSecret
  rw [hi.hashLen_eq, expandLabel_spec hi]

/-- **The Early Secret is `HKDF-Extract(0, PSK)`.** -/
theorem earlySecret_spec {H : Spec.Hkdf} (hi : Implements H) (inp : Spec.Inputs) :
    earlySecret inp.psk = Spec.earlySecret H inp := by
  unfold earlySecret Spec.earlySecret
  rw [hi.extract_eq, hi.hashLen_eq, ← zeros_eq]

/-- The no-PSK case: the implementation's default IKM is the all-zero string. -/
theorem earlySecret_noPsk_spec {H : Spec.Hkdf} (hi : Implements H) (inp : Spec.Inputs)
    (hpsk : inp.psk = zeros) : earlySecret = Spec.earlySecret H inp := by
  rw [← earlySecret_spec hi inp, hpsk]

/-- **The Handshake Secret is
`HKDF-Extract(Derive-Secret(Early, "derived", ""), (EC)DHE)`** — note the
*empty* transcript hash at the `"derived"` step, and that the salt is the Early
Secret rather than the (EC)DHE input. -/
theorem handshakeSecret_spec {H : Spec.Hkdf} (hi : Implements H) (inp : Spec.Inputs) :
    handshakeSecret (earlySecret inp.psk) inp.ecdhe (inp.hash .empty) =
      Spec.handshakeSecret H inp := by
  unfold handshakeSecret Spec.handshakeSecret
  rw [hi.extract_eq, ← earlySecret_spec hi, ← deriveSecret_spec hi]
  rfl

/-- **The Master Secret is
`HKDF-Extract(Derive-Secret(Handshake, "derived", ""), 0)`** — again the empty
transcript hash, and the all-zero IKM. -/
theorem masterSecret_spec {H : Spec.Hkdf} (hi : Implements H) (inp : Spec.Inputs) :
    masterSecret (Spec.handshakeSecret H inp) (inp.hash .empty) =
      Spec.masterSecret H inp := by
  unfold masterSecret Spec.masterSecret
  rw [hi.extract_eq, hi.hashLen_eq, ← zeros_eq, ← deriveSecret_spec hi]
  rfl

/-- The extract chain, as the engines build it: Early from the PSK, Handshake
from Early and the (EC)DHE secret, Master from Handshake. -/
theorem secret_spec {H : Spec.Hkdf} (hi : Implements H) (inp : Spec.Inputs) :
    earlySecret inp.psk = Spec.secret H inp .early ∧
    handshakeSecret (earlySecret inp.psk) inp.ecdhe (inp.hash .empty) =
      Spec.secret H inp .handshake ∧
    masterSecret (Spec.secret H inp .handshake) (inp.hash .empty) =
      Spec.secret H inp .master :=
  ⟨earlySecret_spec hi inp, handshakeSecret_spec hi inp, masterSecret_spec hi inp⟩

/-- **A `Derive-Secret` node of the §7.1 diagram, as the engines call it.** The
implementation's `deriveSecret` applied to a node's parent secret, the text of
its label and the hash of the transcript it binds is exactly the specification's
value for that node — so a call site that passes the wrong parent, the wrong
label or the wrong transcript cannot satisfy this equation. -/
theorem derived_spec {H : Spec.Hkdf} (hi : Implements H) (inp : Spec.Inputs)
    (d : Spec.Derived) :
    deriveSecret (Spec.secret H inp d.parent) d.label.text (inp.hash d.context) =
      Spec.derived H inp d :=
  deriveSecret_spec hi _ _ _

/-! ## Engine-facing forms

The state machines compute the schedule from values they hold — an ECDHE output,
a stored handshake secret, a transcript hash they just took — rather than from a
`Spec.Inputs` record. These are the same theorems with those values supplied as
hypotheses, so an engine law can discharge them one equation at a time. -/

/-- The Handshake Secret as an engine builds it: from the default (all-zero)
PSK, the ECDHE shared secret, and the hash of the empty transcript. -/
theorem handshakeSecret_node_spec {H : Spec.Hkdf} (hi : Implements H)
    (inp : Spec.Inputs) {shared emptyHash : ByteArray} (hpsk : inp.psk = zeros)
    (hecdhe : inp.ecdhe = shared) (hempty : inp.hash .empty = emptyHash) :
    handshakeSecret earlySecret shared emptyHash = Spec.secret H inp .handshake := by
  have h := handshakeSecret_spec hi inp
  rw [hpsk, hecdhe, hempty] at h
  exact h

/-- The Master Secret as an engine builds it: from the handshake secret it
stored and the hash of the empty transcript. -/
theorem masterSecret_node_spec {H : Spec.Hkdf} (hi : Implements H)
    (inp : Spec.Inputs) {handshake emptyHash : ByteArray}
    (hhandshake : handshake = Spec.secret H inp .handshake)
    (hempty : inp.hash .empty = emptyHash) :
    masterSecret handshake emptyHash = Spec.secret H inp .master := by
  have h := masterSecret_spec hi inp
  rw [hempty] at h
  rw [hhandshake]
  exact h

/-- One `Derive-Secret` node as an engine calls it: the parent secret it holds
and the transcript hash it just computed. The hypotheses are exactly "this is
the RFC's parent" and "this is the RFC's transcript"; the label comes from the
node itself, so a mistyped label cannot satisfy the conclusion. -/
theorem deriveSecret_node_spec {H : Spec.Hkdf} (hi : Implements H)
    (inp : Spec.Inputs) (d : Spec.Derived) {parentSecret transcriptHash : ByteArray}
    (hparent : parentSecret = Spec.secret H inp d.parent)
    (hhash : inp.hash d.context = transcriptHash) :
    deriveSecret parentSecret d.label.text transcriptHash = Spec.derived H inp d := by
  rw [hparent, ← hhash]
  exact derived_spec hi inp d

end KeySchedule
end TLS13
