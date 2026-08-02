module

public import HaclStar.Hkdf
public import HaclStar.Sha256

public section

/-!
TLS 1.3 key schedule (RFC 8446 §7.1), for SHA-256 cipher suites.

The cryptographic core is HKDF-Extract/Expand (`HaclStar.Hkdf`); this module
adds the pure-Lean labelled-derivation layer on top: `HKDF-Expand-Label`,
`Derive-Secret`, and the extract steps that chain the Early / Handshake /
Master secrets. Everything here is a total function of its inputs — the state
machine that sequences these calls with real handshake transcripts lives above.
-/

namespace TLS13
namespace KeySchedule

open HaclStar

/-- Output length of the suite hash (SHA-256), in bytes. -/
def hashLen : Nat := 32

/-- The all-zero HashLen-byte string — TLS 1.3's `0` for a secret-sized value
(the default salt and the no-PSK / no-(EC)DHE inputs). -/
def zeros : ByteArray :=
  ByteArray.mk ((List.replicate hashLen (0 : UInt8)).toArray)

private def u16be (n : Nat) : ByteArray :=
  ByteArray.mk #[UInt8.ofNat (n >>> 8), UInt8.ofNat n]

/-- The `HkdfLabel` structure serialized per RFC 8446 §7.1:
`length` (uint16), then `"tls13 " ++ label` and `context`, each with a one-byte
length prefix. `label` is expected to be ≤ 249 bytes and `context` ≤ 255. -/
def hkdfLabel (length : Nat) (label context : ByteArray) : ByteArray :=
  let full := "tls13 ".toUTF8 ++ label
  u16be length
    ++ ByteArray.mk #[UInt8.ofNat full.size] ++ full
    ++ ByteArray.mk #[UInt8.ofNat context.size] ++ context

/-- `HKDF-Expand-Label(secret, label, context, length)`. -/
def expandLabel (secret : ByteArray) (label : String) (context : ByteArray)
    (length : Nat) : ByteArray :=
  Hkdf.expandSha256 secret (hkdfLabel length label.toUTF8 context) (UInt32.ofNat length)

/-- `Derive-Secret(secret, label, transcriptHash)` — `HKDF-Expand-Label` with the
transcript hash as context and the hash length as the output length. The caller
passes the already-computed transcript hash (SHA-256 of the handshake messages),
so this stays independent of transcript bookkeeping. -/
def deriveSecret (secret : ByteArray) (label : String) (transcriptHash : ByteArray) : ByteArray :=
  expandLabel secret label transcriptHash hashLen

/-- Early Secret = `HKDF-Extract(0, PSK)`. With no pre-shared key, `psk` is the
all-zero string, giving RFC 8448's `33ad0a1c…`. -/
def earlySecret (psk : ByteArray := zeros) : ByteArray :=
  Hkdf.extractSha256 zeros psk

/-- Handshake Secret = `HKDF-Extract(Derive-Secret(Early, "derived", ""), (EC)DHE)`.
`ecdheSecret` is the X25519 shared secret; `emptyHash` is SHA-256 of the empty
string (the transcript hash used by the "derived" step). -/
def handshakeSecret (early ecdheSecret emptyHash : ByteArray) : ByteArray :=
  Hkdf.extractSha256 (deriveSecret early "derived" emptyHash) ecdheSecret

/-- Master Secret = `HKDF-Extract(Derive-Secret(Handshake, "derived", ""), 0)`. -/
def masterSecret (handshake emptyHash : ByteArray) : ByteArray :=
  Hkdf.extractSha256 (deriveSecret handshake "derived" emptyHash) zeros

end KeySchedule
end TLS13
