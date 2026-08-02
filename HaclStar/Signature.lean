module

public section

/-!
Signature verification and signing through HACL*.

The wrappers validate every fixed-size input before entering C. P-256 uses a
SEC 1 uncompressed public key and separate fixed-width ECDSA scalars; Ed25519
uses its native 32-byte public key and 64-byte signature encodings.

Signing takes a private key. Ed25519 is deterministic (RFC 8032) and cannot
fail on valid lengths, so it returns a `ByteArray` directly — a 64-byte
signature on success, or an empty `ByteArray` if `privateKey` is not 32 bytes.
ECDSA P-256 takes an explicit per-message nonce and returns `Option ByteArray`,
`none` when a length is wrong or HACL rejects the scalar/nonce as out of range.
-/

namespace HaclStar
namespace Signature

/-- Verify ECDSA P-256 with SHA-256. `publicKey` is `04 || x || y`; `r` and
`s` are exactly 32-byte, big-endian scalars. -/
@[extern "tls13_hacl_p256_ecdsa_sha256_verify"]
opaque ecdsaP256Sha256
    (publicKey message r s : ByteArray) : Bool

/-- Verify an RFC 8032 Ed25519 signature. -/
@[extern "tls13_hacl_ed25519_verify"]
opaque ed25519
    (publicKey message signature : ByteArray) : Bool

/-- Sign `message` with a 32-byte Ed25519 `privateKey` (RFC 8032). Returns the
64-byte signature, or an empty `ByteArray` if `privateKey` is not 32 bytes. -/
@[extern "tls13_hacl_ed25519_sign"]
opaque ed25519Sign
    (privateKey message : ByteArray) : ByteArray

/-- Sign `message` (SHA-256) with a 32-byte P-256 `privateKey` scalar and a
32-byte per-message `nonce`. Returns the 64-byte `r || s` signature, or `none`
if a length is wrong or the scalar/nonce is out of range. -/
@[extern "tls13_hacl_p256_ecdsa_sha256_sign"]
opaque ecdsaP256Sha256Sign
    (privateKey message nonce : ByteArray) : Option ByteArray

end Signature
end HaclStar
