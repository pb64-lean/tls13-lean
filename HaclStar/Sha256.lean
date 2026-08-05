module

public section

/-!
SHA-256, SHA-384, and SHA-512 via HACL*'s one-shot `Hacl_Hash_SHA2_hash_*`
functions. Each binding is pure and total: the digest is a function of the
input bytes. TLS 1.3 uses SHA-256 as the transcript and HKDF hash for the
`*_SHA256` cipher suites; the wider hashes are also used by X.509.
-/

namespace HaclStar

/-- Length of a SHA-256 digest, in bytes. -/
def sha256DigestLen : Nat := 32

/-- The SHA-256 digest of `data` (32 bytes). An input too large for HACL's
`uint32_t` length API returns the empty `ByteArray` misuse sentinel. -/
@[extern "tls13_hacl_sha256"]
opaque sha256 (data : ByteArray) : ByteArray

/-- Length of a SHA-384 digest, in bytes. -/
def sha384DigestLen : Nat := 48

/-- The SHA-384 digest of `data` (48 bytes). An input too large for HACL's
`uint32_t` length API returns the empty `ByteArray` misuse sentinel. -/
@[extern "tls13_hacl_sha384"]
opaque sha384 (data : ByteArray) : ByteArray

/-- Length of a SHA-512 digest, in bytes. -/
def sha512DigestLen : Nat := 64

/-- The SHA-512 digest of `data` (64 bytes). An input too large for HACL's
`uint32_t` length API returns the empty `ByteArray` misuse sentinel. -/
@[extern "tls13_hacl_sha512"]
opaque sha512 (data : ByteArray) : ByteArray

end HaclStar
