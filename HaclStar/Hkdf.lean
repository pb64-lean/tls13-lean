module

public section

/-!
HKDF-SHA256 (RFC 5869), via HACL*'s `Hacl_HKDF_{extract,expand}_sha2_256`.
These two operations are the whole of the TLS 1.3 key schedule's cryptographic
core; the labelled derivations in RFC 8446 §7.1 are built on top in pure Lean.
-/

namespace HaclStar
namespace Hkdf

/-- HKDF-Extract: derive a 32-byte pseudorandom key from input keying material
`ikm` and a `salt`. -/
@[extern "tls13_hacl_hkdf_extract_sha256"]
opaque extractSha256 (salt ikm : ByteArray) : ByteArray

/-- HKDF-Expand: stretch a pseudorandom key `prk` to `len` bytes bound to
`info`. `len` must not exceed 255·32 = 8160 (RFC 5869); the caller is
responsible for that bound. -/
@[extern "tls13_hacl_hkdf_expand_sha256"]
opaque expandSha256 (prk info : ByteArray) (len : UInt32) : ByteArray

end Hkdf
end HaclStar
