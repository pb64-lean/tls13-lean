module

public section

/-!
HMAC-SHA256, via HACL*'s `Hacl_HMAC_compute_sha2_256`. The key may be any
length (hashed if longer than the 64-byte block, padded otherwise). This is the
building block of HKDF and of the Finished message MAC in TLS 1.3.
-/

namespace HaclStar

/-- HMAC-SHA256 of `data` under `key` (32-byte tag). -/
@[extern "tls13_hacl_hmac_sha256"]
opaque hmacSha256 (key data : ByteArray) : ByteArray

end HaclStar
