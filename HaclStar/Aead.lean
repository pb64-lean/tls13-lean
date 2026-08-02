module

public section

/-!
ChaCha20-Poly1305 AEAD (RFC 8439), via HACL*'s scalar
`Hacl_AEAD_Chacha20Poly1305`. This is the record-protection AEAD for the TLS 1.3
cipher suite `TLS_CHACHA20_POLY1305_SHA256`.

The key is 32 bytes and the nonce 12 bytes. To keep the boundary a single
`ByteArray`, `encrypt` returns ciphertext followed by the 16-byte tag, and
`decrypt` expects that same layout.
-/

namespace HaclStar
namespace ChaCha20Poly1305

/-- AEAD-Encrypt. Returns `ciphertext ‖ tag` (`plaintext.size + 16` bytes). -/
@[extern "tls13_hacl_chachapoly_encrypt"]
opaque encrypt (key nonce aad plaintext : ByteArray) : ByteArray

/-- AEAD-Decrypt of `ciphertext ‖ tag`. Returns `none` on tag mismatch (or input
shorter than the 16-byte tag). -/
@[extern "tls13_hacl_chachapoly_decrypt"]
opaque decrypt (key nonce aad ctAndTag : ByteArray) : Option ByteArray

end ChaCha20Poly1305
end HaclStar
