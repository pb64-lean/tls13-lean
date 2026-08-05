/*
 * FFI shim: adapts Lean 4's boxed `ByteArray` representation to the flat
 * `uint8_t* / uint32_t` buffers HACL* expects, for the primitives TLS 1.3 uses.
 *
 * Every argument is a borrowed ByteArray (`b_lean_obj_arg`) — HACL only reads
 * inputs, so we never consume or free them. Each result is a freshly allocated
 * owned ByteArray (or an `Option ByteArray`, where `none = lean_box(0)` and
 * `some x` is constructor tag 1). All of these HACL functions are pure and
 * total given valid buffer lengths, matching the `opaque`/`@[extern]` decls on
 * the Lean side.
 */

#include <lean/lean.h>
#include <stdint.h>
#include <string.h>

#include "Hacl_Hash_SHA2.h"
#include "Hacl_HMAC.h"
#include "Hacl_HKDF.h"
#include "Hacl_Curve25519_51.h"
#include "Hacl_P256.h"
#include "Hacl_AEAD_Chacha20Poly1305.h"
#include "lib_memzero0.h"

/* Allocate an uninitialized Lean ByteArray of `n` bytes. */
static inline lean_object *tls13_alloc_bytes(size_t n) {
  return lean_alloc_sarray(1, n, n);
}

static inline lean_object *tls13_some(lean_object *value) {
  lean_object *o = lean_alloc_ctor(1, 1, 0); /* Option.some */
  lean_ctor_set(o, 0, value);
  return o;
}

/* Non-Option bindings use an empty ByteArray as their misuse sentinel, which
 * preserves their existing Lean APIs. It is distinguishable from successful
 * fixed-output and AEAD operations; HKDF-Expand at the valid length zero is
 * itself empty, so callers that need to distinguish that case must preflight. */
static inline lean_object *tls13_empty_bytes(void) {
  return tls13_alloc_bytes(0);
}

static inline bool tls13_fits_u32(size_t n) {
  return n <= UINT32_MAX;
}

/* ---- SHA-2 ----------------------------------------------------------- */

LEAN_EXPORT lean_object *tls13_hacl_sha256(b_lean_obj_arg data) {
  size_t data_len = lean_sarray_size(data);
  if (!tls13_fits_u32(data_len)) {
    return tls13_empty_bytes();
  }
  lean_object *out = tls13_alloc_bytes(32);
  Hacl_Hash_SHA2_hash_256(lean_sarray_cptr(out),
                          lean_sarray_cptr(data),
                          (uint32_t)data_len);
  return out;
}

LEAN_EXPORT lean_object *tls13_hacl_sha384(b_lean_obj_arg data) {
  size_t data_len = lean_sarray_size(data);
  if (!tls13_fits_u32(data_len)) {
    return tls13_empty_bytes();
  }
  lean_object *out = tls13_alloc_bytes(48);
  Hacl_Hash_SHA2_hash_384(lean_sarray_cptr(out),
                          lean_sarray_cptr(data),
                          (uint32_t)data_len);
  return out;
}

LEAN_EXPORT lean_object *tls13_hacl_sha512(b_lean_obj_arg data) {
  size_t data_len = lean_sarray_size(data);
  if (!tls13_fits_u32(data_len)) {
    return tls13_empty_bytes();
  }
  lean_object *out = tls13_alloc_bytes(64);
  Hacl_Hash_SHA2_hash_512(lean_sarray_cptr(out),
                          lean_sarray_cptr(data),
                          (uint32_t)data_len);
  return out;
}

/* ---- HMAC-SHA256 ----------------------------------------------------- */

LEAN_EXPORT lean_object *tls13_hacl_hmac_sha256(b_lean_obj_arg key,
                                                b_lean_obj_arg data) {
  size_t key_len = lean_sarray_size(key);
  size_t data_len = lean_sarray_size(data);
  if (!tls13_fits_u32(key_len) || !tls13_fits_u32(data_len)) {
    return tls13_empty_bytes();
  }
  lean_object *out = tls13_alloc_bytes(32);
  Hacl_HMAC_compute_sha2_256(lean_sarray_cptr(out),
                             lean_sarray_cptr(key),
                             (uint32_t)key_len,
                             lean_sarray_cptr(data),
                             (uint32_t)data_len);
  return out;
}

/* ---- HKDF-SHA256 ----------------------------------------------------- */

LEAN_EXPORT lean_object *tls13_hacl_hkdf_extract_sha256(b_lean_obj_arg salt,
                                                        b_lean_obj_arg ikm) {
  size_t salt_len = lean_sarray_size(salt);
  size_t ikm_len = lean_sarray_size(ikm);
  if (!tls13_fits_u32(salt_len) || !tls13_fits_u32(ikm_len)) {
    return tls13_empty_bytes();
  }
  lean_object *out = tls13_alloc_bytes(32);
  Hacl_HKDF_extract_sha2_256(lean_sarray_cptr(out),
                             lean_sarray_cptr(salt),
                             (uint32_t)salt_len,
                             lean_sarray_cptr(ikm),
                             (uint32_t)ikm_len);
  return out;
}

/* `len` is the desired output length; RFC 5869 caps it at 255*HashLen. */
LEAN_EXPORT lean_object *tls13_hacl_hkdf_expand_sha256(b_lean_obj_arg prk,
                                                       b_lean_obj_arg info,
                                                       uint32_t len) {
  size_t prk_len = lean_sarray_size(prk);
  size_t info_len = lean_sarray_size(info);
  if (!tls13_fits_u32(prk_len) || !tls13_fits_u32(info_len) ||
      len > 255U * 32U) {
    return tls13_empty_bytes();
  }
  lean_object *out = tls13_alloc_bytes(len);
  Hacl_HKDF_expand_sha2_256(lean_sarray_cptr(out),
                            lean_sarray_cptr(prk),
                            (uint32_t)prk_len,
                            lean_sarray_cptr(info),
                            (uint32_t)info_len,
                            len);
  return out;
}

/* ---- X25519 ---------------------------------------------------------- */

/* Derive the public value from a 32-byte scalar: X25519(priv, 9). A malformed
 * scalar length returns the empty-ByteArray misuse sentinel. */
LEAN_EXPORT lean_object *tls13_hacl_x25519_base(b_lean_obj_arg priv) {
  if (lean_sarray_size(priv) != 32) {
    return tls13_empty_bytes();
  }
  lean_object *out = tls13_alloc_bytes(32);
  Hacl_Curve25519_51_secret_to_public(lean_sarray_cptr(out),
                                       lean_sarray_cptr(priv));
  return out;
}

/* ECDH: returns `none` when the shared secret is all-zero (a low-order point),
 * which RFC 7748 §6.1 / RFC 8446 §7.4.2 require callers to reject. */
LEAN_EXPORT lean_object *tls13_hacl_x25519_ecdh(b_lean_obj_arg priv,
                                                b_lean_obj_arg pub) {
  if (lean_sarray_size(priv) != 32 || lean_sarray_size(pub) != 32) {
    return lean_box(0); /* Option.none */
  }
  lean_object *out = tls13_alloc_bytes(32);
  bool ok = Hacl_Curve25519_51_ecdh(lean_sarray_cptr(out),
                                     lean_sarray_cptr(priv),
                                     lean_sarray_cptr(pub));
  if (!ok) {
    lean_dec_ref(out);
    return lean_box(0); /* Option.none */
  }
  return tls13_some(out);
}

/* ---- P-256 ECDH ------------------------------------------------------ */

/* Derive a 65-byte SEC1 uncompressed public key. HACL's initiator API emits
 * raw x || y, so serialize it with the standard 0x04 prefix before returning.
 * Length checks happen before any HACL routine can read from a Lean array. */
LEAN_EXPORT lean_object *tls13_hacl_p256_public_key(b_lean_obj_arg priv) {
  if (lean_sarray_size(priv) != 32) {
    return lean_box(0); /* Option.none */
  }

  uint8_t raw[64] = {0};
  bool ok = Hacl_P256_dh_initiator(raw, lean_sarray_cptr(priv));
  if (!ok) {
    Lib_Memzero0_memzero0(raw, sizeof(raw));
    return lean_box(0);
  }

  lean_object *out = tls13_alloc_bytes(65);
  Hacl_P256_raw_to_uncompressed(raw, lean_sarray_cptr(out));
  Lib_Memzero0_memzero0(raw, sizeof(raw));
  return tls13_some(out);
}

/* P-256 ECDH for TLS: accept SEC1 uncompressed peer keys and return only the
 * x coordinate of HACL's raw x || y common point. HACL validates both the
 * private scalar and peer point in dh_responder. */
LEAN_EXPORT lean_object *tls13_hacl_p256_ecdh(b_lean_obj_arg priv,
                                              b_lean_obj_arg peer) {
  if (lean_sarray_size(priv) != 32 || lean_sarray_size(peer) != 65) {
    return lean_box(0); /* Option.none */
  }

  uint8_t peer_raw[64] = {0};
  if (!Hacl_P256_uncompressed_to_raw(lean_sarray_cptr(peer), peer_raw)) {
    return lean_box(0);
  }

  uint8_t shared_raw[64] = {0};
  bool ok = Hacl_P256_dh_responder(shared_raw, peer_raw,
                                   lean_sarray_cptr(priv));
  if (!ok) {
    Lib_Memzero0_memzero0(shared_raw, sizeof(shared_raw));
    return lean_box(0);
  }

  lean_object *out = tls13_alloc_bytes(32);
  memcpy(lean_sarray_cptr(out), shared_raw, 32);
  Lib_Memzero0_memzero0(shared_raw, sizeof(shared_raw));
  return tls13_some(out);
}

/* ---- ChaCha20-Poly1305 AEAD ------------------------------------------ */

/* Returns ciphertext ‖ tag (plaintext length + 16). `key` is 32 bytes, `nonce`
 * 12 bytes; `aad` may be empty. Invalid dimensions or lengths that cannot be
 * represented by HACL's uint32_t API return the empty-ByteArray sentinel. */
LEAN_EXPORT lean_object *tls13_hacl_chachapoly_encrypt(b_lean_obj_arg key,
                                                       b_lean_obj_arg nonce,
                                                       b_lean_obj_arg aad,
                                                       b_lean_obj_arg plaintext) {
  size_t aad_len = lean_sarray_size(aad);
  size_t plaintext_len = lean_sarray_size(plaintext);
  if (lean_sarray_size(key) != 32 || lean_sarray_size(nonce) != 12 ||
      !tls13_fits_u32(aad_len) || !tls13_fits_u32(plaintext_len) ||
      plaintext_len > SIZE_MAX - 16) {
    return tls13_empty_bytes();
  }
  uint32_t mlen = (uint32_t)plaintext_len;
  lean_object *out = tls13_alloc_bytes(plaintext_len + 16);
  uint8_t *o = lean_sarray_cptr(out);
  Hacl_AEAD_Chacha20Poly1305_encrypt(o,          /* ciphertext */
                                     o + mlen,   /* 16-byte tag */
                                     lean_sarray_cptr(plaintext), mlen,
                                     lean_sarray_cptr(aad),
                                     (uint32_t)aad_len,
                                     lean_sarray_cptr(key),
                                     lean_sarray_cptr(nonce));
  return out;
}

/* Input is ciphertext ‖ tag. Returns `none` on authentication failure (or a
 * truncated input that cannot contain a tag). */
LEAN_EXPORT lean_object *tls13_hacl_chachapoly_decrypt(b_lean_obj_arg key,
                                                       b_lean_obj_arg nonce,
                                                       b_lean_obj_arg aad,
                                                       b_lean_obj_arg ct_and_tag) {
  size_t total = lean_sarray_size(ct_and_tag);
  size_t aad_len = lean_sarray_size(aad);
  if (lean_sarray_size(key) != 32 || lean_sarray_size(nonce) != 12 ||
      !tls13_fits_u32(aad_len) || total < 16) {
    return lean_box(0); /* Option.none */
  }
  size_t ciphertext_len = total - 16;
  if (!tls13_fits_u32(ciphertext_len)) {
    return lean_box(0); /* Option.none */
  }
  uint32_t clen = (uint32_t)ciphertext_len;
  uint8_t *ct = lean_sarray_cptr(ct_and_tag);
  lean_object *out = tls13_alloc_bytes(ciphertext_len);
  uint32_t r = Hacl_AEAD_Chacha20Poly1305_decrypt(lean_sarray_cptr(out),
                                                  ct, clen,
                                                  lean_sarray_cptr(aad),
                                                  (uint32_t)aad_len,
                                                  lean_sarray_cptr(key),
                                                  lean_sarray_cptr(nonce),
                                                  ct + clen); /* tag */
  if (r != 0) {
    lean_dec_ref(out);
    return lean_box(0); /* Option.none — auth failed */
  }
  return tls13_some(out);
}
