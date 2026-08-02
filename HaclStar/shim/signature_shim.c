/*
 * Lean ByteArray adapters for HACL* signature verification and signing.
 *
 * Verification handles no secrets, so those wrappers need no constant-time
 * marshaling. Signing takes a private key: HACL's signing routines are already
 * constant-time in the scalar, and we zero the transient stack buffer that
 * holds the produced signature before returning. Every wrapper enforces its
 * HACL buffer-size preconditions before entering C.
 */

#include <lean/lean.h>
#include <stdint.h>
#include <string.h>

#include "Hacl_Ed25519.h"
#include "Hacl_P256.h"
#include "lib_memzero0.h"

LEAN_EXPORT uint8_t
tls13_hacl_p256_ecdsa_sha256_verify(b_lean_obj_arg public_key,
                                    b_lean_obj_arg message,
                                    b_lean_obj_arg signature_r,
                                    b_lean_obj_arg signature_s) {
  size_t message_len = lean_sarray_size(message);
  if (lean_sarray_size(public_key) != 65 ||
      lean_sarray_cptr(public_key)[0] != 0x04 ||
      lean_sarray_size(signature_r) != 32 ||
      lean_sarray_size(signature_s) != 32 ||
      message_len > UINT32_MAX) {
    return 0;
  }

  return Hacl_P256_ecdsa_verif_p256_sha2(
             (uint32_t)message_len,
             lean_sarray_cptr(message),
             lean_sarray_cptr(public_key) + 1,
             lean_sarray_cptr(signature_r),
             lean_sarray_cptr(signature_s))
           ? 1
           : 0;
}

LEAN_EXPORT uint8_t
tls13_hacl_ed25519_verify(b_lean_obj_arg public_key,
                          b_lean_obj_arg message,
                          b_lean_obj_arg signature) {
  size_t message_len = lean_sarray_size(message);
  if (lean_sarray_size(public_key) != 32 ||
      lean_sarray_size(signature) != 64 ||
      message_len > UINT32_MAX) {
    return 0;
  }

  return Hacl_Ed25519_verify(lean_sarray_cptr(public_key),
                             (uint32_t)message_len,
                             lean_sarray_cptr(message),
                             lean_sarray_cptr(signature))
           ? 1
           : 0;
}

/* Sign `message` under a 32-byte Ed25519 private key (RFC 8032). Ed25519
 * signing is deterministic and cannot fail given valid lengths, so the result
 * is an unconditional fresh 64-byte owned ByteArray rather than an Option. A
 * bad private-key length or an over-long message is caller misuse: we signal it
 * with a 0-length ByteArray, which the Lean caller can detect (a real signature
 * is always 64 bytes). */
LEAN_EXPORT lean_object *
tls13_hacl_ed25519_sign(b_lean_obj_arg private_key, b_lean_obj_arg message) {
  size_t message_len = lean_sarray_size(message);
  if (lean_sarray_size(private_key) != 32 || message_len > UINT32_MAX) {
    return lean_alloc_sarray(1, 0, 0); /* misuse sentinel: empty ByteArray */
  }

  lean_object *out = lean_alloc_sarray(1, 64, 64);
  Hacl_Ed25519_sign(lean_sarray_cptr(out),
                    lean_sarray_cptr(private_key),
                    (uint32_t)message_len,
                    lean_sarray_cptr(message));
  return out;
}

/* Sign `message` (SHA-256 pre-hash) under a 32-byte P-256 private scalar and a
 * 32-byte per-message nonce, producing a 64-byte r || s signature. Returns
 * `none` when a length precondition fails or HACL rejects the scalar/nonce as
 * out of range; `some (r || s)` otherwise. The signature is computed into a
 * stack buffer and copied into the owned result, then the stack buffer is
 * zeroed. */
LEAN_EXPORT lean_object *
tls13_hacl_p256_ecdsa_sha256_sign(b_lean_obj_arg private_key,
                                  b_lean_obj_arg message,
                                  b_lean_obj_arg nonce) {
  size_t message_len = lean_sarray_size(message);
  if (lean_sarray_size(private_key) != 32 ||
      lean_sarray_size(nonce) != 32 ||
      message_len > UINT32_MAX) {
    return lean_box(0); /* Option.none */
  }

  uint8_t signature[64] = {0};
  bool ok = Hacl_P256_ecdsa_sign_p256_sha2((uint8_t *)signature,
                                           (uint32_t)message_len,
                                           lean_sarray_cptr(message),
                                           lean_sarray_cptr(private_key),
                                           lean_sarray_cptr(nonce));
  if (!ok) {
    Lib_Memzero0_memzero0(signature, sizeof(signature));
    return lean_box(0); /* Option.none — scalar or nonce out of range */
  }

  lean_object *out = lean_alloc_sarray(1, 64, 64);
  memcpy(lean_sarray_cptr(out), signature, 64);
  Lib_Memzero0_memzero0(signature, sizeof(signature));

  lean_object *o = lean_alloc_ctor(1, 1, 0); /* Option.some */
  lean_ctor_set(o, 0, out);
  return o;
}
