# tls13-lean

A TLS 1.3 foundation for Lean 4: a **pure-Lean key schedule** over **formally
verified, constant-time crypto primitives** bound from
[HACL\*](https://github.com/hacl-star/hacl-star) via FFI. The first downstream
client integration lives in sibling `pg-lean`, whose record, handshake, and
sans-I/O client state machines build on this package.

This is the "option 3" design — own the protocol logic, borrow the primitives.
HACL\* supplies the machine-checked C crypto; Lean supplies explicit protocol
state and a path toward proofs of the key schedule and parsers. No system
crypto library (OpenSSL/etc.) is introduced; HACL\* is fetched at a pinned
commit and its portable C has no runtime dependency.

## Layout

Two Bazel packages below the root:

- **`HaclStar/`** — the crypto FFI. Bindings for exactly what TLS 1.3 needs:
  SHA-256, HMAC-SHA256, HKDF-SHA256, X25519, P-256 ECDH, and
  ChaCha20-Poly1305.
- **`TLS13/`** — pure-Lean protocol layer. Currently the RFC 8446 §7.1 key
  schedule. The first record layer, handshake codecs, and client machine are
  currently in `../pg-lean/Pg/Tls/`.

Plus `Test/` (RFC known-answer vectors) and `third_party/hacl/` (the
`http_archive` build overlay).

## The FFI pipeline

The binding pattern, bottom to top:

```
@hacl (http_archive, pinned)          hacl-star dist/gcc-compatible/*.c
    │  cc_library  (third_party/hacl/hacl.BUILD)
    ▼
HaclStar:hacl_shim (cc_library)       shim/hacl_shim.c  — ByteArray <-> uint8_t*
    │  deps: @hacl + :lean_runtime_headers
    ▼
HaclStar:haclstar (lean_library)      @[extern] opaque decls
    │
    ▼
TLS13 / Test                          pure Lean
```

- The **shim** (`HaclStar/shim/hacl_shim.c`) is the only hand-written C: it
  marshals Lean's boxed `ByteArray` to the flat `uint8_t*/uint32_t` buffers HACL
  expects. It `#include`s `<lean/lean.h>`, obtained from a `lean_runtime_headers`
  adapter that reads the active registered `rules_lean` toolchain. This works
  both when this repository is the Bazel root and when it is a dependency.
- HACL's `Hacl_HMAC.c` routes SHA-256 through an agile hash core, so its object
  drags the full hash family (Blake2/SHA3/MD5/SHA1) in at link time. Those are
  all portable C and are compiled; Vale assembly, EverCrypt autodetection,
  bignum, and SIMD variants are excluded. The exact translation-unit set and
  include roots were pinned empirically (see `third_party/hacl/hacl.BUILD`).
- Bindings are `@[extern] opaque` pure functions —
  SHA/HMAC/HKDF/X25519/P-256/AEAD are all deterministic. `ByteArray` in,
  `ByteArray` (or `Option ByteArray` for fallible ECDH / AEAD-open) out.

## Cipher suite scope

The first target is `TLS_CHACHA20_POLY1305_SHA256` with `x25519` preferred and
`secp256r1` available as a compatibility key-exchange group — a real,
widely-supported suite whose every primitive is **portable scalar C** in HACL\*
(no per-CPU assembly), so it builds identically on x86-64 and arm64.
AES-GCM (whose fast constant-time path is x86-only Vale assembly) and the
signature algorithms for certificate verification come later.

## Verification status

`bazel test //...` runs known-answer tests for every primitive against published
vectors — SHA-256 (FIPS 180-2), HMAC (RFC 4231), HKDF (RFC 5869), X25519
(RFC 7748), P-256 ECDH (RFC 5903), ChaCha20-Poly1305 (RFC 8439) — plus the
key schedule against RFC 8448 (Early Secret `33ad0a1c…`, Derived Secret
`6f2615a1…`), and an AEAD tamper-detection check.

## Roadmap

1. ✅ Verified crypto primitives via HACL\* FFI
2. ✅ Key schedule (HKDF-Expand-Label, Derive-Secret, Early/Handshake/Master)
3. ✅ Client record layer in `pg-lean`: framing, nonces, AEAD, peer-initiated
   KeyUpdate
4. ✅ Client handshake codecs in `pg-lean`: first-flight X25519/P-256,
   certificates, Finished, tickets, alerts
5. ✅ Sans-I/O client machine in `pg-lean`: transcript/key schedule, Finished
   verification, PostgreSQL SSLRequest transport integration
6. X.509 path validation (the sharp-edged quarter: ASN.1 DER, trust stores)
7. AES-GCM suites; signature algorithms for cert verification
8. Promote the downstream protocol modules into a reusable client/server core

## Toolchain

Bazel + `rules_lean` (sibling `../rules_lean`), nix-pinned Lean via
`grpc_lean_protobuf`'s overlay — same setup as the sibling `grpc-lean` /
`pg-lean` projects.
