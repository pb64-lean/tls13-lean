# tls13-lean

[![CI](https://github.com/pb64-lean/tls13-lean/actions/workflows/ci.yml/badge.svg?branch=main)](https://github.com/pb64-lean/tls13-lean/actions/workflows/ci.yml) [![Assurance](https://github.com/pb64-lean/tls13-lean/actions/workflows/assurance.yml/badge.svg?branch=main)](https://github.com/pb64-lean/tls13-lean/actions/workflows/assurance.yml)

TLS 1.3 for Lean 4: pure-Lean protocol machinery — record layer, handshake
codecs, sans-I/O **client and server** state machines, and X.509 path
validation — over **formally verified, constant-time crypto primitives** bound
from [HACL\*](https://github.com/hacl-star/hacl-star) via an explicit C FFI.

This is the "own the protocol logic, borrow the primitives" design. HACL\*
supplies the machine-checked C crypto; Lean supplies explicit protocol state.
No system crypto library (OpenSSL etc.) is introduced; HACL\* is fetched at a
pinned commit and its portable C has no runtime dependency.

**Verification status, stated precisely:** the machine-checked component is
the imported HACL\* C code. The Lean protocol code in this repository is
implemented and tested — known-answer vectors for every primitive, wire-level
handshake tests, X.509 corpus tests, and an in-repo client↔server handshake —
but it carries no formal proofs today, and no refinement theorem against
RFC 8446 is claimed. Protocol-level proofs are a direction, not a result.

## Layout

Four Bazel packages:

- **`HaclStar/`** — the crypto FFI: SHA-256/384/512, HMAC-SHA256,
  HKDF-SHA256, X25519, P-256 ECDH, ChaCha20-Poly1305 AEAD, and Ed25519 +
  ECDSA-P256 signatures (verify and sign). 16 `@[extern] opaque`
  declarations over two small C shims.
- **`TLS13/`** — the RFC 8446 §7.1 key schedule plus the X.509 stack:
  strict-DER and PEM decoding, full certificate parsing, chain building and
  validation, hostname verification, RSA (PKCS#1 v1.5 and PSS) signature
  verification in pure Lean, and RFC 5929 `tls-server-end-point` channel
  binding. `TLS13.X509.DER` ends with kernel-checked laws about the decoder
  as implemented: exact-slice retention (a parsed TLV's `encoded` field is
  byte-identical to the input slice it consumed), the re-decode identity,
  encoding uniqueness, trailing-data rejection, and canonical
  length/identifier form lemmas. `Certificate.decode_tbs_encoded` and
  `Chain.checkIssuer_verifies` carry retention to the trust boundary: the
  bytes handed to certificate signature verification are exactly the
  TBSCertificate slice parsed out of the presented DER.
- **`Tls/`** — the sans-I/O protocol core: ChaCha20-Poly1305 record layer
  with KeyUpdate, handshake codecs for both roles (including
  HelloRetryRequest, ALPN, SNI), and the client (`Tls.Client`) and server
  (`Tls.Server`) state machines. `Tls.Record.Laws` proves kernel-checked
  theorems about the record layer as implemented: byte conservation,
  fragmentation independence, encode/decode roundtrips,
  sequence-number/nonce lemmas, and record-protection laws — `seal`
  advances the sequence number exactly once preserving key/IV/secret, and
  (parametrically over the opaque HACL\* AEAD binding) `open` inverts
  `seal`, wire bytes and all. The handshake layer mirrors framing
  conservation: a decoded message's retained `encoded` bytes plus the
  remainder reproduce the input buffer exactly.
- **`Test/`** — nine hermetic test binaries, a one-shot loopback server
  harness, and a scripted (manual-tag) interoperability gate that drives the
  harness with real OpenSSL, curl, and Go `crypto/tls` clients.

## Protocol scope

Implemented and negotiated today:

- **Cipher suite**: `TLS_CHACHA20_POLY1305_SHA256` — deliberately the single
  suite whose every primitive is portable scalar C in HACL\* (no per-CPU
  assembly), so the build is identical on x86-64 and arm64.
- **Key exchange**: X25519 preferred; P-256 available when configured.
- **Server authentication**: Ed25519 (the server signs CertificateVerify
  with a raw Ed25519 key). Clients accept CertificateVerify signatures with
  `ecdsa_secp256r1_sha256`, `ed25519`, `rsa_pss_rsae_sha256`, and
  `rsa_pss_pss_sha256`; PKCS#1 v1.5 is advertised for certificate-*chain*
  selection only, as RFC 8446 requires.
- **Extensions**: server_name, supported_groups, signature_algorithms, ALPN,
  supported_versions, key_share; the server performs HelloRetryRequest with
  the synthetic `message_hash` transcript and strict second-ClientHello
  checks.

Explicitly not yet supported (a candid list): PSK and session resumption
(NewSessionTicket is parsed and discarded; the server never issues tickets),
0-RTT, client certificates, AES-GCM suites, client-side HelloRetryRequest
processing, and post-quantum hybrid groups (a hybrid key share in a
ClientHello is tolerated and skipped, not negotiated). The server's
*negotiated* surface stays deliberately narrow (ChaCha20-Poly1305 +
X25519/P-256 + Ed25519 — algorithms every modern client implements), but
its *acceptance* follows RFC 8446's select-from-overlap rule: unknown cipher
suites, groups, signature schemes, GREASE values, and extensions are
tolerated wherever the RFC permits. Mainstream clients interoperate with
the server today — OpenSSL `s_client`, curl, and Go `crypto/tls` all
complete handshakes and fetch a page over the loopback harness, including
the HelloRetryRequest path when their first flight carries only key shares
this server does not implement (see the interop gate under Tests).

## X.509

`TLS13.X509` implements: strict DER (BER forms rejected), RFC 7468 PEM,
full certificate parsing with byte-exact retention of the signed structures,
path building with backtracking and bounded work
(depth ≤ 10, ≤ 128 issuer attempts by default), expiry, CA / `keyCertSign` /
`pathLenConstraint` enforcement, rejection of unhandled critical extensions,
libpq-style hostname verification (SAN dNSName wildcards, IPv4/IPv6
literals, CN fallback only without SAN; IDNA names must be given in A-label
form), and channel-binding digests. Chain signature algorithms:
ECDSA-P256-SHA256, Ed25519, RSA PKCS#1 v1.5 SHA-256, RSA-PSS SHA-256.

Deliberately out of scope, matching libpq's default behavior: CRL and OCSP
revocation. Also not interpreted: extendedKeyUsage, nameConstraints, policy
constraints (they fail validation only if marked critical, since unhandled
critical extensions are rejected).

## Sans-I/O design

The engines perform no I/O, read no clock, and generate no entropy:

- `Tls.Client.Config` / `Tls.Server.Config` take caller-supplied randoms,
  ephemeral key-exchange scalars, and session ids; callers are responsible
  for sourcing them from a CSPRNG (downstream shells use Lean's
  `IO.getRandomBytes`). The ECDSA signing binding likewise takes an explicit
  per-message nonce — nonce hygiene is the caller's responsibility.
- `feed` consumes wire bytes and returns produced wire bytes + plaintext;
  failures come back as a `Failure` carrying the alert to seal and send
  before discarding the connection.
- Chain validation takes `now` as an argument; trust anchors are supplied
  parsed.
- Certificate-chain and hostname validation are separate, caller-invoked
  policy steps — the handshake itself checks CertificateVerify against the
  presented leaf.

Downstream I/O shells in the sibling repositories:
[`pg-lean`](https://github.com/pb64-lean/pg-lean) drives `Tls.Client` inside
its PostgreSQL connection (plus libpq-style trust-store discovery), and
[`grpc-lean`](https://github.com/pb64-lean/grpc-lean) wraps both engines in
socket sessions for gRPC-over-TLS and a minimal HTTPS JSON endpoint.

## The FFI pipeline

```
@hacl (http_archive, pinned)          hacl-star dist/gcc-compatible/*.c
    │  cc_library  (third_party/hacl/hacl.BUILD)
    ▼
HaclStar:hacl_shim (cc_library)       shim/*.c  — ByteArray <-> uint8_t*
    │  deps: @hacl + :lean_runtime_headers
    ▼
HaclStar:haclstar (lean_library)      @[extern] opaque decls
    │
    ▼
TLS13 / Tls / Test                    pure Lean
```

- HACL\* is pinned by `http_archive` to commit
  `504c2987452f87fe44bce9b9f12e19d6e051761f` (sha256-verified), using the
  karamel-extracted `dist/gcc-compatible` tree. Fifteen portable-C
  translation units are compiled; Vale assembly, EverCrypt CPU
  autodetection, bignum, and SIMD variants are deliberately excluded.
- The shims (`HaclStar/shim/hacl_shim.c`, `shim/signature_shim.c`, ~340
  lines total) are the only hand-written C: they marshal Lean `ByteArray`s
  to flat buffers, enforce length preconditions before entering HACL\*, and
  zero transient signature buffers. `<lean/lean.h>` comes from a
  `lean_runtime_headers` adapter that reads the registered `rules_lean`
  toolchain, so the shim compiles whether this repo is the Bazel root or a
  dependency.
- Bindings are `@[extern] opaque` pure functions: `ByteArray` in,
  `ByteArray` (or `Option ByteArray` for fallible ECDH / AEAD-open /
  signature verify) out.

## Trusted computing base

An assurance-minded reader should count, beyond the Lean protocol code
itself: the two C shims; the fifteen pinned HACL\* translation units (the
agile HMAC core links the full hash family, so MD5/SHA-1/Blake2/SHA-3
objects are present though unused); the Lean compiler and runtime, including
the `Nat` big-integer backend used by the pure-Lean RSA verifier (public
operands only — it is deliberately exact-and-clear rather than
constant-time); and the Bazel/Nix toolchain pins. Secret-bearing state has
no `Repr` instance, handshake secrets and scalars are dropped from state on
completion, and Finished verification is constant-time — but there is no
zeroization of Lean-side key material.

## Tests

`bazel test //...` runs nine hermetic, offline suites:

| Target | Coverage |
| --- | --- |
| `hacl_kat_test` | Known-answer vectors for every binding: SHA-2 (FIPS 180), HMAC (RFC 4231), HKDF (RFC 5869), X25519 (RFC 7748), P-256 ECDH (RFC 5903), ChaCha20-Poly1305 (RFC 8439) + tamper detection, Ed25519 (RFC 8032), ECDSA roundtrip, and the key schedule against RFC 8448 |
| `tls_handshake_test` | Wire codecs against a GREASE-laden, fragmented, reordered ClientHello; record reassembly across TCP boundaries; missing-extension and duplicate-extension alerts; the full HelloRetryRequest flow |
| `tls_server_interop_test` | Authenticated handshake between this repo's client and server engines (no sockets): negotiation, three-record server flight, application data both ways, 50-certificate fragmentation |
| `x509_der_test`, `x509_certificate_test`, `x509_chain_test`, `x509_signature_test`, `x509_hostname_test`, `x509_channel_binding_test` | DER/PEM strictness corpus; OpenSSL-generated RSA/P-256/Ed25519 fixtures; chain validation success and eleven failure classes; RSA/ECDSA/PSS signature vectors and boundary rejections; hostname and channel-binding rules |

Honest interop note: the hermetic "interop" test pairs this repo's own
client and server. Interop against *independent* clients is a separate,
scripted gate — `bazel test //Test:external_interop_test
--test_output=streamed` — which starts the one-shot loopback harness
(`bazel run //Test:tls_external_server -- 8443` runs it manually) and
drives six externally implemented handshakes, asserting completion and the
HTTP/1.1 200 body:

- OpenSSL `s_client` with default groups (tolerating its X25519MLKEM768
  hybrid key share), and a forced HelloRetryRequest run
  (`-groups P-384:X25519`: the only first-flight share is P-384, which this
  server does not implement, so it must retry to X25519);
- curl fetching the page, once normally and once against a server that
  reads the transport 7 bytes at a time (record reassembly at arbitrary
  TCP boundaries);
- Go `crypto/tls` with its default configuration, and a forced
  HelloRetryRequest run (CurvePreferences restricted to
  {X25519MLKEM768, P-256}, so the server must retry to P-256).

The gate is tagged `manual`/`local` — it binds loopback ports and shells
out to host `openssl` and `curl` (the Go cases skip gracefully without a
`go` binary; use `nix shell nixpkgs#go -c bazel test ...`) — so
`bazel test //...` stays hermetic and offline. Verified against OpenSSL
3.6.1, curl 8.18.0, and Go 1.25.6.

## Building

Part of the [pb64-lean](https://github.com/pb64-lean) ecosystem: Bazel 8.5
(`.bazelversion`), sibling checkouts for `../rules_lean` and (for the shared
Nix-pinned Lean toolchain files only) `../grpc-lean`, and **Nix** to build
the pinned Lean 4.31.0-pre toolchain:

```sh
for r in rules_lean grpc-lean tls13-lean; do
  git clone "https://github.com/pb64-lean/$r"
done
cd tls13-lean
bazel test //...
```

`lakefile.lean` is an IDE/LSP project model only; Bazel is the authoritative
build because it compiles and links the HACL\* C shim.

## Roadmap

1. ✅ Verified crypto primitives via HACL\* FFI
2. ✅ Key schedule (HKDF-Expand-Label, Derive-Secret, Early/Handshake/Master)
3. ✅ Record layer: framing, nonces, AEAD, KeyUpdate
4. ✅ Handshake codecs for both roles, including HelloRetryRequest, ALPN, SNI
5. ✅ Sans-I/O client and server state machines
6. ✅ X.509: strict DER/PEM, chain validation, hostname, channel binding
7. ✅ Mainstream-client server interop (OpenSSL, curl, Go `crypto/tls`,
   including their HelloRetryRequest paths) with a scripted gate
   (`//Test:external_interop_test`)
8. AES-GCM suites; client-side HelloRetryRequest
9. PSK, resumption, 0-RTT; client certificates
10. Protocol-level proofs — record-layer laws are done (`Tls.Record.Laws`:
    framing conservation, fragmentation independence, roundtrips,
    nonce/sequence lemmas, seal/open protection laws with the open∘seal
    identity stated parametrically over the opaque AEAD FFI, and
    handshake-message extraction conservation), as are the X.509 DER laws
    (`TLS13.X509.DER`: exact-slice retention — a parsed TLV's `encoded`
    field is byte-identical to the consumed input slice — plus the
    re-decode identity, encoding uniqueness, trailing-data rejection, and
    canonical length/identifier form lemmas) and their signed-bytes
    corollary (`Certificate.decode_tbs_encoded`, `checkIssuer_verifies`:
    the bytes the chain validator hands to signature verification are
    exactly the TBS slice parsed out of the certificate); key schedule,
    handshake parsers, and state-machine invariants remain
