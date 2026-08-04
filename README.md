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

**Verification status, stated precisely.** Two distinct things are
machine-checked, and it matters which is which:

- The imported **HACL\* C primitives** carry externally machine-verified
  correctness and constant-time proofs. This repository does not re-prove
  them; it binds them across an explicit FFI boundary and trusts them.
- The **Lean protocol code** now carries kernel-checked laws about the
  implementation itself — the record framer (byte conservation,
  fragmentation independence, sequence/nonce injectivity, seal/open
  inversion parametric over the opaque AEAD), the handshake codecs (wire
  roundtrips with explicit residual, body inversion, GREASE-tolerant
  extension preservation, ClientHello canonicity — a parsed ClientHello
  re-encodes to exactly the bytes it came from — HelloRetryRequest
  discrimination, no partial frame ever accepted), the **state machines**
  (nonce non-reuse across a whole connection, plus handshake state
  invariants and transition laws), and the DER decoder (exact-slice
  retention carried through to the bytes certificate signatures are
  verified over). These are proofs about the executable definitions, not a
  parallel model.

**Nonce non-reuse, stated exactly.** `Tls.Client.Laws.run_nonce_nodup` and
`Tls.Server.Laws.run_nonce_nodup` say: for any successful run of the engine
there is an explicit `Tls.Record.Laws.WriteRun` — the list of records the run
protected, each tagged with the traffic secret of the epoch that protected it —
leading from the connection's initial write state to its final one, in which no
(secret, nonce) pair repeats. Read the fine print:

- It is about *this engine's own emissions along one chain of states*. A caller
  who clones a `State` and drives two connections from the same keys is outside
  its reach — Lean values are duplicable, and no theorem about a pure function
  can forbid copying one. Single-threading the state is the caller's obligation.
- It covers the **write** direction only. Nonce reuse is a sender property; the
  read-side nonces are the peer's.
- Sequence numbers restart at zero on every KeyUpdate, so the trace is *scoped
  by traffic-secret epoch* and the theorem's one hypothesis is that the epochs'
  secrets are distinct (`secrets.Nodup`). TLS derives each with
  HKDF-Expand-Label, an opaque HACL\* binding here, so that step is assumed —
  the same boundary as the AEAD round trip in `open_seal`. Within one epoch
  nothing is assumed: `seal` uses the nonce of the current sequence number and
  returns the state with that number advanced without wrapping, and for a fixed
  IV the nonce determines the sequence number.

What is **not** claimed: no refinement theorem against RFC 8446, no
security proof of the handshake or state machines, no correctness proof of the
key schedule against the RFC's derivation graph (only the KAT in
`hacl_kat_test`), no timing analysis of Lean control code, and nothing about
the C shims beyond their length preconditions.

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
  advances the sequence number exactly once preserving key/IV/secret (and
  never wraps it: `seal_seq_succ`), and
  (parametrically over the opaque HACL\* AEAD binding) `open` inverts
  `seal`, wire bytes and all. It also defines `WriteRun`, the explicit trace
  of the `seal` calls a state machine performs — every step pinned to a real
  successful `seal` of the state the previous one returned — and proves
  `WriteRun.nodup`, the nonce non-reuse theorem the engines' laws instantiate.
  The handshake layer mirrors framing
  conservation: a decoded message's retained `encoded` bytes plus the
  remainder reproduce the input buffer exactly. `Tls.Handshake` also ends in
  kernel-checked wire-codec laws: every message encoder roundtrips through
  the wire decoder with an explicit residual, the framing outcome depends
  only on the reassembled byte stream and never accepts a partial frame,
  the ServerHello/HelloRetryRequest/EncryptedExtensions/Certificate/
  CertificateVerify/Finished/NewSessionTicket/KeyUpdate bodies invert
  semantically, extension lists, `uint16` vectors and client key-share lists
  roundtrip for arbitrary (including unknown and GREASE) types and values, and
  HelloRetryRequest is discriminated from ServerHello by the RFC 8446 sentinel
  random. `parseClientHello_clientHelloBody_mem` lifts that to a whole
  ClientHello: the cipher suites, offered versions, supported groups, key-share
  groups, signature schemes and the entire extension list — unknown and GREASE
  entries included — are returned in wire order with nothing dropped or
  reordered, with the four interpreted extensions allowed anywhere in the list
  in any interleaving (the only structural hypothesis left is that no two
  extensions share a type, which RFC 8446 forbids and `parseExtensions`
  rejects). `parseClientHello_clientHelloBody_psk` covers the resumption shape
  as well — a `pre_shared_key` offer as the final extension with a non-empty
  `psk_key_exchange_modes` is accepted and retained verbatim (PSK is still not
  *negotiated*; see the scope list below).
  Framing is canonical in both directions: `decodeOne_frame` says the decoder
  accepts what `frame` produced, and `decodeOne_canonical` says the converse —
  everything the decoder produces *is* a frame, so re-framing a decoded
  message's type and body reproduces the message, retained `encoded` bytes and
  all. Comparing two decoded messages' `msgType` and `body` is therefore exactly
  as strong as comparing their wire bytes (`decodeOne_injective`), the
  framing-layer analogue of `parseClientHello_body_injective`.
  `Tls.Handshake.takeMessage?` — the reassembly step both state machines run on
  the bytes the record layer hands up — is proved monotone and exact: every
  proper prefix of a framed message yields nothing rather than an error, the
  arrival of its last byte delivers the whole message with the following bytes
  untouched, delivery conserves the buffer, and bytes arriving after a message
  is already complete never change what is delivered (`takeMessage?_append`,
  for an arbitrary buffer). The list codecs are proved lossless in the other
  direction too: `parseExtensions_image`, `parseUInt16List_image` and
  `parseKeyShareEntries_image` show that every block the parser accepts *is*
  the wire image of the list it produced, so re-encoding a parsed list
  reproduces the original bytes (and for extension blocks and `uint16` vectors
  distinct buffers never parse alike). `parseClientHello_canonical` composes
  those into ClientHello canonicity: a ClientHello that parsed re-encodes to
  exactly the body it came from, so comparing the parsed fields of a retry
  ClientHello against the original is as strong as comparing the bytes
  (`parseClientHello_body_injective`) — which is what the HelloRetryRequest
  flow needs, and now what it *runs*: the server keeps the first ClientHello as
  parsed and compares the second with one named check,
  `Tls.Server.checkRetryClientHello`, whose
  `Tls.Server.Laws.checkRetryClientHello_body_eq` derives byte equality of the
  two message bodies from the canonicity law.

  `Tls.Client.Laws` and `Tls.Server.Laws` carry that discipline into the state
  machines. Every write path of both engines is proved to advance the write
  traffic state along `Tls.Record.Laws.Extends` — records are protected with the
  keys the engine's own state carries and the advanced state is stored straight
  back — which composes into the nonce non-reuse theorem quoted above
  (`run_nonce_nodup`, and `feed_nonce_nodup` for a single feed, which for a
  server covers the whole encrypted handshake flight). Alongside it,
  `State.WellFormed` is a structural invariant of an established connection —
  the client has both application epochs and has dropped the handshake secrets
  and transcript; the server has the client application epoch installed and has
  consumed the expected client Finished — established by `start` and preserved
  by `feed`, `feedWithFailure`, `sealApplication`, `closeNotify`,
  `sealFatalAlert`, and whole `run`s (`run_wellFormed`). The server's invariant
  carries a second, phase-indexed clause (`WellFormed.writeKeys`): from
  `waitingClientFinished` onwards it always holds a write epoch. It has to be
  phase-indexed rather than a bare `connected → …` because the server installs
  its write keys one transition earlier than the client does — in
  `completeClientHello`, since the flight it emits right there is already
  encrypted — and it is what makes `sealApplication`, `closeNotify`,
  `sealFatalAlert` and a KeyUpdate response total on an established
  connection. The transition laws
  cover the rest of the state-machine list: a connection becomes established
  only by verifying the peer `Finished` (`completeServerHandshake_verified`,
  `acceptClientFinished_verified`), application data is protected only by an
  established and open connection (`sealApplication_connected`) and — the
  inbound mirror — application-data plaintext is only ever *delivered* to the
  caller alongside an established connection, for a single feed and for a whole
  run (`feed_plaintext_connected`, `run_plaintext_connected`; both rest on
  `connected` being absorbing, which is proved as `feed_connected` /
  `run_connected`), a closed
  connection is terminal (`feedWithFailure_closed`; every other failure is an
  `Except` error carrying no successor state, so failure is terminal by
  construction), HelloRetryRequest installs the RFC 8446 synthetic
  `message_hash` transcript (`sendHelloRetryRequest_messageHash`), a KeyUpdate
  moves to the successor traffic secret and restarts its sequence number
  (`acceptKeyUpdate_epoch`), and accepting the ServerHello extends the
  transcript by exactly the message consumed (`acceptServerHello_transcript`).
  The engine transitions those laws are stated about — `acceptClientFinished`,
  `sendHelloRetryRequest`, `acceptKeyUpdate`, `completeServerHandshake` — are
  public but not `@[expose]`d: nameable, so the laws are public statements the
  assurance audit can cite, but not unfoldable outside their own modules.
  Laws about the remaining `private` helpers stay `private`.
- **`Test/`** — nine hermetic test binaries, a one-shot loopback server
  harness, and a scripted (manual-tag) interoperability gate that drives the
  harness with real OpenSSL, curl, and Go `crypto/tls` clients. Each of the
  three library packages also carries a `lean_assurance_test` that audits the
  compiled proofs themselves; see [Proof assurance](#proof-assurance).

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

### The `bv_decide` LRAT certificates

One more item belongs on that list, and it sits *inside* the proofs rather than
beside them. Seven byte-(de)composition identities — `hi_lo_recompose`,
`recompose_hi`, `sequenceBytes_inj` and `nonceOf_inj` in `Tls.Record.Laws`,
`uint16_recompose`, `uint32_recompose` and `uint16_hi` in `Tls.Handshake` — are
discharged by `bv_decide`, which runs CaDiCaL on the reflected `BitVec` goal and
checks the resulting LRAT refutation with a *natively compiled* checker rather
than in the kernel. Lean records that shortcut honestly: each call site gets its
own axiom, `<lemma>._native.bv_decide.ax_1_5`, whose statement is
`Std.Tactic.BVDecide.Reflect.verifyBVExpr <that goal> <that certificate> = true`.

So the trust item is narrow and specific — the compiled LRAT checker and the
compiler that built it, applied to seven fixed certificates — but it is real,
and it **does** reach the headline theorems. `Tls.Record.WriteRun.nodup` and both
engines' `run_nonce_nodup` depend on `nonceOf_inj`'s certificate; record
conservation (`Decoder.feed_conservation`) and seal/open
(`decodeStep_seal_open`) on `recompose_hi`'s and `hi_lo_recompose`'s;
ClientHello canonicity (`parseClientHello_canonical`,
`parseClientHello_body_injective`) and the retry check
(`checkRetryClientHello_body_eq`) on `uint16_hi`'s. Everything else listed as a
principal theorem below — the whole X.509/DER tier, `open_seal`, the handshake
message roundtrips, and every state-machine transition law — closes over nothing
but `propext`, `Classical.choice` and `Quot.sound`. The audit prints the exact
axiom set of each theorem, so this is checked rather than asserted; eliminating
the certificates by proving the seven identities from core's `BitVec` `getLsbD`
lemmas is open follow-up work.

## Proof assurance

The claims above are not left to prose. Three `lean_assurance_test` targets
(from `rules_lean`) re-derive them from the compiled `Environment` while the
test binary is built, so a violation is a red target, not a stale README:

| Target | What it certifies |
| --- | --- |
| `//HaclStar:haclstar_assurance` | The trusted C boundary: the 16 `@[extern] opaque` bindings are accounted for and no proof hole exists in the FFI package |
| `//TLS13:tls13_assurance` | 10 principal theorems — DER exact-slice retention, decoder injectivity/idempotence/trailing-data rejection, `Certificate.decode_tbs_encoded`, `Chain.checkIssuer_verifies` |
| `//Tls:tls_assurance` | 46 principal theorems — nonce non-reuse (`WriteRun.nodup`, both `run_nonce_nodup`/`feed_nonce_nodup`, nonce and sequence injectivity), record conservation and seal/open inversion, ClientHello canonicity and body injectivity, and the state-machine transition and invariant laws (including both directions of the connected-only application-data rule) |

Each target also scans every constant of the whole first-party closure
(`HaclStar`, `TLS13`, `Tls` — 26 modules, ~4650 constants): nothing may reach
`sorryAx`, no axiom may be declared outside the allowed set, and **no
`@[extern]` constant may live outside the `HaclStar` modules**. That last check
is what makes the FFI-boundary claim in the previous section mechanical: native
code appearing anywhere else in the closure fails the build. The allowed-axiom
set is the standard three plus the seven `bv_decide` certificates named above,
listed one by one — so a *new* `bv_decide` call site fails the audit until it is
reviewed and added.

## Tests

`bazel test //...` runs nine hermetic, offline suites plus the three assurance
audits above:

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
    exactly the TBS slice parsed out of the certificate) and the handshake
    wire-codec laws (`Tls.Handshake`: framing roundtrips with residual and
    frame canonicity in the converse direction, reassembly independence,
    per-message parse inversion, GREASE-tolerant extension and `uint16`-vector
    roundtrips, HelloRetryRequest discrimination) and the state-machine layer (`Tls.Client.Laws`,
    `Tls.Server.Laws`: nonce non-reuse across a whole run of either engine,
    scoped by traffic-secret epoch and assuming only that the epochs' secrets
    differ; the `State.WellFormed` invariant established by `start` and
    preserved by every operation; and the transition laws — peer `Finished`
    verified before a connection is established, application data protected
    only when established, closed connections terminal, the HelloRetryRequest
    synthetic `message_hash` transcript, KeyUpdate epoch change). What remains:
    a key-schedule correctness proof against RFC 8446 §7.1 (only known-answer
    tested today), a refinement theorem against the RFC, and any security
    argument
