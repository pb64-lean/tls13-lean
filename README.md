# tls13-lean

[![CI](https://github.com/pb64-lean/tls13-lean/actions/workflows/ci.yml/badge.svg?branch=main)](https://github.com/pb64-lean/tls13-lean/actions/workflows/ci.yml) [![Assurance](https://github.com/pb64-lean/tls13-lean/actions/workflows/assurance.yml/badge.svg?branch=main)](https://github.com/pb64-lean/tls13-lean/actions/workflows/assurance.yml)

TLS 1.3 for Lean 4 implementing RFC 9846: pure-Lean protocol machinery —
record layer, handshake codecs, sans-I/O **client and server** state machines,
and X.509 path validation — over **formally verified, constant-time crypto
primitives** bound from [HACL\*](https://github.com/hacl-star/hacl-star) via an
explicit C FFI.

RFC 9846 obsoletes RFC 8446. Compatibility identifiers such as `rfc8446` and
`masterSecret` denote RFC 8446-derived key-schedule structure, unchanged wire
labels, or RFC 8448 test vectors. [Protocol scope](#protocol-scope) defines the
implemented RFC 9846 profile, unsupported features, and caller obligations.

This is the "own the protocol logic, borrow the primitives" design. HACL\*
supplies the machine-checked C crypto; Lean supplies explicit protocol state.
The runtime uses no system crypto library such as OpenSSL; HACL\* is fetched at
a pinned commit and its portable C has no runtime dependency.

**Verification status, stated precisely.** Two distinct things are
machine-checked, and it matters which is which:

- The imported **HACL\* C primitives** carry externally machine-verified
  correctness and constant-time proofs. This repository does not re-prove
  them; it binds them across an explicit FFI boundary and trusts them.
- The **Lean protocol code** carries kernel-checked laws about the
  implementation itself — the record framer (byte conservation,
  fragmentation independence, sequence/nonce injectivity, seal/open
  inversion parametric over the opaque AEAD), the handshake codecs (wire
  roundtrips with explicit residual, body inversion, GREASE-tolerant
  extension preservation, ClientHello canonicity — a parsed ClientHello
  re-encodes to exactly the bytes it came from — HelloRetryRequest
  discrimination, no partial frame ever accepted), the **state machines**
  (finite write traces over the actual `(AEAD key, nonce)` pairs, with
  unconditional within-epoch non-repetition and an explicit finite-run
  derived-key distinctness condition across epochs, plus handshake state
  invariants and transition laws), the
  **key schedule** (structural refinement against RFC 8446 §7.1's derivation
  tree — see below), and the DER decoder (exact-slice retention carried through
  to the bytes certificate signatures are verified over). These are proofs
  about the executable definitions, not a parallel model.

**AEAD write-trace distinctness, stated exactly.**
`Tls.Client.run_nonce_nodup` and `Tls.Server.run_nonce_nodup` say: for any
successful engine run there is an explicit finite `Tls.Record.AeadWriteRun` —
the list of records the run protected, each tagged with the concrete AEAD key
that protected it — leading from the connection's initial write state to its
final one. If the concrete epoch keys in that run are distinct, no
`(AEAD key, nonce)` pair repeats. This is the cryptographically relevant nonce
misuse claim, with derived-key collision freedom left as a visible sufficient
condition on the finite execution. Read the fine print:

- It is about *this engine's own emissions along one chain of states*. A caller
  who clones a `State` and drives two connections from the same keys is outside
  its reach — Lean values are duplicable, and no theorem about a pure function
  can forbid copying one. Single-threading the state is the caller's obligation.
- It covers the **write** direction only. The tracked records are this engine's
  emissions; read-side nonces are the peer's.
- Sequence numbers restart at zero on every KeyUpdate, so the trace is scoped
  by concrete AEAD key. Within one epoch no freshness hypothesis is needed:
  `seal` uses the nonce of the current sequence number and returns the state
  with that number advanced without wrapping, and for a fixed IV the nonce
  determines the sequence number. Pair distinctness *across* epochs uses the
  hypothesis `aeadKeys.Nodup` on this finite trace.

**The key schedule refines the trace; it does not discharge collisions.**
`Tls.Client.run_nonce_trace_spec` and
`Tls.Server.run_nonce_trace_spec` (plus the corresponding `feed` and
`start_run_nonce_trace_spec` forms) return both traces: a `WriteRun` whose
traffic secrets are evaluations of strictly increasing RFC 8446 §7.1 / §7.2
epoch descriptors, and an `AeadWriteRun` over the actual keys, with an equality
showing that they record the same nonce sequence. `c hs traffic` precedes
`c ap traffic`, and every KeyUpdate moves one structural `"traffic upd"` step
forward. Distinct derivation histories need not produce distinct bytes: a
fixed-size KDF cannot be globally injective, and an unbounded fixed-size
KeyUpdate chain must eventually collide. Consequently:

- `aeadKeys.Nodup → keyNonces.Nodup` is an explicit theorem hypothesis. It is a
  satisfiable condition on the particular finite run, and collision resistance
  makes it overwhelmingly likely for feasible executions; it is not a
  deterministic theorem about the opaque HACL\* binding.
- `Spec.Epoch.updates` is an unbounded `Nat`, so the structural result
  covers any number of KeyUpdates without pretending that their evaluated
  byte strings are forever unique.
- The schedule-refined forms start before the first epoch — a client waiting
  for ServerHello or a server waiting for ClientHello, as produced by `start`
  and maintained by `State.WellFormed.noWriteKeys`. The caller's
  single-threading obligation is unchanged.

**Key-schedule refinement, stated exactly.** `TLS13/KeySchedule/Spec.lean` is a
declarative transcription of RFC 8446 §7.1: the `HkdfLabel` wire structure,
`HKDF-Expand-Label`, `Derive-Secret`, and the *whole derivation diagram encoded
as data* — for every named secret (`ext binder`, `res binder`, `c e traffic`,
`e exp master`, `c hs traffic`, `s hs traffic`, `c ap traffic`, `s ap traffic`,
`exp master`, `res master`), which secret it hangs off, under which label, over
which message sequence. `Derived.tree_rfc8446` and `Label.text_rfc8446` are that
diagram, machine-checked. `TLS13/KeySchedule/Refinement.lean` and the engines'
laws then prove the implementation computes it. Read the fine print:

- It is **structural**, not cryptographic. HKDF-Extract and HKDF-Expand are
  opaque `@[extern]` HACL\* bindings, so no theorem here can say the schedule
  produces the right *bytes*. Every refinement theorem is stated for an
  arbitrary `Spec.Hkdf` the bindings implement (`Implements`), and its proof
  uses no property of `extract`/`expand` beyond those defining equations — so
  each one holds *whatever the primitive computes*, the same posture as
  `open_seal`'s hypothesis about the AEAD. What is proved
  is that the implementation applies the primitive in the RFC's shape: the
  RFC's labels, the RFC's contexts, the RFC's parent secrets, the RFC's output
  lengths, in the RFC's order. That is precisely the class real TLS
  key-schedule bugs fall into — a mistyped label, the wrong transcript at a
  `Derive-Secret`, the handshake secret used where the main secret belongs, a
  derivation step omitted.
- One theorem *is* unconditionally about bytes: `hkdfLabel_bytes`. The
  `HkdfLabel` serialization is pure Lean, so its wire image is pinned outright
  — two big-endian length bytes, the length of `"tls13 " + Label`, the six
  ASCII bytes of `"tls13 "` spelled out, the label, the one-byte context
  length, the context.
- The linkage reaches the engines. `Tls.Client.acceptServerHello_keySchedule`
  says the client's handshake epochs are `c hs traffic` / `s hs traffic` of the
  Handshake Secret over ClientHello…ServerHello (the same transcript
  `acceptServerHello_transcript` identifies), and
  `completeServerHandshake_keySchedule` says that at the moment the client
  becomes `connected` its write epoch is `c ap traffic` and its read epoch
  `s ap traffic`, each `Derive-Secret` of the **Main** Secret (the compatibility
  API identifier is `masterSecret`) over ClientHello…server Finished, with
  their §7.3 key/IV/sequence state.
  `Tls.Server.completeClientHello_keySchedule` is the server's mirror, and also
  pins the client Finished it will demand to §4.4.4's `finished_key` of the
  client handshake traffic secret. `processHandshakeBuffer_keySchedule` carries
  the client's link across the *whole* encrypted server flight
  (EncryptedExtensions, Certificate, CertificateVerify, Finished) in one
  statement, so the two client laws compose into ServerHello → established
  connection, and `Tls.Client.feed_keySchedule` carries it the rest of the way
  out to the API boundary, through the record framing, decryption and dispatch
  in between. Two caveats on that last step, both visible in its statement:
  a feed may deliver the server Finished *and* a post-handshake KeyUpdate in
  separate records, so the epochs it ends on are the §7.1 application secrets
  after `n` §7.2 `"traffic upd"` steps (`n = 0` when no KeyUpdate followed), and
  the law is stated for a feed that does not itself accept the ServerHello —
  `acceptServerHello_keySchedule` is the law for that step. There is no single
  theorem joining those two client statements. The server has no `feed`-level
  analogue because its establishment transition also moves the *read* epoch
  from `c hs traffic` to `c ap traffic` when the client Finished arrives, which
  does not fit the same "rolled forward" shape.
- The **empirical** anchor is separate and complementary: `hacl_kat_test` checks
  the schedule against RFC 8448's published values (`33ad0a1c…`, `6f2615a1…`)
  and the `HkdfLabel` layout against a hand-written encoding. A proof cannot say
  the opaque primitive computes the right bytes; a vector cannot say the tree
  has the right shape. **If a theorem and a known-answer test ever disagree, the
  test wins and the specification is what is wrong.**
- Not covered: the PSK/early-data branches (`ext binder`, `res binder`,
  `c e traffic`, `e exp master`) and the exporter/resumption outputs
  (`exp master`, `res master`) are in the specification but this implementation
  does not compute them, so there is nothing to refine — see
  [Protocol scope](#protocol-scope).

What is **not** claimed: no security proof of the handshake or state machines,
no cryptographic correctness of HKDF, the AEAD, the hashes, or the signature
primitives (they are opaque FFI bindings, trusted from HACL\*), no timing
analysis of Lean control code, and nothing about the C shims beyond their length
preconditions.

## Layout

Four Bazel packages:

- **`HaclStar/`** — the crypto FFI: SHA-256/384/512, HMAC-SHA256,
  HKDF-SHA256, X25519, P-256 ECDH, ChaCha20-Poly1305 AEAD, and Ed25519 +
  ECDSA-P256 signatures (verify and sign). 16 `@[extern] opaque`
  declarations over two small C shims.
- **`TLS13/`** — the RFC 8446 §7.1 key schedule, its specification, and the
  X.509 stack. `TLS13.KeySchedule` is the executable schedule
  (`HKDF-Expand-Label`, `Derive-Secret`, Early/Handshake/Main, with the
  compatibility API identifier `masterSecret`);
  `TLS13.KeySchedule.Spec` is §7.1 transcribed declaratively over an abstract
  HKDF interface, with the derivation diagram encoded as data (`Derived.parent`
  / `Derived.label` / `Derived.context`, certified against the RFC by
  `Derived.tree_rfc8446` and `Label.text_rfc8446`); and
  `TLS13.KeySchedule.Refinement` proves the implementation computes the
  specification for *any* HKDF the HACL\* bindings implement — `hkdfLabel`
  byte for byte, then `expandLabel`, `deriveSecret`, and each secret of the
  extract chain and of the `Derive-Secret` tree. Alongside it, the X.509 stack:
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
  `WriteRun.nodup`, the traffic-secret/nonce bookkeeping result. It also defines
  `AeadWriteRun`, converts every `WriteRun` to the corresponding trace over the
  concrete AEAD keys, and proves `AeadWriteRun.nodup`; that is the
  cryptographically relevant theorem the engines instantiate. The schedule
  refinement (`EpochsFrom`, `SpecExtends`) identifies the strictly increasing
  derivation histories behind the traffic-secret trace while retaining
  concrete AEAD-key distinctness as an explicit finite-run condition.
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
  HelloRetryRequest is discriminated from ServerHello by the RFC 9846 sentinel
  random. `parseClientHello_clientHelloBody_mem` lifts that to a whole
  ClientHello: the cipher suites, offered versions, supported groups, key-share
  groups, signature schemes and the entire extension list — unknown and GREASE
  entries included — are returned in wire order with nothing dropped or
  reordered, with the four interpreted extensions allowed anywhere in the list
  in any interleaving (the only structural hypothesis left is that no two
  extensions share a type, which RFC 9846 forbids and `parseExtensions`
  rejects). `parseClientHello_clientHelloBody_psk` covers the resumption shape
  as well — a `pre_shared_key` offer as the final extension with a non-empty
  `psk_key_exchange_modes` is accepted and retained verbatim, but PSK is not
  *negotiated*; see the scope list below.
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
  `parseKeyShareEntries_image` show that every block the parser accepts has a
  lossless existential wire decomposition consistent with the identifiers and
  known-group shares it returned. Unlike extension blocks and `uint16`
  vectors, a parsed key-share result cannot itself be re-encoded to recover the
  input: unknown/GREASE groups retain their identifiers but deliberately drop
  their opaque key bytes, so no parser-injectivity theorem is possible.
  `parseClientHello_canonical` composes
  those into ClientHello canonicity: a ClientHello that parsed re-encodes to
  exactly the body it came from, so comparing the parsed fields of a retry
  ClientHello against the original is as strong as comparing the bytes
  (`parseClientHello_body_injective`) — the property used by the
  HelloRetryRequest flow. The server retains the parsed first ClientHello and
  compares the second with one named check,
  `Tls.Server.checkRetryClientHello`, whose
  `Tls.Server.checkRetryClientHello_body_eq` derives byte equality of the
  two message bodies from the canonicity law.

  `Tls.Client.Laws` and `Tls.Server.Laws` carry that discipline into the state
  machines. Every write path of both engines is proved to advance the write
  traffic state along `Tls.Record.Extends` — records are protected with the
  keys the engine's own state carries and the advanced state is stored straight
  back — which composes into the write-trace distinctness theorem quoted above
  (`run_nonce_nodup`, and `feed_nonce_nodup` for a single feed, which for a
  server covers the whole encrypted handshake flight). The same walk is done a
  second time carrying the *identity* of each epoch as a key-schedule node
  (`run_epochs`); `run_nonce_trace_spec` returns that structural witness beside
  both the traffic-secret bookkeeping trace and the actual AEAD key--nonce
  trace, without conflating distinct nodes with distinct derived-key bytes.
  Alongside it,
  `State.WellFormed` is a structural invariant of an established connection —
  the client has both application epochs and has dropped the handshake secrets
  and transcript; the server has the client application epoch installed and has
  consumed the expected client Finished — established by `start` and preserved
  by `feed`, `feedWithFailure`, `sealApplication`, `closeNotify`,
  `sealFatalAlert`, and whole `run`s (`run_wellFormed`). Each engine's invariant
  carries a second, phase-indexed clause. The server's (`WellFormed.writeKeys`):
  from `waitingClientFinished` onwards it always holds a write epoch. It has to
  be phase-indexed rather than a bare `connected → …` because the server
  installs its write keys one transition earlier than the client does — in
  `completeClientHello`, since the flight it emits right there is already
  encrypted — and it rules out a missing-write-keys failure for
  `sealApplication`, `closeNotify`, `sealFatalAlert`, and a KeyUpdate response
  on an established connection. Record-layer failures such as sequence
  exhaustion are possible.
  The client's (`WellFormed.noReadKeys`) is the inbound mirror, and the
  state-only half of the application-data rule below: while the client is still
  waiting for the ServerHello it holds *no* read epoch, so it cannot decrypt a
  protected record at all and therefore cannot deliver plaintext — only
  `acceptServerHello` installs the first read epoch, and it leaves
  `waitingServerHello` in the same step. The server has the same clause
  (`WellFormed.noReadKeys`, over `waitingClientHello` and
  `waitingSecondClientHello`, so the HelloRetryRequest detour is covered), and
  both engines also carry its write-side half (`WellFormed.noWriteKeys`): before
  the connection's first epoch is installed there is none to replace, which
  anchors `run_nonce_trace_spec` at the beginning of the schedule. The
  transition laws
  cover the rest of the state-machine list: a connection becomes established
  only by verifying the peer `Finished` (`completeServerHandshake_verified`,
  `acceptClientFinished_verified`), application data is protected only by an
  established and open connection (`sealApplication_connected`) and — the
  inbound mirror — application-data plaintext is only ever *delivered* to the
  caller alongside an established connection, for a single feed and for a whole
  run (`feed_plaintext_connected`, `run_plaintext_connected`; both rest on
  `connected` being absorbing, which is proved as `feed_connected` /
  `run_connected`), receiving `close_notify` half-closes only the peer's write
  direction and later peer data is ignored
  (`feedWithFailure_peerClosed_ignored`); after the local direction closes, a
  crossing requested KeyUpdate still advances the read epoch but emits nothing,
  and even fatal alerts are suppressed
  (`acceptKeyUpdate_localClosed_suppresses_response`,
  `sealFatalAlert_localClosed`). HelloRetryRequest installs the RFC
  9846 synthetic `message_hash` transcript
  (`sendHelloRetryRequest_messageHash`), a KeyUpdate
  moves to the successor traffic secret and restarts its sequence number
  (`acceptKeyUpdate_epoch`), and accepting the ServerHello extends the
  transcript by exactly the message consumed (`acceptServerHello_transcript`).
  The engine transitions those laws are stated about — `acceptClientFinished`,
  `sendHelloRetryRequest`, `acceptKeyUpdate`, `completeServerHandshake` — are
  public but not `@[expose]`d: nameable, so the laws are public statements the
  assurance audit can cite, but not unfoldable outside their own modules.
  Laws about the remaining `private` helpers stay `private`.
- **`Test/`** — ten hermetic test binaries, a one-shot loopback server
  harness, and a scripted (manual-tag) interoperability gate that drives the
  harness with real OpenSSL, curl, and Go `crypto/tls` clients. Each of the
  three library packages also carries a `lean_assurance_test` that audits the
  compiled proofs themselves; see [Proof assurance](#proof-assurance).

## Protocol scope

Implemented and negotiated:

- **Cipher suite**: `TLS_CHACHA20_POLY1305_SHA256` — deliberately the single
  suite whose every primitive is portable scalar C in HACL\* (no per-CPU
  assembly), so the build is identical on x86-64 and arm64.
- **Key exchange**: X25519 preferred; P-256 available when configured.
- **Server authentication**: Ed25519 (the server signs CertificateVerify
  with a raw Ed25519 key). Clients accept CertificateVerify signatures with
  `ecdsa_secp256r1_sha256`, `ed25519`, `rsa_pss_rsae_sha256`, and
  `rsa_pss_pss_sha256`; PKCS#1 v1.5 is advertised for certificate-*chain*
  selection only, as RFC 9846 requires.
- **Extensions**: server_name, supported_groups, signature_algorithms, ALPN,
  supported_versions, key_share; the server performs HelloRetryRequest with
  the synthetic `message_hash` transcript and strict second-ClientHello
  checks.
- **Post-handshake core**: both roles receive KeyUpdate, advance the read
  epoch, and, while the local write side remains open, answer
  `update_requested` under the old write epoch before advancing it. Responses
  stop at RFC 9846's `2^48 - 1` sending-epoch limit;
  the receiving direction is intentionally not capped. Key-changing messages
  must finish their protected record. The API does not initiate a
  proactive `update_requested` KeyUpdate, so there is no outstanding-request
  state to manage. It also responds per requested record while processing a
  feed; a batch containing several requested KeyUpdates is not collapsed into
  one deferred response.
- **Orderly closure**: `close_notify` is a directional half-close. It produces
  no automatic echo, leaves the local write direction usable, and causes
  already-framed later records and later input chunks to be ignored. Once the
  local direction has sent its own `close_notify`, it emits no more records:
  a crossing requested KeyUpdate advances only the read epoch, and
  `sealFatalAlert` returns `connectionClosed`.

Unsupported: PSK and session resumption
(NewSessionTicket is silently ignored without semantically parsing its body;
the server never issues tickets),
0-RTT, the exporter and resumption secrets, client certificates,
AES-GCM suites, client-side HelloRetryRequest processing, and post-quantum
hybrid groups (a hybrid key share in a
ClientHello is tolerated and skipped, not negotiated). The server's
*negotiated* surface stays deliberately narrow (ChaCha20-Poly1305 +
X25519/P-256 + Ed25519 — algorithms implemented by the clients in the interop
gate), but its *acceptance* follows RFC 9846's select-from-overlap rule:
unknown cipher suites, groups, signature schemes, GREASE values, and
extensions are tolerated wherever the RFC permits. Mainstream clients
interoperate with the server — OpenSSL `s_client`, curl, and Go `crypto/tls` all
complete handshakes and fetch a page over the loopback harness, including
the HelloRetryRequest path when their first flight carries only key shares
this server does not implement (see the interop gate under Tests).

`Record.Decoder.feed` has an explicit closure limitation: it frames a whole
input chunk before the state machine processes its records. Consequently, a
malformed record header trailing a valid `close_notify` in the *same* `feed`
call can still make framing fail before the alert is observed; the same bytes
in a later call are ignored. Eliminating that chunk-boundary distinction
requires a decode-one/process-one driver rather than the batch decoder.

## X.509

`TLS13.X509` implements: strict DER (BER forms rejected), RFC 7468 PEM,
full certificate parsing with byte-exact retention of the signed structures,
path building with backtracking and bounded work
(depth ≤ 10, ≤ 128 issuer attempts by default), expiry, CA / `keyCertSign` /
`pathLenConstraint` enforcement, the RFC 9846 leaf `digitalSignature` KeyUsage
condition, rejection of unhandled critical extensions,
libpq-style hostname verification (SAN dNSName wildcards, IPv4/IPv6
literals, CN fallback only without SAN; IDNA names must be given in A-label
form), and channel-binding digests. Chain signature algorithms:
ECDSA-P256-SHA256, Ed25519, RSA PKCS#1 v1.5 SHA-256, RSA-PSS SHA-256.

The server applies the relevant leaf policy on the sending side as well:
before constructing its certificate flight it strict-decodes the configured
leaf, rejects a present KeyUsage without `digitalSignature`, and requires an
Ed25519-compatible SPKI for its CertificateVerify scheme.

Deliberately out of scope, matching libpq's default behavior: CRL and OCSP
revocation. Also not interpreted: extendedKeyUsage, nameConstraints, policy
constraints (they fail validation only if marked critical, since unhandled
critical extensions are rejected).

## Sans-I/O design

The engines perform no I/O, read no clock, and generate no entropy:

- `Tls.Client.Config` / `Tls.Server.Config` take caller-supplied randoms,
  ephemeral key-exchange scalars, and session ids. Each key share must be
  generated independently and used for exactly one connection, as RFC 9846
  requires. Reusing a Config drawn from a CSPRNG is invalid. Downstream shells
  generate fresh values per connection with
  Lean's `IO.getRandomBytes`. This cross-connection freshness property cannot
  be enforced by a pure API whose values are freely duplicable. The ECDSA
  signing binding likewise takes an explicit per-message nonce — nonce hygiene
  is the caller's responsibility.
- `feed` consumes wire bytes and returns produced wire bytes + plaintext;
  failures from `feedWithFailure` carry the latest state solely so the caller
  can seal an alert under the correct epoch. That state and every alias of the
  pre-error state must then be discarded. This is a caller contract, not
  linearity enforced by Lean's pure value semantics.
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
- The shims (`HaclStar/shim/hacl_shim.c`,
  `HaclStar/shim/signature_shim.c`, about 400 lines total) are the only
  hand-written C: they marshal Lean `ByteArray`s
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

### Nothing inside the proofs

That list is the whole of it: no proof in this repository adds to it. Every
constant in the first-party closure — `HaclStar`, `TLS13`, `Tls`, theorems and
definitions alike — closes over exactly the three standard Lean axioms,
`propext`, `Classical.choice` and `Quot.sound`, and often fewer. Nothing depends
on `sorryAx`, on `Lean.ofReduceBool`/`ofReduceNat`, or on a generated axiom of
any kind.

The byte-(de)composition identities supporting record framing, write-trace tag
distinctness, and ClientHello canonicity are kernel-checked arithmetic proofs:
`hi_lo_recompose`, `recompose_hi`, `recompose_lo`, `sequenceBytes_inj`, and
`nonceOf_inj` in `Tls.Record.Laws`, plus `uint16_recompose`,
`uint32_recompose`, `uint16_hi`, and `uint16_lo` in `Tls.Handshake`.
`Nat.shiftLeft_add_eq_or_of_lt` rewrites a disjoint `|||` as `+` (packaged as
the local `or_add_lt`), byte extraction becomes division and remainder by a
literal, and `omega` produces the proof term. `sequenceBytes_inj` is an
arithmetic result over the eight extracted bytes; `nonceOf_inj` reduces to it
by cancelling the IV from the XOR (`UInt8.xor_assoc`, `xor_self`, `zero_xor`).
The trusted surface does not import `Std.Tactic.BVDecide` or depend on its
natively checked LRAT certificates.

The audit below prints the exact axiom set of every principal theorem and
rejects anything outside the standard three, so this is checked on every build
rather than asserted here.

## Proof assurance

The claims above are not left to prose. Three `lean_assurance_test` targets
(from `rules_lean`) re-derive them from the compiled `Environment` while the
test binary is built, so a violation is a red target, not a stale README:

| Target | What it certifies |
| --- | --- |
| `//HaclStar:haclstar_assurance` | The trusted C boundary: the 16 `@[extern] opaque` bindings are accounted for and no proof hole exists in the FFI package |
| `//TLS13:tls13_assurance` | 23 principal theorems — the RFC 8446 §7.1 derivation tree as data (`Derived.tree_rfc8446`, `Label.text_rfc8446`), the `HkdfLabel` wire image byte for byte, and the refinement of `expandLabel`/`deriveSecret`/Early/Handshake/Main (compatibility theorem identifier `masterSecret_spec`)/`Derive-Secret`; plus DER exact-slice retention, decoder injectivity/idempotence/trailing-data rejection, `Certificate.decode_tbs_encoded`, `Chain.checkIssuer_verifies`, and `Chain.validate_leaf_keyUsage` |
| `//Tls:tls_assurance` | 88 principal theorems — finite write traces (`WriteRun.nodup`, `AeadWriteRun.nodup`, both `run_nonce_nodup`/`feed_nonce_nodup`, the schedule-refined `run_nonce_trace_spec`/`start_run_nonce_trace_spec`, `run_epochs`, and nonce/sequence injectivity), record conservation, the exact `TLSInnerPlaintext` bound, and seal/open inversion; ClientHello canonicity and body injectivity; the §7.3/§7.2/§4.4.4 record-layer and Finished derivations and the engines' §7.1 epoch installations (including `Tls.Client.feed_keySchedule`, the linkage stated at the `feed` boundary); and the state-machine transition and invariant laws, including KeyUpdate limit/error behavior, no output after local closure, directional peer closure, both directions of the connected-only application-data rule, and both engines' no-epoch-before-the-first-flight clauses |

Each target also scans every constant of the full 28-module first-party closure
(`HaclStar`, `TLS13`, `Tls`): nothing may reach
`sorryAx`, no axiom may be declared outside the allowed set, and **no
`@[extern]` constant may live outside the `HaclStar` modules**. That last check
is what makes the FFI-boundary claim in the previous section mechanical: native
code appearing anywhere else in the closure fails the build. The allowed-axiom
set is exactly `propext`, `Classical.choice` and `Quot.sound` — nothing else is
tolerated, so a `bv_decide` call site (or any other axiom-generating tactic)
reaching a principal theorem fails the audit.

## Tests

`bazel test //...` runs ten hermetic, offline suites plus the three assurance
audits above:

| Target | Coverage |
| --- | --- |
| `hacl_kat_test` | Coverage for every binding, using published vectors where available: SHA-2 (FIPS 180), HMAC (RFC 4231), HKDF (RFC 5869), X25519 (RFC 7748), P-256 ECDH (RFC 5903), ChaCha20-Poly1305 (RFC 8439) + tamper detection, Ed25519 (RFC 8032), ECDSA roundtrip, and broad RFC 8448 key-schedule checkpoints plus a hand-encoded `HkdfLabel`; it also exercises HKDF's expansion ceiling and rejects malformed X25519/AEAD dimensions at the FFI boundary |
| `tls_handshake_test` | Wire codecs against a GREASE-laden, fragmented, reordered ClientHello; record reassembly across TCP boundaries; missing-extension and duplicate-extension alerts; the full HelloRetryRequest flow |
| `tls_record_test` | RFC 9846's exact `TLSInnerPlaintext` boundary for both seal and open, plus rejection one byte above it |
| `tls_server_interop_test` | Authenticated handshake between this repo's client and server engines (no sockets): negotiation, sender-side leaf policy, three-record server flight, application data both ways, 50-certificate fragmentation, KeyUpdate ordering/limits/errors (including crossing requests after local close), unsupported-ticket handling, alert classification, and directional closure behavior |
| `x509_der_test`, `x509_certificate_test`, `x509_chain_test`, `x509_signature_test`, `x509_hostname_test`, `x509_channel_binding_test` | DER/PEM strictness corpus; OpenSSL-generated RSA/P-256/Ed25519 fixtures; chain validation success and eleven exercised failure classes (including leaf `digitalSignature` KeyUsage); RSA/ECDSA/PSS signature vectors and boundary rejections; hostname and channel-binding rules |

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
`bazel test //...` stays hermetic and offline. Reference tool versions are
OpenSSL 3.6.1, curl 8.18.0, and Go 1.25.6.

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

## Coverage summary

The implemented surface comprises the HACL\* FFI, key schedule, record layer,
handshake codecs for both roles, sans-I/O client and server state machines,
X.509 validation, and mainstream-client server interoperability. The protocol
scope above identifies unsupported algorithms and handshake modes.

The proof surface covers record framing and protection, X.509 DER retention and
signature boundaries, handshake wire codecs, state-machine invariants and
transitions, and key-schedule refinement through
`Tls.Client.feed_keySchedule`. The detailed claims and theorem names appear in
[Layout](#layout) and [Proof assurance](#proof-assurance).

The proof boundary excludes a server `feed`-level key-schedule statement and a
single client whole-handshake law joining
`acceptServerHello_keySchedule` with `feed_keySchedule`. The §7.1 branches
without executable support (PSK binders, early data, exporter and resumption
secrets) have a specification but no refinement. No security argument is
claimed for confidentiality, authentication, or the handshake as a
cryptographic protocol.
