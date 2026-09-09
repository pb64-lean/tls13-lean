# Workload identity

The initial workload profile adds Ed25519 client proof of possession to the
existing TLS 1.3 handshake. It is not a general PKI manager or a SPIFFE library.
Certificate issuance, revocation, trust-bundle distribution, workload-name
authorization, entropy, sockets and process supervision remain caller-owned.

## Credentials and rotation

`Tls.Identity.create chain key purpose now requireExplicitPurpose` validates
strict DER, dates, digital-signature key usage, the endpoint's extended key
usage, the Ed25519 public-key profile and private-key consistency. The bounded
input is at most ten certificates / 1 MiB. These local checks do not replace
the remote peer's trust-path validation. Errors never include private keys.

Create an `IdentityStore` from a validated identity. Capture `store.snapshot`
exactly once per new handshake and use the certificate and key from that same
snapshot. `rotate` publishes an already-validated pair under a mutex and
increments a generation atomically. Concurrent snapshot reads cannot overwrite
a rotation. Failed validation leaves the old store unchanged; established
connections and already captured snapshots retain their original generation.
There is no file watcher, automatic renewal, or private-key zeroization claim.

## Client

Set `Tls.Client.Config.identity` to the captured identity and `peerAuth` to a
`PeerAuthPolicy` containing trust anchors, current Unix seconds and the intended
DNS name or IP address. The engine rejects an identity without this policy.
It verifies server Finished, trust path, server purpose and hostname before
building the client Certificate/CertificateVerify flight. A client with no
suitable credential sends an empty Certificate only when requested. A server
that does not request authentication receives no client certificate.

Do not reuse an identity across arbitrary redirected HTTP origins. Transport
adapters must bind credential selection to the configured peer and must not
enable insecure verification when credentials are present.

## Server

Set `Tls.Server.Config.clientAuth` to `ClientAuthPolicy` with current Unix
seconds and trusted client roots. The default requires both a certificate and
an explicit clientAuth EKU; `required := false` allows a missing certificate,
but never allows an invalid presented certificate. `requireExplicitPurpose :=
false` permits absent EKU or anyExtendedKeyUsage. All selected chain members'
present EKU restrictions are respected. No implicit system trust is consulted.

For server certificate rotation, capture a validated serverAuth identity and
copy its `certificateChain` and `signingKey` into the per-handshake Server.Config
along with freshly generated ephemeral keys/random. Do not snapshot these two
fields independently. Existing callers may still construct Config directly.

After `state.connected`, `state.peerCertificates` contains the peer chain only
when path validation and the client signature succeeded. An anonymous optional
handshake has an empty array. Mapping certificate identity to an application
principal and applying authorization are explicit application decisions.

## Protocol and assurance

CertificateRequest is accepted only in its initial-handshake position, with an
empty context and a nonempty signature_algorithms extension. Duplicate requests,
duplicate extensions, unsolicited client entry extensions, omitted required
proofs, role-reflected signatures, invalid chains and invalid Finished messages
fail closed. Post-handshake authentication is not negotiated. Client signing
and client CertificateVerify acceptance currently use Ed25519 only; existing
server-signature verification algorithms are unchanged.

Application traffic secrets still use the transcript through server Finished.
Client Finished additionally commits to client Certificate and CertificateVerify.
Record fragmentation threads a single handshake write epoch. Existing nonce,
epoch and state-machine proofs remain enforced; the server key-schedule theorem
now explicitly quantifies optional CertificateRequest bytes in its transcript.
These are scoped engine proofs, not a whole-library security certification.

The implementation follows [RFC 8446 authentication messages](https://www.rfc-editor.org/rfc/rfc8446.html#section-4.4)
and [RFC 5280 extended key usage](https://www.rfc-editor.org/rfc/rfc5280.html#section-4.2.1.12).

Run `bazel test //Test:workload_identity_test` for mTLS, trust/purpose, fragmented
input, pre-disclosure rejection and concurrent rotation checks. All keys under
`Test/Fixtures/Identity` are deliberately public test material, never production
credentials. `regenerate.sh` creates replacements with OpenSSL; test time is
derived from the fixture, not the machine clock.
