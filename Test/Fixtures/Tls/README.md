# TLS server test identity

`server_cert.pem` is the Ed25519 localhost certificate used by the pure
client/server handshake regression. It was copied from
`grpc-lean/Test/Fixtures/Tls` so the reusable TLS core and its first consumer
exercise the same identity.

The matching 32-byte Ed25519 test seed is intentionally embedded in
`Test/TlsServerInteropTest.lean`; it is public test data and must never be used
outside tests.

The fixture was generated with OpenSSL 3 using the equivalent of:

```sh
openssl genpkey -algorithm ED25519 -out server_key.pem
openssl req -new -x509 -key server_key.pem -days 3650 \
  -subj /CN=localhost \
  -addext basicConstraints=critical,CA:TRUE \
  -addext subjectAltName=DNS:localhost,IP:127.0.0.1 \
  -out server_cert.pem
```

The committed certificate is valid from 2026-07-19 through 2036-07-16.
