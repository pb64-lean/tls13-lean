# TLS server test identity

`server_cert.pem` is the Ed25519 localhost certificate used by the pure
client/server handshake regression. It matches
`grpc-lean/Test/Fixtures/Tls/server_cert.pem`, so the reusable TLS core and its
gRPC consumer exercise the same identity.

The matching 32-byte Ed25519 test seed is intentionally embedded in
`Test/TlsServerInteropTest.lean`; it is public test data and must never be used
outside tests.

The equivalent OpenSSL 3 construction is:

```sh
openssl genpkey -algorithm ED25519 -out server_key.pem
openssl req -new -x509 -key server_key.pem -days 3650 \
  -subj /CN=localhost \
  -addext basicConstraints=critical,CA:TRUE \
  -addext subjectAltName=DNS:localhost,IP:127.0.0.1 \
  -out server_cert.pem
```

The committed certificate is valid from 2026-07-19 through 2036-07-16.
