# X.509 chain-validation fixtures

These certificates are stable OpenSSL 3.6.2 known-answer fixtures for path
building and validation. All keys are RSA-2048 and all certificate signatures
are RSA PKCS#1 v1.5 with SHA-256. Key generation is intentionally random, so
the committed PEM files—not a rerun—are the byte-exact fixtures.

Only public certificates are committed. The temporary private keys and CSRs
were deleted after generation.

## Fixture matrix

| Path | Serials (hex) | Intended result at `2026-07-19T00:00:00Z` |
| --- | --- | --- |
| `valid-leaf.pem` → `valid-intermediate.pem` → `valid-root.pem` | `5102`, `5101`, `5100` | Valid. The root is self-signed with `CA:TRUE,pathlen:2`; the intermediate has `CA:TRUE,pathlen:0`. |
| `not-ca-leaf.pem` → `not-ca-intermediate.pem` → `valid-root.pem` | `5202`, `5201`, `5100` | Reject: the intermediate has critical `BasicConstraints CA:FALSE`. Its critical KeyUsage includes `keyCertSign`, isolating the BasicConstraints failure. |
| `expired-leaf.pem` → `expired-intermediate.pem` → `valid-root.pem` | `5302`, `5301`, `5100` | Reject: the otherwise valid CA intermediate expired at `2020-01-01T00:00:00Z`. |
| `pathlen-leaf.pem` → `pathlen-intermediate.pem` → `pathlen-root.pem` | `5402`, `5401`, `5400` | Reject: the trust anchor has `CA:TRUE,pathlen:0`, but the path contains one intermediate CA below it. |

The unknown-issuer test uses `valid-leaf.pem` and
`valid-intermediate.pem` without `valid-root.pem` in the trust store. Leaf
certificates are valid from 2025 through 2030. Normal CA certificates are
valid from 2025 through 2035 or 2040.

## Generation

The extension file used during generation contained:

```ini
[root_ca]
basicConstraints = critical,CA:TRUE,pathlen:2
keyUsage = critical,keyCertSign,cRLSign
subjectKeyIdentifier = hash
authorityKeyIdentifier = keyid:always

[intermediate_ca]
basicConstraints = critical,CA:TRUE,pathlen:0
keyUsage = critical,keyCertSign,cRLSign
subjectKeyIdentifier = hash
authorityKeyIdentifier = keyid:always

[not_ca]
basicConstraints = critical,CA:FALSE
keyUsage = critical,keyCertSign,cRLSign
subjectKeyIdentifier = hash
authorityKeyIdentifier = keyid:always

[leaf]
basicConstraints = critical,CA:FALSE
keyUsage = critical,digitalSignature
subjectAltName = DNS:chain.example.test
subjectKeyIdentifier = hash
authorityKeyIdentifier = keyid:always

[pathlen_root]
basicConstraints = critical,CA:TRUE,pathlen:0
keyUsage = critical,keyCertSign,cRLSign
subjectKeyIdentifier = hash
authorityKeyIdentifier = keyid:always
```

With that file at `$T/extensions.cnf`, the fixtures were generated as follows:

```sh
umask 077
D=Test/Fixtures/Chain
T="$(mktemp -d)"
E="$T/extensions.cnf"

openssl genpkey -algorithm RSA -pkeyopt rsa_keygen_bits:2048 \
  -out "$T/valid-root.key"
openssl req -new -sha256 -key "$T/valid-root.key" \
  -subj "/C=US/O=tls13-lean M5/CN=M5 Valid Root CA" \
  -out "$T/valid-root.csr"
openssl x509 -req -sha256 -in "$T/valid-root.csr" \
  -signkey "$T/valid-root.key" -set_serial 0x5100 \
  -not_before 20250101000000Z -not_after 20400101000000Z \
  -extfile "$E" -extensions root_ca -out "$D/valid-root.pem"

openssl genpkey -algorithm RSA -pkeyopt rsa_keygen_bits:2048 \
  -out "$T/valid-intermediate.key"
openssl req -new -sha256 -key "$T/valid-intermediate.key" \
  -subj "/C=US/O=tls13-lean M5/CN=M5 Valid Intermediate CA" \
  -out "$T/valid-intermediate.csr"
openssl x509 -req -sha256 -in "$T/valid-intermediate.csr" \
  -CA "$D/valid-root.pem" -CAkey "$T/valid-root.key" \
  -set_serial 0x5101 \
  -not_before 20250101000000Z -not_after 20350101000000Z \
  -extfile "$E" -extensions intermediate_ca \
  -out "$D/valid-intermediate.pem"

openssl genpkey -algorithm RSA -pkeyopt rsa_keygen_bits:2048 \
  -out "$T/valid-leaf.key"
openssl req -new -sha256 -key "$T/valid-leaf.key" \
  -subj "/C=US/O=tls13-lean M5/CN=chain.example.test" \
  -out "$T/valid-leaf.csr"
openssl x509 -req -sha256 -in "$T/valid-leaf.csr" \
  -CA "$D/valid-intermediate.pem" -CAkey "$T/valid-intermediate.key" \
  -set_serial 0x5102 \
  -not_before 20250101000000Z -not_after 20300101000000Z \
  -extfile "$E" -extensions leaf -out "$D/valid-leaf.pem"

openssl genpkey -algorithm RSA -pkeyopt rsa_keygen_bits:2048 \
  -out "$T/not-ca-intermediate.key"
openssl req -new -sha256 -key "$T/not-ca-intermediate.key" \
  -subj "/C=US/O=tls13-lean M5/CN=M5 Not-CA Intermediate" \
  -out "$T/not-ca-intermediate.csr"
openssl x509 -req -sha256 -in "$T/not-ca-intermediate.csr" \
  -CA "$D/valid-root.pem" -CAkey "$T/valid-root.key" \
  -set_serial 0x5201 \
  -not_before 20250101000000Z -not_after 20350101000000Z \
  -extfile "$E" -extensions not_ca -out "$D/not-ca-intermediate.pem"

openssl genpkey -algorithm RSA -pkeyopt rsa_keygen_bits:2048 \
  -out "$T/not-ca-leaf.key"
openssl req -new -sha256 -key "$T/not-ca-leaf.key" \
  -subj "/C=US/O=tls13-lean M5/CN=not-ca.example.test" \
  -out "$T/not-ca-leaf.csr"
openssl x509 -req -sha256 -in "$T/not-ca-leaf.csr" \
  -CA "$D/not-ca-intermediate.pem" -CAkey "$T/not-ca-intermediate.key" \
  -set_serial 0x5202 \
  -not_before 20250101000000Z -not_after 20300101000000Z \
  -extfile "$E" -extensions leaf -out "$D/not-ca-leaf.pem"

openssl genpkey -algorithm RSA -pkeyopt rsa_keygen_bits:2048 \
  -out "$T/expired-intermediate.key"
openssl req -new -sha256 -key "$T/expired-intermediate.key" \
  -subj "/C=US/O=tls13-lean M5/CN=M5 Expired Intermediate CA" \
  -out "$T/expired-intermediate.csr"
openssl x509 -req -sha256 -in "$T/expired-intermediate.csr" \
  -CA "$D/valid-root.pem" -CAkey "$T/valid-root.key" \
  -set_serial 0x5301 \
  -not_before 20190101000000Z -not_after 20200101000000Z \
  -extfile "$E" -extensions intermediate_ca \
  -out "$D/expired-intermediate.pem"

openssl genpkey -algorithm RSA -pkeyopt rsa_keygen_bits:2048 \
  -out "$T/expired-leaf.key"
openssl req -new -sha256 -key "$T/expired-leaf.key" \
  -subj "/C=US/O=tls13-lean M5/CN=expired-path.example.test" \
  -out "$T/expired-leaf.csr"
openssl x509 -req -sha256 -in "$T/expired-leaf.csr" \
  -CA "$D/expired-intermediate.pem" -CAkey "$T/expired-intermediate.key" \
  -set_serial 0x5302 \
  -not_before 20250101000000Z -not_after 20300101000000Z \
  -extfile "$E" -extensions leaf -out "$D/expired-leaf.pem"

openssl genpkey -algorithm RSA -pkeyopt rsa_keygen_bits:2048 \
  -out "$T/pathlen-root.key"
openssl req -new -sha256 -key "$T/pathlen-root.key" \
  -subj "/C=US/O=tls13-lean M5/CN=M5 PathLen Zero Root CA" \
  -out "$T/pathlen-root.csr"
openssl x509 -req -sha256 -in "$T/pathlen-root.csr" \
  -signkey "$T/pathlen-root.key" -set_serial 0x5400 \
  -not_before 20250101000000Z -not_after 20400101000000Z \
  -extfile "$E" -extensions pathlen_root -out "$D/pathlen-root.pem"

openssl genpkey -algorithm RSA -pkeyopt rsa_keygen_bits:2048 \
  -out "$T/pathlen-intermediate.key"
openssl req -new -sha256 -key "$T/pathlen-intermediate.key" \
  -subj "/C=US/O=tls13-lean M5/CN=M5 PathLen Intermediate CA" \
  -out "$T/pathlen-intermediate.csr"
openssl x509 -req -sha256 -in "$T/pathlen-intermediate.csr" \
  -CA "$D/pathlen-root.pem" -CAkey "$T/pathlen-root.key" \
  -set_serial 0x5401 \
  -not_before 20250101000000Z -not_after 20350101000000Z \
  -extfile "$E" -extensions intermediate_ca \
  -out "$D/pathlen-intermediate.pem"

openssl genpkey -algorithm RSA -pkeyopt rsa_keygen_bits:2048 \
  -out "$T/pathlen-leaf.key"
openssl req -new -sha256 -key "$T/pathlen-leaf.key" \
  -subj "/C=US/O=tls13-lean M5/CN=pathlen.example.test" \
  -out "$T/pathlen-leaf.csr"
openssl x509 -req -sha256 -in "$T/pathlen-leaf.csr" \
  -CA "$D/pathlen-intermediate.pem" -CAkey "$T/pathlen-intermediate.key" \
  -set_serial 0x5402 \
  -not_before 20250101000000Z -not_after 20300101000000Z \
  -extfile "$E" -extensions leaf -out "$D/pathlen-leaf.pem"

rm -rf "$T"
```

OpenSSL independently classifies the four paths with:

```sh
openssl verify -show_chain \
  -CAfile "$D/valid-root.pem" \
  -untrusted "$D/valid-intermediate.pem" "$D/valid-leaf.pem"

openssl verify -show_chain \
  -CAfile "$D/valid-root.pem" \
  -untrusted "$D/not-ca-intermediate.pem" "$D/not-ca-leaf.pem"

openssl verify -show_chain \
  -CAfile "$D/valid-root.pem" \
  -untrusted "$D/expired-intermediate.pem" "$D/expired-leaf.pem"

openssl verify -show_chain \
  -CAfile "$D/pathlen-root.pem" \
  -untrusted "$D/pathlen-intermediate.pem" "$D/pathlen-leaf.pem"
```

The first command succeeds. The remaining commands fail respectively with
`invalid CA certificate`, `certificate has expired`, and
`path length constraint exceeded`.
