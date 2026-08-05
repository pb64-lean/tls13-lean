# X.509 parser fixtures

These self-signed leaf certificates were generated with OpenSSL 3.6.2. Their
serial numbers, subjects, validity windows, and extensions are fixed; key
generation is intentionally random, so the committed PEM files are the stable
known-answer vectors.

Only the public certificates are committed; no private keys are retained.

```sh
umask 077
D=Test/Fixtures/X509
T="$(mktemp -d)"

openssl genpkey -algorithm RSA \
  -pkeyopt rsa_keygen_bits:2048 -pkeyopt rsa_keygen_pubexp:65537 \
  -out "$T/rsa.key"
openssl req -new -x509 -config /dev/null -key "$T/rsa.key" \
  -out "$D/rsa2048.pem" \
  -subj "/C=US/O=tls13-lean test/CN=rsa.example.test" \
  -set_serial 0x1001 -not_before 240101000000Z \
  -not_after 20550101000000Z -sha256 \
  -addext "subjectKeyIdentifier=hash" \
  -addext "authorityKeyIdentifier=keyid:always" \
  -addext "subjectAltName=DNS:rsa.example.test,IP:127.0.0.1" \
  -addext "basicConstraints=critical,CA:FALSE" \
  -addext "keyUsage=critical,digitalSignature,keyEncipherment"

openssl genpkey -algorithm EC \
  -pkeyopt ec_paramgen_curve:prime256v1 \
  -pkeyopt ec_param_enc:named_curve -out "$T/p256.key"
openssl req -new -x509 -config /dev/null -key "$T/p256.key" \
  -out "$D/p256.pem" \
  -subj "/C=US/O=tls13-lean test/CN=p256.example.test" \
  -set_serial 0x1002 -not_before 240101000000Z \
  -not_after 20550101000000Z -sha256 \
  -addext "subjectKeyIdentifier=hash" \
  -addext "authorityKeyIdentifier=keyid:always" \
  -addext "subjectAltName=DNS:p256.example.test,IP:2001:db8::1" \
  -addext "basicConstraints=CA:FALSE" \
  -addext "keyUsage=digitalSignature,keyAgreement"

openssl genpkey -algorithm ED25519 -out "$T/ed25519.key"
openssl req -new -x509 -config /dev/null -key "$T/ed25519.key" \
  -out "$D/ed25519.pem" \
  -subj "/C=US/O=tls13-lean test/CN=ed25519.example.test" \
  -set_serial 0x1003 -not_before 240101000000Z \
  -not_after 20550101000000Z \
  -addext "subjectKeyIdentifier=hash" \
  -addext "authorityKeyIdentifier=keyid:always" \
  -addext "subjectAltName=DNS:ed25519.example.test,IP:192.0.2.55" \
  -addext "basicConstraints=critical,CA:FALSE" \
  -addext "keyUsage=digitalSignature"

rm -rf "$T"
```

Inspect a fixture with:

```sh
openssl x509 -in Test/Fixtures/X509/rsa2048.pem -noout -text
```
