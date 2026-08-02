# Signature-verification fixtures

The RSA-PSS certificate is a stable OpenSSL 3.6.2 known-answer vector. Its
SubjectPublicKeyInfo uses `rsaEncryption`; its self-signature uses
RSASSA-PSS with SHA-256, MGF1-SHA256, a 32-byte salt, and trailer field 1.

The RSA PKCS#1 v1.5, P-256 ECDSA, and Ed25519 positive vectors are the
OpenSSL self-signatures already carried by `../X509/rsa2048.pem`,
`../X509/p256.pem`, and `../X509/ed25519.pem`. Tests verify each signature over
the byte-exact retained TBSCertificate, so the fixture's signed message is
stable and no test private key is required.

The committed certificate was generated as follows. Key generation and the
PSS salt are intentionally random, so the committed PEM—not a rerun—is the
byte-exact vector. The private key was deleted.

```sh
umask 077
T="$(mktemp -d)"

openssl genpkey -algorithm RSA \
  -pkeyopt rsa_keygen_bits:2048 \
  -pkeyopt rsa_keygen_pubexp:65537 \
  -out "$T/rsa.key"

openssl req -new -x509 -config /dev/null \
  -key "$T/rsa.key" \
  -out Test/Fixtures/Signature/rsa-pss.pem \
  -subj "/CN=m3-rsa-pss.example.test" \
  -set_serial 0x3004 \
  -not_before 240101000000Z \
  -not_after 20550101000000Z \
  -sha256 \
  -sigopt rsa_padding_mode:pss \
  -sigopt rsa_pss_saltlen:32 \
  -sigopt rsa_mgf1_md:sha256 \
  -addext "basicConstraints=critical,CA:FALSE" \
  -addext "keyUsage=digitalSignature"

openssl verify -check_ss_sig \
  -CAfile Test/Fixtures/Signature/rsa-pss.pem \
  Test/Fixtures/Signature/rsa-pss.pem

rm -rf "$T"
```

The Ed25519 test also includes RFC 8032 section 7.1 test vector 1 (empty
message), transcribed directly into the Lean test. Malformed RSA encodings are
tested at the EMSA boundary so individual padding, DigestInfo, PSS mask, salt,
and trailer failures are exercised deterministically.
