#!/usr/bin/env bash
# Public, disposable test credentials. Never use these keys outside tests.
set -euo pipefail
cd "$(dirname "$0")"
fixture_tmp=$(mktemp -d)
trap 'rm -rf "$fixture_tmp"' EXIT
openssl genpkey -algorithm ED25519 -out root-key.pem
openssl req -new -x509 -key root-key.pem -out root.pem -days 3650 \
  -subj /CN=tls13-lean-test-root -set_serial 7001 \
  -addext basicConstraints=critical,CA:TRUE \
  -addext keyUsage=critical,keyCertSign,cRLSign
for identity in client rotated server; do
  openssl genpkey -algorithm ED25519 -out "${identity}-key.pem"
  openssl pkey -in "${identity}-key.pem" -outform DER -out "${identity}-key.der"
  purpose=clientAuth
  if [[ "$identity" == server ]]; then purpose=serverAuth; fi
  openssl req -new -key "${identity}-key.pem" -out "$fixture_tmp/$identity.csr" \
    -subj "/CN=$identity" -addext basicConstraints=critical,CA:FALSE \
    -addext subjectAltName=DNS:localhost \
    -addext keyUsage=critical,digitalSignature \
    -addext "extendedKeyUsage=critical,$purpose"
  openssl x509 -req -in "$fixture_tmp/$identity.csr" -CA root.pem -CAkey root-key.pem \
    -set_serial "0x$(openssl rand -hex 8)" -days 3650 -copy_extensions copyall \
    -out "$identity.pem"
done
