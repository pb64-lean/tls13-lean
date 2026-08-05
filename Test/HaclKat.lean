import HaclStar.Sha256
import HaclStar.Hmac
import HaclStar.Hkdf
import HaclStar.Curve25519
import HaclStar.P256
import HaclStar.Signature
import HaclStar.Aead
import HaclStar.Hex
import TLS13.KeySchedule

/-!
Known-answer tests for the HACL* bindings and the TLS 1.3 key schedule, against
published RFC vectors. This doubles as the end-to-end check that the FFI links.
-/

open HaclStar

/-- Hex-decode a test vector (panics on malformed input). -/
private def h (s : String) : ByteArray := Hex.decode! s

/-- Assert that `got` hex-encodes to `wantHex`. -/
private def check (label : String) (got : ByteArray) (wantHex : String) : IO Unit := do
  let g := Hex.encode got
  unless g == wantHex do
    throw (IO.userError s!"{label}:\n  got  {g}\n  want {wantHex}")

def main : IO Unit := do
  -- SHA-256 — FIPS 180-2, "abc"
  check "sha256" (sha256 "abc".toUTF8)
    "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad"

  -- SHA-384 and SHA-512 — FIPS 180-4, "abc"
  check "sha384" (sha384 "abc".toUTF8)
    ("cb00753f45a35e8bb5a03d699ac65007272c32ab0eded1631a8b605a43ff5bed" ++
     "8086072ba1e7cc2358baeca134c825a7")
  check "sha512" (sha512 "abc".toUTF8)
    ("ddaf35a193617abacc417349ae20413112e6fa4e89a97ea20a9eeee64b55d39a" ++
     "2192992a274fc1a836ba3c23a3feebbd454d4423643ce80e2a9ac94fa54ca49f")

  -- HMAC-SHA256 — RFC 4231 test case 2
  check "hmac-sha256" (hmacSha256 "Jefe".toUTF8 "what do ya want for nothing?".toUTF8)
    "5bdcc146bf60754e6a042426089575c75a003f089d2739839dec58b964ec3843"

  -- HKDF-SHA256 — RFC 5869 test case 1
  let prk := Hkdf.extractSha256 (h "000102030405060708090a0b0c")
    (h "0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b")
  check "hkdf-extract" prk
    "077709362c2e32df0ddc3f0dc47bba6390b6c73bb50f9c3122ec844ad7c2b3e5"
  check "hkdf-expand" (Hkdf.expandSha256 prk (h "f0f1f2f3f4f5f6f7f8f9") 42)
    "3cb25f25faacd57a90434f64d0362f2a2d2d0a90cf1a5a4c5db02d56ecc4c5bf34007208d5b887185865"
  -- The native boundary enforces RFC 5869's 255*HashLen expansion limit.
  unless (Hkdf.expandSha256 prk ByteArray.empty 8160).size == 8160 do
    throw (IO.userError "hkdf-expand: rejected the RFC 5869 maximum length")
  unless (Hkdf.expandSha256 prk ByteArray.empty 8161).isEmpty do
    throw (IO.userError "hkdf-expand: accepted a length above the RFC 5869 maximum")

  -- X25519 — RFC 7748 §6.1
  let alicePriv := h "77076d0a7318a57d3c16c17251b26645df4c2f87ebc0992ab177fba51db92c2a"
  let bobPub := h "de9edb7d7b7dc1b4d35b61c2ece435373f8343c85b78674dadfc7e146f882b4f"
  check "x25519-base" (X25519.base alicePriv)
    "8520f0098930a754748b7ddcb43ef75a0dbf3a0d26381af4eba4a98eaa9b4e6a"
  let ss ← match X25519.ecdh alicePriv bobPub with
    | some ss => pure ss
    | none => throw (IO.userError "x25519-ecdh: unexpected none")
  check "x25519-ecdh" ss
    "4a5d9d5ba4ce2de1728e3bf480350f25e07e21c947d19e3376f09b3c1e161742"
  -- Fixed-width guards reject malformed arrays before HACL can read 32 bytes.
  unless (X25519.base ByteArray.empty).isEmpty do
    throw (IO.userError "x25519-base: accepted a short private key")
  unless (X25519.base (alicePriv.push 0)).isEmpty do
    throw (IO.userError "x25519-base: accepted a long private key")
  unless (X25519.ecdh ByteArray.empty bobPub).isNone do
    throw (IO.userError "x25519-ecdh: accepted a short private key")
  unless (X25519.ecdh (alicePriv.push 0) bobPub).isNone do
    throw (IO.userError "x25519-ecdh: accepted a long private key")
  unless (X25519.ecdh alicePriv ByteArray.empty).isNone do
    throw (IO.userError "x25519-ecdh: accepted a short public key")
  unless (X25519.ecdh alicePriv (bobPub.push 0)).isNone do
    throw (IO.userError "x25519-ecdh: accepted a long public key")

  -- P-256 ECDH — RFC 5903 §8.1. Public keys in that RFC are raw x || y;
  -- TLS carries the same points in SEC1 uncompressed form (04 || x || y).
  let p256InitiatorPriv :=
    h "c88f01f510d9ac3f70a292daa2316de544e9aab8afe84049c62a9c57862d1433"
  let p256ResponderPriv :=
    h "c6ef9c5d78ae012a011164acb397ce2088685d8f06bf9be0b283ab46476bee53"
  let p256InitiatorPub :=
    h ("04" ++
      "dad0b65394221cf9b051e1feca5787d098dfe637fc90b9ef945d0c3772581180" ++
      "5271a0461cdb8252d61f1c456fa3e59ab1f45b33accf5f58389e0577b8990bb3")
  let p256ResponderPub :=
    h ("04" ++
      "d12dfb5289c8d4f81208b70270398c342296970a0bccb74c736fc7554494bf63" ++
      "56fbf3ca366cc23e8157854c13c58d6aac23f046ada30f8353e74f33039872ab")
  let derivedInitiatorPub ← match P256.publicKey p256InitiatorPriv with
    | some key => pure key
    | none => throw (IO.userError "p256-public: valid initiator scalar rejected")
  check "p256-public" derivedInitiatorPub (Hex.encode p256InitiatorPub)
  let derivedResponderPub ← match P256.publicKey p256ResponderPriv with
    | some key => pure key
    | none => throw (IO.userError "p256-public: valid responder scalar rejected")
  check "p256-public-responder" derivedResponderPub (Hex.encode p256ResponderPub)
  let p256SharedI ← match P256.ecdh p256InitiatorPriv p256ResponderPub with
    | some shared => pure shared
    | none => throw (IO.userError "p256-ecdh: valid responder point rejected")
  check "p256-ecdh-initiator" p256SharedI
    "d6840f6b42f6edafd13116e0e12565202fef8e9ece7dce03812464d04b9442de"
  let p256SharedR ← match P256.ecdh p256ResponderPriv p256InitiatorPub with
    | some shared => pure shared
    | none => throw (IO.userError "p256-ecdh: valid initiator point rejected")
  check "p256-ecdh-responder" p256SharedR (Hex.encode p256SharedI)
  -- Length/encoding checks must fail before the C API can read out of bounds.
  unless (P256.publicKey ByteArray.empty).isNone do
    throw (IO.userError "p256-public: accepted a short private key")
  unless (P256.ecdh ByteArray.empty p256ResponderPub).isNone do
    throw (IO.userError "p256-ecdh: accepted a short private key")
  unless (P256.ecdh p256InitiatorPriv ByteArray.empty).isNone do
    throw (IO.userError "p256-ecdh: accepted a short public key")
  let badPrefix := p256ResponderPub.set! 0 0x02
  unless (P256.ecdh p256InitiatorPriv badPrefix).isNone do
    throw (IO.userError "p256-ecdh: accepted a non-uncompressed point")
  let offCurve := ByteArray.mk ((#[0x04] ++ Array.replicate 64 0))
  unless (P256.ecdh p256InitiatorPriv offCurve).isNone do
    throw (IO.userError "p256-ecdh: accepted an off-curve point")
  unless (P256.publicKey (ByteArray.mk (Array.replicate 32 0))).isNone do
    throw (IO.userError "p256-public: accepted scalar zero")

  -- ChaCha20-Poly1305 — RFC 8439 §2.8.2
  let key := h "808182838485868788898a8b8c8d8e8f909192939495969798999a9b9c9d9e9f"
  let nonce := h "070000004041424344454647"
  let aad := h "50515253c0c1c2c3c4c5c6c7"
  let pt := h ("4c616469657320616e642047656e746c656d656e206f662074686520636c6173" ++
    "73206f66202739393a204966204920636f756c64206f6666657220796f75206f6e" ++
    "6c79206f6e652074697020666f7220746865206675747572652c2073756e736372" ++
    "65656e20776f756c642062652069742e")
  let sealed := ChaCha20Poly1305.encrypt key nonce aad pt
  check "chachapoly-seal" sealed
    ("d31a8d34648e60db7b86afbc53ef7ec2a4aded51296e08fea9e2b5a736ee62d63d" ++
     "bea45e8ca9671282fafb69da92728b1a71de0a9e060b2905d6a5b67ecd3b3692dd" ++
     "bd7f2d778b8c9803aee328091b58fab324e4fad675945585808b4831d7bc3ff4de" ++
     "f08e4b7a9de576d26586cec64b61161ae10b594f09e26a7e902ecbd0600691")
  -- decrypt round-trips to the plaintext
  match ChaCha20Poly1305.decrypt key nonce aad sealed with
  | some dec => check "chachapoly-open" dec (Hex.encode pt)
  | none => throw (IO.userError "chachapoly-open: unexpected auth failure")
  -- a single flipped byte must fail authentication
  let tampered := sealed.set! 0 (sealed.get! 0 ^^^ 1)
  match ChaCha20Poly1305.decrypt key nonce aad tampered with
  | some _ => throw (IO.userError "chachapoly: tampered ciphertext authenticated!")
  | none => pure ()
  -- Boundary misuse is rejected before HACL sees a short key or nonce. Encrypt
  -- preserves its historical ByteArray API with an empty sentinel; decrypt is
  -- already fallible and returns none.
  unless (ChaCha20Poly1305.encrypt ByteArray.empty nonce aad pt).isEmpty do
    throw (IO.userError "chachapoly-seal: accepted a short key")
  unless (ChaCha20Poly1305.encrypt (key.push 0) nonce aad pt).isEmpty do
    throw (IO.userError "chachapoly-seal: accepted a long key")
  unless (ChaCha20Poly1305.encrypt key ByteArray.empty aad pt).isEmpty do
    throw (IO.userError "chachapoly-seal: accepted a short nonce")
  unless (ChaCha20Poly1305.encrypt key (nonce.push 0) aad pt).isEmpty do
    throw (IO.userError "chachapoly-seal: accepted a long nonce")
  unless (ChaCha20Poly1305.decrypt ByteArray.empty nonce aad sealed).isNone do
    throw (IO.userError "chachapoly-open: accepted a short key")
  unless (ChaCha20Poly1305.decrypt (key.push 0) nonce aad sealed).isNone do
    throw (IO.userError "chachapoly-open: accepted a long key")
  unless (ChaCha20Poly1305.decrypt key ByteArray.empty aad sealed).isNone do
    throw (IO.userError "chachapoly-open: accepted a short nonce")
  unless (ChaCha20Poly1305.decrypt key (nonce.push 0) aad sealed).isNone do
    throw (IO.userError "chachapoly-open: accepted a long nonce")
  unless (ChaCha20Poly1305.encrypt key nonce aad ByteArray.empty).size == 16 do
    throw (IO.userError "chachapoly-seal: empty plaintext did not produce a tag")

  -- TLS 1.3 key schedule — RFC 8448 (no PSK, empty transcript).
  --
  -- These vectors are the *empirical* anchor of the key schedule; the
  -- structural one is the RFC 8446 §7.1 refinement in
  -- `TLS13.KeySchedule.Refinement` (labels, contexts, parents, lengths). The
  -- two are complementary: a proof cannot say the opaque HKDF bindings compute
  -- the right bytes, and a vector cannot say the derivation tree has the right
  -- shape. If they ever disagree, the vector wins and the specification is
  -- wrong.
  let early := TLS13.KeySchedule.earlySecret
  check "tls13-early-secret" early
    "33ad0a1c607ec03b09e6cd9893680ce210adf300aa1f2660e1b22e10f170f92a"
  let emptyHash := sha256 ByteArray.empty
  check "tls13-derived-secret"
    (TLS13.KeySchedule.deriveSecret early "derived" emptyHash)
    "6f2615a108c702c5678f54fc9dbab69716c076189c48250cebeac3576c3611ba"
  -- The HkdfLabel wire structure of that very `Derive-Secret`, hand-encoded
  -- from RFC 8446 §7.1: uint16 length 32, then `"tls13 derived"` (13 bytes) and
  -- an empty context, each with a one-byte length prefix. This cross-checks
  -- `TLS13.KeySchedule.hkdfLabel_bytes`, which proves the same layout.
  check "tls13-hkdf-label"
    (TLS13.KeySchedule.hkdfLabel 32 "derived".toUTF8 ByteArray.empty)
    "00200d746c733133206465726976656400"

  -- RFC 8448 §3's complete 1-RTT schedule checkpoints. Transcript hashes are
  -- the published values at ClientHello..ServerHello, ..server Finished, and
  -- ..client Finished respectively. This covers both extraction stages, both
  -- directions' handshake/application secrets, key/IV/Finished derivations,
  -- and the exporter/resumption branches rather than only the Early Secret.
  let sharedSecret :=
    h "8bd4054fb55b9d63fdfbacf9f04b9f0d35e6d63f537563efd46272900f89492d"
  let handshake := TLS13.KeySchedule.handshakeSecret early sharedSecret emptyHash
  check "tls13-handshake-secret" handshake
    "1dc826e93606aa6fdc0aadc12f741b01046aa6b99f691ed221a9f0ca043fbeac"

  let serverHelloHash :=
    h "860c06edc07858ee8e78f0e7428c58edd6b43f2ca3e6e95f02ed063cf0e1cad8"
  let clientHandshake :=
    TLS13.KeySchedule.deriveSecret handshake "c hs traffic" serverHelloHash
  let serverHandshake :=
    TLS13.KeySchedule.deriveSecret handshake "s hs traffic" serverHelloHash
  check "tls13-client-handshake-traffic-secret" clientHandshake
    "b3eddb126e067f35a780b3abf45e2d8f3b1a950738f52e9600746a0e27a55a21"
  check "tls13-server-handshake-traffic-secret" serverHandshake
    "b67b7d690cc16c4e75e54213cb2d37b4e9c912bcded9105d42befd59d391ad38"
  check "tls13-client-handshake-key"
    (TLS13.KeySchedule.expandLabel clientHandshake "key" ByteArray.empty 16)
    "dbfaa693d1762c5b666af5d950258d01"
  check "tls13-client-handshake-iv"
    (TLS13.KeySchedule.expandLabel clientHandshake "iv" ByteArray.empty 12)
    "5bd3c71b836e0b76bb73265f"
  check "tls13-client-finished-key"
    (TLS13.KeySchedule.expandLabel clientHandshake "finished" ByteArray.empty 32)
    "b80ad01015fb2f0bd65ff7d4da5d6bf83f84821d1f87fdc7d3c75b5a7b42d9c4"
  check "tls13-server-handshake-key"
    (TLS13.KeySchedule.expandLabel serverHandshake "key" ByteArray.empty 16)
    "3fce516009c21727d0f2e4e86ee403bc"
  check "tls13-server-handshake-iv"
    (TLS13.KeySchedule.expandLabel serverHandshake "iv" ByteArray.empty 12)
    "5d313eb2671276ee13000b30"
  check "tls13-server-finished-key"
    (TLS13.KeySchedule.expandLabel serverHandshake "finished" ByteArray.empty 32)
    "008d3b66f816ea559f96b537e885c31fc068bf492c652f01f288a1d8cdc19fc8"

  check "tls13-handshake-derived-secret"
    (TLS13.KeySchedule.deriveSecret handshake "derived" emptyHash)
    "43de77e0c77713859a944db9db2590b53190a65b3ee2e4f12dd7a0bb7ce254b4"
  let master := TLS13.KeySchedule.masterSecret handshake emptyHash
  check "tls13-master-secret" master
    "18df06843d13a08bf2a449844c5f8a478001bc4d4c627984d5a41da8d0402919"

  let serverFinishedHash :=
    h "9608102a0f1ccc6db6250b7b7e417b1a000eaada3daae4777a7686c9ff83df13"
  let clientApplication :=
    TLS13.KeySchedule.deriveSecret master "c ap traffic" serverFinishedHash
  let serverApplication :=
    TLS13.KeySchedule.deriveSecret master "s ap traffic" serverFinishedHash
  check "tls13-client-application-traffic-secret" clientApplication
    "9e40646ce79a7f9dc05af8889bce6552875afa0b06df0087f792ebb7c17504a5"
  check "tls13-server-application-traffic-secret" serverApplication
    "a11af9f05531f856ad47116b45a950328204b4f44bfb6b3a4b4f1f3fcb631643"
  check "tls13-exporter-master-secret"
    (TLS13.KeySchedule.deriveSecret master "exp master" serverFinishedHash)
    "fe22f881176eda18eb8f44529e6792c50c9a3f89452f68d8ae311b4309d3cf50"
  check "tls13-client-application-key"
    (TLS13.KeySchedule.expandLabel clientApplication "key" ByteArray.empty 16)
    "17422dda596ed5d9acd890e3c63f5051"
  check "tls13-client-application-iv"
    (TLS13.KeySchedule.expandLabel clientApplication "iv" ByteArray.empty 12)
    "5b78923dee08579033e523d9"
  check "tls13-server-application-key"
    (TLS13.KeySchedule.expandLabel serverApplication "key" ByteArray.empty 16)
    "9f02283b6c9c07efc26bb9f2ac92e356"
  check "tls13-server-application-iv"
    (TLS13.KeySchedule.expandLabel serverApplication "iv" ByteArray.empty 12)
    "cf782b88dd83549aadf1e984"

  let clientFinishedHash :=
    h "209145a96ee8e2a122ff810047cc952684658d6049e86429426db87c54ad143d"
  let resumptionMaster :=
    TLS13.KeySchedule.deriveSecret master "res master" clientFinishedHash
  check "tls13-resumption-master-secret" resumptionMaster
    "7df235f2031d2a051287d02b0241b0bfdaf86cc856231f2d5aba46c434ec196c"
  check "tls13-resumption-secret"
    (TLS13.KeySchedule.expandLabel resumptionMaster "resumption" (h "0000") 32)
    "4ecd0eb6ec3b4d87f5d6028f922ca4c5851a277fd41311c9e62d2c9492e1c4f3"

  -- Ed25519 signing — RFC 8032 §7.1, TEST 1 (empty message).
  let edSecret := h "9d61b19deffd5a60ba844af492ec2cc44449c5697b326919703bac031cae7f60"
  let edPublic := h "d75a980182b10ab7d54bfed3c964073a0ee172f3daa62325af021a68f707511a"
  let edSig := Signature.ed25519Sign edSecret ByteArray.empty
  check "ed25519-sign"
    edSig
    ("e5564300c360ac729086e2cc806e828a84877f1eb8e5d974d873e0652249015" ++
     "55fb8821590a33bacc61e39701cf9b46bd25bf5f0595bbe24655141438e7a100b")
  -- The freshly produced signature must verify under the matching public key.
  unless Signature.ed25519 edPublic ByteArray.empty edSig do
    throw (IO.userError "ed25519-sign: produced signature failed to verify")
  -- Sign→verify roundtrip over a non-empty message, with the public key derived
  -- from the same secret via Ed25519's secret_to_public (not the RFC vector's).
  let edMsg := "TLS 1.3 CertificateVerify".toUTF8
  let edSig2 := Signature.ed25519Sign edSecret edMsg
  unless edSig2.size == 64 do
    throw (IO.userError s!"ed25519-sign: expected 64-byte signature, got {edSig2.size}")
  unless Signature.ed25519 edPublic edMsg edSig2 do
    throw (IO.userError "ed25519-sign: roundtrip signature failed to verify")
  -- A tampered message must not verify against the honest signature.
  unless (Signature.ed25519 edPublic ("tampered".toUTF8) edSig2) == false do
    throw (IO.userError "ed25519-sign: signature verified against wrong message")
  -- Misuse: a non-32-byte private key yields the empty-ByteArray sentinel.
  unless (Signature.ed25519Sign ByteArray.empty edMsg).size == 0 do
    throw (IO.userError "ed25519-sign: accepted a short private key")

  -- ECDSA-P256 with SHA-256 sign→verify roundtrip — RFC 4754 §8.1 key/nonce.
  let ecPriv := h "dc51d3866a15bacde33d96f992fca99da7e6ef0934e7097559c27f1614c88a7f"
  let ecNonce := h "9e56f509196784d963d1c0a401510ee7ada3dcc5dee04b154bf61af1d5a6dece"
  let ecMsg := "TLS 1.3 CertificateVerify".toUTF8
  let ecSig ← match Signature.ecdsaP256Sha256Sign ecPriv ecMsg ecNonce with
    | some sig => pure sig
    | none => throw (IO.userError "ecdsa-p256-sign: valid scalar/nonce rejected")
  unless ecSig.size == 64 do
    throw (IO.userError s!"ecdsa-p256-sign: expected 64-byte r||s, got {ecSig.size}")
  -- Verify needs a 65-byte SEC1 public key and r, s as two 32-byte halves.
  let ecPub ← match P256.publicKey ecPriv with
    | some key => pure key
    | none => throw (IO.userError "ecdsa-p256-sign: could not derive public key")
  let ecR := ecSig.extract 0 32
  let ecS := ecSig.extract 32 64
  unless Signature.ecdsaP256Sha256 ecPub ecMsg ecR ecS do
    throw (IO.userError "ecdsa-p256-sign: produced signature failed to verify")
  -- A tampered message must not verify against the honest signature.
  unless (Signature.ecdsaP256Sha256 ecPub ("tampered".toUTF8) ecR ecS) == false do
    throw (IO.userError "ecdsa-p256-sign: signature verified against wrong message")
  -- Misuse: wrong-length private key or nonce rejects with `none`.
  unless (Signature.ecdsaP256Sha256Sign ByteArray.empty ecMsg ecNonce).isNone do
    throw (IO.userError "ecdsa-p256-sign: accepted a short private key")
  unless (Signature.ecdsaP256Sha256Sign ecPriv ecMsg ByteArray.empty).isNone do
    throw (IO.userError "ecdsa-p256-sign: accepted a short nonce")

  IO.println "all HACL* KAT assertions passed"
