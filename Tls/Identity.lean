module

public import HaclStar.Signature
public import TLS13.X509
public import Std.Sync.Mutex

public section

namespace Tls

/-- Validated Ed25519 certificate/key pair. No Repr instance; never log this
value. A snapshot is immutable and can be shared by in-flight handshakes. -/
structure Identity where
  private mk ::
  certificateChain : Array ByteArray
  signingKey : ByteArray
  purpose : TLS13.X509.Chain.Purpose

namespace Identity

/-- Validate local credentials before publishing them. Peer trust, revocation,
and application identity mapping remain separate policies. Bounds apply before
DER decoding. A proof-of-possession signature prevents publishing a mismatched
key and certificate (the challenge is public, not an authentication token). -/
def create (chain : Array ByteArray) (key : ByteArray)
    (purpose : TLS13.X509.Chain.Purpose) (now : Int)
    (requireExplicitPurpose : Bool := false) : Except String Identity := do
  unless !chain.isEmpty && chain.size ≤ 10 do
    throw "identity certificate chain must contain between 1 and 10 certificates"
  unless chain.foldl (fun total der => total + der.size) 0 ≤ 1048576 do
    throw "identity certificate chain exceeds 1 MiB"
  unless key.size == 32 do
    throw "identity requires a 32-byte Ed25519 private key"
  let parsed ← chain.mapM TLS13.X509.Certificate.decode
  let leaf := parsed[0]!
  for certificate in parsed do
    let validity := certificate.tbsCertificate.validity
    unless validity.notBefore.unixSeconds ≤ now && now ≤ validity.notAfter.unixSeconds do
      throw "identity certificate is not currently valid"
    unless TLS13.X509.Chain.permitsPurpose certificate purpose do
      throw "identity certificate purpose is not permitted"
  unless TLS13.X509.Chain.permitsPurpose leaf purpose requireExplicitPurpose do
    throw "identity requires an explicit certificate purpose"
  unless TLS13.X509.Chain.leafKeyUsagePermitsDigitalSignature leaf do
    throw "identity certificate does not permit digital signatures"
  let spki := leaf.tbsCertificate.subjectPublicKeyInfo
  unless TLS13.X509.Signature.certificateVerifySchemeCompatible .ed25519 spki do
    throw "identity certificate is not Ed25519"
  let challenge := "tls13-lean local identity key consistency check v1".toUTF8
  let signature := HaclStar.Signature.ed25519Sign key challenge
  unless TLS13.X509.Signature.verify .ed25519 spki.key challenge signature do
    throw "identity key does not match certificate"
  pure ⟨chain, key, purpose⟩

end Identity

/-- A coherent certificate/key generation, captured exactly once at handshake
creation. Rotation never mutates an existing connection's credentials. -/
structure IdentitySnapshot where
  generation : Nat
  identity : Identity

structure IdentityStore where
  private mk ::
  private current : Std.Mutex IdentitySnapshot

def IdentityStore.create (identity : Identity) : IO IdentityStore := do
  pure ⟨← Std.Mutex.new { generation := 0, identity }⟩

def IdentityStore.snapshot (store : IdentityStore) : IO IdentitySnapshot :=
  store.current.atomically get

/-- Call `Identity.create` before rotation; failures leave the store untouched.
The single atomic update publishes the pair and generation together. -/
def IdentityStore.rotate (store : IdentityStore) (identity : Identity) : IO Nat :=
  store.current.atomically <| modifyGet fun current =>
    let next := { generation := current.generation + 1, identity }
    (next.generation, next)

end Tls
