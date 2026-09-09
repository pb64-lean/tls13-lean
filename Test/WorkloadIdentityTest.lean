import Tls.Client
import Tls.Server

open Tls

private def check (label : String) (ok : Bool) : IO Unit :=
  unless ok do throw (IO.userError label)

private def get [ToString ε] (result : Except ε α) : IO α :=
  match result with
  | .ok value => pure value
  | .error error => throw (IO.userError (toString error))

private def rejected (label : String) (result : Except ε α) : IO Unit :=
  match result with
  | .error _ => pure ()
  | .ok _ => throw (IO.userError (label ++ " unexpectedly succeeded"))

private def load (name : String) : IO (ByteArray × TLS13.X509.Certificate) := do
  let pem ← IO.FS.readFile s!"Test/Fixtures/Identity/{name}.pem"
  let certs ← get (TLS13.X509.PEM.decodeCertificates pem)
  let der := certs[0]!
  pure (der, ← get (TLS13.X509.Certificate.decode der))

private def key (name : String) : IO ByteArray := do
  let der ← IO.FS.readBinFile s!"Test/Fixtures/Identity/{name}-key.der"
  check "test key is an Ed25519 PKCS8 seed" (der.size == 48)
  pure (der.extract 16 48)

private def bytes (value : UInt8) : ByteArray := ByteArray.mk (Array.replicate 32 value)

def main : IO Unit := do
  let (rootDer, root) ← load "root"
  let (clientDer, clientCert) ← load "client"
  let (rotatedDer, _) ← load "rotated"
  let (serverDer, _) ← load "server"
  let clientKey ← key "client"
  let rotatedKey ← key "rotated"
  let serverKey ← key "server"
  let now := clientCert.tbsCertificate.validity.notBefore.unixSeconds + 3600
  let client ← get (Identity.create #[clientDer, rootDer] clientKey .clientAuth now true)
  let rotated ← get (Identity.create #[rotatedDer, rootDer] rotatedKey .clientAuth now true)
  rejected "wrong identity role" (Identity.create #[clientDer] clientKey .serverAuth now)
  rejected "mismatched private key" (Identity.create #[clientDer] rotatedKey .clientAuth now)
  rejected "expired local identity" (Identity.create #[clientDer] clientKey .clientAuth (now + 400000000))
  rejected "empty identity" (Identity.create #[] clientKey .clientAuth now)
  let trust : TLS13.X509.Chain.TrustStore := { anchors := #[root] }
  let _ ← get (TLS13.X509.Chain.validate now clientCert #[] trust 10 128 .clientAuth true)
  rejected "clientAuth certificate as server" (TLS13.X509.Chain.validate now clientCert #[] trust)
  let store ← IdentityStore.create client
  let old ← store.snapshot
  let generation ← store.rotate rotated
  let fresh ← store.snapshot
  check "rotation generation" (generation == 1 && fresh.generation == 1 && old.generation == 0)
  check "rotation retains coherent old snapshot" (old.identity.certificateChain[0]! == clientDer &&
    old.identity.signingKey == clientKey && fresh.identity.certificateChain[0]! == rotatedDer &&
    fresh.identity.signingKey == rotatedKey)
  let tasks ← (List.range 16).mapM fun worker => IO.asTask do
    let mut previous := 0
    for index in [:100] do
      let _ ← store.rotate (if (worker + index) % 2 == 0 then client else rotated)
      let snapshot ← store.snapshot
      check "concurrent snapshots never regress" (snapshot.generation ≥ previous)
      previous := snapshot.generation
      check "concurrent rotation never mixes key and certificate"
        ((snapshot.identity.certificateChain[0]! == clientDer && snapshot.identity.signingKey == clientKey) ||
         (snapshot.identity.certificateChain[0]! == rotatedDer && snapshot.identity.signingKey == rotatedKey))
  for task in tasks do
    match task.get with
    | .ok () => pure ()
    | .error error => throw error
  check "all concurrent rotations retained" ((← store.snapshot).generation == 1601)

  let config : Client.Config := {
    clientRandom := bytes 1
    x25519Private := bytes 2
    identity := some old.identity
    peerAuth := some { trustStore := trust, now, hostname := "localhost" } }
  let server : Server.Config := {
    serverRandom := bytes 3
    x25519Private := bytes 4
    certificateChain := #[serverDer, rootDer]
    signingKey := serverKey
    clientAuth := some { trustStore := trust, now } }
  let hello ← get (Client.start config)
  rejected "identity without server verification" (Client.start { config with peerAuth := none })
  let flight ← get (Server.feed (Server.start server) hello.wireBytes)
  let untrustedServer ← get (Client.start { config with
    peerAuth := some { trustStore := { anchors := #[] }, now, hostname := "localhost" } })
  rejected "untrusted server before client credential disclosure"
    (Client.feed untrustedServer.state flight.wireBytes)
  let wrongHostname ← get (Client.start { config with
    peerAuth := some { trustStore := trust, now, hostname := "elsewhere.invalid" } })
  rejected "wrong server hostname before credential disclosure"
    (Client.feed wrongHostname.state flight.wireBytes)
  let response ← get (Client.feed hello.state flight.wireBytes)
  check "client connected and cleared credentials" (response.state.connected && response.state.identity.isNone)
  let completed ← get (Server.feed flight.state response.wireBytes)
  check "mutually authenticated server" (completed.state.connected &&
    completed.state.peerCertificates.size == 2 &&
    completed.state.peerCertificates[0]!.encoded == clientDer)
  check "server clears handshake secret/transcript" (completed.state.clientHandshakeSecret?.isNone &&
    completed.state.transcript.isEmpty && completed.state.clientAuth.isNone)
  let request ← get (Client.sealApplication response.state "authenticated request".toUTF8)
  let delivered ← get (Server.feed completed.state request.wireBytes)
  check "application data after mTLS" (delivered.plaintext == "authenticated request".toUTF8)
  -- Transport chunk fragmentation cannot skip or duplicate authentication.
  let mut fragmented := flight.state
  for octet in response.wireBytes do
    fragmented := (← get (Server.feed fragmented (ByteArray.mk #[octet]))).state
  check "one-byte fragmented mTLS" (fragmented.connected && fragmented.peerCertificates.size == 2)

  let noIdentity ← get (Client.start { config with identity := none })
  let required ← get (Server.feed (Server.start server) noIdentity.wireBytes)
  let emptyCertificate ← get (Client.feed noIdentity.state required.wireBytes)
  rejected "required client certificate" (Server.feed required.state emptyCertificate.wireBytes)
  let optional ← get (Server.feed (Server.start { server with
    clientAuth := some { trustStore := trust, now, required := false } }) noIdentity.wireBytes)
  let noCertificate ← get (Client.feed noIdentity.state optional.wireBytes)
  let anonymous ← get (Server.feed optional.state noCertificate.wireBytes)
  check "optional client authentication" (anonymous.state.connected && anonymous.state.peerCertificates.isEmpty)

  let untrusted ← get (Server.feed (Server.start { server with
    clientAuth := some { trustStore := { anchors := #[] }, now } }) hello.wireBytes)
  let untrustedResponse ← get (Client.feed hello.state untrusted.wireBytes)
  rejected "untrusted client chain" (Server.feed untrusted.state untrustedResponse.wireBytes)
  let expired ← get (Server.feed (Server.start { server with
    clientAuth := some { trustStore := trust, now := now + 400000000 } }) hello.wireBytes)
  let expiredResponse ← get (Client.feed hello.state expired.wireBytes)
  rejected "expired peer chain" (Server.feed expired.state expiredResponse.wireBytes)

  let skipped ← get (Handshake.encodeFinished (required.state.expectedClientFinished?.getD .empty))
  let (_, skipWire) ← get (Record.«seal» (required.state.readKeys?.getD default) .handshake skipped.encoded)
  rejected "Finished without required client proof" (Server.feed required.state skipWire)
  let requestMessage ← get Handshake.encodeCertificateRequest
  let parsedRequest ← get (Handshake.parseCertificateRequest requestMessage)
  check "CertificateRequest codec" (parsedRequest.signatureAlgorithms == #[Handshake.ed25519])
  rejected "duplicate CertificateRequest" (Client.processHandshakeBuffer { hello.state with
    phase := .waitingCertificate, certificateRequested := true
    handshakeBuffered := requestMessage.encoded })
  let clientContent ← get (TLS13.X509.Signature.clientCertificateVerifyContent (bytes 5))
  let serverContent ← get (TLS13.X509.Signature.serverCertificateVerifyContent (bytes 5))
  check "role-separated CertificateVerify" (clientContent != serverContent)
  let badSignature := HaclStar.Signature.ed25519Sign clientKey serverContent
  check "reject reflected server signature" (!TLS13.X509.Signature.verifyClientCertificateVerify
    clientCert.tbsCertificate.subjectPublicKeyInfo (bytes 5) badSignature)
  IO.println "workload identity: purpose, trust, mTLS, fragmentation, rotation, and negative tests passed"
