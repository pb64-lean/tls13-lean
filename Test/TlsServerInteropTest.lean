import Tls.Client
import Tls.Server

/-!
Pure end-to-end regression for the TLS 1.3 client and server machines. This
drives a complete authenticated handshake with no sockets, checks the
compatibility-CCS/server-flight shape, and exchanges protected application
data in both directions.
-/

open Tls

private def expect (label : String) (condition : Bool) : IO Unit := do
  unless condition do
    throw (IO.userError s!"{label}: assertion failed")

private def expectEq [BEq α] (label : String) (actual expected : α) : IO Unit :=
  expect label (actual == expected)

private def clientResult (result : Except Client.Error α) : IO α :=
  match result with
  | .ok value => pure value
  | .error error => throw (IO.userError s!"unexpected client TLS error: {error}")

private def serverResult (result : Except Server.Error α) : IO α :=
  match result with
  | .ok value => pure value
  | .error error => throw (IO.userError s!"unexpected server TLS error: {error}")

private def expectInterleaved (label : String) (result : Except Server.Error α) :
    IO Unit :=
  match result with
  | .error .interleavedHandshake => pure ()
  | .error error => throw (IO.userError s!"{label}: wrong error: {error}")
  | .ok _ => throw (IO.userError s!"{label}: unexpectedly succeeded")

private def expectUnexpectedRecord (label : String)
    (result : Except Server.Error α) : IO Unit :=
  match result with
  | .error (.unexpectedRecord _ _) => pure ()
  | .error error => throw (IO.userError s!"{label}: wrong error: {error}")
  | .ok _ => throw (IO.userError s!"{label}: unexpectedly succeeded")

private def recordResult (result : Except Record.Error α) : IO α :=
  match result with
  | .ok value => pure value
  | .error error => throw (IO.userError s!"unexpected TLS record error: {error}")

private def handshakeResult (result : Except String α) : IO α :=
  match result with
  | .ok value => pure value
  | .error error => throw (IO.userError s!"unexpected TLS handshake error: {error}")

private def x509Result (result : Except String α) : IO α :=
  match result with
  | .ok value => pure value
  | .error error => throw (IO.userError s!"unexpected X.509 fixture error: {error}")

private def fill (count : Nat) (octet : UInt8) : ByteArray :=
  ByteArray.mk (Array.replicate count octet)

private def hexNibble? (char : Char) : Option UInt8 :=
  if '0' ≤ char ∧ char ≤ '9' then
    some (UInt8.ofNat (char.toNat - '0'.toNat))
  else if 'a' ≤ char ∧ char ≤ 'f' then
    some (UInt8.ofNat (char.toNat - 'a'.toNat + 10))
  else if 'A' ≤ char ∧ char ≤ 'F' then
    some (UInt8.ofNat (char.toNat - 'A'.toNat + 10))
  else
    none

private def decodeHex : List Char → ByteArray → Option ByteArray
  | [], output => some output
  | [_], _ => none
  | high :: low :: rest, output =>
      match hexNibble? high, hexNibble? low with
      | some high, some low =>
          decodeHex rest (output.push (high * 16 + low))
      | _, _ => none

private def hex (encoded : String) : ByteArray :=
  match decodeHex encoded.toList ByteArray.empty with
  | some bytes => bytes
  | none => panic! "invalid embedded test hex"

def main : IO Unit := do
  let pem ← IO.FS.readFile "Test/Fixtures/Tls/server_cert.pem"
  let certificates ← x509Result (TLS13.X509.PEM.decodeCertificates pem)
  let certificateDer ← match certificates[0]? with
    | some der => pure der
    | none => throw (IO.userError "TLS fixture PEM contained no certificate")
  let signingKey :=
    hex "471761974da12938977eca1b40cc0ea3d6e9c52897648a1661681e88fd31f4be"
  expectEq "Ed25519 signing-key size" signingKey.size 32

  let clientConfig : Client.Config := {
    clientRandom := fill 32 0x11
    x25519Private := fill 32 0x22
    legacySessionId := fill 32 0x55
    serverName := some "localhost"
    alpnProtocols := #["h2", "http/1.1"]
  }
  let serverConfig : Server.Config := {
    serverRandom := fill 32 0x33
    x25519Private := fill 32 0x44
    certificateChain := #[certificateDer]
    signingKey
    alpnProtocols := ["h2"]
  }

  -- The client validates the selection against what this connection offered,
  -- rather than assuming the server picked its first/local default group.
  let p256ClientPrivate :=
    hex "c88f01f510d9ac3f70a292daa2316de544e9aab8afe84049c62a9c57862d1433"
  let p256ServerPrivate :=
    hex "c6ef9c5d78ae012a011164acb397ce2088685d8f06bf9be0b283ab46476bee53"
  let some p256ServerPublic := HaclStar.P256.publicKey p256ServerPrivate
    | throw (IO.userError "P-256 interop fixture private key was rejected")
  let p256Start ← clientResult (Client.start {
    clientConfig with p256Private := some p256ClientPrivate
  })
  let p256ServerHello ← handshakeResult
    (Handshake.encodeServerHello (fill 32 0x34) clientConfig.legacySessionId
      .secp256r1 p256ServerPublic)
  let p256ServerHelloWire ← recordResult
    (Record.encodePlaintext .handshake p256ServerHello.encoded)
  let p256Accepted ← clientResult
    (Client.feed p256Start.state p256ServerHelloWire)
  expectEq "client accepts server-selected offered P-256 group"
    p256Accepted.state.phase .waitingEncryptedExtensions

  let clientHello ← clientResult (Client.start clientConfig)
  let serverFlight ← serverResult
    (Server.feed (Server.start serverConfig) clientHello.wireBytes)
  expectEq "server phase after its flight" serverFlight.state.phase
    .waitingClientFinished
  expectEq "selected cipher suite" serverFlight.state.cipherSuiteSelected
    (some Handshake.tlsChaCha20Poly1305Sha256)
  expectEq "selected key-exchange group" serverFlight.state.groupSelected
    (some .x25519)
  expectEq "server-side SNI" serverFlight.state.peerServerName
    (some "localhost")
  expectEq "server-side ALPN" serverFlight.state.alpnSelected (some "h2")

  -- A nonempty legacy_session_id requests TLS 1.3 middlebox compatibility:
  -- plaintext ServerHello, one dummy CCS, then protected server handshake.
  let (_, serverRecords) ← recordResult
    (({} : Record.Decoder).feed serverFlight.wireBytes)
  expectEq "server-flight record count" serverRecords.size 3
  expectEq "first server record" serverRecords[0]!.contentType .handshake
  expectEq "middle compatibility record" serverRecords[1]!.contentType
    .changeCipherSpec
  expectEq "dummy CCS payload" serverRecords[1]!.fragment (ByteArray.empty.push 1)
  expectEq "protected server flight record" serverRecords[2]!.contentType
    .applicationData
  let serverHelloMessage ← handshakeResult
    (Handshake.decode serverRecords[0]!.fragment)
  let serverHello ← handshakeResult
    (Handshake.parseServerHello serverHelloMessage)
  expectEq "ServerHello session-id echo" serverHello.legacySessionIdEcho
    clientConfig.legacySessionId
  expectEq "ServerHello cipher" serverHello.cipherSuite
    Handshake.tlsChaCha20Poly1305Sha256
  expectEq "ServerHello group" serverHello.selectedGroup .x25519

  let clientFinished ← clientResult
    (Client.feed clientHello.state serverFlight.wireBytes)
  expect "client connected after server flight" clientFinished.state.connected
  expectEq "client-side ALPN" clientFinished.state.alpnSelected (some "h2")

  -- Finished changes the read-key epoch and therefore must end its record.
  let some clientHandshakeKeys := serverFlight.state.readKeys?
    | throw (IO.userError "server retained no client handshake keys")
  let some expectedClientFinished := serverFlight.state.expectedClientFinished?
    | throw (IO.userError "server retained no expected client Finished")
  let forgedFinished ← handshakeResult
    (Handshake.encodeFinished expectedClientFinished)
  let trailingKeyUpdate ← handshakeResult
    (Handshake.encodeKeyUpdate .updateNotRequested)
  let (fragmentedFinishedKeys, firstFinishedFragment) ← recordResult
    (Record.«seal» clientHandshakeKeys .handshake
      (forgedFinished.encoded.extract 0 9))
  let bufferedFinished ← serverResult
    (Server.feed serverFlight.state firstFinishedFragment)
  let compatibilityCcs ← recordResult
    (Record.encodePlaintext .changeCipherSpec (ByteArray.empty.push 1))
  expectInterleaved "server accepted CCS inside fragmented client Finished"
    (Server.feed bufferedFinished.state compatibilityCcs)
  let (_, emptyProtectedHandshake) ← recordResult
    (Record.«seal» fragmentedFinishedKeys .handshake ByteArray.empty)
  expectUnexpectedRecord "server accepted an empty protected Handshake record"
    (Server.feed bufferedFinished.state emptyProtectedHandshake)
  let (_, badFinishedWire) ← recordResult
    (Record.«seal» clientHandshakeKeys .handshake
      (forgedFinished.encoded ++ trailingKeyUpdate.encoded))
  expectInterleaved "server accepted bytes after client Finished in one record"
    (Server.feed serverFlight.state badFinishedWire)

  let serverDone ← serverResult
    (Server.feed serverFlight.state clientFinished.wireBytes)
  expect "server connected after client Finished" serverDone.state.connected

  let request := "mainstream interop request".toUTF8
  let sealedRequest ← clientResult
    (Client.sealApplication clientFinished.state request)
  let receivedRequest ← serverResult
    (Server.feed serverDone.state sealedRequest.wireBytes)
  expectEq "client-to-server application data" receivedRequest.plaintext request

  let response := "mainstream interop response".toUTF8
  let sealedResponse ← serverResult
    (Server.sealApplication receivedRequest.state response)
  let receivedResponse ← clientResult
    (Client.feed sealedRequest.state sealedResponse.wireBytes)
  expectEq "server-to-client application data" receivedResponse.plaintext response

  -- A certificate flight larger than 2^14 must be split across protected
  -- records while remaining one continuous handshake byte stream.
  let largeChainConfig : Server.Config := {
    serverConfig with certificateChain := Array.replicate 50 certificateDer
  }
  let largeClientStart ← clientResult (Client.start clientConfig)
  let largeServerFlight ← serverResult
    (Server.feed (Server.start largeChainConfig) largeClientStart.wireBytes)
  let (_, largeFlightRecords) ← recordResult
    (({} : Record.Decoder).feed largeServerFlight.wireBytes)
  let protectedRecords :=
    largeFlightRecords.filter (fun record => record.contentType == .applicationData)
  expect "large certificate flight was not split across protected records"
    (protectedRecords.size > 1)
  let largeClientDone ← clientResult
    (Client.feed largeClientStart.state largeServerFlight.wireBytes)
  expect "client did not reassemble the fragmented certificate flight"
    largeClientDone.state.connected
  expectEq "client did not retain every certificate entry"
    largeClientDone.state.peerCertificates.size 50
  let largeServerDone ← serverResult
    (Server.feed largeServerFlight.state largeClientDone.wireBytes)
  expect "server did not finish after a fragmented certificate flight"
    largeServerDone.state.connected

  IO.println "TLS client/server interop regression passed"
