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

private def expectClientInterleaved (label : String)
    (result : Except Client.Error α) : IO Unit :=
  match result with
  | .error .interleavedHandshake => pure ()
  | .error error => throw (IO.userError s!"{label}: wrong error: {error}")
  | .ok _ => throw (IO.userError s!"{label}: unexpectedly succeeded")

private def expectClientIllegalParameter (label : String)
    (result : Except Client.Error α) : IO Unit :=
  match result with
  | .error (.illegalParameter _) => pure ()
  | .error error => throw (IO.userError s!"{label}: wrong error: {error}")
  | .ok _ => throw (IO.userError s!"{label}: unexpectedly succeeded")

private def expectServerIllegalParameter (label : String)
    (result : Except Server.Error α) : IO Unit :=
  match result with
  | .error (.illegalParameter _) => pure ()
  | .error error => throw (IO.userError s!"{label}: wrong error: {error}")
  | .ok _ => throw (IO.userError s!"{label}: unexpectedly succeeded")

private def expectUnexpectedRecord (label : String)
    (result : Except Server.Error α) : IO Unit :=
  match result with
  | .error (.unexpectedRecord _ _) => pure ()
  | .error error => throw (IO.userError s!"{label}: wrong error: {error}")
  | .ok _ => throw (IO.userError s!"{label}: unexpectedly succeeded")

private def expectClientUnexpectedRecord (label : String)
    (result : Except Client.Error α) : IO Unit :=
  match result with
  | .error (.unexpectedRecord _ _) => pure ()
  | .error error => throw (IO.userError s!"{label}: wrong error: {error}")
  | .ok _ => throw (IO.userError s!"{label}: unexpectedly succeeded")

private def expectClientConnectionClosed (label : String)
    (result : Except Client.Error α) : IO Unit :=
  match result with
  | .error .connectionClosed => pure ()
  | .error error => throw (IO.userError s!"{label}: wrong error: {error}")
  | .ok _ => throw (IO.userError s!"{label}: unexpectedly succeeded")

private def expectServerConnectionClosed (label : String)
    (result : Except Server.Error α) : IO Unit :=
  match result with
  | .error .connectionClosed => pure ()
  | .error error => throw (IO.userError s!"{label}: wrong error: {error}")
  | .ok _ => throw (IO.userError s!"{label}: unexpectedly succeeded")

private def expectServerInvalidConfig (label expected : String)
    (result : Except Server.Error α) : IO Unit :=
  match result with
  | .error (.invalidConfig actual) => expectEq label actual expected
  | .error error => throw (IO.userError s!"{label}: wrong error: {error}")
  | .ok _ => throw (IO.userError s!"{label}: unexpectedly succeeded")

private def expectClientInvalidAlertLength (label : String) (length : Nat)
    (description : UInt8) (result : Except Client.Error α) : IO Unit :=
  match result with
  | .error (.invalidAlertLength actual) => do
      expectEq (label ++ " length") actual length
      expectEq (label ++ " fatal alert")
        (Client.Error.fatalAlertDescription? (.invalidAlertLength actual))
        (some description)
  | .error error => throw (IO.userError s!"{label}: wrong error: {error}")
  | .ok _ => throw (IO.userError s!"{label}: unexpectedly succeeded")

private def expectServerInvalidAlertLength (label : String) (length : Nat)
    (description : UInt8) (result : Except Server.Error α) : IO Unit :=
  match result with
  | .error (.invalidAlertLength actual) => do
      expectEq (label ++ " length") actual length
      expectEq (label ++ " fatal alert")
        (Server.Error.fatalAlertDescription? (.invalidAlertLength actual))
        (some description)
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

/-- Seal a KeyUpdate under the current sending epoch, then move the synthetic
peer to the next epoch exactly as a conforming sender does. -/
private def sealKeyUpdate (keys : Record.TrafficKeys)
    (request : Handshake.KeyUpdateRequest) :
    IO (Record.TrafficKeys × ByteArray) := do
  let message ← handshakeResult (Handshake.encodeKeyUpdate request)
  let (advanced, wire) ← recordResult
    (Record.«seal» keys .handshake message.encoded)
  let updated ← recordResult advanced.update
  pure (updated, wire)

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
  let p256SessionId := fill 32 0x56
  let some p256ServerPublic := HaclStar.P256.publicKey p256ServerPrivate
    | throw (IO.userError "P-256 interop fixture private key was rejected")
  let p256Start ← clientResult (Client.start {
    clientConfig with
    clientRandom := fill 32 0x12
    x25519Private := fill 32 0x23
    legacySessionId := p256SessionId
    p256Private := some p256ClientPrivate
  })
  let p256ServerHello ← handshakeResult
    (Handshake.encodeServerHello (fill 32 0x34) p256SessionId
      .secp256r1 p256ServerPublic)
  let p256ServerHelloWire ← recordResult
    (Record.encodePlaintext .handshake p256ServerHello.encoded)
  let p256Accepted ← clientResult
    (Client.feed p256Start.state p256ServerHelloWire)
  expectEq "client accepts server-selected offered P-256 group"
    p256Accepted.state.phase .waitingEncryptedExtensions

  let clientHello ← clientResult (Client.start clientConfig)
  -- A configured leaf whose present KeyUsage omits digitalSignature cannot
  -- justify the Ed25519 CertificateVerify operation, even if the private-key
  -- fixture itself has the right shape.
  let noDigitalSignaturePem ←
    IO.FS.readFile "Test/Fixtures/Chain/valid-root.pem"
  let noDigitalSignatureCertificates ← x509Result
    (TLS13.X509.PEM.decodeCertificates noDigitalSignaturePem)
  let noDigitalSignatureDer ← match noDigitalSignatureCertificates[0]? with
    | some der => pure der
    | none => throw (IO.userError
        "KeyUsage fixture PEM contained no certificate")
  let noDigitalSignatureServerConfig : Server.Config := {
    serverConfig with
    serverRandom := fill 32 0x36
    x25519Private := fill 32 0x46
    certificateChain := #[noDigitalSignatureDer]
  }
  expectServerInvalidConfig
    "server accepted a leaf whose KeyUsage omits digitalSignature"
    "leaf certificate KeyUsage does not permit TLS digital signatures"
    (Server.feed (Server.start noDigitalSignatureServerConfig)
      clientHello.wireBytes)
  let rsaLeafPem ← IO.FS.readFile "Test/Fixtures/Chain/valid-leaf.pem"
  let rsaLeafCertificates ← x509Result
    (TLS13.X509.PEM.decodeCertificates rsaLeafPem)
  let rsaLeafDer ← match rsaLeafCertificates[0]? with
    | some der => pure der
    | none => throw (IO.userError "RSA leaf fixture PEM contained no certificate")
  let incompatibleLeafServerConfig : Server.Config := {
    serverConfig with
    serverRandom := fill 32 0x37
    x25519Private := fill 32 0x47
    certificateChain := #[rsaLeafDer]
  }
  expectServerInvalidConfig
    "server accepted an RSA leaf for Ed25519 CertificateVerify"
    "leaf certificate public key is not compatible with Ed25519 CertificateVerify"
    (Server.feed (Server.start incompatibleLeafServerConfig)
      clientHello.wireBytes)
  let emptyPlaintextHandshake ← recordResult
    (Record.encodePlaintext .handshake ByteArray.empty)
  expectClientUnexpectedRecord
    "client accepted an empty plaintext Handshake record"
    (Client.feed clientHello.state emptyPlaintextHandshake)
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

  -- KeyUpdate is encrypted under the old epoch and changes keys only at the
  -- record boundary. Two successive records protected under successive keys
  -- are accepted; two KeyUpdates coalesced into one old-key record are not.
  let keyUpdateNotRequested ← handshakeResult
    (Handshake.encodeKeyUpdate .updateNotRequested)
  let some clientUpdateKeys := sealedRequest.state.writeKeys?
    | throw (IO.userError "client retained no application write keys")
  let (clientUpdateKeys1, clientUpdateWire1) ←
    sealKeyUpdate clientUpdateKeys .updateNotRequested
  let (_, clientUpdateWire2) ←
    sealKeyUpdate clientUpdateKeys1 .updateNotRequested
  let serverAfterTwoUpdates ← serverResult
    (Server.feed receivedRequest.state (clientUpdateWire1 ++ clientUpdateWire2))
  expect "unrequested client KeyUpdates generated a server response"
    serverAfterTwoUpdates.wireBytes.isEmpty
  let (_, coalescedClientUpdates) ← recordResult
    (Record.«seal» clientUpdateKeys .handshake
      (keyUpdateNotRequested.encoded ++ keyUpdateNotRequested.encoded))
  expectInterleaved "server accepted two KeyUpdates in one old-epoch record"
    (Server.feed receivedRequest.state coalescedClientUpdates)

  let some serverUpdateKeys := sealedResponse.state.writeKeys?
    | throw (IO.userError "server retained no application write keys")
  let (_, emptyServerHandshakeWire) ← recordResult
    (Record.«seal» serverUpdateKeys .handshake ByteArray.empty)
  expectClientUnexpectedRecord
    "client accepted an empty protected Handshake record"
    (Client.feed receivedResponse.state emptyServerHandshakeWire)
  let (serverUpdateKeys1, serverUpdateWire1) ←
    sealKeyUpdate serverUpdateKeys .updateNotRequested
  let (_, serverUpdateWire2) ←
    sealKeyUpdate serverUpdateKeys1 .updateNotRequested
  let clientAfterTwoUpdates ← clientResult
    (Client.feed receivedResponse.state (serverUpdateWire1 ++ serverUpdateWire2))
  expect "unrequested server KeyUpdates generated a client response"
    clientAfterTwoUpdates.wireBytes.isEmpty
  let (_, coalescedServerUpdates) ← recordResult
    (Record.«seal» serverUpdateKeys .handshake
      (keyUpdateNotRequested.encoded ++ keyUpdateNotRequested.encoded))
  expectClientInterleaved
    "client accepted two KeyUpdates in one old-epoch record"
    (Client.feed receivedResponse.state coalescedServerUpdates)

  -- The request enum is semantic: a one-byte value other than 0 or 1 is an
  -- illegal_parameter, not a framing/decode error.
  let invalidKeyUpdate ← handshakeResult
    (Handshake.frame Handshake.keyUpdateType (ByteArray.empty.push 2))
  let (_, invalidClientUpdateWire) ← recordResult
    (Record.«seal» clientUpdateKeys .handshake invalidKeyUpdate.encoded)
  expectServerIllegalParameter "server misclassified invalid KeyUpdate enum"
    (Server.feed receivedRequest.state invalidClientUpdateWire)
  expectEq "server invalid-KeyUpdate fatal alert mapping"
    (Server.Error.fatalAlertDescription? (.illegalParameter "invalid KeyUpdate"))
    (some 47)
  let (_, invalidServerUpdateWire) ← recordResult
    (Record.«seal» serverUpdateKeys .handshake invalidKeyUpdate.encoded)
  expectClientIllegalParameter "client misclassified invalid KeyUpdate enum"
    (Client.feed receivedResponse.state invalidServerUpdateWire)
  expectEq "client invalid-KeyUpdate fatal alert mapping"
    (Client.Error.fatalAlertDescription? (.illegalParameter "invalid KeyUpdate"))
    (some 47)

  -- Alert syntax errors use unexpected_message for an empty alert and
  -- decode_error for every other non-two-byte payload. Exercise both roles
  -- through protected records, not only through the error mapper.
  let (_, emptyClientAlertWire) ← recordResult
    (Record.«seal» clientUpdateKeys .alert ByteArray.empty)
  expectServerInvalidAlertLength "server empty-alert classification" 0 10
    (Server.feed receivedRequest.state emptyClientAlertWire)
  let (_, shortClientAlertWire) ← recordResult
    (Record.«seal» clientUpdateKeys .alert (ByteArray.empty.push 1))
  expectServerInvalidAlertLength "server short-alert classification" 1 50
    (Server.feed receivedRequest.state shortClientAlertWire)
  let (_, emptyServerAlertWire) ← recordResult
    (Record.«seal» serverUpdateKeys .alert ByteArray.empty)
  expectClientInvalidAlertLength "client empty-alert classification" 0 10
    (Client.feed receivedResponse.state emptyServerAlertWire)
  let (_, shortServerAlertWire) ← recordResult
    (Record.«seal» serverUpdateKeys .alert (ByteArray.empty.push 1))
  expectClientInvalidAlertLength "client short-alert classification" 1 50
    (Client.feed receivedResponse.state shortServerAlertWire)
  expectEq "client trailing-Finished fatal alert mapping"
    (Client.Error.fatalAlertDescription? .trailingHandshakeAfterFinished)
    (some 10)

  -- RFC 9846 caps the sending epoch at 2^48-1. At max-1, a requested
  -- response is emitted and reaches max; at max, the response is suppressed
  -- while the peer's read epoch still advances.
  let (_, clientRequestedUpdateWire) ←
    sealKeyUpdate clientUpdateKeys .updateRequested
  let serverBelowCap := {
    receivedRequest.state with
    sendingKeyUpdates := Server.maxSendingKeyUpdates - 1
  }
  let serverReachedCap ← serverResult
    (Server.feed serverBelowCap clientRequestedUpdateWire)
  expect "server suppressed a permitted final KeyUpdate response"
    (!serverReachedCap.wireBytes.isEmpty)
  expectEq "server did not reach the sending-KeyUpdate cap"
    serverReachedCap.state.sendingKeyUpdates Server.maxSendingKeyUpdates
  let serverAtCap := {
    receivedRequest.state with
    sendingKeyUpdates := Server.maxSendingKeyUpdates
  }
  let some serverReadBeforeCap := serverAtCap.readKeys?
    | throw (IO.userError "server retained no application read keys")
  let expectedServerReadAfterCap ← recordResult serverReadBeforeCap.update
  let serverSuppressed ← serverResult
    (Server.feed serverAtCap clientRequestedUpdateWire)
  expect "server exceeded the sending-KeyUpdate cap"
    serverSuppressed.wireBytes.isEmpty
  expectEq "server changed its write keys at the sending cap"
    serverSuppressed.state.writeKeys? serverAtCap.writeKeys?
  expectEq "server changed its sending count at the cap"
    serverSuppressed.state.sendingKeyUpdates Server.maxSendingKeyUpdates
  expectEq "server failed to advance read keys at its sending cap"
    serverSuppressed.state.readKeys? (some expectedServerReadAfterCap)

  let (_, serverRequestedUpdateWire) ←
    sealKeyUpdate serverUpdateKeys .updateRequested
  let clientBelowCap := {
    receivedResponse.state with
    sendingKeyUpdates := Client.maxSendingKeyUpdates - 1
  }
  let clientReachedCap ← clientResult
    (Client.feed clientBelowCap serverRequestedUpdateWire)
  expect "client suppressed a permitted final KeyUpdate response"
    (!clientReachedCap.wireBytes.isEmpty)
  expectEq "client did not reach the sending-KeyUpdate cap"
    clientReachedCap.state.sendingKeyUpdates Client.maxSendingKeyUpdates
  let clientAtCap := {
    receivedResponse.state with
    sendingKeyUpdates := Client.maxSendingKeyUpdates
  }
  let some clientReadBeforeCap := clientAtCap.readKeys?
    | throw (IO.userError "client retained no application read keys")
  let expectedClientReadAfterCap ← recordResult clientReadBeforeCap.update
  let clientSuppressed ← clientResult
    (Client.feed clientAtCap serverRequestedUpdateWire)
  expect "client exceeded the sending-KeyUpdate cap"
    clientSuppressed.wireBytes.isEmpty
  expectEq "client changed its write keys at the sending cap"
    clientSuppressed.state.writeKeys? clientAtCap.writeKeys?
  expectEq "client changed its sending count at the cap"
    clientSuppressed.state.sendingKeyUpdates Client.maxSendingKeyUpdates
  expectEq "client failed to advance read keys at its sending cap"
    clientSuppressed.state.readKeys? (some expectedClientReadAfterCap)

  -- A crossing update_requested is still consumed in the read direction
  -- after local close_notify, but the closed write direction cannot emit the
  -- reciprocal KeyUpdate or move its write epoch/counter. Fatal alerts are
  -- likewise forbidden once that local direction has closed.
  let serverClosedForUpdate ← serverResult
    (Server.closeNotify receivedRequest.state)
  expectServerConnectionClosed "server emitted a fatal alert after local close"
    (Server.sealFatalAlert serverClosedForUpdate.state 80)
  let some serverClosedReadBefore := serverClosedForUpdate.state.readKeys?
    | throw (IO.userError "closed server retained no application read keys")
  let expectedServerClosedRead ← recordResult serverClosedReadBefore.update
  let serverCrossingUpdate ← serverResult
    (Server.feed serverClosedForUpdate.state clientRequestedUpdateWire)
  expect "closed server emitted a crossing KeyUpdate response"
    serverCrossingUpdate.wireBytes.isEmpty
  expectEq "closed server failed to advance crossing-update read keys"
    serverCrossingUpdate.state.readKeys? (some expectedServerClosedRead)
  expectEq "closed server changed crossing-update write keys"
    serverCrossingUpdate.state.writeKeys? serverClosedForUpdate.state.writeKeys?
  expectEq "closed server changed crossing-update send count"
    serverCrossingUpdate.state.sendingKeyUpdates
    serverClosedForUpdate.state.sendingKeyUpdates
  expect "crossing update reopened the server write direction"
    serverCrossingUpdate.state.localClosed

  let clientClosedForUpdate ← clientResult
    (Client.closeNotify receivedResponse.state)
  expectClientConnectionClosed "client emitted a fatal alert after local close"
    (Client.sealFatalAlert clientClosedForUpdate.state 80)
  let some clientClosedReadBefore := clientClosedForUpdate.state.readKeys?
    | throw (IO.userError "closed client retained no application read keys")
  let expectedClientClosedRead ← recordResult clientClosedReadBefore.update
  let clientCrossingUpdate ← clientResult
    (Client.feed clientClosedForUpdate.state serverRequestedUpdateWire)
  expect "closed client emitted a crossing KeyUpdate response"
    clientCrossingUpdate.wireBytes.isEmpty
  expectEq "closed client failed to advance crossing-update read keys"
    clientCrossingUpdate.state.readKeys? (some expectedClientClosedRead)
  expectEq "closed client changed crossing-update write keys"
    clientCrossingUpdate.state.writeKeys? clientClosedForUpdate.state.writeKeys?
  expectEq "closed client changed crossing-update send count"
    clientCrossingUpdate.state.sendingKeyUpdates
    clientClosedForUpdate.state.sendingKeyUpdates
  expect "crossing update reopened the client write direction"
    clientCrossingUpdate.state.localClosed

  -- This client does not implement resumption, so RFC 9846 requires it to
  -- ignore NewSessionTicket without semantically parsing the body. Exercise a
  -- deliberately malformed (empty) ticket body under valid record protection.
  let malformedTicket ← handshakeResult
    (Handshake.frame Handshake.newSessionTicketType ByteArray.empty)
  let some serverTicketKeys := sealedResponse.state.writeKeys?
    | throw (IO.userError "server retained no application write keys")
  let (serverAfterTicketKeys, malformedTicketWire) ← recordResult
    (Record.«seal» serverTicketKeys .handshake malformedTicket.encoded)
  let serverAfterTicket := {
    sealedResponse.state with writeKeys? := some serverAfterTicketKeys
  }
  let clientAfterTicket ← clientResult
    (Client.feed receivedResponse.state malformedTicketWire)
  expectEq "unsupported malformed NewSessionTicket was not ignored"
    clientAfterTicket.state.phase .connected

  -- AlertLevel is a legacy field in TLS 1.3. Classification comes from the
  -- description, so even a nonstandard level must not turn close_notify into
  -- a fatal parsing error.
  let legacyLevelClose := (ByteArray.empty.push 0xff).push 0
  let some serverLegacyAlertKeys := serverAfterTicket.writeKeys?
    | throw (IO.userError "server retained no keys for alert-level test")
  let (_, serverLegacyCloseWire) ← recordResult
    (Record.«seal» serverLegacyAlertKeys .alert legacyLevelClose)
  let clientLegacyClose ← clientResult
    (Client.feed clientAfterTicket.state serverLegacyCloseWire)
  expect "client interpreted close_notify using the legacy alert level"
    clientLegacyClose.state.peerClosed
  let userCanceled := (ByteArray.empty.push 1).push 90
  let closeNotify := (ByteArray.empty.push 1).push 0
  let (serverAfterCanceledKeys, userCanceledWire) ← recordResult
    (Record.«seal» serverLegacyAlertKeys .alert userCanceled)
  let (_, closeAfterCanceledWire) ← recordResult
    (Record.«seal» serverAfterCanceledKeys .alert closeNotify)
  let clientAfterCanceled ← clientResult
    (Client.feed clientAfterTicket.state
      (userCanceledWire ++ closeAfterCanceledWire))
  expect "client did not continue through user_canceled to close_notify"
    clientAfterCanceled.state.peerClosed
  expect "client responded to user_canceled or close_notify"
    clientAfterCanceled.wireBytes.isEmpty
  let some clientLegacyAlertKeys := sealedRequest.state.writeKeys?
    | throw (IO.userError "client retained no keys for alert-level test")
  let (_, clientLegacyCloseWire) ← recordResult
    (Record.«seal» clientLegacyAlertKeys .alert legacyLevelClose)
  let serverLegacyClose ← serverResult
    (Server.feed receivedRequest.state clientLegacyCloseWire)
  expect "server interpreted close_notify using the legacy alert level"
    serverLegacyClose.state.peerClosed

  -- close_notify is a directional half-close. Receiving it emits no automatic
  -- response and does not prevent the still-open local write direction from
  -- sending its final application data.
  let serverClose ← serverResult (Server.closeNotify serverAfterTicket)
  let some serverPostCloseKeys := serverClose.state.writeKeys?
    | throw (IO.userError "server retained no post-close traffic state")
  let (_, forbiddenServerTail) ← recordResult
    (Record.«seal» serverPostCloseKeys .applicationData
      "must be ignored after close".toUTF8)
  let clientIgnoredSameChunk ← clientResult
    (Client.feed clientAfterTicket.state
      (serverClose.wireBytes ++ forbiddenServerTail))
  expect "client lost close_notify before a same-chunk trailing record"
    clientIgnoredSameChunk.state.peerClosed
  expect "client delivered same-chunk data after close_notify"
    clientIgnoredSameChunk.plaintext.isEmpty
  expect "client responded to same-chunk data after close_notify"
    clientIgnoredSameChunk.wireBytes.isEmpty
  let clientSawClose ← clientResult
    (Client.feed clientAfterTicket.state serverClose.wireBytes)
  expect "client did not retain peer half-close" clientSawClose.state.peerClosed
  expect "client replied to close_notify automatically" clientSawClose.wireBytes.isEmpty
  expect "peer close incorrectly closed client write side" (!clientSawClose.state.localClosed)

  let finalRequest := "final request after peer half-close".toUTF8
  let finalSealed ← clientResult
    (Client.sealApplication clientSawClose.state finalRequest)
  let finalReceived ← serverResult
    (Server.feed serverClose.state finalSealed.wireBytes)
  expectEq "application data after peer half-close" finalReceived.plaintext finalRequest

  let clientClose ← clientResult (Client.closeNotify finalSealed.state)
  let some clientPostCloseKeys := clientClose.state.writeKeys?
    | throw (IO.userError "client retained no post-close traffic state")
  let (_, forbiddenClientTail) ← recordResult
    (Record.«seal» clientPostCloseKeys .applicationData
      "must also be ignored after close".toUTF8)
  let serverIgnoredSameChunk ← serverResult
    (Server.feed finalReceived.state
      (clientClose.wireBytes ++ forbiddenClientTail))
  expect "server lost close_notify before a same-chunk trailing record"
    serverIgnoredSameChunk.state.peerClosed
  expect "server delivered same-chunk data after close_notify"
    serverIgnoredSameChunk.plaintext.isEmpty
  expect "server responded to same-chunk data after close_notify"
    serverIgnoredSameChunk.wireBytes.isEmpty
  let serverSawClose ← serverResult
    (Server.feed finalReceived.state clientClose.wireBytes)
  expect "server did not retain peer half-close" serverSawClose.state.peerClosed
  expect "server replied to close_notify automatically" serverSawClose.wireBytes.isEmpty

  -- Once the peer direction is closed, subsequent transport bytes are ignored
  -- rather than being surfaced as application data or a resumable error.
  let ignored ← clientResult (Client.feed clientClose.state (fill 17 0xff))
  expect "post-close transport produced plaintext" ignored.plaintext.isEmpty
  expect "post-close transport produced outbound bytes" ignored.wireBytes.isEmpty

  -- A certificate flight larger than 2^14 must be split across protected
  -- records while remaining one continuous handshake byte stream.
  let largeChainConfig : Server.Config := {
    serverConfig with
    serverRandom := fill 32 0x35
    x25519Private := fill 32 0x45
    certificateChain := Array.replicate 50 certificateDer
  }
  let largeClientStart ← clientResult (Client.start {
    clientConfig with
    clientRandom := fill 32 0x13
    x25519Private := fill 32 0x24
    legacySessionId := fill 32 0x57
  })
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
