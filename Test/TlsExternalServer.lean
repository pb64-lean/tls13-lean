import Std.Async.TCP
import Tls.Server

/-!
A deliberately small, one-shot socket shell around the sans-I/O TLS server.
It exists for manual interoperability gates against independently implemented
TLS 1.3 clients (OpenSSL and Go), not as a hermetic unit test.

Run with a loopback port and, optionally, a deliberately small socket read
size for transport-fragmentation testing:

```
bazel run //Test:tls_external_server -- 8443
bazel run //Test:tls_external_server -- 8443 257
```

The certificate and private key are public test fixtures.
-/

open Std
open Std.Async
open Tls

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

private def sendBytes (client : TCP.Socket.Client) (bytes : ByteArray) : IO Unit := do
  unless bytes.isEmpty do
    (client.send bytes).block

private def sendFatalAlert (client : TCP.Socket.Client)
    (failure : Server.Failure) : IO Unit := do
  if let some description := failure.error.fatalAlertDescription? then
    match Server.sealFatalAlert failure.state description with
    | .ok output => sendBytes client output.wireBytes
    | .error _ => pure ()

private partial def completeHandshake (client : TCP.Socket.Client)
    (readSize : UInt64) (state : Server.State)
    (auditDecoder : Record.Decoder := {}) : IO Server.State := do
  if state.connected then
    pure state
  else
    let some chunk ← (client.recv? readSize).block
      | throw (IO.userError "client closed during TLS handshake")
    let (auditDecoder, records) ←
      match auditDecoder.feed chunk with
      | .ok decoded => pure decoded
      | .error error => throw (IO.userError s!"record audit decoder: {error}")
    IO.println s!"RECV phase={repr state.phase} tcp_bytes={chunk.size} records={records.size}"
    for record in records do
      IO.println s!"RECORD type={repr record.contentType} fragment_bytes={record.fragment.size}"
    match Server.feedWithFailure state chunk with
    | .error failure =>
        sendFatalAlert client failure
        throw (IO.userError s!"TLS server: {failure.error}")
    | .ok output =>
        sendBytes client output.wireBytes
        completeHandshake client readSize output.state auditDecoder

private def parseArgs (args : List String) : IO (UInt16 × UInt64) := do
  let (encodedPort, encodedReadSize) ←
    match args with
    | [port] => pure (port, "16384")
    | [port, readSize] => pure (port, readSize)
    | _ => throw (IO.userError "usage: tls_external_server PORT [READ-SIZE]")
  let some port := encodedPort.toNat?
    | throw (IO.userError s!"invalid TCP port: {encodedPort}")
  unless port > 0 && port ≤ 65535 do
    throw (IO.userError s!"TCP port out of range: {encodedPort}")
  let some readSize := encodedReadSize.toNat?
    | throw (IO.userError s!"invalid read size: {encodedReadSize}")
  unless readSize > 0 do
    throw (IO.userError "read size must be positive")
  pure (UInt16.ofNat port, UInt64.ofNat readSize)

def main (args : List String) : IO Unit := do
  let (port, readSize) ← parseArgs args
  let pem ← IO.FS.readFile "Test/Fixtures/Tls/server_cert.pem"
  let certificateDer ←
    match TLS13.X509.PEM.decodeCertificates pem with
    | .error error => throw (IO.userError s!"could not decode test certificate: {error}")
    | .ok certificates =>
        match certificates[0]? with
        | some certificate => pure certificate
        | none => throw (IO.userError "test certificate PEM contained no certificate")
  let config : Server.Config := {
    serverRandom := fill 32 0x33
    x25519Private := fill 32 0x44
    p256Private := some (fill 32 0x45)
    certificateChain := #[certificateDer]
    signingKey :=
      hex "471761974da12938977eca1b40cc0ea3d6e9c52897648a1661681e88fd31f4be"
    alpnProtocols := ["http/1.1"]
  }

  let listener ← TCP.Socket.Server.mk
  listener.bind (.v4 {
    addr := Std.Net.IPv4Addr.ofParts 127 0 0 1
    port
  })
  listener.listen 1
  IO.println s!"READY 127.0.0.1:{port}"

  let client ← listener.accept.block
  try
    let connected ← completeHandshake client readSize (Server.start config)
    IO.println s!"NEGOTIATED suite={connected.cipherSuiteSelected} group={repr connected.groupSelected}"
    if connected.peerClosed then
      IO.println "peer closed immediately after the handshake"
    else
      -- A tiny response lets curl exercise the same TLS endpoint without
      -- turning this interoperability harness into a full HTTP server.
      let response :=
        "HTTP/1.1 200 OK\r\nContent-Length: 2\r\nConnection: close\r\n\r\nOK".toUTF8
      let responded ←
        match Server.sealApplication connected response with
        | .error error => throw (IO.userError s!"TLS application response: {error}")
        | .ok output =>
            sendBytes client output.wireBytes
            pure output.state
      match Server.closeNotify responded with
      | .error error => throw (IO.userError s!"TLS close_notify: {error}")
      | .ok output => sendBytes client output.wireBytes
  finally
    try (client.shutdown).block catch _ => pure ()
