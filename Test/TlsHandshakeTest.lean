import Tls.Server

/-!
Wire-level tests for the shared TLS 1.3 handshake codecs. The rich ClientHello
deliberately looks unlike `encodeClientHello`: extensions are reordered, GREASE
and unknown values are present, and a 1216-byte X25519MLKEM768 share precedes
GREASE, P-256, and classical X25519 shares. This protects the server input
boundary from becoming coupled to the minimal in-repo client encoder.
-/

open Tls

private def u16 (n : UInt16) : ByteArray :=
  (ByteArray.empty.push (n >>> 8).toUInt8).push n.toUInt8

private def u32 (n : UInt32) : ByteArray :=
  (((ByteArray.empty.push (n >>> 24).toUInt8).push
    (n >>> 16).toUInt8).push (n >>> 8).toUInt8).push n.toUInt8

private def v8 (bytes : ByteArray) : ByteArray :=
  ByteArray.empty.push (UInt8.ofNat bytes.size) ++ bytes

private def v16 (bytes : ByteArray) : ByteArray :=
  u16 (UInt16.ofNat bytes.size) ++ bytes

private def ext (extensionType : UInt16) (data : ByteArray) : ByteArray :=
  u16 extensionType ++ v16 data

private def repeated (n : Nat) (byte : UInt8) : ByteArray :=
  ByteArray.mk (Array.replicate n byte)

private def keyShare (group : UInt16) (keyExchange : ByteArray) : ByteArray :=
  u16 group ++ v16 keyExchange

private def pskExtension (identity : String) (age : UInt32)
    (binderByte : UInt8) : ByteArray :=
  let identities := v16 identity.toUTF8 ++ u32 age
  let binders := v8 (repeated 32 binderByte)
  ext Handshake.preSharedKeyExtension (v16 identities ++ v16 binders)

-- IANA X25519MLKEM768. It is intentionally unknown to this implementation:
-- the same ClientHello also carries a classical X25519 share.
private def x25519Mlkem768Group : UInt16 := 0x11ec

private def makeClientHello (extensions : Option ByteArray)
    (compression : ByteArray := ByteArray.empty.push 0)
    (cipherSuites : ByteArray :=
      u16 0x0a0a ++ u16 0x1301 ++ u16 Handshake.tlsChaCha20Poly1305Sha256) :
    Except String Handshake.Message := do
  let mut body := u16 Handshake.legacyTls12Version
  body := body ++ repeated 32 0x42
  -- Deliberately nonstandard length: real ClientHellos need not use the
  -- common 32-byte compatibility value.
  body := body ++ v8 (repeated 17 0xa5)
  body := body ++ v16 cipherSuites
  body := body ++ v8 compression
  if let some extensionBytes := extensions then
    body := body ++ v16 extensionBytes
  Handshake.frame Handshake.clientHelloType body

private def unwrap (label : String) (result : Except String α) : IO α :=
  match result with
  | .ok value => pure value
  | .error error => throw (IO.userError s!"{label}: unexpected error: {error}")

private def unwrapRecord (label : String) (result : Except Record.Error α) : IO α :=
  match result with
  | .ok value => pure value
  | .error error => throw (IO.userError s!"{label}: unexpected error: {error}")

private def unwrapServer (label : String) (result : Except Server.Error α) : IO α :=
  match result with
  | .ok value => pure value
  | .error error => throw (IO.userError s!"{label}: unexpected error: {error}")

private def expectNoCipher (label : String) (result : Except Server.Error α) : IO Unit :=
  match result with
  | .error .noSupportedCipherSuite => pure ()
  | .error error => throw (IO.userError s!"{label}: wrong error: {error}")
  | .ok _ => throw (IO.userError s!"{label}: unexpectedly succeeded")

private def expectMissingExtension (label : String) (extensionType : UInt16)
    (result : Except Server.Error α) : IO Unit :=
  match result with
  | .error (.missingRequiredExtension actual) =>
      unless actual == extensionType do
        throw (IO.userError
          s!"{label}: wrong missing extension {actual}, expected {extensionType}")
  | .error error => throw (IO.userError s!"{label}: wrong error: {error}")
  | .ok _ => throw (IO.userError s!"{label}: unexpectedly succeeded")

private def expectInvalidRetry (label : String) (result : Except Server.Error α) : IO Unit :=
  match result with
  | .error (.invalidRetryClientHello _) => pure ()
  | .error error => throw (IO.userError s!"{label}: wrong error: {error}")
  | .ok _ => throw (IO.userError s!"{label}: unexpectedly succeeded")

private def expectUnexpectedRecord (label : String)
    (result : Except Server.Error α) : IO Unit :=
  match result with
  | .error (.unexpectedRecord _ _) => pure ()
  | .error error => throw (IO.userError s!"{label}: wrong error: {error}")
  | .ok _ => throw (IO.userError s!"{label}: unexpectedly succeeded")

private def expectError (label : String) (result : Except String α) : IO Unit :=
  match result with
  | .error _ => pure ()
  | .ok _ => throw (IO.userError s!"{label}: unexpectedly succeeded")

private def check (label : String) (condition : Bool) : IO Unit := do
  unless condition do
    throw (IO.userError label)

private def richExtensions : ByteArray :=
  let greaseExtension := ext 0x1a1a (ByteArray.mk #[0xde, 0xad, 0xbe, 0xef, 0x01])
  let shares :=
    keyShare x25519Mlkem768Group (repeated 1216 0x91) ++
    keyShare 0x2a2a (ByteArray.mk #[0x99, 0x98, 0x97]) ++
    keyShare Handshake.secp256r1Group
      (ByteArray.empty.push 4 ++ repeated 64 0x33) ++
    keyShare Handshake.x25519Group (repeated 32 0x44)
  let keyShareExtension := ext Handshake.keyShareExtension (v16 shares)
  let alpnNames :=
    v8 (ByteArray.mk #[0xff, 0xfe]) ++ v8 "h2".toUTF8 ++ v8 "http/1.1".toUTF8
  let alpn := ext Handshake.alpnExtension (v16 alpnNames)
  let versions := ext Handshake.supportedVersionsExtension
    (v8 (u16 0x7a7a ++ u16 Handshake.tls13Version ++ u16 0x0303))
  let hostName := ByteArray.empty.push 0 ++ v16 "interop.example".toUTF8
  let sni := ext Handshake.serverNameExtension (v16 hostName)
  let signatures := ext Handshake.signatureAlgorithmsExtension
    (v16 (u16 0x3a3a ++ u16 Handshake.ed25519 ++
      u16 Handshake.ecdsaSecp256r1Sha256))
  let groups := ext Handshake.supportedGroupsExtension
    (v16 (u16 x25519Mlkem768Group ++ u16 0x2a2a ++
      u16 Handshake.secp256r1Group ++ u16 Handshake.x25519Group))
  -- In particular, supported_versions and supported_groups are not first and
  -- key_share precedes supported_groups.
  greaseExtension ++ keyShareExtension ++ alpn ++ versions ++ sni ++ signatures ++ groups

private def testRequiredExtensionAndEmptyRecordFailures
    (serverConfig : Server.Config) : IO Unit := do
  let emptyHandshakeRecord ← unwrapRecord "frame empty Handshake record"
    (Record.encodePlaintext .handshake ByteArray.empty)
  expectUnexpectedRecord "server accepted an empty Handshake record"
    (Server.feed (Server.start serverConfig) emptyHandshakeRecord)

  let noSupportedGroups :=
    ext Handshake.supportedVersionsExtension (v8 (u16 Handshake.tls13Version)) ++
    ext Handshake.keyShareExtension
      (v16 (keyShare Handshake.x25519Group (repeated 32 0x44))) ++
    ext Handshake.signatureAlgorithmsExtension (v16 (u16 Handshake.ed25519))
  let noSupportedGroupsMessage ← unwrap "frame missing supported_groups"
    (makeClientHello (some noSupportedGroups))
  let noSupportedGroupsWire ← unwrapRecord "record missing supported_groups"
    (Record.encodePlaintext .handshake noSupportedGroupsMessage.encoded)
  expectMissingExtension "server accepted missing supported_groups"
    Handshake.supportedGroupsExtension
    (Server.feed (Server.start serverConfig) noSupportedGroupsWire)

  let noKeyShare :=
    ext Handshake.supportedVersionsExtension (v8 (u16 Handshake.tls13Version)) ++
    ext Handshake.supportedGroupsExtension (v16 (u16 Handshake.x25519Group)) ++
    ext Handshake.signatureAlgorithmsExtension (v16 (u16 Handshake.ed25519))
  let noKeyShareMessage ← unwrap "frame missing key_share"
    (makeClientHello (some noKeyShare))
  let noKeyShareWire ← unwrapRecord "record missing key_share"
    (Record.encodePlaintext .handshake noKeyShareMessage.encoded)
  expectMissingExtension "server emitted HRR for an unoffered key_share extension"
    Handshake.keyShareExtension
    (Server.feed (Server.start serverConfig) noKeyShareWire)

  let noSignatureAlgorithms :=
    ext Handshake.supportedVersionsExtension (v8 (u16 Handshake.tls13Version)) ++
    ext Handshake.supportedGroupsExtension (v16 (u16 Handshake.x25519Group)) ++
    ext Handshake.keyShareExtension
      (v16 (keyShare Handshake.x25519Group (repeated 32 0x44)))
  let noSignatureMessage ← unwrap "frame missing signature_algorithms"
    (makeClientHello (some noSignatureAlgorithms))
  let noSignatureWire ← unwrapRecord "record missing signature_algorithms"
    (Record.encodePlaintext .handshake noSignatureMessage.encoded)
  expectMissingExtension "server accepted missing signature_algorithms"
    Handshake.signatureAlgorithmsExtension
    (Server.feed (Server.start serverConfig) noSignatureWire)
  check "missing extension does not map to missing_extension alert"
    (Server.Error.fatalAlertDescription?
      (.missingRequiredExtension Handshake.keyShareExtension) == some 109)

set_option maxRecDepth 2048 in
def main : IO Unit := do
  let certificatePem ← IO.FS.readFile "Test/Fixtures/Tls/server_cert.pem"
  let certificates ← unwrap "decode server certificate fixture"
    (TLS13.X509.PEM.decodeCertificates certificatePem)
  let certificateDer ← match certificates[0]? with
    | some der => pure der
    | none => throw (IO.userError "server certificate fixture was empty")
  let richMessage ← unwrap "frame rich ClientHello" (makeClientHello (some richExtensions))
  let hello ← unwrap "parse rich ClientHello" (Handshake.parseClientHello richMessage)
  check "rich ClientHello did not offer TLS 1.3" hello.offersTls13
  check "supported versions lost unknown/GREASE values"
    (hello.supportedVersionIds == #[0x7a7a, Handshake.tls13Version, 0x0303])
  check "cipher suites lost unknown/GREASE values"
    (hello.cipherSuites == #[0x0a0a, 0x1301, Handshake.tlsChaCha20Poly1305Sha256])
  check "raw supported-group IDs were not retained"
    (hello.supportedGroupIds ==
      #[x25519Mlkem768Group, 0x2a2a,
        Handshake.secp256r1Group, Handshake.x25519Group])
  check "known supported groups were not filtered in wire order"
    (hello.supportedGroups == #[.secp256r1, .x25519])
  check "unknown key share was not ignored"
    (hello.keyShares.map (·.group) == #[.secp256r1, .x25519])
  check "raw key-share group IDs were not retained"
    (hello.keyShareGroupIds ==
      #[x25519Mlkem768Group, 0x2a2a,
        Handshake.secp256r1Group, Handshake.x25519Group])
  check "variable-sized P-256 key share was not retained"
    (hello.keyShares[0]!.keyExchange.size == 65)
  check "X25519 key share was not retained"
    (hello.keyShares[1]!.keyExchange.size == 32)
  check "signature scheme list changed"
    (hello.signatureAlgorithms ==
      #[0x3a3a, Handshake.ed25519, Handshake.ecdsaSecp256r1Sha256])
  check "SNI did not parse" (hello.serverName == some "interop.example")
  check "ALPN list changed" (hello.alpnProtocols == #["h2", "http/1.1"])
  check "exact ClientHello transcript bytes were not retained"
    (hello.encoded == richMessage.encoded)

  -- The server must apply policy to this mainstream-shaped offer rather than
  -- assuming its own encoder's ordering. AES and GREASE precede ChaCha in the
  -- client's list, and P-256 precedes X25519 in supported_groups, but the
  -- current server selects its first mutually implemented suite and group.
  let richWire ← unwrapRecord "frame rich ClientHello record"
    (Record.encodePlaintext .handshake richMessage.encoded)
  let richServerConfig : Server.Config := {
    serverRandom := repeated 32 0x71
    x25519Private := repeated 32 0x72
    certificateChain := #[certificateDer]
    signingKey := repeated 32 0x73
    alpnProtocols := ["http/1.1", "h2"]
  }

  -- Reassemble one PQ-sized ClientHello across three handshake records and
  -- three unrelated TCP delivery boundaries. The first TCP chunk even ends
  -- inside the first record header; the second ends inside record two.
  check "PQ-rich ClientHello was not large enough to exercise fragmentation"
    (richMessage.encoded.size > 1400)
  let firstFragment := richMessage.encoded.extract 0 311
  let secondFragment := richMessage.encoded.extract 311 977
  let thirdFragment := richMessage.encoded.extract 977 richMessage.encoded.size
  let firstRecord0 ← unwrapRecord "frame first fragmented ClientHello record"
    (Record.encodePlaintext .handshake firstFragment)
  let firstRecord := (firstRecord0.set! 1 0x03).set! 2 0x01
  let secondRecord ← unwrapRecord "frame second fragmented ClientHello record"
    (Record.encodePlaintext .handshake secondFragment)
  let thirdRecord ← unwrapRecord "frame third fragmented ClientHello record"
    (Record.encodePlaintext .handshake thirdFragment)
  let fragmentedWire := firstRecord ++ secondRecord ++ thirdRecord
  let tcpCut1 := 3
  let tcpCut2 := firstRecord.size + 197
  let partialHeader ← unwrapServer "buffer partial TLS record header"
    (Server.feed (Server.start richServerConfig)
      (fragmentedWire.extract 0 tcpCut1))
  check "partial record header produced output" partialHeader.wireBytes.isEmpty
  check "partial record header advanced handshake phase"
    (partialHeader.state.phase == .waitingClientHello)
  let partialSecondRecord ← unwrapServer "buffer fragmented handshake records"
    (Server.feed partialHeader.state
      (fragmentedWire.extract tcpCut1 tcpCut2))
  check "incomplete multi-record ClientHello produced output"
    partialSecondRecord.wireBytes.isEmpty
  check "incomplete multi-record ClientHello advanced handshake phase"
    (partialSecondRecord.state.phase == .waitingClientHello)
  let fragmentedFlight ← unwrapServer "complete fragmented ClientHello"
    (Server.feed partialSecondRecord.state
      (fragmentedWire.extract tcpCut2 fragmentedWire.size))
  check "fragmented ClientHello did not complete the server flight"
    (fragmentedFlight.state.phase == .waitingClientFinished)
  check "PQ-hybrid offer prevented classical X25519 selection"
    (fragmentedFlight.state.groupSelected == some .x25519)

  let prematureCcs ← unwrapRecord "frame premature compatibility CCS"
    (Record.encodePlaintext .changeCipherSpec (ByteArray.empty.push 1))
  expectUnexpectedRecord "server accepted CCS before a complete first ClientHello"
    (Server.feed (Server.start richServerConfig) prematureCcs)
  testRequiredExtensionAndEmptyRecordFailures richServerConfig

  let richFlight ← unwrapServer "server accepts rich ClientHello"
    (Server.feed (Server.start richServerConfig) richWire)
  check "server did not advance after rich ClientHello"
    (richFlight.state.phase == .waitingClientFinished)
  check "server did not select supported ChaCha suite"
    (richFlight.state.cipherSuiteSelected ==
      some Handshake.tlsChaCha20Poly1305Sha256)
  check "server did not select its preferred mutual X25519 group"
    (richFlight.state.groupSelected == some .x25519)
  check "server did not retain rich ClientHello SNI"
    (richFlight.state.peerServerName == some "interop.example")
  check "server did not apply server-preference ALPN"
    (richFlight.state.alpnSelected == some "http/1.1")
  let (_, richRecords) ← unwrapRecord "decode rich server flight"
    (({} : Record.Decoder).feed richFlight.wireBytes)
  check "rich server flight should be ServerHello, CCS, ciphertext"
    (richRecords.map (·.contentType) ==
      #[.handshake, .changeCipherSpec, .applicationData])
  let selectedMessage ← unwrap "decode selected ServerHello"
    (Handshake.decode richRecords[0]!.fragment)
  let selectedHello ← unwrap "parse selected ServerHello"
    (Handshake.parseServerHello selectedMessage)
  check "selected ServerHello did not echo variable session ID"
    (selectedHello.legacySessionIdEcho == hello.legacySessionId)
  check "selected ServerHello used the wrong suite"
    (selectedHello.cipherSuite == Handshake.tlsChaCha20Poly1305Sha256)
  check "selected ServerHello used the wrong group"
    (selectedHello.selectedGroup == .x25519)

  let noCipherMessage ← unwrap "frame no-overlap ClientHello"
    (makeClientHello (some richExtensions)
      (cipherSuites := u16 0x0a0a ++ u16 0x1301))
  let noCipherWire ← unwrapRecord "frame no-overlap ClientHello record"
    (Record.encodePlaintext .handshake noCipherMessage.encoded)
  expectNoCipher "server must report no cipher overlap"
    (Server.feed (Server.start richServerConfig) noCipherWire)
  check "no-cipher alert is not handshake_failure"
    (Server.Error.fatalAlertDescription? .noSupportedCipherSuite == some 40)

  -- RFC 8446 explicitly permits the initial ClientHello record to use the
  -- TLS 1.0 legacy record version. OpenSSL uses this compatibility form.
  let legacyRecordWire := (richWire.set! 1 0x03).set! 2 0x01
  let legacyRecordFlight ← unwrapServer "server accepts 0x0301 ClientHello record"
    (Server.feed (Server.start richServerConfig) legacyRecordWire)
  check "0x0301 ClientHello record did not negotiate"
    (legacyRecordFlight.state.phase == .waitingClientFinished)
  let ignoredVersionWire := (richWire.set! 1 0x7a).set! 2 0x7a
  let ignoredVersionFlight ← unwrapServer "server ignores TLSPlaintext legacy version"
    (Server.feed (Server.start richServerConfig) ignoredVersionWire)
  check "nonstandard TLSPlaintext legacy version affected negotiation"
    (ignoredVersionFlight.state.phase == .waitingClientFinished)

  -- An empty KeyShareClientHello vector is explicitly allowed to request HRR.
  let emptyShares :=
    ext Handshake.supportedVersionsExtension (v8 (u16 Handshake.tls13Version)) ++
    ext Handshake.supportedGroupsExtension (v16 (u16 Handshake.x25519Group)) ++
    ext Handshake.keyShareExtension (v16 ByteArray.empty) ++
    ext Handshake.signatureAlgorithmsExtension
      (v16 (u16 Handshake.ed25519))
  let emptyShareMessage ← unwrap "frame empty key_share"
    (makeClientHello (some emptyShares))
  let emptyShareHello ← unwrap "parse empty key_share"
    (Handshake.parseClientHello emptyShareMessage)
  check "empty key_share was not accepted" emptyShareHello.keyShares.isEmpty
  check "supported group was lost with empty key_share"
    (emptyShareHello.supportedGroups == #[.x25519])

  -- An empty first-flight key_share for a mutually supported group drives the
  -- real server machine through HRR. The transcript must replace CH1 with the
  -- synthetic message_hash before appending HRR and CH2.
  let emptyShareWire ← unwrapRecord "frame HRR ClientHello record"
    (Record.encodePlaintext .handshake emptyShareMessage.encoded)
  let retryFlight ← unwrapServer "server emits HRR"
    (Server.feed (Server.start richServerConfig) emptyShareWire)
  check "server did not wait for a second ClientHello"
    (retryFlight.state.phase == .waitingSecondClientHello)
  check "server did not request X25519"
    (retryFlight.state.retryGroup? == some .x25519)
  let (_, retryRecords) ← unwrapRecord "decode HRR flight"
    (({} : Record.Decoder).feed retryFlight.wireBytes)
  check "HRR compatibility flight should be HRR followed by CCS"
    (retryRecords.map (·.contentType) == #[.handshake, .changeCipherSpec])
  let retryMessage ← unwrap "decode emitted HRR"
    (Handshake.decode retryRecords[0]!.fragment)
  check "server's retry was not recognized as HRR"
    (Handshake.isHelloRetryRequest retryMessage)
  let parsedRetry ← unwrap "parse emitted HRR"
    (Handshake.parseHelloRetryRequest retryMessage)
  check "server's HRR requested the wrong group"
    (parsedRetry.selectedGroup == .x25519)
  check "server's HRR did not echo session ID"
    (parsedRetry.legacySessionIdEcho == emptyShareHello.legacySessionId)

  let (syntheticHash, transcriptTail) ← unwrap "decode synthetic message_hash"
    (Handshake.decodeOne retryFlight.state.transcript)
  check "synthetic transcript message has the wrong type"
    (syntheticHash.msgType == Handshake.messageHashType)
  check "synthetic transcript did not hash exact CH1 bytes"
    (syntheticHash.body == HaclStar.sha256 emptyShareMessage.encoded)
  check "HRR was not appended to the synthetic transcript"
    (transcriptTail == retryMessage.encoded)

  let secondShares :=
    ext Handshake.supportedVersionsExtension (v8 (u16 Handshake.tls13Version)) ++
    ext Handshake.supportedGroupsExtension (v16 (u16 Handshake.x25519Group)) ++
    ext Handshake.keyShareExtension
      (v16 (keyShare Handshake.x25519Group (repeated 32 0x61))) ++
    ext Handshake.signatureAlgorithmsExtension
      (v16 (u16 Handshake.ed25519))
  let secondMessage ← unwrap "frame second ClientHello"
    (makeClientHello (some secondShares))
  -- CH2 is the original ClientHello with only the RFC-permitted retry
  -- differences. A changed random must be rejected before key derivation.
  let changedSecond ← unwrap "decode changed second ClientHello"
    (Handshake.decode (secondMessage.encoded.set! 6 0x43))
  let changedSecondWire ← unwrapRecord "frame changed second ClientHello"
    (Record.encodePlaintext .handshake changedSecond.encoded)
  expectInvalidRetry "server accepted changed CH2 random"
    (Server.feed retryFlight.state changedSecondWire)
  let secondWire ← unwrapRecord "frame second ClientHello record"
    (Record.encodePlaintext .handshake secondMessage.encoded)
  let partialSecondWire ← unwrapRecord "frame partial second ClientHello"
    (Record.encodePlaintext .handshake
      (secondMessage.encoded.extract 0 11))
  let partialSecond ← unwrapServer "buffer partial second ClientHello"
    (Server.feed retryFlight.state partialSecondWire)
  match Server.feed partialSecond.state prematureCcs with
  | .error .interleavedHandshake => pure ()
  | .error error =>
      throw (IO.userError s!"server accepted CCS inside fragmented CH2: {error}")
  | .ok _ =>
      throw (IO.userError "server accepted CCS inside fragmented CH2")
  let retryCompleted ← unwrapServer "server accepts requested retry share"
    (Server.feed retryFlight.state secondWire)
  check "server did not complete its flight after CH2"
    (retryCompleted.state.phase == .waitingClientFinished)
  check "server changed the group selected by HRR"
    (retryCompleted.state.groupSelected == some .x25519)

  -- The server never selects PSK, but a well-formed ignored offer still has
  -- mandatory placement/mode rules and restricted HRR changes.
  let pskModes :=
    ext Handshake.pskKeyExchangeModesExtension
      (v8 (ByteArray.empty.push 1))
  let pskBase :=
    ext Handshake.supportedVersionsExtension (v8 (u16 Handshake.tls13Version)) ++
    ext Handshake.supportedGroupsExtension (v16 (u16 Handshake.x25519Group)) ++
    ext Handshake.keyShareExtension (v16 ByteArray.empty) ++
    ext Handshake.signatureAlgorithmsExtension (v16 (u16 Handshake.ed25519))
  let pskWithoutModes ← unwrap "frame PSK without modes"
    (makeClientHello (some (pskBase ++ pskExtension "ticket-a" 7 0x11)))
  expectError "pre_shared_key without psk_key_exchange_modes"
    (Handshake.parseClientHello pskWithoutModes)
  let pskNotFinal ← unwrap "frame non-final PSK"
    (makeClientHello (some
      (pskBase ++ pskModes ++ pskExtension "ticket-a" 7 0x11 ++
        ext Handshake.paddingExtension ByteArray.empty)))
  expectError "pre_shared_key was not final"
    (Handshake.parseClientHello pskNotFinal)

  let pskFirst ← unwrap "frame PSK retry ClientHello"
    (makeClientHello (some
      (pskBase ++ pskModes ++ pskExtension "ticket-a" 7 0x11)))
  let pskFirstWire ← unwrapRecord "frame PSK retry ClientHello record"
    (Record.encodePlaintext .handshake pskFirst.encoded)
  let pskRetry ← unwrapServer "server emits HRR for PSK ClientHello"
    (Server.feed (Server.start richServerConfig) pskFirstWire)
  let pskSecondExtensions :=
    ext Handshake.supportedVersionsExtension (v8 (u16 Handshake.tls13Version)) ++
    ext Handshake.supportedGroupsExtension (v16 (u16 Handshake.x25519Group)) ++
    ext Handshake.keyShareExtension
      (v16 (keyShare Handshake.x25519Group (repeated 32 0x61))) ++
    ext Handshake.signatureAlgorithmsExtension (v16 (u16 Handshake.ed25519)) ++
    pskModes ++ pskExtension "ticket-b" 8 0x22
  let changedPskSecond ← unwrap "frame changed PSK identity in CH2"
    (makeClientHello (some pskSecondExtensions))
  let changedPskSecondWire ← unwrapRecord "frame changed PSK CH2 record"
    (Record.encodePlaintext .handshake changedPskSecond.encoded)
  expectInvalidRetry "server accepted changed PSK identity in CH2"
    (Server.feed pskRetry.state changedPskSecondWire)

  -- A pre-extension ClientHello remains structurally decodable but cannot
  -- negotiate TLS 1.3.
  let oldMessage ← unwrap "frame extensionless ClientHello" (makeClientHello none)
  let oldHello ← unwrap "parse extensionless ClientHello"
    (Handshake.parseClientHello oldMessage)
  check "extensionless ClientHello offered TLS 1.3" (!oldHello.offersTls13)

  -- RFC 8446 forbids duplicate extension types even when their bodies match.
  let duplicateVersion :=
    ext Handshake.supportedVersionsExtension (v8 (u16 Handshake.tls13Version)) ++
    ext Handshake.supportedVersionsExtension (v8 (u16 Handshake.tls13Version))
  let duplicateMessage ← unwrap "frame duplicate extension"
    (makeClientHello (some duplicateVersion))
  expectError "duplicate extension"
    (Handshake.parseClientHello duplicateMessage)

  -- Recognized extension bodies must be consumed exactly; this catches
  -- length-confusion while unknown extension bodies remain opaque.
  let trailingVersion :=
    ext Handshake.supportedVersionsExtension
      (v8 (u16 Handshake.tls13Version) ++ ByteArray.empty.push 0)
  let trailingMessage ← unwrap "frame trailing supported_versions"
    (makeClientHello (some trailingVersion))
  expectError "trailing supported_versions"
    (Handshake.parseClientHello trailingMessage)

  let duplicateShareEntries :=
    keyShare Handshake.x25519Group (repeated 32 0x11) ++
    keyShare Handshake.x25519Group (repeated 32 0x22)
  let duplicateShares :=
    ext Handshake.supportedVersionsExtension (v8 (u16 Handshake.tls13Version)) ++
    ext Handshake.supportedGroupsExtension (v16 (u16 Handshake.x25519Group)) ++
    ext Handshake.keyShareExtension (v16 duplicateShareEntries)
  let duplicateShareMessage ← unwrap "frame duplicate key share"
    (makeClientHello (some duplicateShares))
  expectError "duplicate key share"
    (Handshake.parseClientHello duplicateShareMessage)

  let outOfOrderShares :=
    keyShare Handshake.x25519Group (repeated 32 0x11) ++
    keyShare Handshake.secp256r1Group
      (ByteArray.empty.push 4 ++ repeated 64 0x22)
  let outOfOrder :=
    ext Handshake.supportedVersionsExtension (v8 (u16 Handshake.tls13Version)) ++
    ext Handshake.supportedGroupsExtension
      (v16 (u16 Handshake.secp256r1Group ++ u16 Handshake.x25519Group)) ++
    ext Handshake.keyShareExtension (v16 outOfOrderShares)
  let outOfOrderMessage ← unwrap "frame out-of-order key shares"
    (makeClientHello (some outOfOrder))
  expectError "key shares outside supported_groups order"
    (Handshake.parseClientHello outOfOrderMessage)

  let badCompressionMessage ← unwrap "frame bad compression"
    (makeClientHello (some richExtensions) (ByteArray.mk #[0, 1]))
  expectError "multiple compression methods"
    (Handshake.parseClientHello badCompressionMessage)

  -- The shared ServerHello representation retains the chosen suite instead
  -- of imposing suite policy inside the wire codec.
  let serverHello ← unwrap "encode ServerHello"
    (Handshake.encodeServerHello (repeated 32 0x55) (repeated 32 0xa5)
      .x25519 (repeated 32 0x66) (cipherSuite := 0x1301))
  let parsedServerHello ← unwrap "parse ServerHello"
    (Handshake.parseServerHello serverHello)
  check "ServerHello cipher suite was not retained"
    (parsedServerHello.cipherSuite == 0x1301)
  check "ordinary ServerHello mistaken for HRR"
    (!Handshake.isHelloRetryRequest serverHello)

  let hrr ← unwrap "encode HelloRetryRequest"
    (Handshake.encodeHelloRetryRequest (repeated 32 0xa5) .secp256r1
      (cipherSuite := Handshake.tlsChaCha20Poly1305Sha256))
  check "HRR discriminator failed" (Handshake.isHelloRetryRequest hrr)
  let parsedHrr ← unwrap "parse HelloRetryRequest"
    (Handshake.parseHelloRetryRequest hrr)
  check "HRR session ID was not retained"
    (parsedHrr.legacySessionIdEcho == repeated 32 0xa5)
  check "HRR cipher suite was not retained"
    (parsedHrr.cipherSuite == Handshake.tlsChaCha20Poly1305Sha256)
  check "HRR group was not retained" (parsedHrr.selectedGroup == .secp256r1)
  check "message_hash handshake type is wrong" (Handshake.messageHashType == 254)
