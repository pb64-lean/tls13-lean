module

public import HaclStar.Curve25519
public import HaclStar.Hmac
public import HaclStar.P256
public import HaclStar.Sha256
public import HaclStar.Signature
public import Tls.Handshake
public import Tls.Record
public import TLS13.KeySchedule
public import TLS13.X509

public section

namespace Tls
namespace Server

/-!
A pure, sans-I/O TLS 1.3 *server* handshake and record machine — the mirror of
`Tls.Client`. It performs no I/O and obtains no entropy itself: the caller
supplies the ServerHello random and ephemeral private scalar(s), the DER
certificate chain, and the Ed25519 signing key in `Config`, then feeds transport
bytes to `feed` and writes the returned `wireBytes`.

The single supported cipher suite matches the client:
TLS_CHACHA20_POLY1305_SHA256. The server negotiates that suite from the
client's offered set and chooses X25519 (or P-256 when configured) from
supported_groups. When the preferred mutual group has no first-flight share,
the server performs one HelloRetryRequest with the RFC 8446 synthetic
message_hash transcript. Authentication is Ed25519; PSK and client
authentication are not yet supported. ALPN is negotiated and the selected
protocol is surfaced in `State.alpnSelected` so the caller can route h2 (gRPC)
versus http/1.1 (REST).
-/

/-- Server certificate, key, and policy. Ephemeral values must be fresh per
connection. `signingKey` is the 32-byte Ed25519 private scalar for the leaf. -/
structure Config where
  serverRandom : ByteArray
  x25519Private : ByteArray
  /-- Optional P-256 ephemeral, used only when a client offers no X25519 share. -/
  p256Private : Option ByteArray := none
  /-- DER certificates, leaf first. -/
  certificateChain : Array ByteArray
  /-- Ed25519 private scalar matching the leaf certificate's public key. -/
  signingKey : ByteArray
  /-- ALPN protocols the server supports, in server preference order. The first
  one the client also offers is selected. Empty disables ALPN. -/
  alpnProtocols : List String := []
  deriving Inhabited

inductive Phase where
  | waitingClientHello
  | waitingSecondClientHello
  | waitingClientFinished
  | connected
  deriving Repr, BEq, DecidableEq, Inhabited

namespace Phase

def render : Phase → String
  | .waitingClientHello => "ClientHello"
  | .waitingSecondClientHello => "second ClientHello after HelloRetryRequest"
  | .waitingClientFinished => "client Finished"
  | .connected => "post-handshake message"

end Phase

inductive Error where
  | invalidConfig (message : String)
  | handshakeCodec (message : String)
  | recordLayer (error : Record.Error)
  | missingRequiredExtension (extensionType : UInt16)
  | noSupportedCipherSuite
  | noSupportedGroup
  | noSupportedSignatureScheme
  | invalidClientKeyShare (group : Handshake.NamedGroup) (message : String)
  | invalidRetryClientHello (message : String)
  | keyExchangeFailed
  | clientDidNotOfferTls13
  | signingFailed
  | clientFinishedMismatch
  | unexpectedRecord (phase : Phase) (contentType : Record.ContentType)
  | unexpectedHandshake (phase : Phase) (actual : UInt8)
  | invalidCompatibilityChangeCipherSpec
  | interleavedHandshake
  | invalidAlertLength (actual : Nat)
  | invalidAlertLevel (actual : UInt8)
  | peerAlert (level description : UInt8)
  | peerClosedDuringHandshake
  | notConnected (phase : Phase)
  | connectionClosed
  | internalState (message : String)
  deriving Repr, Inhabited

namespace Error

def render : Error → String
  | .invalidConfig message => s!"invalid TLS server config: {message}"
  | .handshakeCodec message => s!"TLS handshake codec: {message}"
  | .recordLayer error => s!"TLS record layer: {error}"
  | .missingRequiredExtension extensionType =>
      s!"TLS 1.3 ClientHello is missing required extension {extensionType}"
  | .noSupportedCipherSuite =>
      "client offered no supported cipher suite (need TLS_CHACHA20_POLY1305_SHA256)"
  | .noSupportedGroup =>
      "client offered no mutually supported group (need X25519 or configured P-256)"
  | .noSupportedSignatureScheme =>
      "client offered no signature scheme usable with the server Ed25519 key"
  | .invalidClientKeyShare group message =>
      s!"invalid client {repr group} key share: {message}"
  | .invalidRetryClientHello message =>
      s!"invalid second ClientHello after HelloRetryRequest: {message}"
  | .keyExchangeFailed => "TLS key exchange rejected the client public key"
  | .clientDidNotOfferTls13 => "client did not offer TLS 1.3 in supported_versions"
  | .signingFailed => "server CertificateVerify signing failed"
  | .clientFinishedMismatch => "client Finished verification failed"
  | .unexpectedRecord phase contentType =>
      s!"unexpected TLS {repr contentType} record while waiting for {phase.render}"
  | .unexpectedHandshake phase actual =>
      s!"unexpected TLS handshake message {actual} while waiting for {phase.render}"
  | .invalidCompatibilityChangeCipherSpec => "invalid TLS 1.3 compatibility ChangeCipherSpec"
  | .interleavedHandshake => "TLS handshake fragments were interleaved with another content type"
  | .invalidAlertLength actual => s!"TLS alert payload must be two bytes, got {actual}"
  | .invalidAlertLevel actual => s!"invalid TLS alert level {actual}"
  | .peerAlert level description => s!"TLS peer alert level {level}, description {description}"
  | .peerClosedDuringHandshake => "TLS peer sent close_notify during the handshake"
  | .notConnected phase => s!"TLS connection not ready for application data (waiting for {phase.render})"
  | .connectionClosed => "TLS connection is closed"
  | .internalState message => s!"invalid internal TLS server state: {message}"

/-- Fatal alert to seal (when write keys exist) before discarding the connection. -/
def fatalAlertDescription? : Error → Option UInt8
  | .handshakeCodec _ => some 50            -- decode_error
  | .unexpectedHandshake _ _ => some 10     -- unexpected_message
  | .unexpectedRecord _ _ => some 10
  | .interleavedHandshake => some 10
  | .clientFinishedMismatch => some 51      -- decrypt_error
  | .missingRequiredExtension _ => some 109 -- missing_extension
  | .noSupportedCipherSuite => some 40      -- handshake_failure
  | .noSupportedGroup => some 40            -- handshake_failure
  | .noSupportedSignatureScheme => some 40  -- handshake_failure
  | .invalidClientKeyShare _ _ => some 47   -- illegal_parameter
  | .invalidRetryClientHello _ => some 47   -- illegal_parameter
  | .keyExchangeFailed => some 47        -- illegal_parameter
  | .clientDidNotOfferTls13 => some 70      -- protocol_version
  | _ => none

end Error

instance : ToString Error := ⟨Error.render⟩

/-- Pure server connection state. No `Repr` instance: secrets never print. -/
structure State where
  phase : Phase
  decoder : Record.Decoder := {}
  handshakeBuffered : ByteArray := ByteArray.empty
  transcript : ByteArray := ByteArray.empty
  -- Config carried through the handshake, cleared once connected.
  serverRandom : ByteArray
  x25519Private : ByteArray
  p256Private : Option ByteArray := none
  certificateChain : Array ByteArray := #[]
  signingKey : ByteArray
  alpnProtocols : List String := []
  -- Negotiated results, surfaced to the caller.
  alpnSelected : Option String := none
  peerServerName : Option String := none
  cipherSuiteSelected : Option UInt16 := none
  groupSelected : Option Handshake.NamedGroup := none
  -- HelloRetryRequest state. `transcript` is message_hash(CH1) || HRR while
  -- waiting for CH2, and is cleared once the final server flight is built.
  retryGroup? : Option Handshake.NamedGroup := none
  retryClientRandom : ByteArray := ByteArray.empty
  retryLegacySessionId : ByteArray := ByteArray.empty
  retryCipherSuites : Array UInt16 := #[]
  retrySupportedVersionIds : Array UInt16 := #[]
  retrySupportedGroupIds : Array UInt16 := #[]
  retrySignatureAlgorithms : Array UInt16 := #[]
  retryServerName : Option String := none
  retryAlpnProtocols : Array String := #[]
  retryStableExtensions : Array Handshake.Extension := #[]
  /-- PSK identities paired with their binder hash width. Ages and binder
  bytes may change in CH2; only identities incompatible with the selected
  SHA-256 suite may be removed, while order is preserved. This server never
  selects PSK. -/
  retryPsks : Option (Array (ByteArray × Nat)) := none
  compatibilityCcsSent : Bool := false
  -- Traffic keys.
  readKeys? : Option Record.TrafficKeys := none
  writeKeys? : Option Record.TrafficKeys := none
  clientApplicationKeys? : Option Record.TrafficKeys := none
  expectedClientFinished? : Option ByteArray := none
  localClosed : Bool := false
  peerClosed : Bool := false
  deriving Inhabited

namespace State

def connected (state : State) : Bool :=
  state.phase == .connected

def closed (state : State) : Bool :=
  state.localClosed && state.peerClosed

end State

/-- Bytes and state produced by every engine operation. -/
structure Output where
  state : State
  wireBytes : ByteArray := ByteArray.empty
  plaintext : ByteArray := ByteArray.empty
  deriving Inhabited

structure Failure where
  state : State
  error : Error

/-! ## Shared helpers (mirror of the client engine). -/

private def liftHandshake {α : Type} (result : Except String α) : Except Error α :=
  result.mapError Error.handshakeCodec

private def liftRecord {α : Type} (result : Except Record.Error α) : Except Error α :=
  result.mapError Error.recordLayer

private def sealHandshakeFlight (initialKeys : Record.TrafficKeys)
    (flight : ByteArray) : Except Error ByteArray := do
  let mut keys := initialKeys
  let mut offset := 0
  let mut wireBytes := ByteArray.empty
  while offset < flight.size do
    let stop := min flight.size (offset + Record.maxPlaintextLength)
    let fragment := flight.extract offset stop
    let (nextKeys, record) ←
      liftRecord (Record.«seal» keys .handshake fragment)
    keys := nextKeys
    wireBytes := wireBytes ++ record
    offset := stop
  pure wireBytes

private def requireReadKeys (state : State) : Except Error Record.TrafficKeys :=
  match state.readKeys? with
  | some keys => pure keys
  | none => throw (.internalState "missing read traffic keys")

private def requireWriteKeys (state : State) : Except Error Record.TrafficKeys :=
  match state.writeKeys? with
  | some keys => pure keys
  | none => throw (.internalState "missing write traffic keys")

private def emptyTranscriptHash : ByteArray :=
  HaclStar.sha256 ByteArray.empty

private def uint24AtOne (bytes : ByteArray) : Nat :=
  (bytes.get! 1).toNat <<< 16 |||
    (bytes.get! 2).toNat <<< 8 |||
    (bytes.get! 3).toNat

private def takeHandshake? (buffered : ByteArray) :
    Except Error (Option (Handshake.Message × ByteArray)) := do
  if buffered.size < 4 then
    pure none
  else
    let total := 4 + uint24AtOne buffered
    if buffered.size < total then
      pure none
    else
      let encoded := buffered.extract 0 total
      let rest := buffered.extract total buffered.size
      let message ← liftHandshake (Handshake.decode encoded)
      pure (some (message, rest))

private def constantTimeEq (left right : ByteArray) : Bool :=
  if left.size != right.size then
    false
  else
    Id.run do
      let mut different : UInt8 := 0
      for i in [0:left.size] do
        different := different ||| (left.get! i ^^^ right.get! i)
      return different == 0

private def finishedVerifyData (trafficSecret transcriptHash : ByteArray) : ByteArray :=
  let finishedKey := TLS13.KeySchedule.expandLabel trafficSecret "finished"
    ByteArray.empty TLS13.KeySchedule.hashLen
  HaclStar.hmacSha256 finishedKey transcriptHash

private def validCompatibilityChangeCipherSpec (fragment : ByteArray) : Bool :=
  fragment.size == 1 && fragment.get! 0 == 1

/-! ## Handshake construction. -/

/-- Build the initial state; the server sends nothing until it sees a ClientHello. -/
def start (config : Config) : State :=
  {
    phase := .waitingClientHello
    serverRandom := config.serverRandom
    x25519Private := config.x25519Private
    p256Private := config.p256Private
    certificateChain := config.certificateChain
    signingKey := config.signingKey
    alpnProtocols := config.alpnProtocols
  }

private def clientShare? (hello : Handshake.ClientHello) (group : Handshake.NamedGroup) :
    Option ByteArray :=
  (hello.keyShares.find? (fun share => share.group == group)).map (·.keyExchange)

/-- Select the server's preferred mutually supported group. Group negotiation
is based on supported_groups, not merely on the first-flight key_share list:
the latter distinction is what makes HelloRetryRequest possible. -/
private def selectGroup (state : State) (hello : Handshake.ClientHello) :
    Except Error Handshake.NamedGroup := do
  if hello.supportedGroups.contains .x25519 then
    pure .x25519
  else
    match state.p256Private with
    | some _ =>
        if hello.supportedGroups.contains .secp256r1 then
          pure .secp256r1
        else
          throw .noSupportedGroup
    | none => throw .noSupportedGroup

/-- Compute the ECDHE result for an already negotiated group. Returns
`(serverPublicValue, sharedSecret)`. -/
private def keyExchange (state : State) (hello : Handshake.ClientHello)
    (group : Handshake.NamedGroup) : Except Error (ByteArray × ByteArray) := do
  let some clientPublic := clientShare? hello group
    | throw (.invalidClientKeyShare group "missing requested key share")
  match group with
  | .x25519 =>
      unless clientPublic.size == 32 do
        throw (.invalidClientKeyShare group
          s!"X25519 public value must be 32 bytes, got {clientPublic.size}")
      let some shared := HaclStar.X25519.ecdh state.x25519Private clientPublic
        | throw .keyExchangeFailed
      pure (HaclStar.X25519.base state.x25519Private, shared)
  | .secp256r1 =>
      let some p256Private := state.p256Private
        | throw (.internalState "P-256 was selected without a configured ephemeral")
      unless clientPublic.size == 65 && clientPublic.get! 0 == 4 do
        throw (.invalidClientKeyShare group
          "P-256 public value must be a 65-byte uncompressed point")
      let some serverPublic := HaclStar.P256.publicKey p256Private
        | throw (.internalState "server P-256 ephemeral produced no public key")
      let some shared := HaclStar.P256.ecdh p256Private clientPublic
        | throw .keyExchangeFailed
      pure (serverPublic, shared)

private def parseOfferedPsks (hello : Handshake.ClientHello) :
    Except String (Option (Array (ByteArray × Nat))) := do
  let some extension := hello.extensions.find?
      (fun extension =>
        extension.extensionType == Handshake.preSharedKeyExtension)
    | pure none
  let r : Handshake.Reader := { bytes := extension.data }
  let (identitiesBytes, r) ← r.readVector16
  let (bindersBytes, r) ← r.readVector16
  r.requireEnd "ClientHello pre_shared_key"

  let mut identities : Array ByteArray := #[]
  let mut ir : Handshake.Reader := { bytes := identitiesBytes }
  while !ir.atEnd do
    let (identity, ir') ← ir.readVector16
    if identity.isEmpty then
      throw "ClientHello PSK identity must not be empty"
    let (_, ir') ← ir'.readUInt32
    identities := identities.push identity
    ir := ir'
  if identities.isEmpty then
    throw "ClientHello PSK identities must not be empty"

  let mut binderLengths : Array Nat := #[]
  let mut br : Handshake.Reader := { bytes := bindersBytes }
  while !br.atEnd do
    let (binder, br') ← br.readVector8
    if binder.size < 32 then
      throw s!"ClientHello PSK binder is too short ({binder.size} bytes)"
    binderLengths := binderLengths.push binder.size
    br := br'
  unless binderLengths.size == identities.size do
    throw "ClientHello PSK identity and binder counts differ"

  let mut psks : Array (ByteArray × Nat) := #[]
  for i in [0:identities.size] do
    psks := psks.push (identities[i]!, binderLengths[i]!)
  pure (some psks)

private def psksAreOrderedSubset (subset superset : Array (ByteArray × Nat)) :
    Bool := Id.run do
  let mut next := 0
  for psk in subset do
    let mut found := false
    while next < superset.size && !found do
      if superset[next]! == psk then
        found := true
      next := next + 1
    unless found do
      return false
  return true

private def checkCommonOffers (hello : Handshake.ClientHello) : Except Error Unit := do
  unless hello.offersTls13 do
    throw .clientDidNotOfferTls13
  let hasExtension (extensionType : UInt16) : Bool :=
    hello.extensions.any (fun extension =>
      extension.extensionType == extensionType)
  unless hasExtension Handshake.supportedGroupsExtension do
    throw (.missingRequiredExtension Handshake.supportedGroupsExtension)
  unless hasExtension Handshake.keyShareExtension do
    throw (.missingRequiredExtension Handshake.keyShareExtension)
  unless hasExtension Handshake.signatureAlgorithmsExtension do
    throw (.missingRequiredExtension Handshake.signatureAlgorithmsExtension)
  unless hello.cipherSuites.contains Handshake.tlsChaCha20Poly1305Sha256 do
    throw .noSupportedCipherSuite
  unless hello.signatureAlgorithms.contains Handshake.ed25519 do
    throw .noSupportedSignatureScheme
  let _ ← liftHandshake (parseOfferedPsks hello)

private def retryStableExtensions (hello : Handshake.ClientHello) :
    Array Handshake.Extension :=
  hello.extensions.filter fun extension =>
    -- RFC 8446 §4.1.2 permits replacing key_share, removing early_data,
    -- updating a PSK binder, and changing padding. This server sends no
    -- cookie, so a cookie is checked separately and cannot appear in CH2.
    extension.extensionType != Handshake.keyShareExtension &&
      extension.extensionType != Handshake.earlyDataExtension &&
      extension.extensionType != Handshake.preSharedKeyExtension &&
      extension.extensionType != Handshake.cookieExtension &&
      extension.extensionType != Handshake.paddingExtension

private def checkConfig (state : State) : Except Error Unit := do
  unless state.serverRandom.size == 32 do
    throw (.invalidConfig s!"ServerHello random must be 32 bytes, got {state.serverRandom.size}")
  if state.serverRandom == Handshake.helloRetryRequestRandom then
    throw (.invalidConfig "ServerHello random equals the reserved HelloRetryRequest value")
  unless state.x25519Private.size == 32 do
    throw (.invalidConfig
      s!"X25519 private scalar must be 32 bytes, got {state.x25519Private.size}")
  if let some privateKey := state.p256Private then
    unless privateKey.size == 32 do
      throw (.invalidConfig s!"P-256 private scalar must be 32 bytes, got {privateKey.size}")
  if state.certificateChain.isEmpty then
    throw (.invalidConfig "certificate chain must not be empty")
  if state.certificateChain.any ByteArray.isEmpty then
    throw (.invalidConfig "certificate chain contains an empty DER entry")
  unless state.signingKey.size == 32 do
    throw (.invalidConfig
      s!"Ed25519 signing key must be 32 bytes, got {state.signingKey.size}")

/-- Choose the first server-preferred ALPN protocol the client also offered. -/
private def selectAlpn (serverProtocols : List String) (clientProtocols : Array String) :
    Option String :=
  serverProtocols.find? (fun protocol => clientProtocols.contains protocol)

/-- Given a ClientHello with the selected group's key share, derive keys, build
the full server flight (ServerHello, then encrypted EncryptedExtensions/
Certificate/CertificateVerify/Finished), and advance to
`waitingClientFinished`. `transcriptPrefix` is either CH1 or
message_hash(CH1)||HRR||CH2. -/
private def completeClientHello (state : State) (hello : Handshake.ClientHello)
    (group : Handshake.NamedGroup)
    (transcriptPrefix : ByteArray) :
    Except Error (State × ByteArray) := do
  let (serverPublic, sharedSecret) ← keyExchange state hello group
  unless sharedSecret.size == TLS13.KeySchedule.hashLen do
    throw (.internalState s!"ECDHE returned a {sharedSecret.size}-byte shared secret")

  -- ServerHello and handshake-traffic secrets.
  let serverHello ← liftHandshake
    (Handshake.encodeServerHello state.serverRandom hello.legacySessionId group serverPublic)
  let earlySecret := TLS13.KeySchedule.earlySecret
  let handshakeSecret :=
    TLS13.KeySchedule.handshakeSecret earlySecret sharedSecret emptyTranscriptHash
  let transcript := transcriptPrefix ++ serverHello.encoded
  let serverHelloHash := HaclStar.sha256 transcript
  let clientHandshakeSecret :=
    TLS13.KeySchedule.deriveSecret handshakeSecret "c hs traffic" serverHelloHash
  let serverHandshakeSecret :=
    TLS13.KeySchedule.deriveSecret handshakeSecret "s hs traffic" serverHelloHash
  let serverWriteKeys ← liftRecord (Record.deriveTrafficKeys serverHandshakeSecret)
  let clientReadKeys ← liftRecord (Record.deriveTrafficKeys clientHandshakeSecret)

  -- EncryptedExtensions (ALPN) and Certificate.
  let alpnSelected := selectAlpn state.alpnProtocols hello.alpnProtocols
  let encryptedExtensions ← liftHandshake (Handshake.encodeEncryptedExtensions alpnSelected)
  let transcript := transcript ++ encryptedExtensions.encoded
  let certificate ← liftHandshake (Handshake.encodeCertificate state.certificateChain)
  let transcript := transcript ++ certificate.encoded

  -- CertificateVerify: sign the standard content over the transcript hash.
  let certVerifyContent ←
    match TLS13.X509.Signature.serverCertificateVerifyContent (HaclStar.sha256 transcript) with
    | .ok content => pure content
    | .error message => throw (.internalState message)
  let signature := HaclStar.Signature.ed25519Sign state.signingKey certVerifyContent
  unless signature.size == 64 do
    throw .signingFailed
  let certVerify ← liftHandshake
    (Handshake.encodeCertificateVerify Handshake.ed25519 signature)
  let transcript := transcript ++ certVerify.encoded

  -- Server Finished.
  let serverVerifyData := finishedVerifyData serverHandshakeSecret (HaclStar.sha256 transcript)
  let serverFinished ← liftHandshake (Handshake.encodeFinished serverVerifyData)
  let transcript := transcript ++ serverFinished.encoded
  let finishedHash := HaclStar.sha256 transcript

  -- The client's Finished is over the transcript through the server Finished.
  let expectedClientFinished := finishedVerifyData clientHandshakeSecret finishedHash

  -- Application-traffic keys.
  let masterSecret := TLS13.KeySchedule.masterSecret handshakeSecret emptyTranscriptHash
  let serverApplicationSecret :=
    TLS13.KeySchedule.deriveSecret masterSecret "s ap traffic" finishedHash
  let clientApplicationSecret :=
    TLS13.KeySchedule.deriveSecret masterSecret "c ap traffic" finishedHash
  let serverApplicationKeys ← liftRecord (Record.deriveTrafficKeys serverApplicationSecret)
  let clientApplicationKeys ← liftRecord (Record.deriveTrafficKeys clientApplicationSecret)

  -- Seal EE‖Cert‖CertVerify‖Finished as protected handshake, after the
  -- plaintext ServerHello (and a compatibility CCS when the client used a
  -- nonempty legacy session id).
  let flight := encryptedExtensions.encoded ++ certificate.encoded
    ++ certVerify.encoded ++ serverFinished.encoded
  let sealedFlight ← sealHandshakeFlight serverWriteKeys flight
  let serverHelloWire ← liftRecord (Record.encodePlaintext .handshake serverHello.encoded)
  let sendCompatibilityCcs :=
    !hello.legacySessionId.isEmpty && !state.compatibilityCcsSent
  let ccsWire ←
    if !sendCompatibilityCcs then
      pure ByteArray.empty
    else
      liftRecord (Record.encodePlaintext .changeCipherSpec (ByteArray.empty.push 1))
  let wireBytes := serverHelloWire ++ ccsWire ++ sealedFlight

  pure ({
    state with
    phase := .waitingClientFinished
    handshakeBuffered := ByteArray.empty
    transcript := ByteArray.empty
    x25519Private := ByteArray.empty
    p256Private := none
    signingKey := ByteArray.empty
    certificateChain := #[]
    readKeys? := some clientReadKeys
    writeKeys? := some serverApplicationKeys
    clientApplicationKeys? := some clientApplicationKeys
    expectedClientFinished? := some expectedClientFinished
    alpnSelected := alpnSelected
    peerServerName := hello.serverName
    cipherSuiteSelected := some Handshake.tlsChaCha20Poly1305Sha256
    groupSelected := some group
    retryGroup? := none
    retryClientRandom := ByteArray.empty
    retryLegacySessionId := ByteArray.empty
    retryCipherSuites := #[]
    retrySupportedVersionIds := #[]
    retrySupportedGroupIds := #[]
    retrySignatureAlgorithms := #[]
    retryServerName := none
    retryAlpnProtocols := #[]
    retryStableExtensions := #[]
    retryPsks := none
    compatibilityCcsSent := state.compatibilityCcsSent || sendCompatibilityCcs
  }, wireBytes)

/-- Emit one RFC 8446 HelloRetryRequest and replace CH1 in the transcript with
its synthetic message_hash. No handshake keys exist at this point. -/
private def sendHelloRetryRequest (state : State) (message : Handshake.Message)
    (hello : Handshake.ClientHello) (group : Handshake.NamedGroup) :
    Except Error (State × ByteArray) := do
  let retry ← liftHandshake
    (Handshake.encodeHelloRetryRequest hello.legacySessionId group)
  let messageHash ← liftHandshake
    (Handshake.frame Handshake.messageHashType (HaclStar.sha256 message.encoded))
  let retryPsks ← liftHandshake (parseOfferedPsks hello)
  let retryWire ← liftRecord (Record.encodePlaintext .handshake retry.encoded)
  let sendCompatibilityCcs := !hello.legacySessionId.isEmpty
  let ccsWire ←
    if sendCompatibilityCcs then
      liftRecord (Record.encodePlaintext .changeCipherSpec (ByteArray.empty.push 1))
    else
      pure ByteArray.empty
  pure ({
    state with
    phase := .waitingSecondClientHello
    handshakeBuffered := ByteArray.empty
    transcript := messageHash.encoded ++ retry.encoded
    retryGroup? := some group
    retryClientRandom := hello.random
    retryLegacySessionId := hello.legacySessionId
    retryCipherSuites := hello.cipherSuites
    retrySupportedVersionIds := hello.supportedVersionIds
    retrySupportedGroupIds := hello.supportedGroupIds
    retrySignatureAlgorithms := hello.signatureAlgorithms
    retryServerName := hello.serverName
    retryAlpnProtocols := hello.alpnProtocols
    retryStableExtensions := retryStableExtensions hello
    retryPsks
    cipherSuiteSelected := some Handshake.tlsChaCha20Poly1305Sha256
    groupSelected := some group
    compatibilityCcsSent := sendCompatibilityCcs
  }, retryWire ++ ccsWire)

/-- Process an initial or retry ClientHello. The first may produce HRR; a
second HRR is forbidden and a malformed CH2 fails with illegal_parameter. -/
private def acceptClientHello (state : State) (message : Handshake.Message) :
    Except Error (State × ByteArray) := do
  let hello ← liftHandshake (Handshake.parseClientHello message)
  checkConfig state
  checkCommonOffers hello
  match state.phase with
  | .waitingClientHello =>
      let group ← selectGroup state hello
      if (clientShare? hello group).isSome then
        completeClientHello state hello group message.encoded
      else
        sendHelloRetryRequest state message hello group
  | .waitingSecondClientHello =>
      let some group := state.retryGroup?
        | throw (.internalState "retry phase has no requested group")
      unless hello.random == state.retryClientRandom do
        throw (.invalidRetryClientHello "random changed")
      unless hello.legacySessionId == state.retryLegacySessionId do
        throw (.invalidRetryClientHello "legacy_session_id changed")
      unless hello.cipherSuites == state.retryCipherSuites do
        throw (.invalidRetryClientHello "cipher_suites changed")
      unless hello.supportedVersionIds == state.retrySupportedVersionIds do
        throw (.invalidRetryClientHello "supported_versions changed")
      unless hello.supportedGroupIds == state.retrySupportedGroupIds do
        throw (.invalidRetryClientHello "supported_groups changed")
      unless hello.signatureAlgorithms == state.retrySignatureAlgorithms do
        throw (.invalidRetryClientHello "signature_algorithms changed")
      unless hello.serverName == state.retryServerName do
        throw (.invalidRetryClientHello "server_name changed")
      unless hello.alpnProtocols == state.retryAlpnProtocols do
        throw (.invalidRetryClientHello "ALPN offer changed")
      unless retryStableExtensions hello == state.retryStableExtensions do
        throw (.invalidRetryClientHello "an extension not permitted to change was modified")
      if hello.extensions.any
          (fun extension => extension.extensionType == Handshake.earlyDataExtension) then
        throw (.invalidRetryClientHello "early_data was not removed")
      if hello.extensions.any
          (fun extension => extension.extensionType == Handshake.cookieExtension) then
        throw (.invalidRetryClientHello "unsolicited cookie extension")
      let retryPsks ← liftHandshake (parseOfferedPsks hello)
      match retryPsks, state.retryPsks with
      | none, none => pure ()
      | none, some original =>
          if original.any (fun psk => psk.2 == 32) then
            throw (.invalidRetryClientHello
              "pre_shared_key removed despite containing a SHA-256 identity")
      | some _, none =>
          throw (.invalidRetryClientHello "pre_shared_key was added")
      | some current, some original =>
          let required := original.filter (fun psk => psk.2 == 32)
          unless psksAreOrderedSubset current original &&
              psksAreOrderedSubset required current do
            throw (.invalidRetryClientHello
              "pre_shared_key identities were added, reordered, changed, or \
                removed despite matching SHA-256")
      unless hello.supportedGroups.contains group do
        throw (.invalidRetryClientHello "requested group was removed from supported_groups")
      unless hello.keyShareGroupIds == #[group.toUInt16] do
        throw (.invalidRetryClientHello
          "key_share must contain exactly the single group requested by HelloRetryRequest")
      unless (clientShare? hello group).isSome do
        throw (.invalidRetryClientHello "requested key share is still absent")
      completeClientHello state hello group (state.transcript ++ message.encoded)
  | phase =>
      throw (.internalState s!"acceptClientHello called while waiting for {phase.render}")

private def acceptClientFinished (state : State) (message : Handshake.Message) :
    Except Error State := do
  let finished ← liftHandshake (Handshake.parseFinished message)
  let some expected := state.expectedClientFinished?
    | throw (.internalState "missing expected client Finished")
  unless constantTimeEq expected finished.verifyData do
    throw .clientFinishedMismatch
  let some clientApplicationKeys := state.clientApplicationKeys?
    | throw (.internalState "missing client application keys")
  pure {
    state with
    phase := .connected
    handshakeBuffered := ByteArray.empty
    readKeys? := some clientApplicationKeys
    clientApplicationKeys? := none
    expectedClientFinished? := none
  }

/-! ## Post-handshake and alerts (role-symmetric). -/

private def emitCloseNotify (state : State) : Except Error (State × ByteArray) := do
  if state.localClosed then
    pure (state, ByteArray.empty)
  else
    let writeKeys ← requireWriteKeys state
    let alert := (ByteArray.empty.push 1).push 0
    let (writeKeys, wireBytes) ← liftRecord (Record.«seal» writeKeys .alert alert)
    pure ({ state with writeKeys? := some writeKeys, localClosed := true }, wireBytes)

private def processAlert (state : State) (fragment : ByteArray) (duringHandshake : Bool) :
    Except Error (State × ByteArray) := do
  unless fragment.size == 2 do
    throw (.invalidAlertLength fragment.size)
  let level := fragment.get! 0
  let description := fragment.get! 1
  unless level == 1 || level == 2 do
    throw (.invalidAlertLevel level)
  if description == 0 then
    if duringHandshake then
      throw .peerClosedDuringHandshake
    else
      emitCloseNotify { state with peerClosed := true }
  else
    throw (.peerAlert level description)

private def sendKeyUpdateResponse (state : State) : Except Error (State × ByteArray) := do
  let message ← liftHandshake (Handshake.encodeKeyUpdate .updateNotRequested)
  let writeKeys ← requireWriteKeys state
  let (advancedKeys, wireBytes) ← liftRecord (Record.«seal» writeKeys .handshake message.encoded)
  let updatedKeys ← liftRecord advancedKeys.update
  pure ({ state with writeKeys? := some updatedKeys }, wireBytes)

private def acceptKeyUpdate (state : State) (message : Handshake.Message) :
    Except Error (State × ByteArray) := do
  let update ← liftHandshake (Handshake.parseKeyUpdate message)
  let readKeys ← requireReadKeys state
  let updatedReadKeys ← liftRecord readKeys.update
  let state := { state with readKeys? := some updatedReadKeys }
  match update.request with
  | .updateNotRequested => pure (state, ByteArray.empty)
  | .updateRequested => sendKeyUpdateResponse state

private partial def processHandshakeBuffer (state : State) :
    Except Error (State × ByteArray) := do
  let some (message, rest) ← takeHandshake? state.handshakeBuffered
    | pure (state, ByteArray.empty)
  let state := { state with handshakeBuffered := rest }
  match state.phase with
  | .waitingClientHello =>
      unless message.msgType == Handshake.clientHelloType do
        throw (.unexpectedHandshake state.phase message.msgType)
      unless rest.isEmpty do
        throw .interleavedHandshake
      acceptClientHello { state with handshakeBuffered := ByteArray.empty } message
  | .waitingSecondClientHello =>
      unless message.msgType == Handshake.clientHelloType do
        throw (.unexpectedHandshake state.phase message.msgType)
      unless rest.isEmpty do
        throw .interleavedHandshake
      acceptClientHello { state with handshakeBuffered := ByteArray.empty } message
  | .waitingClientFinished =>
      unless message.msgType == Handshake.finishedType do
        throw (.unexpectedHandshake state.phase message.msgType)
      unless rest.isEmpty do
        throw .interleavedHandshake
      let state ← acceptClientFinished state message
      pure (state, ByteArray.empty)
  | .connected =>
      if message.msgType == Handshake.keyUpdateType then
        let (state, wireBytes) ← acceptKeyUpdate state message
        let (state, more) ← processHandshakeBuffer state
        pure (state, wireBytes ++ more)
      else
        throw (.unexpectedHandshake state.phase message.msgType)

private def processProtectedRecord (state : State) (record : Record.RawRecord) :
    Except Error (State × ByteArray × ByteArray) := do
  let readKeys ← requireReadKeys state
  let (readKeys, plaintext) ← liftRecord (Record.«open» readKeys record)
  let state := { state with readKeys? := some readKeys }
  match plaintext.contentType with
  | .applicationData =>
      unless state.phase == .connected do
        throw (.unexpectedRecord state.phase plaintext.contentType)
      if state.peerClosed then
        throw .connectionClosed
      unless state.handshakeBuffered.isEmpty do
        throw .interleavedHandshake
      pure (state, plaintext.fragment, ByteArray.empty)
  | .handshake =>
      if plaintext.fragment.isEmpty then
        throw (.unexpectedRecord state.phase .handshake)
      let state := { state with handshakeBuffered := state.handshakeBuffered ++ plaintext.fragment }
      let (state, wireBytes) ← processHandshakeBuffer state
      pure (state, ByteArray.empty, wireBytes)
  | .alert =>
      unless state.handshakeBuffered.isEmpty do
        throw .interleavedHandshake
      let duringHandshake := state.phase != .connected
      let (state, wireBytes) ← processAlert state plaintext.fragment duringHandshake
      pure (state, ByteArray.empty, wireBytes)
  | .changeCipherSpec =>
      throw (.unexpectedRecord state.phase plaintext.contentType)

private def feedPlaintextClientHello (state : State) (fragment : ByteArray) :
    Except Error (State × ByteArray) := do
  if fragment.isEmpty then
    throw (.unexpectedRecord state.phase .handshake)
  let state := { state with handshakeBuffered := state.handshakeBuffered ++ fragment }
  processHandshakeBuffer state

private def processRecord (state : State) (record : Record.RawRecord) :
    Except Error (State × ByteArray × ByteArray) := do
  match state.phase with
  | .waitingClientHello =>
      match record.contentType with
      | .handshake =>
          let (state, wireBytes) ← feedPlaintextClientHello state record.fragment
          pure (state, ByteArray.empty, wireBytes)
      | .changeCipherSpec =>
          -- Compatibility CCS is only in-window after a *complete* CH1. If
          -- CH1 and CCS are coalesced, processing CH1 advances the phase
          -- before this record is visited. Reaching this branch therefore
          -- means CCS preceded or interrupted CH1.
          throw (.unexpectedRecord state.phase record.contentType)
      | .alert =>
          unless state.handshakeBuffered.isEmpty do
            throw .interleavedHandshake
          let (state, wireBytes) ← processAlert state record.fragment true
          pure (state, ByteArray.empty, wireBytes)
      | contentType => throw (.unexpectedRecord state.phase contentType)
  | .waitingSecondClientHello =>
      match record.contentType with
      | .handshake =>
          let (state, wireBytes) ← feedPlaintextClientHello state record.fragment
          pure (state, ByteArray.empty, wireBytes)
      | .changeCipherSpec =>
          unless state.handshakeBuffered.isEmpty do
            throw .interleavedHandshake
          unless validCompatibilityChangeCipherSpec record.fragment do
            throw .invalidCompatibilityChangeCipherSpec
          pure (state, ByteArray.empty, ByteArray.empty)
      | .alert =>
          unless state.handshakeBuffered.isEmpty do
            throw .interleavedHandshake
          let (state, wireBytes) ← processAlert state record.fragment true
          pure (state, ByteArray.empty, wireBytes)
      | contentType => throw (.unexpectedRecord state.phase contentType)
  | .waitingClientFinished =>
      match record.contentType with
      | .changeCipherSpec =>
          unless state.handshakeBuffered.isEmpty do
            throw .interleavedHandshake
          unless validCompatibilityChangeCipherSpec record.fragment do
            throw .invalidCompatibilityChangeCipherSpec
          pure (state, ByteArray.empty, ByteArray.empty)
      | .applicationData => processProtectedRecord state record
      | contentType => throw (.unexpectedRecord state.phase contentType)
  | .connected =>
      match record.contentType with
      | .applicationData => processProtectedRecord state record
      | contentType => throw (.unexpectedRecord state.phase contentType)

/-- Incrementally consume transport bytes, retaining the latest advanced state on
failure so an I/O shell can seal a fatal alert under the correct epoch. -/
def feedWithFailure (initial : State) (chunk : ByteArray) : Except Failure Output := do
  if initial.closed && !chunk.isEmpty then
    throw { state := initial, error := .connectionClosed }
  let (decoder, records) ←
    match liftRecord (initial.decoder.feed chunk) with
    | .ok decoded => pure decoded
    | .error error => throw { state := initial, error }
  let mut state := { initial with decoder }
  let mut plaintext := ByteArray.empty
  let mut wireBytes := ByteArray.empty
  for record in records do
    let (next, cleartext, outbound) ←
      match processRecord state record with
      | .ok output => pure output
      | .error error => throw { state, error }
    state := next
    plaintext := plaintext ++ cleartext
    wireBytes := wireBytes ++ outbound
  pure { state, wireBytes, plaintext }

/-- Consume transport bytes. `wireBytes` carries the server flight (in response to
ClientHello) plus any KeyUpdate/close_notify; `plaintext` is decrypted
application data once connected. -/
def feed (state : State) (chunk : ByteArray) : Except Error Output :=
  (feedWithFailure state chunk).mapError Failure.error

/-! ## Application data. -/

private def sealChunks (keys : Record.TrafficKeys) (plaintext : ByteArray)
    (offset : Nat) (records : Array ByteArray) :
    Except Error (Record.TrafficKeys × Array ByteArray) :=
  if plaintext.size ≤ offset then
    .ok (keys, records)
  else
    let stop := min plaintext.size (offset + Record.maxPlaintextLength)
    let chunk := plaintext.extract offset stop
    match liftRecord (Record.«seal» keys .applicationData chunk) with
    | .error e => .error e
    | .ok (keys, wire) => sealChunks keys plaintext stop (records.push wire)
  termination_by plaintext.size - offset
  decreasing_by
    have : 0 < Record.maxPlaintextLength := by decide
    omega

private def concatByteArrays (parts : Array ByteArray) : ByteArray := Id.run do
  let total := parts.foldl (fun size part => size + part.size) 0
  let mut out := ByteArray.mk (Array.replicate total 0)
  let mut offset := 0
  for part in parts do
    out := part.copySlice 0 out offset part.size
    offset := offset + part.size
  return out

/-- Protect application bytes, splitting at TLS's 2^14-byte record limit. -/
def sealApplication (state : State) (plaintext : ByteArray) : Except Error Output := do
  unless state.phase == .connected do
    throw (.notConnected state.phase)
  if state.localClosed || state.peerClosed then
    throw .connectionClosed
  if plaintext.isEmpty then
    pure { state }
  else
    let writeKeys ← requireWriteKeys state
    let (writeKeys, records) ← sealChunks writeKeys plaintext 0 #[]
    pure { state := { state with writeKeys? := some writeKeys }, wireBytes := concatByteArrays records }

/-- Send `close_notify` under the current write keys. Idempotent. -/
def closeNotify (state : State) : Except Error Output := do
  unless state.phase == .connected do
    throw (.notConnected state.phase)
  let (state, wireBytes) ← emitCloseNotify state
  pure { state, wireBytes }

/-- Emit a fatal, level-2 alert. Before handshake write keys exist (including
after HRR), the alert is a TLSPlaintext record; after ServerHello it is sealed
under the current write epoch. Callers must discard the connection afterwards. -/
def sealFatalAlert (state : State) (description : UInt8) : Except Error Output := do
  let fragment := ByteArray.mk #[2, description]
  match state.writeKeys? with
  | some writeKeys =>
      let (writeKeys, wireBytes) ← liftRecord (Record.«seal» writeKeys .alert fragment)
      pure {
        state := { state with writeKeys? := some writeKeys, localClosed := true }
        wireBytes
      }
  | none =>
      unless state.phase == .waitingClientHello ||
          state.phase == .waitingSecondClientHello do
        throw (.internalState "missing write keys for fatal alert")
      let wireBytes ← liftRecord (Record.encodePlaintext .alert fragment)
      pure { state := { state with localClosed := true }, wireBytes }

end Server
end Tls
