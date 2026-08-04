module

public import HaclStar.Curve25519
public import HaclStar.Hmac
public import HaclStar.P256
public import HaclStar.Sha256
public import Tls.Handshake
public import Tls.Record
public import TLS13.KeySchedule
public import TLS13.X509

public section

namespace Tls
namespace Client

/-!
A minimal, pure TLS 1.3 client handshake and record machine.

The engine deliberately performs no I/O and obtains no entropy itself. A
caller supplies the ClientHello random, legacy session id, and ephemeral
private scalars to `start`, writes the returned `wireBytes`, and subsequently
passes transport chunks to `feed`. Every server CertificateVerify is checked
cryptographically against the leaf certificate before the handshake can
complete. Certificate-chain and hostname validation remain separate policy
steps for verification modes.
-/

/-- Fresh values and policy used to construct a TLS connection. -/
structure Config where
  clientRandom : ByteArray
  x25519Private : ByteArray
  /-- An independent P-256 private scalar. When present, the ClientHello sends
  both X25519 and P-256 shares so pre-18 PostgreSQL defaults need no HRR. -/
  p256Private : Option ByteArray := none
  legacySessionId : ByteArray := ByteArray.empty
  serverName : Option String := none
  /-- ALPN protocols to offer, in preference order (empty omits ALPN). -/
  alpnProtocols : Array String := #[]
  deriving Inhabited

/-- Strict server-handshake ordering for the no-PSK, no-client-auth flow. -/
inductive Phase where
  | waitingServerHello
  | waitingEncryptedExtensions
  | waitingCertificate
  | waitingCertificateVerify
  | waitingServerFinished
  | connected
  deriving Repr, BEq, DecidableEq, Inhabited

namespace Phase

def render : Phase → String
  | .waitingServerHello => "ServerHello"
  | .waitingEncryptedExtensions => "EncryptedExtensions"
  | .waitingCertificate => "Certificate"
  | .waitingCertificateVerify => "CertificateVerify"
  | .waitingServerFinished => "Finished"
  | .connected => "post-handshake message"

end Phase

/-- Errors are protocol-fatal: the caller must discard the state supplied to
the operation that returned the error. -/
inductive Error where
  | invalidEntropy (field : String) (expected actual : Nat)
  | invalidPrivateKey (group : Handshake.NamedGroup)
  | handshakeCodec (message : String)
  | recordLayer (error : Record.Error)
  | keyExchangeFailed
  | unexpectedRecord (phase : Phase) (contentType : Record.ContentType)
  | unexpectedHandshake (phase : Phase) (actual : UInt8)
  | invalidCompatibilityChangeCipherSpec
  | interleavedHandshake
  | invalidAlertLength (actual : Nat)
  | invalidAlertLevel (actual : UInt8)
  | peerAlert (level description : UInt8)
  | peerClosedDuringHandshake
  | badCertificate (message : String)
  | illegalParameter (message : String)
  | certificateVerifySchemeMismatch (algorithm : UInt16)
  | certificateVerifyFailed
  | finishedMismatch
  | trailingHandshakeAfterFinished
  | notConnected (phase : Phase)
  | connectionClosed
  | internalState (message : String)
  deriving Repr, Inhabited

private def contentTypeName : Record.ContentType → String
  | .changeCipherSpec => "change_cipher_spec"
  | .alert => "alert"
  | .handshake => "handshake"
  | .applicationData => "application_data"

namespace Error

def render : Error → String
  | .invalidEntropy field expected actual =>
      s!"TLS {field} must be {expected} bytes, got {actual}"
  | .invalidPrivateKey group =>
      s!"TLS {repr group} private scalar is outside the valid group order"
  | .handshakeCodec message => s!"TLS handshake codec: {message}"
  | .recordLayer error => s!"TLS record layer: {error}"
  | .keyExchangeFailed => "TLS key exchange rejected the server public key"
  | .unexpectedRecord phase contentType =>
      s!"unexpected TLS {contentTypeName contentType} record while waiting for {phase.render}"
  | .unexpectedHandshake phase actual =>
      s!"unexpected TLS handshake message {actual} while waiting for {phase.render}"
  | .invalidCompatibilityChangeCipherSpec =>
      "invalid TLS 1.3 compatibility ChangeCipherSpec"
  | .interleavedHandshake =>
      "TLS handshake fragments were interleaved with another content type"
  | .invalidAlertLength actual =>
      s!"TLS alert payload must be exactly two bytes, got {actual}"
  | .invalidAlertLevel actual => s!"invalid TLS alert level {actual}"
  | .peerAlert level description =>
      s!"TLS peer sent alert level {level}, description {description}"
  | .peerClosedDuringHandshake => "TLS peer sent close_notify during the handshake"
  | .badCertificate message => s!"TLS bad_certificate: {message}"
  | .illegalParameter message => s!"TLS illegal_parameter: {message}"
  | .certificateVerifySchemeMismatch algorithm =>
      s!"TLS illegal_parameter: CertificateVerify scheme {algorithm} \
        is inconsistent with the leaf public key"
  | .certificateVerifyFailed =>
      "TLS decrypt_error: server CertificateVerify signature verification failed"
  | .finishedMismatch => "TLS server Finished verification failed"
  | .trailingHandshakeAfterFinished =>
      "TLS server Finished shared a record with data protected under different keys"
  | .notConnected phase =>
      s!"TLS connection is not ready for application data (waiting for {phase.render})"
  | .connectionClosed => "TLS connection is closed"
  | .internalState message => s!"invalid internal TLS client state: {message}"

/-- Fatal TLS alert description associated with a locally detected handshake
failure. The I/O shell seals and sends this alert before discarding the
connection when handshake write keys are available. -/
def fatalAlertDescription? : Error → Option UInt8
  | .badCertificate _ => some 42
  | .illegalParameter _ => some 47
  | .certificateVerifySchemeMismatch _ => some 47
  | .certificateVerifyFailed => some 51
  | .finishedMismatch => some 51
  | .handshakeCodec _ => some 50
  | .unexpectedHandshake _ _ => some 10
  | .keyExchangeFailed => some 47
  | _ => none

end Error

instance : ToString Error := ⟨Error.render⟩

/--
Pure connection state. Traffic keys and ephemeral private values are kept
inside the state but the structure intentionally has no `Repr` instance, so
ordinary debugging cannot accidentally print them.
-/
structure State where
  phase : Phase
  decoder : Record.Decoder := {}
  handshakeBuffered : ByteArray := ByteArray.empty
  transcript : ByteArray := ByteArray.empty
  x25519Private : ByteArray
  p256Private : Option ByteArray := none
  legacySessionId : ByteArray
  /-- Exact cipher suites advertised by this connection's ClientHello. The
  ServerHello selection is checked against this list rather than against a
  hard-coded singleton, so adding suites does not weaken negotiation checks. -/
  offeredCipherSuites : Array UInt16 := #[]
  /-- Key-share groups actually sent in this connection's ClientHello. -/
  offeredKeyShareGroups : Array Handshake.NamedGroup := #[]
  /-- ALPN protocol IDs advertised by this connection's ClientHello. -/
  offeredAlpnProtocols : Array String := #[]
  handshakeSecret? : Option ByteArray := none
  clientHandshakeTrafficSecret? : Option ByteArray := none
  serverHandshakeTrafficSecret? : Option ByteArray := none
  readKeys? : Option Record.TrafficKeys := none
  writeKeys? : Option Record.TrafficKeys := none
  leafCertificate? : Option ByteArray := none
  /-- The peer's Certificate-list entries, strict-parsed once from the exact
  handshake bytes and retained in wire order (leaf first). Post-handshake
  verification policy consumes these values without decoding DER again. -/
  peerCertificates : Array TLS13.X509.Certificate := #[]
  leafPublicKey? : Option TLS13.X509.SubjectPublicKeyInfo := none
  /-- The ALPN protocol the server selected, once EncryptedExtensions is seen. -/
  alpnSelected : Option String := none
  localClosed : Bool := false
  peerClosed : Bool := false
  deriving Inhabited

namespace State

def connected (state : State) : Bool :=
  state.phase == .connected

/-- Both TLS write directions have exchanged `close_notify`. -/
def closed (state : State) : Bool :=
  state.localClosed && state.peerClosed

end State

/-- Bytes and state produced by every engine operation. -/
structure Output where
  state : State
  wireBytes : ByteArray := ByteArray.empty
  plaintext : ByteArray := ByteArray.empty
  deriving Inhabited

/-- A failed incremental feed together with the latest state completed before
the failing record. Keeping the state lets an I/O shell use the correct write
traffic epoch for a fatal alert, even when one transport chunk coalesces
ServerHello with the encrypted server flight. The decoder may already have
consumed the failing record, so this state is only for sealing an alert and
must not be resumed. -/
structure Failure where
  state : State
  error : Error

private def liftHandshake {α : Type} (result : Except String α) : Except Error α :=
  match result with
  | .ok value => .ok value
  | .error message => .error (.handshakeCodec message)

private def liftRecord {α : Type} (result : Except Record.Error α) : Except Error α :=
  match result with
  | .ok value => .ok value
  | .error error => .error (.recordLayer error)

private def requireReadKeys (state : State) : Except Error Record.TrafficKeys :=
  match state.readKeys? with
  | some keys => pure keys
  | none => throw (.internalState "missing read traffic keys")

private def requireWriteKeys (state : State) : Except Error Record.TrafficKeys :=
  match state.writeKeys? with
  | some keys => pure keys
  | none => throw (.internalState "missing write traffic keys")

private def requireHandshakeSecret (state : State) : Except Error ByteArray :=
  match state.handshakeSecret? with
  | some secret => pure secret
  | none => throw (.internalState "missing handshake secret")

private def requireClientHandshakeTrafficSecret (state : State) : Except Error ByteArray :=
  match state.clientHandshakeTrafficSecret? with
  | some secret => pure secret
  | none => throw (.internalState "missing client handshake traffic secret")

private def requireServerHandshakeTrafficSecret (state : State) : Except Error ByteArray :=
  match state.serverHandshakeTrafficSecret? with
  | some secret => pure secret
  | none => throw (.internalState "missing server handshake traffic secret")

private def requireLeafPublicKey (state : State) :
    Except Error TLS13.X509.SubjectPublicKeyInfo :=
  match state.leafPublicKey? with
  | some publicKey => pure publicKey
  | none => throw (.internalState "missing parsed leaf public key")

private def decodeCertificate (der : ByteArray) :
    Except Error TLS13.X509.Certificate :=
  match TLS13.X509.Certificate.decode der with
  | .ok certificate => pure certificate
  | .error message => throw (.badCertificate message)

private def certificateVerifyScheme? (algorithm : UInt16) :
    Option TLS13.X509.Signature.CertificateVerifyScheme :=
  if algorithm == Handshake.ecdsaSecp256r1Sha256 then
    some .ecdsaSecp256r1Sha256
  else if algorithm == Handshake.ed25519 then
    some .ed25519
  else if algorithm == Handshake.rsaPssRsaeSha256 then
    some .rsaPssRsaeSha256
  else if algorithm == Handshake.rsaPssPssSha256 then
    some .rsaPssPssSha256
  else
    none

private theorem liftHandshake_ok {α : Type} {result : Except String α}
    {value : α} (h : liftHandshake result = .ok value) : result = .ok value := by
  unfold liftHandshake at h
  cases result with
  | error e => simp at h
  | ok b => simpa [Except.mapError] using h

/-- Return one complete framed handshake message without treating an
incomplete prefix as a codec error. The reassembly itself, and its laws, live
in `Tls.Handshake`; this only adapts the error type. -/
private def takeHandshake? (buffered : ByteArray) :
    Except Error (Option (Handshake.Message × ByteArray)) :=
  liftHandshake (Handshake.takeMessage? buffered)

/-- A successful `takeHandshake?` consumes the four-byte message header plus
the body, strictly shrinking the buffer. -/
private theorem takeHandshake?_size {buffered rest : ByteArray}
    {message : Handshake.Message}
    (h : takeHandshake? buffered = .ok (some (message, rest))) :
    rest.size < buffered.size :=
  Handshake.takeMessage?_size (liftHandshake_ok h)

/-- A successful `takeHandshake?` conserves bytes: the decoded message's
retained exact encoding followed by the returned remainder is the input
buffer — the handshake-layer mirror of the record-framing conservation law
(`Tls.Record.Laws.decodeStep_conservation`). -/
private theorem takeHandshake?_conservation {buffered rest : ByteArray}
    {message : Handshake.Message}
    (h : takeHandshake? buffered = .ok (some (message, rest))) :
    message.encoded ++ rest = buffered :=
  Handshake.takeMessage?_conservation (liftHandshake_ok h)

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

private def emptyTranscriptHash : ByteArray :=
  HaclStar.sha256 ByteArray.empty

/--
Create a ClientHello and initial state.  No entropy is generated here:
`clientRandom` and each supplied private key must be exactly 32 bytes, while
the legacy session id follows TLS's zero-to-32-byte vector constraint.
-/
def start (config : Config) : Except Error Output := do
  unless config.clientRandom.size == 32 do
    throw (.invalidEntropy "ClientHello random" 32 config.clientRandom.size)
  unless config.x25519Private.size == 32 do
    throw (.invalidEntropy "X25519 private key" 32 config.x25519Private.size)
  if let some privateKey := config.p256Private then
    unless privateKey.size == 32 do
      throw (.invalidEntropy "P-256 private key" 32 privateKey.size)
  if config.legacySessionId.size > 32 then
    throw (.invalidEntropy "legacy session id (maximum)" 32 config.legacySessionId.size)

  let publicKey := HaclStar.X25519.base config.x25519Private
  unless publicKey.size == 32 do
    throw (.internalState s!"X25519 returned a {publicKey.size}-byte public key")
  let p256PublicKey ← match config.p256Private with
    | none => pure none
    | some privateKey =>
      let some publicKey := HaclStar.P256.publicKey privateKey
        | throw (.invalidPrivateKey .secp256r1)
      unless publicKey.size == 65 && publicKey.get! 0 == 4 do
        throw (.internalState "P-256 returned a malformed public key")
      pure (some publicKey)
  let hello ← liftHandshake <| Handshake.encodeClientHello {
    random := config.clientRandom
    x25519PublicKey := publicKey
    p256PublicKey
    serverName := config.serverName
    legacySessionId := config.legacySessionId
    alpnProtocols := config.alpnProtocols
  }
  let wireBytes ← liftRecord <| Record.encodePlaintext .handshake hello.encoded
  let state : State := {
    phase := .waitingServerHello
    transcript := hello.encoded
    x25519Private := config.x25519Private
    p256Private := config.p256Private
    legacySessionId := config.legacySessionId
    offeredCipherSuites := #[Handshake.tlsChaCha20Poly1305Sha256]
    offeredKeyShareGroups :=
      if config.p256Private.isSome then
        #[.x25519, .secp256r1]
      else
        #[.x25519]
    offeredAlpnProtocols := config.alpnProtocols
  }
  pure { state, wireBytes }

private def acceptServerHello (state : State) (message : Handshake.Message) :
    Except Error State := do
  unless state.phase == .waitingServerHello do
    throw (.unexpectedHandshake state.phase message.msgType)
  let hello ← liftHandshake (Handshake.parseServerHello message)
  unless hello.legacySessionIdEcho == state.legacySessionId do
    throw (.illegalParameter
      "ServerHello legacy_session_id_echo does not match ClientHello")
  unless state.offeredCipherSuites.contains hello.cipherSuite do
    throw (.illegalParameter
      s!"server selected cipher suite {hello.cipherSuite} that the client did not offer")
  unless state.offeredKeyShareGroups.contains hello.selectedGroup do
    throw (.illegalParameter
      s!"server selected key-share group {hello.selectedGroup.toUInt16} \
        that the client did not offer")
  let sharedSecret ← match hello.selectedGroup with
    | .x25519 =>
      let some sharedSecret :=
          HaclStar.X25519.ecdh state.x25519Private hello.keyExchange
        | throw .keyExchangeFailed
      pure sharedSecret
    | .secp256r1 =>
      let some privateKey := state.p256Private
        | throw (.illegalParameter "server selected P-256 without a client key share")
      let some sharedSecret := HaclStar.P256.ecdh privateKey hello.keyExchange
        | throw .keyExchangeFailed
      pure sharedSecret
  unless sharedSecret.size == TLS13.KeySchedule.hashLen do
    throw (.internalState
      s!"ECDHE returned a {sharedSecret.size}-byte shared secret")

  let earlySecret := TLS13.KeySchedule.earlySecret
  let handshakeSecret :=
    TLS13.KeySchedule.handshakeSecret earlySecret sharedSecret emptyTranscriptHash
  let transcript := state.transcript ++ message.encoded
  let transcriptHash := HaclStar.sha256 transcript
  let clientTrafficSecret :=
    TLS13.KeySchedule.deriveSecret handshakeSecret "c hs traffic" transcriptHash
  let serverTrafficSecret :=
    TLS13.KeySchedule.deriveSecret handshakeSecret "s hs traffic" transcriptHash
  let writeKeys ← liftRecord (Record.deriveTrafficKeys clientTrafficSecret)
  let readKeys ← liftRecord (Record.deriveTrafficKeys serverTrafficSecret)
  pure {
    state with
    phase := .waitingEncryptedExtensions
    handshakeBuffered := ByteArray.empty
    transcript
    handshakeSecret? := some handshakeSecret
    clientHandshakeTrafficSecret? := some clientTrafficSecret
    serverHandshakeTrafficSecret? := some serverTrafficSecret
    readKeys? := some readKeys
    writeKeys? := some writeKeys
  }

private def feedPlaintextHandshake (state : State) (fragment : ByteArray) :
    Except Error State := do
  let buffered := state.handshakeBuffered ++ fragment
  let some (message, rest) ← takeHandshake? buffered
    | pure { state with handshakeBuffered := buffered }
  unless rest.isEmpty do
    throw (.unexpectedHandshake .waitingServerHello (rest.get! 0))
  acceptServerHello { state with handshakeBuffered := ByteArray.empty } message

private def appendTranscript (state : State) (message : Handshake.Message) : State :=
  { state with transcript := state.transcript ++ message.encoded }

private def completeServerHandshake (state : State) (message : Handshake.Message) :
    Except Error (State × ByteArray) := do
  let finished ← liftHandshake (Handshake.parseFinished message)
  let serverTrafficSecret ← requireServerHandshakeTrafficSecret state
  let expected := finishedVerifyData serverTrafficSecret (HaclStar.sha256 state.transcript)
  unless constantTimeEq expected finished.verifyData do
    throw .finishedMismatch

  let transcriptThroughServerFinished := state.transcript ++ message.encoded
  let transcriptHash := HaclStar.sha256 transcriptThroughServerFinished
  let handshakeSecret ← requireHandshakeSecret state
  let masterSecret := TLS13.KeySchedule.masterSecret handshakeSecret emptyTranscriptHash
  let clientApplicationSecret :=
    TLS13.KeySchedule.deriveSecret masterSecret "c ap traffic" transcriptHash
  let serverApplicationSecret :=
    TLS13.KeySchedule.deriveSecret masterSecret "s ap traffic" transcriptHash
  let clientApplicationKeys ← liftRecord (Record.deriveTrafficKeys clientApplicationSecret)
  let serverApplicationKeys ← liftRecord (Record.deriveTrafficKeys serverApplicationSecret)

  let clientHandshakeSecret ← requireClientHandshakeTrafficSecret state
  let clientVerifyData := finishedVerifyData clientHandshakeSecret transcriptHash
  let clientFinished ← liftHandshake (Handshake.encodeFinished clientVerifyData)
  let handshakeWriteKeys ← requireWriteKeys state
  let (_, finishedWireBytes) ←
    liftRecord (Record.«seal» handshakeWriteKeys .handshake clientFinished.encoded)
  -- A nonempty legacy session id opts into RFC 8446 appendix D.4's
  -- middlebox-compatibility mode.  The dummy CCS is deliberately plaintext
  -- and immediately precedes the client's encrypted second flight.
  let compatibilityWireBytes ←
    if state.legacySessionId.isEmpty then
      pure ByteArray.empty
    else
      liftRecord (Record.encodePlaintext .changeCipherSpec (ByteArray.empty.push 1))
  let wireBytes := compatibilityWireBytes ++ finishedWireBytes
  pure ({
    state with
    phase := .connected
    handshakeBuffered := ByteArray.empty
    -- The application traffic secrets are now independent of these handshake
    -- inputs. Do not retain obsolete private scalars, handshake traffic
    -- secrets, or a potentially large certificate transcript for the life of
    -- the PostgreSQL connection.
    transcript := ByteArray.empty
    x25519Private := ByteArray.empty
    p256Private := none
    legacySessionId := ByteArray.empty
    offeredCipherSuites := #[]
    offeredKeyShareGroups := #[]
    offeredAlpnProtocols := #[]
    handshakeSecret? := none
    clientHandshakeTrafficSecret? := none
    serverHandshakeTrafficSecret? := none
    readKeys? := some serverApplicationKeys
    writeKeys? := some clientApplicationKeys
  }, wireBytes)

/-- Seal a fatal, level-2 TLS alert under the current write traffic keys.
Callers must discard the connection after sending the returned bytes. -/
def sealFatalAlert (state : State) (description : UInt8) :
    Except Error Output := do
  let writeKeys ← requireWriteKeys state
  let fragment := ByteArray.mk #[2, description]
  let (writeKeys, wireBytes) ←
    liftRecord (Record.«seal» writeKeys .alert fragment)
  pure {
    state := { state with writeKeys? := some writeKeys, localClosed := true }
    wireBytes
  }

private def sendKeyUpdateResponse (state : State) : Except Error (State × ByteArray) := do
  let message ← liftHandshake <|
    Handshake.encodeKeyUpdate .updateNotRequested
  let writeKeys ← requireWriteKeys state
  let (advancedKeys, wireBytes) ←
    liftRecord (Record.«seal» writeKeys .handshake message.encoded)
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

/-! Reduction lemmas used to prove that key updates and transcript appends
leave the handshake buffer untouched, which bounds the
`processHandshakeBuffer` recursion. -/

private theorem except_bind_ok {ε α β : Type} (a : α) (f : α → Except ε β) :
    (Except.ok a >>= f) = f a := rfl
private theorem except_bind_error {ε α β : Type} (e : ε)
    (f : α → Except ε β) :
    ((Except.error e : Except ε α) >>= f) = Except.error e := rfl
private theorem except_pure {ε α : Type} (a : α) :
    (pure a : Except ε α) = Except.ok a := rfl

private theorem appendTranscript_buffered (state : State)
    (message : Handshake.Message) :
    (appendTranscript state message).handshakeBuffered =
      state.handshakeBuffered := rfl

private theorem sendKeyUpdateResponse_buffered {state next : State}
    {wireBytes : ByteArray}
    (h : sendKeyUpdateResponse state = .ok (next, wireBytes)) :
    next.handshakeBuffered = state.handshakeBuffered := by
  unfold sendKeyUpdateResponse at h
  cases h1 : liftHandshake (Handshake.encodeKeyUpdate .updateNotRequested) with
  | error e => rw [h1, except_bind_error] at h; cases h
  | ok message =>
      rw [h1, except_bind_ok] at h
      cases h2 : requireWriteKeys state with
      | error e => rw [h2, except_bind_error] at h; cases h
      | ok writeKeys =>
          rw [h2, except_bind_ok] at h
          cases h3 : liftRecord
              (Record.«seal» writeKeys .handshake message.encoded) with
          | error e => rw [h3, except_bind_error] at h; cases h
          | ok sealed =>
              obtain ⟨advancedKeys, sealedBytes⟩ := sealed
              rw [h3, except_bind_ok] at h
              cases h4 : liftRecord advancedKeys.update with
              | error e =>
                  simp only [h4, except_bind_error] at h
                  cases h
              | ok updatedKeys =>
                  simp only [h4, except_bind_ok, except_pure,
                    Except.ok.injEq, Prod.mk.injEq] at h
                  rw [← h.1]

private theorem acceptKeyUpdate_buffered {state next : State}
    {message : Handshake.Message} {wireBytes : ByteArray}
    (h : acceptKeyUpdate state message = .ok (next, wireBytes)) :
    next.handshakeBuffered = state.handshakeBuffered := by
  unfold acceptKeyUpdate at h
  cases h1 : liftHandshake (Handshake.parseKeyUpdate message) with
  | error e => rw [h1, except_bind_error] at h; cases h
  | ok update =>
      rw [h1, except_bind_ok] at h
      cases h2 : requireReadKeys state with
      | error e => rw [h2, except_bind_error] at h; cases h
      | ok readKeys =>
          rw [h2, except_bind_ok] at h
          cases h3 : liftRecord readKeys.update with
          | error e => rw [h3, except_bind_error] at h; cases h
          | ok updatedReadKeys =>
              rw [h3, except_bind_ok] at h
              cases hreq : update.request with
              | updateNotRequested =>
                  simp only [hreq, except_pure, Except.ok.injEq,
                    Prod.mk.injEq] at h
                  rw [← h.1]
              | updateRequested =>
                  simp only [hreq] at h
                  rw [sendKeyUpdateResponse_buffered h]

private def processHandshakeBuffer (state : State) :
    Except Error (State × ByteArray) :=
  match htake : takeHandshake? state.handshakeBuffered with
  | .error e => .error e
  | .ok none => .ok (state, ByteArray.empty)
  | .ok (some (message, rest)) =>
    have hrest : rest.size < state.handshakeBuffered.size :=
      takeHandshake?_size htake
    let state' := { state with handshakeBuffered := rest }
    match state'.phase with
    | .waitingServerHello =>
        .error (.unexpectedHandshake state'.phase message.msgType)
    | .waitingEncryptedExtensions => do
        unless message.msgType == Handshake.encryptedExtensionsType do
          throw (.unexpectedHandshake state'.phase message.msgType)
        let encryptedExtensions ← liftHandshake (Handshake.parseEncryptedExtensions message)
        let alpnSelected ← liftHandshake (Handshake.selectedAlpnProtocol encryptedExtensions)
        if let some protocol := alpnSelected then
          unless state'.offeredAlpnProtocols.contains protocol do
            throw (.illegalParameter
              s!"server selected ALPN protocol {protocol} that the client did not offer")
        processHandshakeBuffer (appendTranscript
          { state' with phase := .waitingCertificate, alpnSelected } message)
    | .waitingCertificate => do
        unless message.msgType == Handshake.certificateType do
          throw (.unexpectedHandshake state'.phase message.msgType)
        let certificate ← liftHandshake (Handshake.parseCertificate message)
        let parsedCertificates ← certificate.entries.mapM fun entry =>
          decodeCertificate entry.der
        let parsedLeaf := parsedCertificates[0]!
        processHandshakeBuffer (appendTranscript {
          state' with
          phase := .waitingCertificateVerify
          leafCertificate? := some certificate.leafDer
          peerCertificates := parsedCertificates
          leafPublicKey? := some parsedLeaf.tbsCertificate.subjectPublicKeyInfo
        } message)
    | .waitingCertificateVerify => do
        unless message.msgType == Handshake.certificateVerifyType do
          throw (.unexpectedHandshake state'.phase message.msgType)
        let certificateVerify ←
          liftHandshake (Handshake.parseCertificateVerify message)
        let some scheme := certificateVerifyScheme? certificateVerify.algorithm
          | throw (.certificateVerifySchemeMismatch certificateVerify.algorithm)
        let publicKey ← requireLeafPublicKey state'
        unless TLS13.X509.Signature.certificateVerifySchemeCompatible
            scheme publicKey do
          throw (.certificateVerifySchemeMismatch certificateVerify.algorithm)
        let transcriptHash := HaclStar.sha256 state'.transcript
        unless TLS13.X509.Signature.verifyServerCertificateVerify
            scheme publicKey transcriptHash certificateVerify.signature do
          throw .certificateVerifyFailed
        processHandshakeBuffer (appendTranscript {
          state' with
          phase := .waitingServerFinished
          leafPublicKey? := none
        } message)
    | .waitingServerFinished => do
        unless message.msgType == Handshake.finishedType do
          throw (.unexpectedHandshake state'.phase message.msgType)
        unless rest.isEmpty do
          throw .trailingHandshakeAfterFinished
        completeServerHandshake state' message
    | .connected =>
        if message.msgType == Handshake.newSessionTicketType then do
          let _ ← liftHandshake (Handshake.parseNewSessionTicket message)
          processHandshakeBuffer state'
        else if message.msgType == Handshake.keyUpdateType then
          match hacc : acceptKeyUpdate state' message with
          | .error e => .error e
          | .ok (stateK, wireBytes) =>
            have hbuf : stateK.handshakeBuffered.size <
                state.handshakeBuffered.size := by
              rw [acceptKeyUpdate_buffered hacc]
              exact hrest
            match processHandshakeBuffer stateK with
            | .error e => .error e
            | .ok (stateF, moreWireBytes) =>
                .ok (stateF, wireBytes ++ moreWireBytes)
        else
          .error (.unexpectedHandshake state'.phase message.msgType)
  termination_by state.handshakeBuffered.size
  decreasing_by
    all_goals first
      | exact hbuf
      | exact hrest
      | (simp only [appendTranscript_buffered]
         exact hrest)

private def validCompatibilityChangeCipherSpec (fragment : ByteArray) : Bool :=
  fragment.size == 1 && fragment.get! 0 == 1

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
      let state := { state with peerClosed := true }
      emitCloseNotify state
  else
    throw (.peerAlert level description)

private def processProtectedRecord (state : State) (record : Record.RawRecord) :
    Except Error (State × ByteArray × ByteArray) := do
  let readKeys ← requireReadKeys state
  let (readKeys, plaintext) ← liftRecord (Record.«open» readKeys record)
  let state := { state with readKeys? := some readKeys }
  if state.phase == .connected then
    if state.peerClosed then
      throw .connectionClosed
    match plaintext.contentType with
    | .applicationData =>
        unless state.handshakeBuffered.isEmpty do
          throw .interleavedHandshake
        pure (state, plaintext.fragment, ByteArray.empty)
    | .handshake =>
        let state := {
          state with handshakeBuffered := state.handshakeBuffered ++ plaintext.fragment
        }
        let (state, wireBytes) ← processHandshakeBuffer state
        pure (state, ByteArray.empty, wireBytes)
    | .alert =>
        unless state.handshakeBuffered.isEmpty do
          throw .interleavedHandshake
        let (state, wireBytes) ← processAlert state plaintext.fragment false
        pure (state, ByteArray.empty, wireBytes)
    | .changeCipherSpec =>
        throw (.unexpectedRecord state.phase plaintext.contentType)
  else
    match plaintext.contentType with
    | .handshake =>
        let state := {
          state with handshakeBuffered := state.handshakeBuffered ++ plaintext.fragment
        }
        let (state, wireBytes) ← processHandshakeBuffer state
        pure (state, ByteArray.empty, wireBytes)
    | .alert =>
        unless state.handshakeBuffered.isEmpty do
          throw .interleavedHandshake
        let (state, wireBytes) ← processAlert state plaintext.fragment true
        pure (state, ByteArray.empty, wireBytes)
    | contentType =>
        throw (.unexpectedRecord state.phase contentType)

private def processRecord (state : State) (record : Record.RawRecord) :
    Except Error (State × ByteArray × ByteArray) := do
  match state.phase with
  | .waitingServerHello =>
      match record.contentType with
      | .handshake =>
          let state ← feedPlaintextHandshake state record.fragment
          pure (state, ByteArray.empty, ByteArray.empty)
      | .changeCipherSpec =>
          unless validCompatibilityChangeCipherSpec record.fragment do
            throw .invalidCompatibilityChangeCipherSpec
          pure (state, ByteArray.empty, ByteArray.empty)
      | .alert =>
          unless state.handshakeBuffered.isEmpty do
            throw .interleavedHandshake
          let (state, wireBytes) ← processAlert state record.fragment true
          pure (state, ByteArray.empty, wireBytes)
      | contentType =>
          throw (.unexpectedRecord state.phase contentType)
  | .waitingEncryptedExtensions
  | .waitingCertificate
  | .waitingCertificateVerify
  | .waitingServerFinished =>
      match record.contentType with
      | .changeCipherSpec =>
          unless validCompatibilityChangeCipherSpec record.fragment do
            throw .invalidCompatibilityChangeCipherSpec
          pure (state, ByteArray.empty, ByteArray.empty)
      | .applicationData => processProtectedRecord state record
      | contentType => throw (.unexpectedRecord state.phase contentType)
  | .connected =>
      match record.contentType with
      | .applicationData => processProtectedRecord state record
      | contentType => throw (.unexpectedRecord state.phase contentType)

/-- Incrementally consume arbitrary transport bytes, retaining the latest
successfully advanced state on failure for fatal-alert emission. -/
def feedWithFailure (initial : State) (chunk : ByteArray) :
    Except Failure Output := do
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

/--
Incrementally consume arbitrary transport bytes. The returned plaintext is
the concatenation of application-data records in wire order; `wireBytes`
contains any generated client Finished, reciprocal KeyUpdate, or close_notify.
Use `feedWithFailure` when the caller can emit protocol-fatal alerts.
-/
def feed (state : State) (chunk : ByteArray) : Except Error Output :=
  match feedWithFailure state chunk with
  | .ok output => pure output
  | .error failure => throw failure.error

private def concatByteArrays (parts : Array ByteArray) : ByteArray := Id.run do
  let total := parts.foldl (fun size part => size + part.size) 0
  let mut out := ByteArray.mk (Array.replicate total 0)
  let mut offset := 0
  for part in parts do
    out := part.copySlice 0 out offset part.size
    offset := offset + part.size
  return out

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

/-- Protect application bytes, splitting them at TLS's 2^14-byte limit. -/
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
    let wireBytes := concatByteArrays records
    pure { state := { state with writeKeys? := some writeKeys }, wireBytes }

/--
Send `close_notify` under the current application keys.  Repeated calls are a
no-op and return the same state with empty `wireBytes`.
-/
def closeNotify (state : State) : Except Error Output := do
  unless state.phase == .connected do
    throw (.notConnected state.phase)
  let (state, wireBytes) ← emitCloseNotify state
  pure { state, wireBytes }

end Client
end Tls
