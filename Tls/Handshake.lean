module

public section

namespace Tls
namespace Handshake

/-!
Minimal TLS 1.3 handshake codecs for the PostgreSQL client.

This module deliberately stops at the handshake-message boundary.  The record
layer is responsible for collecting/decrypting handshake bytes and for
protecting the messages produced here.  Every decoded `Message` retains its
exact wire encoding so callers can append `encoded` to the transcript without
re-encoding it.
-/

-- Handshake message types (RFC 8446, section 4).

def clientHelloType : UInt8 := 1
def serverHelloType : UInt8 := 2
def newSessionTicketType : UInt8 := 4
def encryptedExtensionsType : UInt8 := 8
def certificateType : UInt8 := 11
def certificateVerifyType : UInt8 := 15
def finishedType : UInt8 := 20
def keyUpdateType : UInt8 := 24
/-- Synthetic handshake type used for the transcript after HelloRetryRequest. -/
def messageHashType : UInt8 := 254

-- Protocol and algorithm identifiers used by the minimal client.

def legacyTls12Version : UInt16 := 0x0303
def tls13Version : UInt16 := 0x0304
def tlsChaCha20Poly1305Sha256 : UInt16 := 0x1303
def x25519Group : UInt16 := 0x001d
def secp256r1Group : UInt16 := 0x0017

inductive NamedGroup where
  | x25519
  | secp256r1
  deriving Inhabited, Repr, BEq, DecidableEq

namespace NamedGroup

def toUInt16 : NamedGroup → UInt16
  | .x25519 => x25519Group
  | .secp256r1 => secp256r1Group

def ofUInt16? : UInt16 → Option NamedGroup
  | 0x001d => some .x25519
  | 0x0017 => some .secp256r1
  | _ => none

end NamedGroup

def rsaPssRsaeSha256 : UInt16 := 0x0804
def rsaPssPssSha256 : UInt16 := 0x0809
def rsaPkcs1Sha256 : UInt16 := 0x0401
def ecdsaSecp256r1Sha256 : UInt16 := 0x0403
def ed25519 : UInt16 := 0x0807

def serverNameExtension : UInt16 := 0
def supportedGroupsExtension : UInt16 := 10
def signatureAlgorithmsExtension : UInt16 := 13
def supportedVersionsExtension : UInt16 := 43
def keyShareExtension : UInt16 := 51
def preSharedKeyExtension : UInt16 := 41
def earlyDataExtension : UInt16 := 42
def cookieExtension : UInt16 := 44
def pskKeyExchangeModesExtension : UInt16 := 45
def paddingExtension : UInt16 := 21
-- application_layer_protocol_negotiation (RFC 7301).
def alpnExtension : UInt16 := 16

private def appendUInt16 (out : ByteArray) (n : UInt16) : ByteArray :=
  (out.push (n >>> 8).toUInt8).push n.toUInt8

private def appendUInt32 (out : ByteArray) (n : UInt32) : ByteArray :=
  let out := out.push (n >>> 24).toUInt8
  let out := out.push (n >>> 16).toUInt8
  let out := out.push (n >>> 8).toUInt8
  out.push n.toUInt8

/-- Encode an unsigned one-byte length, rejecting truncation. -/
def encodeLength8 (n : Nat) : Except String ByteArray := do
  if n > 0xff then
    throw s!"length {n} does not fit in uint8"
  pure (ByteArray.empty.push (UInt8.ofNat n))

/-- Encode an unsigned two-byte length, rejecting truncation. -/
def encodeLength16 (n : Nat) : Except String ByteArray := do
  if n > 0xffff then
    throw s!"length {n} does not fit in uint16"
  pure <| appendUInt16 ByteArray.empty (UInt16.ofNat n)

/-- Encode an unsigned three-byte length, rejecting truncation. -/
def encodeLength24 (n : Nat) : Except String ByteArray := do
  if n > 0xffffff then
    throw s!"length {n} does not fit in uint24"
  pure <| (((ByteArray.empty.push (UInt8.ofNat (n >>> 16))).push
    (UInt8.ofNat (n >>> 8))).push (UInt8.ofNat n))

def encodeVector8 (bytes : ByteArray) : Except String ByteArray := do
  pure ((← encodeLength8 bytes.size) ++ bytes)

def encodeVector16 (bytes : ByteArray) : Except String ByteArray := do
  pure ((← encodeLength16 bytes.size) ++ bytes)

def encodeVector24 (bytes : ByteArray) : Except String ByteArray := do
  pure ((← encodeLength24 bytes.size) ++ bytes)

/-- A checked cursor over a bounded byte string. -/
structure Reader where
  bytes : ByteArray
  offset : Nat := 0
  deriving Inhabited

namespace Reader

def remaining (r : Reader) : Nat :=
  r.bytes.size - r.offset

def atEnd (r : Reader) : Bool :=
  r.offset == r.bytes.size

def take (r : Reader) (n : Nat) : Except String (ByteArray × Reader) := do
  if r.offset + n > r.bytes.size then
    throw s!"truncated input at offset {r.offset}: need {n} bytes, have {r.remaining}"
  let stop := r.offset + n
  pure (r.bytes.extract r.offset stop, { r with offset := stop })

def readUInt8 (r : Reader) : Except String (UInt8 × Reader) := do
  let (bytes, r) ← r.take 1
  pure (bytes.get! 0, r)

def readUInt16 (r : Reader) : Except String (UInt16 × Reader) := do
  let (bytes, r) ← r.take 2
  let n := (bytes.get! 0).toUInt16 <<< 8 ||| (bytes.get! 1).toUInt16
  pure (n, r)

def readUInt24 (r : Reader) : Except String (Nat × Reader) := do
  let (bytes, r) ← r.take 3
  let n := (bytes.get! 0).toNat <<< 16 |||
    (bytes.get! 1).toNat <<< 8 ||| (bytes.get! 2).toNat
  pure (n, r)

def readUInt32 (r : Reader) : Except String (UInt32 × Reader) := do
  let (bytes, r) ← r.take 4
  let n := (bytes.get! 0).toUInt32 <<< 24 |||
    (bytes.get! 1).toUInt32 <<< 16 |||
    (bytes.get! 2).toUInt32 <<< 8 ||| (bytes.get! 3).toUInt32
  pure (n, r)

def readVector8 (r : Reader) : Except String (ByteArray × Reader) := do
  let (len, r) ← r.readUInt8
  r.take len.toNat

def readVector16 (r : Reader) : Except String (ByteArray × Reader) := do
  let (len, r) ← r.readUInt16
  r.take len.toNat

def readVector24 (r : Reader) : Except String (ByteArray × Reader) := do
  let (len, r) ← r.readUInt24
  r.take len

def requireEnd (r : Reader) (context : String) : Except String Unit := do
  unless r.atEnd do
    throw s!"{context}: {r.remaining} trailing bytes"

end Reader

/-- One complete TLS handshake message, including the exact transcript bytes. -/
structure Message where
  msgType : UInt8
  body : ByteArray
  encoded : ByteArray
  deriving Inhabited, BEq

/-- Frame a handshake body as `type || uint24(length) || body`. -/
def frame (msgType : UInt8) (body : ByteArray) : Except String Message := do
  let encoded := (ByteArray.empty.push msgType) ++ (← encodeLength24 body.size) ++ body
  pure { msgType, body, encoded }

/-- Decode the first complete handshake message and return unconsumed bytes. -/
def decodeOne (bytes : ByteArray) : Except String (Message × ByteArray) := do
  let start : Reader := { bytes }
  let (msgType, r) ← start.readUInt8
  let (len, r) ← r.readUInt24
  let (body, r) ← r.take len
  let consumed := r.offset
  let encoded := bytes.extract 0 consumed
  let rest := bytes.extract consumed bytes.size
  pure ({ msgType, body, encoded }, rest)

/-- Decode exactly one framed handshake message. -/
def decode (bytes : ByteArray) : Except String Message := do
  let (msg, rest) ← decodeOne bytes
  unless rest.isEmpty do
    throw s!"handshake message has {rest.size} trailing bytes"
  pure msg

structure Extension where
  extensionType : UInt16
  data : ByteArray
  deriving Inhabited, BEq

private def encodeExtension (extensionType : UInt16) (data : ByteArray) :
    Except String ByteArray := do
  pure (appendUInt16 ByteArray.empty extensionType ++ (← encodeVector16 data))

private def parseExtensions (bytes : ByteArray) : Except String (Array Extension) := do
  let mut r : Reader := { bytes }
  let mut out : Array Extension := #[]
  while !r.atEnd do
    let (extensionType, r') ← r.readUInt16
    let (data, r') ← r'.readVector16
    if out.any (fun ext => ext.extensionType == extensionType) then
      throw s!"duplicate TLS extension {extensionType}"
    out := out.push { extensionType, data }
    r := r'
  pure out

private def findExtension? (extensions : Array Extension) (extensionType : UInt16) :
    Option Extension :=
  extensions.find? (fun ext => ext.extensionType == extensionType)

private def requireExtension (extensions : Array Extension) (extensionType : UInt16)
    (name : String) : Except String Extension := do
  let some ext := findExtension? extensions extensionType
    | throw s!"ServerHello is missing {name}"
  pure ext

/-- Inputs whose values must be freshly generated for each ClientHello. -/
structure ClientHelloConfig where
  random : ByteArray
  x25519PublicKey : ByteArray
  p256PublicKey : Option ByteArray := none
  serverName : Option String := none
  legacySessionId : ByteArray := ByteArray.empty
  /-- ALPN protocols to offer, in client preference order (empty omits ALPN). -/
  alpnProtocols : Array String := #[]
  deriving Inhabited

/-- Encode a client ALPN offer: a ProtocolNameList of length-prefixed names. -/
private def alpnClientExtension (protocols : Array String) : Except String ByteArray := do
  let mut inner := ByteArray.empty
  for protocol in protocols do
    let name := protocol.toUTF8
    if name.isEmpty then
      throw "ALPN protocol name must not be empty"
    inner := inner ++ (← encodeVector8 name)
  encodeExtension alpnExtension (← encodeVector16 inner)

private def supportedVersionsClientExtension : Except String ByteArray := do
  let versions := appendUInt16 ByteArray.empty tls13Version
  encodeExtension supportedVersionsExtension (← encodeVector8 versions)

private def supportedGroupsClientExtension (includeP256 : Bool) :
    Except String ByteArray := do
  let groups := if includeP256 then
      appendUInt16 (appendUInt16 ByteArray.empty x25519Group) secp256r1Group
    else
      appendUInt16 ByteArray.empty x25519Group
  encodeExtension supportedGroupsExtension (← encodeVector16 groups)

private def signatureAlgorithmsClientExtension : Except String ByteArray := do
  let algorithms := #[
    rsaPssRsaeSha256, rsaPssPssSha256, ecdsaSecp256r1Sha256, ed25519,
    -- TLS 1.3 CertificateVerify cannot use PKCS#1 v1.5, but many otherwise
    -- usable RSA certificate chains are themselves signed with it. The same
    -- extension constrains both uses, so advertise it for certificate-chain
    -- selection while `parseCertificateVerify` still rejects it.
    rsaPkcs1Sha256
  ].foldl appendUInt16 ByteArray.empty
  encodeExtension signatureAlgorithmsExtension (← encodeVector16 algorithms)

private def keyShareClientExtension (x25519PublicKey : ByteArray)
    (p256PublicKey : Option ByteArray) : Except String ByteArray := do
  let mut entries :=
    appendUInt16 ByteArray.empty x25519Group ++ (← encodeVector16 x25519PublicKey)
  if let some publicKey := p256PublicKey then
    entries := entries ++ appendUInt16 ByteArray.empty secp256r1Group ++
      (← encodeVector16 publicKey)
  encodeExtension keyShareExtension (← encodeVector16 entries)

private def serverNameClientExtension (name : String) : Except String ByteArray := do
  let nameBytes := name.toUTF8
  if nameBytes.isEmpty then
    throw "SNI server name must not be empty"
  if nameBytes.foldl (fun found b => found || b == 0) false then
    throw "SNI server name must not contain NUL"
  let hostName := ByteArray.empty.push 0 ++ (← encodeVector16 nameBytes)
  encodeExtension serverNameExtension (← encodeVector16 hostName)

/--
Encode the minimal TLS 1.3 ClientHello used by pg-lean:
TLS_CHACHA20_POLY1305_SHA256, first-flight X25519 and optional P-256 shares,
TLS 1.3 only, the supported certificate-signature schemes, and optional SNI.
-/
def encodeClientHello (cfg : ClientHelloConfig) : Except String Message := do
  unless cfg.random.size == 32 do
    throw s!"ClientHello random must be 32 bytes, got {cfg.random.size}"
  unless cfg.x25519PublicKey.size == 32 do
    throw s!"x25519 public key must be 32 bytes, got {cfg.x25519PublicKey.size}"
  if let some publicKey := cfg.p256PublicKey then
    unless publicKey.size == 65 && publicKey.get! 0 == 4 do
      throw "P-256 public key must be a 65-byte SEC1 uncompressed point"
  if cfg.legacySessionId.size > 32 then
    throw s!"legacy session id exceeds 32 bytes ({cfg.legacySessionId.size})"

  let mut extensions := ← supportedVersionsClientExtension
  extensions := extensions ++ (← supportedGroupsClientExtension cfg.p256PublicKey.isSome)
  extensions := extensions ++ (← signatureAlgorithmsClientExtension)
  extensions := extensions ++
    (← keyShareClientExtension cfg.x25519PublicKey cfg.p256PublicKey)
  if let some name := cfg.serverName then
    extensions := extensions ++ (← serverNameClientExtension name)
  if !cfg.alpnProtocols.isEmpty then
    extensions := extensions ++ (← alpnClientExtension cfg.alpnProtocols)

  let mut body := appendUInt16 ByteArray.empty legacyTls12Version
  body := body ++ cfg.random
  body := body ++ (← encodeVector8 cfg.legacySessionId)
  body := body ++ (← encodeVector16 (appendUInt16 ByteArray.empty
    tlsChaCha20Poly1305Sha256))
  body := body ++ (← encodeVector8 (ByteArray.empty.push 0))
  body := body ++ (← encodeVector16 extensions)
  frame clientHelloType body

/-- The fixed RFC 8446 HelloRetryRequest random value. -/
def helloRetryRequestRandom : ByteArray :=
  ByteArray.mk #[
    0xcf, 0x21, 0xad, 0x74, 0xe5, 0x9a, 0x61, 0x11,
    0xbe, 0x1d, 0x8c, 0x02, 0x1e, 0x65, 0xb8, 0x91,
    0xc2, 0xa2, 0x11, 0x16, 0x7a, 0xbb, 0x8c, 0x5e,
    0x07, 0x9e, 0x09, 0xe2, 0xc8, 0xa8, 0x33, 0x9c
  ]

/-- Check whether a framed ServerHello carries the fixed HRR random. This is
only a discriminator; `parseHelloRetryRequest` still performs full validation. -/
def isHelloRetryRequest (msg : Message) : Bool :=
  msg.msgType == serverHelloType &&
    msg.body.size >= 34 &&
    msg.body.extract 2 34 == helloRetryRequestRandom

structure ServerHello where
  random : ByteArray
  legacySessionIdEcho : ByteArray
  cipherSuite : UInt16
  selectedGroup : NamedGroup
  keyExchange : ByteArray
  extensions : Array Extension
  encoded : ByteArray
  deriving Inhabited, BEq

def parseServerHello (msg : Message) : Except String ServerHello := do
  unless msg.msgType == serverHelloType do
    throw s!"expected ServerHello ({serverHelloType}), got handshake type {msg.msgType}"
  let r : Reader := { bytes := msg.body }
  let (legacyVersion, r) ← r.readUInt16
  unless legacyVersion == legacyTls12Version do
    throw s!"ServerHello legacy_version must be 0x0303, got {legacyVersion}"
  let (random, r) ← r.take 32
  if random == helloRetryRequestRandom then
    throw "expected ServerHello, got HelloRetryRequest"
  let (sessionId, r) ← r.readVector8
  if sessionId.size > 32 then
    throw s!"ServerHello legacy session id exceeds 32 bytes ({sessionId.size})"
  let (cipherSuite, r) ← r.readUInt16
  let (compression, r) ← r.readUInt8
  unless compression == 0 do
    throw s!"ServerHello selected non-null legacy compression {compression}"
  let (extensionBytes, r) ← r.readVector16
  r.requireEnd "ServerHello"
  let extensions ← parseExtensions extensionBytes

  let versionExt ← requireExtension extensions supportedVersionsExtension "supported_versions"
  unless versionExt.data == appendUInt16 ByteArray.empty tls13Version do
    throw "server did not select TLS 1.3"

  let keyExt ← requireExtension extensions keyShareExtension "key_share"
  let kr : Reader := { bytes := keyExt.data }
  let (groupId, kr) ← kr.readUInt16
  let some selectedGroup := NamedGroup.ofUInt16? groupId
    | throw s!"server selected unsupported key-share group {groupId}"
  let (keyExchange, kr) ← kr.readVector16
  kr.requireEnd "ServerHello key_share"
  match selectedGroup with
  | .x25519 =>
    unless keyExchange.size == 32 do
      throw s!"server x25519 public key must be 32 bytes, got {keyExchange.size}"
  | .secp256r1 =>
    unless keyExchange.size == 65 && keyExchange.get! 0 == 4 do
      throw "server P-256 key share must be a 65-byte SEC1 uncompressed point"

  pure {
    random
    legacySessionIdEcho := sessionId
    cipherSuite
    selectedGroup
    keyExchange
    extensions
    encoded := msg.encoded
  }

/-- The parsed wire fields of a HelloRetryRequest. An HRR uses the
ServerHello handshake type and is distinguished by its fixed random. -/
structure HelloRetryRequest where
  legacySessionIdEcho : ByteArray
  cipherSuite : UInt16
  selectedGroup : NamedGroup
  extensions : Array Extension
  encoded : ByteArray
  deriving Inhabited, BEq

def parseHelloRetryRequest (msg : Message) : Except String HelloRetryRequest := do
  unless msg.msgType == serverHelloType do
    throw s!"expected HelloRetryRequest ({serverHelloType}), got handshake type {msg.msgType}"
  let r : Reader := { bytes := msg.body }
  let (legacyVersion, r) ← r.readUInt16
  unless legacyVersion == legacyTls12Version do
    throw s!"HelloRetryRequest legacy_version must be 0x0303, got {legacyVersion}"
  let (random, r) ← r.take 32
  unless random == helloRetryRequestRandom do
    throw "ServerHello random is not the HelloRetryRequest sentinel"
  let (sessionId, r) ← r.readVector8
  if sessionId.size > 32 then
    throw s!"HelloRetryRequest legacy session id exceeds 32 bytes ({sessionId.size})"
  let (cipherSuite, r) ← r.readUInt16
  let (compression, r) ← r.readUInt8
  unless compression == 0 do
    throw s!"HelloRetryRequest selected non-null legacy compression {compression}"
  let (extensionBytes, r) ← r.readVector16
  r.requireEnd "HelloRetryRequest"
  let extensions ← parseExtensions extensionBytes

  let versionExt ←
    requireExtension extensions supportedVersionsExtension "supported_versions"
  unless versionExt.data == appendUInt16 ByteArray.empty tls13Version do
    throw "HelloRetryRequest did not select TLS 1.3"

  let keyExt ← requireExtension extensions keyShareExtension "key_share"
  let kr : Reader := { bytes := keyExt.data }
  let (groupId, kr) ← kr.readUInt16
  kr.requireEnd "HelloRetryRequest key_share"
  let some selectedGroup := NamedGroup.ofUInt16? groupId
    | throw s!"HelloRetryRequest selected unsupported group {groupId}"

  pure {
    legacySessionIdEcho := sessionId
    cipherSuite
    selectedGroup
    extensions
    encoded := msg.encoded
  }

structure EncryptedExtensions where
  extensions : Array Extension
  encoded : ByteArray
  deriving Inhabited, BEq

def parseEncryptedExtensions (msg : Message) : Except String EncryptedExtensions := do
  unless msg.msgType == encryptedExtensionsType do
    throw s!"expected EncryptedExtensions ({encryptedExtensionsType}), got {msg.msgType}"
  let r : Reader := { bytes := msg.body }
  let (extensionBytes, r) ← r.readVector16
  r.requireEnd "EncryptedExtensions"
  pure { extensions := ← parseExtensions extensionBytes, encoded := msg.encoded }

/-- The single ALPN protocol a server selected (from EncryptedExtensions), if any. -/
def selectedAlpnProtocol (ee : EncryptedExtensions) : Except String (Option String) := do
  match findExtension? ee.extensions alpnExtension with
  | none => pure none
  | some ext =>
      let r : Reader := { bytes := ext.data }
      let (list, r) ← r.readVector16
      r.requireEnd "ALPN extension"
      let lr : Reader := { bytes := list }
      let (name, lr) ← lr.readVector8
      if name.isEmpty then
        throw "ALPN selected protocol must not be empty"
      lr.requireEnd "ALPN ProtocolNameList"
      match String.fromUTF8? name with
      | some s => pure (some s)
      | none => throw "ALPN protocol name is not valid UTF-8"

structure CertificateEntry where
  der : ByteArray
  extensions : Array Extension
  deriving Inhabited, BEq

structure Certificate where
  requestContext : ByteArray
  entries : Array CertificateEntry
  leafDer : ByteArray
  encoded : ByteArray
  deriving Inhabited, BEq

def parseCertificate (msg : Message) : Except String Certificate := do
  unless msg.msgType == certificateType do
    throw s!"expected Certificate ({certificateType}), got {msg.msgType}"
  let r : Reader := { bytes := msg.body }
  let (requestContext, r) ← r.readVector8
  unless requestContext.isEmpty do
    throw "server Certificate request_context must be empty"
  let (certificateList, r) ← r.readVector24
  r.requireEnd "Certificate"

  let mut lr : Reader := { bytes := certificateList }
  let mut entries : Array CertificateEntry := #[]
  while !lr.atEnd do
    let (der, lr') ← lr.readVector24
    if der.isEmpty then
      throw "Certificate contains an empty certificate entry"
    let (extensionBytes, lr') ← lr'.readVector16
    let extensions ← parseExtensions extensionBytes
    entries := entries.push { der, extensions }
    lr := lr'
  if entries.isEmpty then
    throw "server sent an empty certificate_list"
  pure {
    requestContext
    entries
    leafDer := entries[0]!.der
    encoded := msg.encoded
  }

structure CertificateVerify where
  algorithm : UInt16
  signature : ByteArray
  encoded : ByteArray
  deriving Inhabited, BEq

/-- Parse CertificateVerify structurally. Scheme policy belongs to the TLS
client: it rejects forbidden or unoffered schemes, checks the leaf SPKI, and
verifies the signature over the raw transcript before advancing to Finished. -/
def parseCertificateVerify (msg : Message) : Except String CertificateVerify := do
  unless msg.msgType == certificateVerifyType do
    throw s!"expected CertificateVerify ({certificateVerifyType}), got {msg.msgType}"
  let r : Reader := { bytes := msg.body }
  let (algorithm, r) ← r.readUInt16
  let (signature, r) ← r.readVector16
  r.requireEnd "CertificateVerify"
  if signature.isEmpty then
    throw "CertificateVerify signature must not be empty"
  pure { algorithm, signature, encoded := msg.encoded }

structure Finished where
  verifyData : ByteArray
  encoded : ByteArray
  deriving Inhabited, BEq

def parseFinished (msg : Message) : Except String Finished := do
  unless msg.msgType == finishedType do
    throw s!"expected Finished ({finishedType}), got {msg.msgType}"
  unless msg.body.size == 32 do
    throw s!"TLS_CHACHA20_POLY1305_SHA256 Finished must contain 32 bytes, got {msg.body.size}"
  pure { verifyData := msg.body, encoded := msg.encoded }

def encodeFinished (verifyData : ByteArray) : Except String Message := do
  unless verifyData.size == 32 do
    throw s!"TLS_CHACHA20_POLY1305_SHA256 Finished must contain 32 bytes, got {verifyData.size}"
  frame finishedType verifyData

structure NewSessionTicket where
  ticketLifetime : UInt32
  ticketAgeAdd : UInt32
  ticketNonce : ByteArray
  ticket : ByteArray
  extensions : Array Extension
  encoded : ByteArray
  deriving Inhabited, BEq

def parseNewSessionTicket (msg : Message) : Except String NewSessionTicket := do
  unless msg.msgType == newSessionTicketType do
    throw s!"expected NewSessionTicket ({newSessionTicketType}), got {msg.msgType}"
  let r : Reader := { bytes := msg.body }
  let (lifetime, r) ← r.readUInt32
  if lifetime > 604800 then
    throw s!"NewSessionTicket lifetime exceeds seven days ({lifetime})"
  let (ageAdd, r) ← r.readUInt32
  let (nonce, r) ← r.readVector8
  let (ticket, r) ← r.readVector16
  if ticket.isEmpty then
    throw "NewSessionTicket ticket must not be empty"
  let (extensionBytes, r) ← r.readVector16
  r.requireEnd "NewSessionTicket"
  let extensions ← parseExtensions extensionBytes
  if let some earlyData := findExtension? extensions earlyDataExtension then
    unless earlyData.data.size == 4 do
      throw "NewSessionTicket early_data extension must contain uint32 max_early_data_size"
  pure {
    ticketLifetime := lifetime
    ticketAgeAdd := ageAdd
    ticketNonce := nonce
    ticket
    extensions
    encoded := msg.encoded
  }

inductive KeyUpdateRequest where
  | updateNotRequested
  | updateRequested
  deriving Inhabited, Repr, BEq, DecidableEq

def KeyUpdateRequest.toUInt8 : KeyUpdateRequest → UInt8
  | .updateNotRequested => 0
  | .updateRequested => 1

def KeyUpdateRequest.ofUInt8? : UInt8 → Option KeyUpdateRequest
  | 0 => some .updateNotRequested
  | 1 => some .updateRequested
  | _ => none

structure KeyUpdate where
  request : KeyUpdateRequest
  encoded : ByteArray
  deriving Inhabited, BEq

def parseKeyUpdate (msg : Message) : Except String KeyUpdate := do
  unless msg.msgType == keyUpdateType do
    throw s!"expected KeyUpdate ({keyUpdateType}), got {msg.msgType}"
  unless msg.body.size == 1 do
    throw s!"KeyUpdate body must be exactly one byte, got {msg.body.size}"
  let value := msg.body.get! 0
  let some request := KeyUpdateRequest.ofUInt8? value
    | throw s!"invalid KeyUpdate request value {value}"
  pure { request, encoded := msg.encoded }

def encodeKeyUpdate (request : KeyUpdateRequest) : Except String Message :=
  frame keyUpdateType (ByteArray.empty.push request.toUInt8)

/-! ## Server-side codecs

The client codecs above cover a TLS client's needs. The following add the mirror
image used by a TLS *server*: parsing a ClientHello and building the server
flight (ServerHello, EncryptedExtensions, Certificate, CertificateVerify). They
share the same wire primitives, extension helpers, and type constants. -/

/-- One key-share offered by a client, group plus its public value. -/
structure ClientKeyShare where
  group : NamedGroup
  keyExchange : ByteArray
  deriving Inhabited, BEq

structure ClientHello where
  random : ByteArray
  legacySessionId : ByteArray
  cipherSuites : Array UInt16
  /-- Protocol versions exactly as offered in supported_versions, including
  unknown/GREASE values and preserving client preference order. -/
  supportedVersionIds : Array UInt16
  /-- All supported-group identifiers exactly as offered, including values
  unknown to this implementation (and therefore including GREASE values). -/
  supportedGroupIds : Array UInt16
  /-- The supported groups this implementation knows, preserving wire order. -/
  supportedGroups : Array NamedGroup
  /-- Every key-share group identifier in wire order, including unknown and
  GREASE groups. This is retained separately from `keyShares` so retry policy
  can enforce the one-entry second-ClientHello rule without treating unknown
  groups as implemented. -/
  keyShareGroupIds : Array UInt16
  keyShares : Array ClientKeyShare
  signatureAlgorithms : Array UInt16
  serverName : Option String := none
  /-- Offered ALPN protocol names in client preference order (empty if absent). -/
  alpnProtocols : Array String := #[]
  /-- All extensions in exact wire order. Unknown bodies remain opaque. This is
  used to enforce the restricted set of changes permitted in a retry
  ClientHello without reconstructing or normalizing the original message. -/
  extensions : Array Extension
  offersTls13 : Bool
  encoded : ByteArray
  deriving Inhabited

private def parseUInt16List (bytes : ByteArray) : Except String (Array UInt16) := do
  if bytes.size % 2 != 0 then
    throw "uint16 list has an odd byte length"
  let mut r : Reader := { bytes }
  let mut out : Array UInt16 := #[]
  while !r.atEnd do
    let (value, r') ← r.readUInt16
    out := out.push value
    r := r'
  pure out

private def parseSupportedGroups (bytes : ByteArray) :
    Except String (Array UInt16 × Array NamedGroup) := do
  let ids ← parseUInt16List bytes
  if ids.isEmpty then
    throw "supported_groups list must not be empty"
  let mut known : Array NamedGroup := #[]
  for id in ids do
    if let some group := NamedGroup.ofUInt16? id then
      known := known.push group
  pure (ids, known)

private def parseKeyShareEntries (bytes : ByteArray) :
    Except String (Array UInt16 × Array ClientKeyShare) := do
  let mut r : Reader := { bytes }
  let mut out : Array ClientKeyShare := #[]
  let mut seenGroupIds : Array UInt16 := #[]
  while !r.atEnd do
    let (groupId, r') ← r.readUInt16
    let (keyExchange, r') ← r'.readVector16
    if keyExchange.isEmpty then
      throw s!"key_share entry for group {groupId} has an empty key_exchange"
    if seenGroupIds.contains groupId then
      throw s!"duplicate key_share entry for group {groupId}"
    seenGroupIds := seenGroupIds.push groupId
    match NamedGroup.ofUInt16? groupId with
    | some group => out := out.push { group, keyExchange }
    | none => pure ()  -- ignore groups we do not implement
    r := r'
  pure (seenGroupIds, out)

private def isOrderedSubset (subset superset : Array UInt16) : Bool := Id.run do
  let mut next := 0
  for value in subset do
    let mut found := false
    while next < superset.size && !found do
      if superset[next]! == value then
        found := true
      next := next + 1
    unless found do
      return false
  return true

private def parseServerNameList (bytes : ByteArray) : Except String (Option String) := do
  if bytes.isEmpty then
    throw "SNI server_name list must not be empty"
  let mut r : Reader := { bytes }
  let mut seenNameTypes : Array UInt8 := #[]
  let mut result : Option String := none
  while !r.atEnd do
    let (nameType, r') ← r.readUInt8
    let (name, r') ← r'.readVector16
    if name.isEmpty then
      throw s!"SNI name of type {nameType} must not be empty"
    if seenNameTypes.contains nameType then
      throw s!"duplicate SNI name type {nameType}"
    seenNameTypes := seenNameTypes.push nameType
    if nameType == 0 then
      if name.foldl (fun found b => found || b == 0) false then
        throw "SNI host_name must not contain NUL"
      match String.fromUTF8? name with
      | some hostName => result := some hostName
      | none => throw "SNI host_name is not valid UTF-8"
    -- Unknown name types are structurally length-delimited and ignored.
    r := r'
  pure result

private def parseAlpnProtocolList (bytes : ByteArray) : Except String (Array String) := do
  if bytes.isEmpty then
    throw "ALPN protocol list must not be empty"
  let mut r : Reader := { bytes }
  let mut out : Array String := #[]
  while !r.atEnd do
    let (name, r') ← r.readVector8
    if name.isEmpty then
      throw "ALPN protocol name must not be empty"
    match String.fromUTF8? name with
    | some s => out := out.push s
    | none =>
        -- ProtocolName is an opaque byte string, not text. This server's
        -- application-facing API uses String protocol IDs, so retain the
        -- UTF-8 offers it can negotiate and ignore other well-formed IDs.
        pure ()
    r := r'
  pure out

/-- Parse a ClientHello for the server flow. Extracts the fields the server needs
to select a key-exchange group, verify TLS 1.3 support, and negotiate ALPN/SNI. -/
def parseClientHello (msg : Message) : Except String ClientHello := do
  unless msg.msgType == clientHelloType do
    throw s!"expected ClientHello ({clientHelloType}), got handshake type {msg.msgType}"
  let r : Reader := { bytes := msg.body }
  let (legacyVersion, r) ← r.readUInt16
  unless legacyVersion == legacyTls12Version do
    throw s!"ClientHello legacy_version must be 0x0303, got {legacyVersion}"
  let (random, r) ← r.take 32
  let (sessionId, r) ← r.readVector8
  unless sessionId.size ≤ 32 do
    throw s!"ClientHello legacy session id exceeds 32 bytes ({sessionId.size})"
  let (cipherSuitesBytes, r) ← r.readVector16
  let cipherSuites ← parseUInt16List cipherSuitesBytes
  if cipherSuites.isEmpty then
    throw "ClientHello cipher_suites must not be empty"
  let (compression, r) ← r.readVector8
  unless compression.size == 1 && compression.get! 0 == 0 do
    throw "ClientHello legacy_compression_methods must contain exactly null compression"
  let extensions ←
    if r.atEnd then
      -- The extension block was optional in pre-extension ClientHellos. Such
      -- a message cannot negotiate TLS 1.3, but is structurally decodable.
      pure #[]
    else
      let (extensionBytes, r) ← r.readVector16
      r.requireEnd "ClientHello"
      parseExtensions extensionBytes

  if let some _ := findExtension? extensions preSharedKeyExtension then
    unless !extensions.isEmpty &&
        extensions[extensions.size - 1]!.extensionType == preSharedKeyExtension do
      throw "ClientHello pre_shared_key must be the final extension"
    let some modes := findExtension? extensions pskKeyExchangeModesExtension
      | throw "ClientHello offered pre_shared_key without psk_key_exchange_modes"
    let mr : Reader := { bytes := modes.data }
    let (values, mr) ← mr.readVector8
    mr.requireEnd "ClientHello psk_key_exchange_modes"
    if values.isEmpty then
      throw "ClientHello psk_key_exchange_modes must not be empty"

  let supportedVersionIds ←
    match findExtension? extensions supportedVersionsExtension with
    | none => pure #[]
    | some ext =>
        let vr : Reader := { bytes := ext.data }
        let (list, vr) ← vr.readVector8
        vr.requireEnd "ClientHello supported_versions"
        if list.isEmpty then
          throw "ClientHello supported_versions list must not be empty"
        parseUInt16List list
  let offersTls13 := supportedVersionIds.contains tls13Version

  let (supportedGroupIds, supportedGroups) ←
    match findExtension? extensions supportedGroupsExtension with
    | none => pure (#[], #[])
    | some ext =>
        let gr : Reader := { bytes := ext.data }
        let (list, gr) ← gr.readVector16
        gr.requireEnd "ClientHello supported_groups"
        parseSupportedGroups list

  let (keyShareGroupIds, keyShares) ←
    match findExtension? extensions keyShareExtension with
    | none => pure (#[], #[])
    | some ext =>
        let kr : Reader := { bytes := ext.data }
        let (entries, kr) ← kr.readVector16
        kr.requireEnd "ClientHello key_share"
        parseKeyShareEntries entries
  -- Keep missing-extension policy at the connection layer so it can emit the
  -- TLS 1.3 `missing_extension` alert. When supported_groups is present, its
  -- ordering constraint on key_share entries is still a wire-codec invariant.
  if (findExtension? extensions supportedGroupsExtension).isSome then
    unless isOrderedSubset keyShareGroupIds supportedGroupIds do
      throw "ClientHello key_share groups must occur in supported_groups order"

  let signatureAlgorithms ←
    match findExtension? extensions signatureAlgorithmsExtension with
    | none => pure #[]
    | some ext =>
        let sr : Reader := { bytes := ext.data }
        let (list, sr) ← sr.readVector16
        sr.requireEnd "ClientHello signature_algorithms"
        if list.isEmpty then
          throw "ClientHello signature_algorithms list must not be empty"
        parseUInt16List list

  let serverName ←
    match findExtension? extensions serverNameExtension with
    | none => pure none
    | some ext =>
        let sr : Reader := { bytes := ext.data }
        let (list, sr) ← sr.readVector16
        sr.requireEnd "ClientHello server_name"
        parseServerNameList list

  let alpnProtocols ←
    match findExtension? extensions alpnExtension with
    | none => pure #[]
    | some ext =>
        let ar : Reader := { bytes := ext.data }
        let (list, ar) ← ar.readVector16
        ar.requireEnd "ClientHello ALPN"
        parseAlpnProtocolList list

  pure {
    random, legacySessionId := sessionId, cipherSuites,
    supportedVersionIds, supportedGroupIds, supportedGroups,
    keyShareGroupIds, keyShares,
    signatureAlgorithms, serverName, alpnProtocols, extensions, offersTls13,
    encoded := msg.encoded
  }

/-- Build a ServerHello selecting TLS 1.3, a caller-selected cipher suite, and
one key-share group. `legacySessionIdEcho` must echo the ClientHello's
legacy_session_id. The trailing default preserves the original ChaCha-only API. -/
def encodeServerHello (random legacySessionIdEcho : ByteArray)
    (group : NamedGroup) (keyExchange : ByteArray)
    (cipherSuite : UInt16 := tlsChaCha20Poly1305Sha256) : Except String Message := do
  unless random.size == 32 do
    throw s!"ServerHello random must be 32 bytes, got {random.size}"
  if legacySessionIdEcho.size > 32 then
    throw s!"legacy session id echo exceeds 32 bytes ({legacySessionIdEcho.size})"
  let supportedVersion ←
    encodeExtension supportedVersionsExtension (appendUInt16 ByteArray.empty tls13Version)
  let keyShareData := appendUInt16 ByteArray.empty group.toUInt16 ++ (← encodeVector16 keyExchange)
  let keyShare ← encodeExtension keyShareExtension keyShareData
  let extensions := supportedVersion ++ keyShare
  let mut body := appendUInt16 ByteArray.empty legacyTls12Version
  body := body ++ random
  body := body ++ (← encodeVector8 legacySessionIdEcho)
  body := body ++ appendUInt16 ByteArray.empty cipherSuite
  body := body ++ (ByteArray.empty.push 0)  -- null compression
  body := body ++ (← encodeVector16 extensions)
  frame serverHelloType body

/-- Build an RFC 8446 HelloRetryRequest selecting TLS 1.3, a cipher suite, and
the group for which the client must provide a fresh key share. -/
def encodeHelloRetryRequest (legacySessionIdEcho : ByteArray)
    (group : NamedGroup)
    (cipherSuite : UInt16 := tlsChaCha20Poly1305Sha256) : Except String Message := do
  if legacySessionIdEcho.size > 32 then
    throw s!"legacy session id echo exceeds 32 bytes ({legacySessionIdEcho.size})"
  let supportedVersion ←
    encodeExtension supportedVersionsExtension (appendUInt16 ByteArray.empty tls13Version)
  let keyShare ←
    encodeExtension keyShareExtension (appendUInt16 ByteArray.empty group.toUInt16)
  let extensions := supportedVersion ++ keyShare
  let mut body := appendUInt16 ByteArray.empty legacyTls12Version
  body := body ++ helloRetryRequestRandom
  body := body ++ (← encodeVector8 legacySessionIdEcho)
  body := body ++ appendUInt16 ByteArray.empty cipherSuite
  body := body ++ (ByteArray.empty.push 0)  -- null compression
  body := body ++ (← encodeVector16 extensions)
  frame serverHelloType body

private def encodeAlpnServerExtension (protocol : String) : Except String ByteArray := do
  let name := protocol.toUTF8
  if name.isEmpty then
    throw "ALPN protocol name must not be empty"
  encodeExtension alpnExtension (← encodeVector16 (← encodeVector8 name))

/-- Build EncryptedExtensions. Includes the ALPN extension echoing the selected
protocol when one was negotiated; otherwise sends no extensions. -/
def encodeEncryptedExtensions (alpnSelected : Option String := none) :
    Except String Message := do
  let mut extensions := ByteArray.empty
  if let some protocol := alpnSelected then
    extensions := extensions ++ (← encodeAlpnServerExtension protocol)
  frame encryptedExtensionsType (← encodeVector16 extensions)

/-- Build a server Certificate message from a DER chain (leaf first). Uses an
empty certificate_request_context and empty per-entry extensions. -/
def encodeCertificate (chain : Array ByteArray) : Except String Message := do
  if chain.isEmpty then
    throw "server Certificate chain must not be empty"
  let mut list := ByteArray.empty
  for der in chain do
    if der.isEmpty then
      throw "server Certificate chain contains an empty entry"
    list := list ++ (← encodeVector24 der) ++ (← encodeVector16 ByteArray.empty)
  let body := (← encodeVector8 ByteArray.empty) ++ (← encodeVector24 list)
  frame certificateType body

/-- Build a CertificateVerify from a signature scheme and signature bytes. -/
def encodeCertificateVerify (algorithm : UInt16) (signature : ByteArray) :
    Except String Message := do
  if signature.isEmpty then
    throw "CertificateVerify signature must not be empty"
  frame certificateVerifyType
    (appendUInt16 ByteArray.empty algorithm ++ (← encodeVector16 signature))

end Handshake
end Tls
