module

import Std.Tactic.BVDecide
public meta import Std.Tactic.BVDecide.Reflect

public section

namespace Tls
namespace Handshake

/-!
Minimal TLS 1.3 handshake codecs shared by the client and server state
machines and by downstream protocol consumers.

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

/-- Append a big-endian `uint16`. Public because the wire-codec laws below
state extension and length encodings in terms of it. -/
def appendUInt16 (out : ByteArray) (n : UInt16) : ByteArray :=
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

-- The cursor primitives are written as pure `if`/`match` chains (not `do`) so
-- the retention and wire-codec laws at the end of this file can reason about
-- them by case analysis and evaluate them by rewriting.
def take (r : Reader) (n : Nat) : Except String (ByteArray × Reader) :=
  if r.offset + n > r.bytes.size then
    .error s!"truncated input at offset {r.offset}: need {n} bytes, have {r.remaining}"
  else
    .ok (r.bytes.extract r.offset (r.offset + n), { r with offset := r.offset + n })

def readUInt8 (r : Reader) : Except String (UInt8 × Reader) :=
  match r.take 1 with
  | .error e => .error e
  | .ok (bytes, r) => .ok (bytes.get! 0, r)

def readUInt16 (r : Reader) : Except String (UInt16 × Reader) :=
  match r.take 2 with
  | .error e => .error e
  | .ok (bytes, r) =>
      .ok ((bytes.get! 0).toUInt16 <<< 8 ||| (bytes.get! 1).toUInt16, r)

def readUInt24 (r : Reader) : Except String (Nat × Reader) :=
  match r.take 3 with
  | .error e => .error e
  | .ok (bytes, r) =>
      .ok ((bytes.get! 0).toNat <<< 16 |||
        (bytes.get! 1).toNat <<< 8 ||| (bytes.get! 2).toNat, r)

def readUInt32 (r : Reader) : Except String (UInt32 × Reader) :=
  match r.take 4 with
  | .error e => .error e
  | .ok (bytes, r) =>
      .ok ((bytes.get! 0).toUInt32 <<< 24 |||
        (bytes.get! 1).toUInt32 <<< 16 |||
        (bytes.get! 2).toUInt32 <<< 8 ||| (bytes.get! 3).toUInt32, r)

def readVector8 (r : Reader) : Except String (ByteArray × Reader) :=
  match r.readUInt8 with
  | .error e => .error e
  | .ok (len, r) => r.take len.toNat

def readVector16 (r : Reader) : Except String (ByteArray × Reader) :=
  match r.readUInt16 with
  | .error e => .error e
  | .ok (len, r) => r.take len.toNat

def readVector24 (r : Reader) : Except String (ByteArray × Reader) :=
  match r.readUInt24 with
  | .error e => .error e
  | .ok (len, r) => r.take len

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
def decodeOne (bytes : ByteArray) : Except String (Message × ByteArray) :=
  match ({ bytes } : Reader).readUInt8 with
  | .error e => .error e
  | .ok (msgType, r) =>
    match r.readUInt24 with
    | .error e => .error e
    | .ok (len, r) =>
      match r.take len with
      | .error e => .error e
      | .ok (body, r) =>
          .ok ({ msgType, body, encoded := bytes.extract 0 r.offset },
            bytes.extract r.offset bytes.size)

/-- Decode exactly one framed handshake message. -/
def decode (bytes : ByteArray) : Except String Message :=
  match decodeOne bytes with
  | .error e => .error e
  | .ok (msg, rest) =>
      if rest.isEmpty then
        .ok msg
      else
        .error s!"handshake message has {rest.size} trailing bytes"

/-! Retention laws: a decoded message's `encoded` field holds exactly the
input bytes, so appending it to a transcript never re-encodes. -/

private theorem take_ok {r r' : Reader} {n : Nat} {b : ByteArray}
    (h : r.take n = .ok (b, r')) :
    r'.bytes = r.bytes ∧ r'.offset = r.offset + n ∧ r'.offset ≤ r.bytes.size := by
  unfold Reader.take at h
  split at h
  · cases h
  · rename_i hle
    simp only [Except.ok.injEq, Prod.mk.injEq] at h
    rw [← h.2]
    exact ⟨rfl, rfl, show r.offset + n ≤ r.bytes.size by omega⟩

private theorem readUInt8_ok {r r' : Reader} {v : UInt8}
    (h : r.readUInt8 = .ok (v, r')) :
    r'.bytes = r.bytes ∧ r'.offset = r.offset + 1 ∧ r'.offset ≤ r.bytes.size := by
  unfold Reader.readUInt8 at h
  split at h
  · cases h
  · rename_i b r'' htake
    simp only [Except.ok.injEq, Prod.mk.injEq] at h
    rw [← h.2]
    exact take_ok htake

private theorem readUInt16_ok {r r' : Reader} {v : UInt16}
    (h : r.readUInt16 = .ok (v, r')) :
    r'.bytes = r.bytes ∧ r'.offset = r.offset + 2 ∧ r'.offset ≤ r.bytes.size := by
  unfold Reader.readUInt16 at h
  split at h
  · cases h
  · rename_i b r'' htake
    simp only [Except.ok.injEq, Prod.mk.injEq] at h
    rw [← h.2]
    exact take_ok htake

/-- A vector read consumes its two length bytes plus the payload, never
running past the end of the buffer. -/
private theorem readVector16_ok {r r' : Reader} {b : ByteArray}
    (h : r.readVector16 = .ok (b, r')) :
    r'.bytes = r.bytes ∧ r.offset + 2 ≤ r'.offset ∧ r'.offset ≤ r.bytes.size := by
  unfold Reader.readVector16 at h
  split at h
  · cases h
  · rename_i len r₁ h16
    obtain ⟨hb1, ho1, hle1⟩ := readUInt16_ok h16
    obtain ⟨hb2, ho2, hle2⟩ := take_ok h
    rw [hb1] at hle2
    exact ⟨hb2.trans hb1, by omega, hle2⟩

private theorem readUInt24_ok {r r' : Reader} {n : Nat}
    (h : r.readUInt24 = .ok (n, r')) :
    r'.bytes = r.bytes ∧ r'.offset = r.offset + 3 ∧ r'.offset ≤ r.bytes.size := by
  unfold Reader.readUInt24 at h
  split at h
  · cases h
  · rename_i b r'' htake
    simp only [Except.ok.injEq, Prod.mk.injEq] at h
    rw [← h.2]
    exact take_ok htake

private theorem readVector24_ok {r r' : Reader} {b : ByteArray}
    (h : r.readVector24 = .ok (b, r')) :
    r'.bytes = r.bytes ∧ r.offset + 3 ≤ r'.offset ∧ r'.offset ≤ r.bytes.size := by
  unfold Reader.readVector24 at h
  split at h
  · cases h
  · rename_i len r₁ h24
    obtain ⟨hb1, ho1, hle1⟩ := readUInt24_ok h24
    obtain ⟨hb2, ho2, hle2⟩ := take_ok h
    rw [hb1] at hle2
    exact ⟨hb2.trans hb1, by omega, hle2⟩

private theorem decodeOne_ok {bytes rest : ByteArray} {msg : Message}
    (h : decodeOne bytes = .ok (msg, rest)) :
    ∃ consumed, consumed ≤ bytes.size ∧
      msg.encoded = bytes.extract 0 consumed ∧
      rest = bytes.extract consumed bytes.size := by
  unfold decodeOne at h
  split at h
  · cases h
  · rename_i msgType r1 h1
    split at h
    · cases h
    · rename_i len r2 h2
      split at h
      · cases h
      · rename_i body r3 h3
        simp only [Except.ok.injEq, Prod.mk.injEq] at h
        refine ⟨r3.offset, ?_, ?_, ?_⟩
        · have hb2 : r2.bytes = bytes := by
            rw [(readUInt24_ok h2).1, (readUInt8_ok h1).1]
          rw [← hb2]
          exact (take_ok h3).2.2
        · rw [← h.1]
        · rw [← h.2]

/-- A successfully decoded handshake message retains exactly its input bytes
in `encoded`. -/
theorem decode_encoded {bytes : ByteArray} {msg : Message}
    (h : decode bytes = .ok msg) : msg.encoded = bytes := by
  unfold decode at h
  split at h
  · cases h
  · rename_i m rest hone
    split at h
    · rename_i hempty
      cases h
      obtain ⟨consumed, hle, henc, hrest⟩ := decodeOne_ok hone
      have hrest0 : rest = ByteArray.empty := by
        simpa [ByteArray.isEmpty] using hempty
      have hsize : rest.size = 0 := by
        rw [hrest0]
        rfl
      have hconsumed : consumed = bytes.size := by
        rw [hrest, ByteArray.size_extract] at hsize
        omega
      rw [henc, hconsumed]
      exact ByteArray.extract_zero_size
    · cases h

structure Extension where
  extensionType : UInt16
  data : ByteArray
  deriving Inhabited, BEq

private def encodeExtension (extensionType : UInt16) (data : ByteArray) :
    Except String ByteArray := do
  pure (appendUInt16 ByteArray.empty extensionType ++ (← encodeVector16 data))

/-- The wire image of one extension: `extension_type ‖ uint16 length ‖ data`.
This is what `encodeExtension` emits, phrased as a total function so the
extension laws below can talk about it. -/
def extensionBytes (e : Extension) : ByteArray :=
  appendUInt16 ByteArray.empty e.extensionType ++
    (appendUInt16 ByteArray.empty (UInt16.ofNat e.data.size) ++ e.data)

/-- The wire image of an extension list: its members' images concatenated in
order, which is exactly the payload of an extensions block. -/
def extensionsBytes : List Extension → ByteArray
  | [] => ByteArray.empty
  | e :: rest => extensionBytes e ++ extensionsBytes rest

/-- One step of extension-list parsing: read `type ‖ uint16 length ‖ data`
until the cursor is exhausted, rejecting duplicate extension types.

Written as explicit well-founded recursion over the unconsumed bytes rather
than a `while` loop (whose `Loop.forIn` is a `partial def`, hence opaque to
the kernel) so the extension laws at the end of this file can evaluate it. -/
private def parseExtensionsLoop (r : Reader) (out : Array Extension) :
    Except String (Array Extension) :=
  if r.atEnd then
    .ok out
  else
    match h16 : r.readUInt16 with
    | .error e => .error e
    | .ok (extensionType, r₁) =>
      match hv : r₁.readVector16 with
      | .error e => .error e
      | .ok (data, r₂) =>
        if out.any (fun ext => ext.extensionType == extensionType) then
          .error s!"duplicate TLS extension {extensionType}"
        else
          have hlt : r₂.bytes.size - r₂.offset < r.bytes.size - r.offset := by
            obtain ⟨hb1, ho1, hle1⟩ := readUInt16_ok h16
            obtain ⟨hb2, ho2, hle2⟩ := readVector16_ok hv
            rw [hb2, hb1]
            rw [hb1] at hle2
            omega
          parseExtensionsLoop r₂ (out.push { extensionType, data })
  termination_by r.bytes.size - r.offset
  decreasing_by exact hlt

/-- Parse an extensions block: `type ‖ uint16 length ‖ data` repeated until
the block is exhausted, rejecting duplicate types. Extension types are not
interpreted here, so unknown (including GREASE) types are kept verbatim. -/
def parseExtensions (bytes : ByteArray) : Except String (Array Extension) :=
  parseExtensionsLoop { bytes } #[]

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

/-- Validate an optional first-flight P-256 share. Split out (like the two
optional-extension helpers below) so the `encodeClientHello` do-chain stays
linear, which lets `encodeClientHello_frame` peel it one bind at a time. -/
private def checkP256PublicKey : Option ByteArray → Except String Unit
  | none => pure ()
  | some publicKey => do
    unless publicKey.size == 65 && publicKey.get! 0 == 4 do
      throw "P-256 public key must be a 65-byte SEC1 uncompressed point"

/-- The SNI extension bytes, or empty when no name is offered. -/
private def serverNameExtensionBytes : Option String → Except String ByteArray
  | none => pure ByteArray.empty
  | some name => serverNameClientExtension name

/-- The ALPN extension bytes, or empty when no protocol is offered. -/
private def alpnExtensionBytes (protocols : Array String) :
    Except String ByteArray :=
  if protocols.isEmpty then
    pure ByteArray.empty
  else
    alpnClientExtension protocols

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
  checkP256PublicKey cfg.p256PublicKey
  if cfg.legacySessionId.size > 32 then
    throw s!"legacy session id exceeds 32 bytes ({cfg.legacySessionId.size})"

  let mut extensions := ← supportedVersionsClientExtension
  extensions := extensions ++ (← supportedGroupsClientExtension cfg.p256PublicKey.isSome)
  extensions := extensions ++ (← signatureAlgorithmsClientExtension)
  extensions := extensions ++
    (← keyShareClientExtension cfg.x25519PublicKey cfg.p256PublicKey)
  extensions := extensions ++ (← serverNameExtensionBytes cfg.serverName)
  extensions := extensions ++ (← alpnExtensionBytes cfg.alpnProtocols)

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

/-- The per-group key-share size check shared by the ServerHello parser and
its laws. -/
private def checkKeyShareSize : NamedGroup → ByteArray → Except String Unit
  | .x25519, keyExchange =>
      if keyExchange.size == 32 then
        .ok ()
      else
        .error s!"server x25519 public key must be 32 bytes, got {keyExchange.size}"
  | .secp256r1, keyExchange =>
      if keyExchange.size == 65 && keyExchange.get! 0 == 4 then
        .ok ()
      else
        .error "server P-256 key share must be a 65-byte SEC1 uncompressed point"

/-- The ServerHello key_share extension body: one `group ‖ uint16 key` entry.
Split out of `parseServerHello` so its law can be stated on its own. -/
private def parseServerKeyShare (data : ByteArray) :
    Except String (NamedGroup × ByteArray) :=
  match ({ bytes := data } : Reader).readUInt16 with
  | .error e => .error e
  | .ok (groupId, kr) =>
    match NamedGroup.ofUInt16? groupId with
    | none => .error s!"server selected unsupported key-share group {groupId}"
    | some selectedGroup =>
      match kr.readVector16 with
      | .error e => .error e
      | .ok (keyExchange, kr) =>
        match kr.requireEnd "ServerHello key_share" with
        | .error e => .error e
        | .ok () =>
          match checkKeyShareSize selectedGroup keyExchange with
          | .error e => .error e
          | .ok () => .ok (selectedGroup, keyExchange)

/-- Parse a ServerHello. (Written as a pure `if`/`match` chain so the
ServerHello laws below can evaluate it.) -/
def parseServerHello (msg : Message) : Except String ServerHello :=
  if msg.msgType == serverHelloType then
    match ({ bytes := msg.body } : Reader).readUInt16 with
    | .error e => .error e
    | .ok (legacyVersion, r) =>
      if legacyVersion == legacyTls12Version then
        match r.take 32 with
        | .error e => .error e
        | .ok (random, r) =>
          if random == helloRetryRequestRandom then
            .error "expected ServerHello, got HelloRetryRequest"
          else
            match r.readVector8 with
            | .error e => .error e
            | .ok (sessionId, r) =>
              if sessionId.size > 32 then
                .error s!"ServerHello legacy session id exceeds 32 bytes ({sessionId.size})"
              else
                match r.readUInt16 with
                | .error e => .error e
                | .ok (cipherSuite, r) =>
                  match r.readUInt8 with
                  | .error e => .error e
                  | .ok (compression, r) =>
                    if compression == 0 then
                      match r.readVector16 with
                      | .error e => .error e
                      | .ok (extensionBytes, r) =>
                        match r.requireEnd "ServerHello" with
                        | .error e => .error e
                        | .ok () =>
                          match parseExtensions extensionBytes with
                          | .error e => .error e
                          | .ok extensions =>
                            match requireExtension extensions
                                supportedVersionsExtension "supported_versions" with
                            | .error e => .error e
                            | .ok versionExt =>
                              if versionExt.data ==
                                  appendUInt16 ByteArray.empty tls13Version then
                                match requireExtension extensions keyShareExtension
                                    "key_share" with
                                | .error e => .error e
                                | .ok keyExt =>
                                  match parseServerKeyShare keyExt.data with
                                  | .error e => .error e
                                  | .ok (selectedGroup, keyExchange) =>
                                    .ok { random, legacySessionIdEcho := sessionId,
                                          cipherSuite, selectedGroup, keyExchange,
                                          extensions, encoded := msg.encoded }
                              else
                                .error "server did not select TLS 1.3"
                    else
                      .error s!"ServerHello selected non-null legacy compression {compression}"
      else
        .error s!"ServerHello legacy_version must be 0x0303, got {legacyVersion}"
  else
    .error s!"expected ServerHello ({serverHelloType}), got handshake type {msg.msgType}"

/-- The parsed wire fields of a HelloRetryRequest. An HRR uses the
ServerHello handshake type and is distinguished by its fixed random. -/
structure HelloRetryRequest where
  legacySessionIdEcho : ByteArray
  cipherSuite : UInt16
  selectedGroup : NamedGroup
  extensions : Array Extension
  encoded : ByteArray
  deriving Inhabited, BEq

/-- The HelloRetryRequest key_share extension body: a bare selected group.
Split out of `parseHelloRetryRequest` so its law can be stated on its own. -/
private def parseHrrKeyShare (data : ByteArray) : Except String NamedGroup :=
  match ({ bytes := data } : Reader).readUInt16 with
  | .error e => .error e
  | .ok (groupId, kr) =>
    match kr.requireEnd "HelloRetryRequest key_share" with
    | .error e => .error e
    | .ok () =>
      match NamedGroup.ofUInt16? groupId with
      | none => .error s!"HelloRetryRequest selected unsupported group {groupId}"
      | some selectedGroup => .ok selectedGroup

/-- Parse a HelloRetryRequest. (Written as a pure `if`/`match` chain so the
HelloRetryRequest laws below can evaluate it.) -/
def parseHelloRetryRequest (msg : Message) : Except String HelloRetryRequest :=
  if msg.msgType == serverHelloType then
    match ({ bytes := msg.body } : Reader).readUInt16 with
    | .error e => .error e
    | .ok (legacyVersion, r) =>
      if legacyVersion == legacyTls12Version then
        match r.take 32 with
        | .error e => .error e
        | .ok (random, r) =>
          if random == helloRetryRequestRandom then
            match r.readVector8 with
            | .error e => .error e
            | .ok (sessionId, r) =>
              if sessionId.size > 32 then
                .error s!"HelloRetryRequest legacy session id exceeds 32 bytes ({sessionId.size})"
              else
                match r.readUInt16 with
                | .error e => .error e
                | .ok (cipherSuite, r) =>
                  match r.readUInt8 with
                  | .error e => .error e
                  | .ok (compression, r) =>
                    if compression == 0 then
                      match r.readVector16 with
                      | .error e => .error e
                      | .ok (extensionBytes, r) =>
                        match r.requireEnd "HelloRetryRequest" with
                        | .error e => .error e
                        | .ok () =>
                          match parseExtensions extensionBytes with
                          | .error e => .error e
                          | .ok extensions =>
                            match requireExtension extensions
                                supportedVersionsExtension "supported_versions" with
                            | .error e => .error e
                            | .ok versionExt =>
                              if versionExt.data ==
                                  appendUInt16 ByteArray.empty tls13Version then
                                match requireExtension extensions keyShareExtension
                                    "key_share" with
                                | .error e => .error e
                                | .ok keyExt =>
                                  match parseHrrKeyShare keyExt.data with
                                  | .error e => .error e
                                  | .ok selectedGroup =>
                                    .ok { legacySessionIdEcho := sessionId, cipherSuite,
                                          selectedGroup, extensions,
                                          encoded := msg.encoded }
                              else
                                .error "HelloRetryRequest did not select TLS 1.3"
                    else
                      .error s!"HelloRetryRequest selected non-null legacy compression {compression}"
          else
            .error "ServerHello random is not the HelloRetryRequest sentinel"
      else
        .error s!"HelloRetryRequest legacy_version must be 0x0303, got {legacyVersion}"
  else
    .error s!"expected HelloRetryRequest ({serverHelloType}), got handshake type {msg.msgType}"

structure EncryptedExtensions where
  extensions : Array Extension
  encoded : ByteArray
  deriving Inhabited, BEq

/-- Parse EncryptedExtensions. (Written as a pure `if`/`match` chain so
`encodeEncryptedExtensions_parse` below can evaluate it.) -/
def parseEncryptedExtensions (msg : Message) : Except String EncryptedExtensions :=
  if msg.msgType == encryptedExtensionsType then
    match ({ bytes := msg.body } : Reader).readVector16 with
    | .error e => .error e
    | .ok (extensionBytes, r) =>
      match r.requireEnd "EncryptedExtensions" with
      | .error e => .error e
      | .ok () =>
        match parseExtensions extensionBytes with
        | .error e => .error e
        | .ok extensions => .ok { extensions, encoded := msg.encoded }
  else
    .error s!"expected EncryptedExtensions ({encryptedExtensionsType}), got {msg.msgType}"

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

/-- One step of certificate_list parsing: `uint24 cert ‖ uint16 extensions`
entries until the list is exhausted. Explicit well-founded recursion over the
unconsumed bytes (not a `while` loop) so the Certificate laws below can
evaluate it. -/
private def parseCertificateEntries (r : Reader) (entries : Array CertificateEntry) :
    Except String (Array CertificateEntry) :=
  if r.atEnd then
    .ok entries
  else
    match h24 : r.readVector24 with
    | .error e => .error e
    | .ok (der, r₁) =>
      if der.isEmpty then
        .error "Certificate contains an empty certificate entry"
      else
        match hv : r₁.readVector16 with
        | .error e => .error e
        | .ok (extensionBytes, r₂) =>
          match parseExtensions extensionBytes with
          | .error e => .error e
          | .ok extensions =>
            have hlt : r₂.bytes.size - r₂.offset < r.bytes.size - r.offset := by
              obtain ⟨hb1, ho1, hle1⟩ := readVector24_ok h24
              obtain ⟨hb2, ho2, hle2⟩ := readVector16_ok hv
              rw [hb2, hb1]
              rw [hb1] at hle2
              omega
            parseCertificateEntries r₂ (entries.push { der, extensions })
  termination_by r.bytes.size - r.offset
  decreasing_by exact hlt

/-- Parse a server Certificate. (Written as a pure `if`/`match` chain so
`encodeCertificate_parse` below can evaluate it.) -/
def parseCertificate (msg : Message) : Except String Certificate :=
  if msg.msgType == certificateType then
    match ({ bytes := msg.body } : Reader).readVector8 with
    | .error e => .error e
    | .ok (requestContext, r) =>
      if requestContext.isEmpty then
        match r.readVector24 with
        | .error e => .error e
        | .ok (certificateList, r) =>
          match r.requireEnd "Certificate" with
          | .error e => .error e
          | .ok () =>
            match parseCertificateEntries { bytes := certificateList } #[] with
            | .error e => .error e
            | .ok entries =>
              if entries.isEmpty then
                .error "server sent an empty certificate_list"
              else
                .ok { requestContext, entries, leafDer := entries[0]!.der,
                      encoded := msg.encoded }
      else
        .error "server Certificate request_context must be empty"
  else
    .error s!"expected Certificate ({certificateType}), got {msg.msgType}"

structure CertificateVerify where
  algorithm : UInt16
  signature : ByteArray
  encoded : ByteArray
  deriving Inhabited, BEq

/-- Parse CertificateVerify structurally. Scheme policy belongs to the TLS
client: it rejects forbidden or unoffered schemes, checks the leaf SPKI, and
verifies the signature over the raw transcript before advancing to Finished.
(Written as a pure `if`/`match` chain so `encodeCertificateVerify_parse` can
evaluate it.) -/
def parseCertificateVerify (msg : Message) : Except String CertificateVerify :=
  if msg.msgType == certificateVerifyType then
    match ({ bytes := msg.body } : Reader).readUInt16 with
    | .error e => .error e
    | .ok (algorithm, r) =>
      match r.readVector16 with
      | .error e => .error e
      | .ok (signature, r) =>
        match r.requireEnd "CertificateVerify" with
        | .error e => .error e
        | .ok () =>
          if signature.isEmpty then
            .error "CertificateVerify signature must not be empty"
          else
            .ok { algorithm, signature, encoded := msg.encoded }
  else
    .error s!"expected CertificateVerify ({certificateVerifyType}), got {msg.msgType}"

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

/-- The early_data check applied to a parsed NewSessionTicket extension list.
Split out so `parseNewSessionTicket` stays a flat `if`/`match` chain. -/
private def checkTicketEarlyData (extensions : Array Extension) :
    Except String Unit :=
  match findExtension? extensions earlyDataExtension with
  | none => .ok ()
  | some earlyData =>
      if earlyData.data.size == 4 then
        .ok ()
      else
        .error
          "NewSessionTicket early_data extension must contain uint32 max_early_data_size"

/-- Parse a NewSessionTicket. (Written as a pure `if`/`match` chain so
`encodeNewSessionTicket_parse` below can evaluate it.) -/
def parseNewSessionTicket (msg : Message) : Except String NewSessionTicket :=
  if msg.msgType == newSessionTicketType then
    match ({ bytes := msg.body } : Reader).readUInt32 with
    | .error e => .error e
    | .ok (lifetime, r) =>
      if lifetime > 604800 then
        .error s!"NewSessionTicket lifetime exceeds seven days ({lifetime})"
      else
        match r.readUInt32 with
        | .error e => .error e
        | .ok (ageAdd, r) =>
          match r.readVector8 with
          | .error e => .error e
          | .ok (nonce, r) =>
            match r.readVector16 with
            | .error e => .error e
            | .ok (ticket, r) =>
              if ticket.isEmpty then
                .error "NewSessionTicket ticket must not be empty"
              else
                match r.readVector16 with
                | .error e => .error e
                | .ok (extensionBytes, r) =>
                  match r.requireEnd "NewSessionTicket" with
                  | .error e => .error e
                  | .ok () =>
                    match parseExtensions extensionBytes with
                    | .error e => .error e
                    | .ok extensions =>
                      match checkTicketEarlyData extensions with
                      | .error e => .error e
                      | .ok () =>
                        .ok { ticketLifetime := lifetime, ticketAgeAdd := ageAdd,
                              ticketNonce := nonce, ticket, extensions,
                              encoded := msg.encoded }
  else
    .error s!"expected NewSessionTicket ({newSessionTicketType}), got {msg.msgType}"

/-- Build a NewSessionTicket carrying no extensions. Mirrors
`parseNewSessionTicket`: the same lifetime and non-empty-ticket checks, in the
same order. -/
def encodeNewSessionTicket (ticketLifetime ticketAgeAdd : UInt32)
    (ticketNonce ticket : ByteArray) : Except String Message :=
  if ticketLifetime > 604800 then
    .error s!"NewSessionTicket lifetime exceeds seven days ({ticketLifetime})"
  else if ticket.isEmpty then
    .error "NewSessionTicket ticket must not be empty"
  else
    match encodeVector8 ticketNonce with
    | .error e => .error e
    | .ok nonceVector =>
      match encodeVector16 ticket with
      | .error e => .error e
      | .ok ticketVector =>
        match encodeVector16 ByteArray.empty with
        | .error e => .error e
        | .ok extensionsVector =>
          frame newSessionTicketType
            (appendUInt32 ByteArray.empty ticketLifetime ++
              appendUInt32 ByteArray.empty ticketAgeAdd ++ nonceVector ++
              ticketVector ++ extensionsVector)

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

/-- Encode a certificate_list body: `uint24 cert ‖ uint16 extensions` per
entry, with empty per-entry extensions. Explicit recursion (not a `for` loop)
so the Certificate laws below can evaluate it. -/
private def encodeCertificateList : List ByteArray → Except String ByteArray
  | [] => .ok ByteArray.empty
  | der :: rest =>
    if der.isEmpty then
      .error "server Certificate chain contains an empty entry"
    else
      match encodeVector24 der with
      | .error e => .error e
      | .ok entry =>
        match encodeVector16 ByteArray.empty with
        | .error e => .error e
        | .ok noExtensions =>
          match encodeCertificateList rest with
          | .error e => .error e
          | .ok tail => .ok (entry ++ noExtensions ++ tail)

/-- Build a server Certificate message from a DER chain (leaf first). Uses an
empty certificate_request_context and empty per-entry extensions. -/
def encodeCertificate (chain : Array ByteArray) : Except String Message :=
  if chain.isEmpty then
    .error "server Certificate chain must not be empty"
  else
    match encodeCertificateList chain.toList with
    | .error e => .error e
    | .ok list =>
      match encodeVector8 ByteArray.empty with
      | .error e => .error e
      | .ok requestContext =>
        match encodeVector24 list with
        | .error e => .error e
        | .ok certificateList => frame certificateType (requestContext ++ certificateList)

/-- Build a CertificateVerify from a signature scheme and signature bytes. -/
def encodeCertificateVerify (algorithm : UInt16) (signature : ByteArray) :
    Except String Message := do
  if signature.isEmpty then
    throw "CertificateVerify signature must not be empty"
  frame certificateVerifyType
    (appendUInt16 ByteArray.empty algorithm ++ (← encodeVector16 signature))

/-!
## Wire-codec roundtrip laws

Kernel-checked encode/parse inversion for the handshake framing layer:
`frame` output is accepted byte-for-byte by `decodeOne` with an explicit
residual (`decodeOne_frame`), and every message encoder therefore roundtrips
through the wire decoder (`encode*_decode`). The loop-free message bodies
also invert semantically (`encodeFinished_parse`, `encodeKeyUpdate_parse`,
`encodeCertificateVerify_parse`). -/

/-! ### `ByteArray.get!` bridges -/

private theorem get!_eq_getElem {a : ByteArray} {i : Nat} (h : i < a.size) :
    a.get! i = a[i] := by
  rcases a with ⟨data⟩
  show data[i]! = _
  rw [getElem!_pos data i h]
  rfl

private theorem get!_append_left {a b : ByteArray} {i : Nat} (h : i < a.size) :
    (a ++ b).get! i = a.get! i := by
  rw [get!_eq_getElem (by simp [ByteArray.size_append]; omega),
    get!_eq_getElem h, ByteArray.getElem_append_left h]

private theorem get!_append_right {a b : ByteArray} {i : Nat}
    (h1 : a.size ≤ i) (h2 : i < a.size + b.size) :
    (a ++ b).get! i = b.get! (i - a.size) := by
  rw [get!_eq_getElem (by simp [ByteArray.size_append]; omega),
    get!_eq_getElem (by omega), ByteArray.getElem_append_right h1]

private theorem extract_get! {a : ByteArray} {s e k : Nat} (hk : s + k < e)
    (he : e ≤ a.size) : (a.extract s e).get! k = a.get! (s + k) := by
  have hsize : (a.extract s e).size = e - s := by
    rw [ByteArray.size_extract]
    omega
  rw [get!_eq_getElem (by omega), ByteArray.getElem_extract,
    get!_eq_getElem (by omega)]

/-- `ByteArray` has no `LawfulBEq` instance, but its `BEq` is `Array`'s. -/
private theorem beq_self (b : ByteArray) : (b == b) = true := by
  show (b.data == b.data) = true
  exact beq_self_eq_true b.data

/-! ### `Except` peeling helpers -/

private theorem bind_ok_ex {α β : Type} {x : Except String α}
    {f : α → Except String β} {b : β} (h : (x >>= f) = .ok b) :
    ∃ a, x = .ok a ∧ f a = .ok b := by
  cases x with
  | error e => cases h
  | ok a => exact ⟨a, rfl, h⟩

private theorem ite_ok_cases {β : Type} {c : Prop} [Decidable c]
    {t e : Except String β} {b : β} (h : (if c then t else e) = .ok b) :
    (c ∧ t = .ok b) ∨ (¬c ∧ e = .ok b) := by
  split at h
  · exact .inl ⟨‹_›, h⟩
  · exact .inr ⟨‹_›, h⟩

private theorem pure_eq_ok {α : Type} {a b : α}
    (h : (pure a : Except String α) = .ok b) : a = b := by
  have h' : Except.ok a = Except.ok b := h
  injection h'

/-! ### The `type ‖ uint24 length ‖ body` frame -/

/-- The big-endian `uint24` length bytes of a handshake frame header. -/
def length24Bytes (n : Nat) : ByteArray :=
  ((ByteArray.empty.push (UInt8.ofNat (n >>> 16))).push
    (UInt8.ofNat (n >>> 8))).push (UInt8.ofNat n)

private theorem encodeLength24_ok {n : Nat} {out : ByteArray}
    (h : encodeLength24 n = .ok out) :
    n < 2 ^ 24 ∧ out = length24Bytes n := by
  unfold encodeLength24 at h
  obtain ⟨hc, h⟩ | ⟨hc, h⟩ := ite_ok_cases h
  · obtain ⟨_, hu, _⟩ := bind_ok_ex h
    cases hu
  · exact ⟨by omega, (pure_eq_ok h).symm⟩

/-- Everything a successful `frame` says: the body fit, and the message is
its exact `type ‖ uint24 length ‖ body` encoding. -/
theorem frame_spec {msgType : UInt8} {body : ByteArray} {msg : Message}
    (h : frame msgType body = .ok msg) :
    body.size < 2 ^ 24 ∧
    msg = { msgType := msgType, body := body,
            encoded := ByteArray.empty.push msgType ++
              length24Bytes body.size ++ body } := by
  unfold frame at h
  obtain ⟨len, hlen, h⟩ := bind_ok_ex h
  obtain ⟨hsize, hbytes⟩ := encodeLength24_ok hlen
  refine ⟨hsize, ?_⟩
  rw [← pure_eq_ok h, hbytes]

private theorem uint24_recompose {n : Nat} (h : n < 2 ^ 24) :
    (UInt8.ofNat (n >>> 16)).toNat <<< 16 |||
      (UInt8.ofNat (n >>> 8)).toNat <<< 8 ||| (UInt8.ofNat n).toNat = n := by
  rw [UInt8.toNat_ofNat', UInt8.toNat_ofNat', UInt8.toNat_ofNat']
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Nat.testBit_or, Nat.testBit_shiftLeft, Nat.testBit_mod_two_pow,
    Nat.testBit_shiftRight]
  by_cases h8 : i < 8
  · have e1 : ¬i ≥ 16 := by omega
    have e2 : ¬i ≥ 8 := by omega
    simp [e1, e2, h8]
  · by_cases h16 : i < 16
    · have e1 : ¬i ≥ 16 := by omega
      have e2 : i ≥ 8 := by omega
      have e3 : i - 8 < 8 := by omega
      have e4 : 8 + (i - 8) = i := by omega
      simp [e1, e2, e3, e4, h8]
    · by_cases h24 : i < 24
      · have e1 : i ≥ 16 := by omega
        have e3 : i - 16 < 8 := by omega
        have e4 : 16 + (i - 16) = i := by omega
        have e5 : ¬i - 8 < 8 := by omega
        simp [e1, e3, e4, e5, h8]
      · have e1 : ¬i - 16 < 8 := by omega
        have e5 : ¬i - 8 < 8 := by omega
        have hn : n.testBit i = false :=
          Nat.testBit_lt_two_pow
            (Nat.lt_of_lt_of_le h (Nat.pow_le_pow_right (by omega) (by omega)))
        simp [e1, e5, h8, hn]

/-! ### Reader evaluation lemmas -/

private theorem take_eval {b : ByteArray} {off n : Nat}
    (h : off + n ≤ b.size) :
    Reader.take { bytes := b, offset := off } n =
      .ok (b.extract off (off + n), { bytes := b, offset := off + n }) := by
  unfold Reader.take
  rw [if_neg]
  show ¬off + n > b.size
  omega

private theorem readUInt8_eval {b : ByteArray} {off : Nat} (h : off < b.size) :
    Reader.readUInt8 { bytes := b, offset := off } =
      .ok (b.get! off, { bytes := b, offset := off + 1 }) := by
  unfold Reader.readUInt8
  rw [take_eval (by omega)]
  show Except.ok ((b.extract off (off + 1)).get! 0,
    ({ bytes := b, offset := off + 1 } : Reader)) = _
  rw [extract_get! (by omega) (by omega)]
  rfl

private theorem readUInt24_eval {b : ByteArray} {off : Nat}
    (h : off + 3 ≤ b.size) :
    Reader.readUInt24 { bytes := b, offset := off } =
      .ok ((b.get! off).toNat <<< 16 ||| (b.get! (off + 1)).toNat <<< 8 |||
        (b.get! (off + 2)).toNat, { bytes := b, offset := off + 3 }) := by
  unfold Reader.readUInt24
  rw [take_eval (by omega)]
  show Except.ok (((b.extract off (off + 3)).get! 0).toNat <<< 16 |||
      ((b.extract off (off + 3)).get! 1).toNat <<< 8 |||
      ((b.extract off (off + 3)).get! 2).toNat,
    ({ bytes := b, offset := off + 3 } : Reader)) = _
  rw [extract_get! (by omega) (by omega), extract_get! (by omega) (by omega),
    extract_get! (by omega) (by omega)]
  rfl

private theorem uint32_recompose (v : UInt32) :
    ((v >>> 24).toUInt8.toUInt32 <<< 24 ||| (v >>> 16).toUInt8.toUInt32 <<< 16 |||
      (v >>> 8).toUInt8.toUInt32 <<< 8 ||| v.toUInt8.toUInt32) = v := by
  bv_decide

private theorem readUInt32_eval {b : ByteArray} {off : Nat}
    (h : off + 4 ≤ b.size) :
    Reader.readUInt32 (Reader.mk b off) =
      .ok ((b.get! off).toUInt32 <<< 24 ||| (b.get! (off + 1)).toUInt32 <<< 16 |||
        (b.get! (off + 2)).toUInt32 <<< 8 ||| (b.get! (off + 3)).toUInt32,
        Reader.mk b (off + 4)) := by
  unfold Reader.readUInt32
  rw [take_eval (by omega)]
  show Except.ok (((b.extract off (off + 4)).get! 0).toUInt32 <<< 24 |||
      ((b.extract off (off + 4)).get! 1).toUInt32 <<< 16 |||
      ((b.extract off (off + 4)).get! 2).toUInt32 <<< 8 |||
      ((b.extract off (off + 4)).get! 3).toUInt32,
    Reader.mk b (off + 4)) = _
  rw [extract_get! (by omega) (by omega), extract_get! (by omega) (by omega),
    extract_get! (by omega) (by omega), extract_get! (by omega) (by omega)]
  rfl

/-! ### Framing roundtrip with residual -/

/-- **Wire roundtrip with residual**: `decodeOne` accepts a framed message's
exact encoding, returns it unchanged, and consumes nothing beyond it. -/
theorem decodeOne_frame {msgType : UInt8} {body : ByteArray} {msg : Message}
    (h : frame msgType body = .ok msg) (rest : ByteArray) :
    decodeOne (msg.encoded ++ rest) = .ok (msg, rest) := by
  obtain ⟨hlt, hmsg⟩ := frame_spec h
  subst hmsg
  have hP1 : (ByteArray.empty.push msgType).size = 1 := rfl
  have hL3 : (length24Bytes body.size).size = 3 := rfl
  have hPL : (ByteArray.empty.push msgType ++ length24Bytes body.size).size
      = 4 := by
    rw [ByteArray.size_append, hP1, hL3]
  show decodeOne (ByteArray.empty.push msgType ++ length24Bytes body.size ++
    body ++ rest) = _
  rw [ByteArray.append_assoc]
  -- Facts about the assembled wire bytes, proved before generalizing.
  have hXsize : (ByteArray.empty.push msgType ++ length24Bytes body.size ++
      (body ++ rest)).size = 4 + (body.size + rest.size) := by
    rw [ByteArray.size_append, hPL, ByteArray.size_append]
  have hb0 : (ByteArray.empty.push msgType ++ length24Bytes body.size ++
      (body ++ rest)).get! 0 = msgType := by
    rw [get!_append_left (by omega), get!_append_left (by omega)]
    rfl
  have hb1 : (ByteArray.empty.push msgType ++ length24Bytes body.size ++
      (body ++ rest)).get! 1 = UInt8.ofNat (body.size >>> 16) := by
    rw [get!_append_left (by omega), get!_append_right (by omega) (by omega)]
    rfl
  have hb2 : (ByteArray.empty.push msgType ++ length24Bytes body.size ++
      (body ++ rest)).get! 2 = UInt8.ofNat (body.size >>> 8) := by
    rw [get!_append_left (by omega), get!_append_right (by omega) (by omega)]
    rfl
  have hb3 : (ByteArray.empty.push msgType ++ length24Bytes body.size ++
      (body ++ rest)).get! 3 = UInt8.ofNat body.size := by
    rw [get!_append_left (by omega), get!_append_right (by omega) (by omega)]
    rfl
  have hassoc : ByteArray.empty.push msgType ++ length24Bytes body.size ++
      (body ++ rest) = (ByteArray.empty.push msgType ++
        length24Bytes body.size ++ body) ++ rest :=
    ByteArray.append_assoc.symm
  have hbody : (ByteArray.empty.push msgType ++ length24Bytes body.size ++
      (body ++ rest)).extract 4 (4 + body.size) = body := by
    rw [ByteArray.extract_append,
      show ((ByteArray.empty.push msgType ++ length24Bytes body.size).extract
          4 (4 + body.size)) = ByteArray.empty from
        ByteArray.extract_eq_empty_iff.mpr (by rw [hPL]; omega),
      ByteArray.empty_append, hPL,
      show (4 : Nat) - 4 = 0 from rfl,
      show 4 + body.size - 4 = body.size from by omega,
      ByteArray.extract_append_eq_left rfl]
  have hencoded : (ByteArray.empty.push msgType ++ length24Bytes body.size ++
      (body ++ rest)).extract 0 (4 + body.size) =
      ByteArray.empty.push msgType ++ length24Bytes body.size ++ body := by
    rw [hassoc]
    exact ByteArray.extract_append_eq_left
      (by rw [ByteArray.size_append, hPL])
  have hrest : (ByteArray.empty.push msgType ++ length24Bytes body.size ++
      (body ++ rest)).extract (4 + body.size)
      (ByteArray.empty.push msgType ++ length24Bytes body.size ++
        (body ++ rest)).size = rest := by
    rw [hassoc]
    exact ByteArray.extract_append_eq_right
      (by rw [ByteArray.size_append, hPL]) ByteArray.size_append
  generalize hE : ByteArray.empty.push msgType ++ length24Bytes body.size ++
    (body ++ rest) = E at hXsize hb0 hb1 hb2 hb3 hbody hencoded hrest ⊢
  have h8 := readUInt8_eval (b := E) (off := 0) (by omega)
  rw [hb0] at h8
  have h24 : ({ bytes := E, offset := 1 } : Reader).readUInt24 =
      .ok ((E.get! 1).toNat <<< 16 ||| (E.get! 2).toNat <<< 8 |||
        (E.get! 3).toNat, { bytes := E, offset := 4 }) :=
    readUInt24_eval (by omega)
  rw [hb1, hb2, hb3, uint24_recompose hlt] at h24
  have htk : ({ bytes := E, offset := 4 } : Reader).take body.size =
      .ok (E.extract 4 (4 + body.size),
        { bytes := E, offset := 4 + body.size }) :=
    take_eval (by omega)
  rw [hbody] at htk
  unfold decodeOne
  simp only [h8, h24, htk]
  rw [hencoded, hrest]

/-- Exact wire roundtrip: `decode` inverts `frame`. -/
theorem decode_frame {msgType : UInt8} {body : ByteArray} {msg : Message}
    (h : frame msgType body = .ok msg) : decode msg.encoded = .ok msg := by
  have hone := decodeOne_frame h ByteArray.empty
  rw [ByteArray.append_empty] at hone
  unfold decode
  simp only [hone]
  rw [if_pos (show ByteArray.empty.isEmpty = true from rfl)]

/-! ### Every message encoder roundtrips through the wire decoder

Each encoder ends in `frame`, so peeling its do-chain produces the frame
equation and `decodeOne_frame`/`decode_frame` apply. -/

private theorem encodeFinished_frame {verifyData : ByteArray} {msg : Message}
    (h : encodeFinished verifyData = .ok msg) :
    ∃ body, frame finishedType body = .ok msg := by
  unfold encodeFinished at h
  obtain ⟨hc, h⟩ | ⟨hc, h⟩ := ite_ok_cases h
  · obtain ⟨_, _, h⟩ := bind_ok_ex h
    exact ⟨_, h⟩
  · obtain ⟨_, hu, _⟩ := bind_ok_ex h
    cases hu

private theorem encodeKeyUpdate_frame {request : KeyUpdateRequest}
    {msg : Message} (h : encodeKeyUpdate request = .ok msg) :
    ∃ body, frame keyUpdateType body = .ok msg :=
  ⟨_, h⟩

private theorem encodeCertificateVerify_frame {algorithm : UInt16}
    {signature : ByteArray} {msg : Message}
    (h : encodeCertificateVerify algorithm signature = .ok msg) :
    ∃ body, frame certificateVerifyType body = .ok msg := by
  unfold encodeCertificateVerify at h
  obtain ⟨hc, h⟩ | ⟨hc, h⟩ := ite_ok_cases h
  · obtain ⟨_, hu, _⟩ := bind_ok_ex h
    cases hu
  · obtain ⟨_, _, h⟩ := bind_ok_ex h
    obtain ⟨_, _, h⟩ := bind_ok_ex h
    exact ⟨_, h⟩

private theorem encodeEncryptedExtensions_frame {alpnSelected : Option String}
    {msg : Message} (h : encodeEncryptedExtensions alpnSelected = .ok msg) :
    ∃ body, frame encryptedExtensionsType body = .ok msg := by
  unfold encodeEncryptedExtensions at h
  cases halpn : alpnSelected with
  | some protocol =>
    rw [halpn] at h
    obtain ⟨_, _, h⟩ := bind_ok_ex h
    obtain ⟨_, _, h⟩ := bind_ok_ex h
    obtain ⟨_, _, h⟩ := bind_ok_ex h
    exact ⟨_, h⟩
  | none =>
    rw [halpn] at h
    obtain ⟨_, _, h⟩ := bind_ok_ex h
    obtain ⟨_, _, h⟩ := bind_ok_ex h
    exact ⟨_, h⟩

private theorem encodeCertificate_frame {chain : Array ByteArray}
    {msg : Message} (h : encodeCertificate chain = .ok msg) :
    ∃ body, frame certificateType body = .ok msg := by
  unfold encodeCertificate at h
  split at h
  · cases h
  · split at h
    · cases h
    · split at h
      · cases h
      · split at h
        · cases h
        · exact ⟨_, h⟩

private theorem encodeClientHello_frame {cfg : ClientHelloConfig}
    {msg : Message} (h : encodeClientHello cfg = .ok msg) :
    ∃ body, frame clientHelloType body = .ok msg := by
  unfold encodeClientHello at h
  obtain ⟨hc1, h⟩ | ⟨hc1, h⟩ := ite_ok_cases h
  · obtain ⟨_, _, h⟩ := bind_ok_ex h
    obtain ⟨hc2, h⟩ | ⟨hc2, h⟩ := ite_ok_cases h
    · obtain ⟨_, _, h⟩ := bind_ok_ex h
      obtain ⟨_, _, h⟩ := bind_ok_ex h
      obtain ⟨hc3, h⟩ | ⟨hc3, h⟩ := ite_ok_cases h
      · obtain ⟨_, hu, _⟩ := bind_ok_ex h
        cases hu
      · obtain ⟨_, _, h⟩ := bind_ok_ex h
        obtain ⟨_, _, h⟩ := bind_ok_ex h
        obtain ⟨_, _, h⟩ := bind_ok_ex h
        obtain ⟨_, _, h⟩ := bind_ok_ex h
        obtain ⟨_, _, h⟩ := bind_ok_ex h
        obtain ⟨_, _, h⟩ := bind_ok_ex h
        obtain ⟨_, _, h⟩ := bind_ok_ex h
        obtain ⟨_, _, h⟩ := bind_ok_ex h
        obtain ⟨_, _, h⟩ := bind_ok_ex h
        obtain ⟨_, _, h⟩ := bind_ok_ex h
        obtain ⟨_, _, h⟩ := bind_ok_ex h
        exact ⟨_, h⟩
    · obtain ⟨_, hu, _⟩ := bind_ok_ex h
      cases hu
  · obtain ⟨_, hu, _⟩ := bind_ok_ex h
    cases hu

private theorem encodeServerHello_frame {random legacySessionIdEcho : ByteArray}
    {group : NamedGroup} {keyExchange : ByteArray} {cipherSuite : UInt16}
    {msg : Message}
    (h : encodeServerHello random legacySessionIdEcho group keyExchange
      cipherSuite = .ok msg) :
    ∃ body, frame serverHelloType body = .ok msg := by
  unfold encodeServerHello at h
  obtain ⟨hc, h⟩ | ⟨hc, h⟩ := ite_ok_cases h
  · obtain ⟨hc2, h⟩ | ⟨hc2, h⟩ := ite_ok_cases h
    · obtain ⟨_, hu, _⟩ := bind_ok_ex h
      cases hu
    · obtain ⟨_, _, h⟩ := bind_ok_ex h
      obtain ⟨_, _, h⟩ := bind_ok_ex h
      obtain ⟨_, _, h⟩ := bind_ok_ex h
      obtain ⟨_, _, h⟩ := bind_ok_ex h
      obtain ⟨_, _, h⟩ := bind_ok_ex h
      obtain ⟨_, _, h⟩ := bind_ok_ex h
      exact ⟨_, h⟩
  · obtain ⟨_, hu, _⟩ := bind_ok_ex h
    cases hu

private theorem encodeHelloRetryRequest_frame {legacySessionIdEcho : ByteArray}
    {group : NamedGroup} {cipherSuite : UInt16} {msg : Message}
    (h : encodeHelloRetryRequest legacySessionIdEcho group cipherSuite
      = .ok msg) :
    ∃ body, frame serverHelloType body = .ok msg := by
  unfold encodeHelloRetryRequest at h
  obtain ⟨hc, h⟩ | ⟨hc, h⟩ := ite_ok_cases h
  · obtain ⟨_, hu, _⟩ := bind_ok_ex h
    cases hu
  · obtain ⟨_, _, h⟩ := bind_ok_ex h
    obtain ⟨_, _, h⟩ := bind_ok_ex h
    obtain ⟨_, _, h⟩ := bind_ok_ex h
    obtain ⟨_, _, h⟩ := bind_ok_ex h
    obtain ⟨_, _, h⟩ := bind_ok_ex h
    exact ⟨_, h⟩

/-- ClientHello wire roundtrip with residual. -/
theorem encodeClientHello_decodeOne {cfg : ClientHelloConfig} {msg : Message}
    (h : encodeClientHello cfg = .ok msg) (rest : ByteArray) :
    decodeOne (msg.encoded ++ rest) = .ok (msg, rest) :=
  (encodeClientHello_frame h).elim fun _ hf => decodeOne_frame hf rest

/-- ClientHello exact wire roundtrip. -/
theorem encodeClientHello_decode {cfg : ClientHelloConfig} {msg : Message}
    (h : encodeClientHello cfg = .ok msg) : decode msg.encoded = .ok msg :=
  (encodeClientHello_frame h).elim fun _ hf => decode_frame hf

/-- ServerHello wire roundtrip with residual. -/
theorem encodeServerHello_decodeOne {random legacySessionIdEcho : ByteArray}
    {group : NamedGroup} {keyExchange : ByteArray} {cipherSuite : UInt16}
    {msg : Message}
    (h : encodeServerHello random legacySessionIdEcho group keyExchange
      cipherSuite = .ok msg) (rest : ByteArray) :
    decodeOne (msg.encoded ++ rest) = .ok (msg, rest) :=
  (encodeServerHello_frame h).elim fun _ hf => decodeOne_frame hf rest

/-- ServerHello exact wire roundtrip. -/
theorem encodeServerHello_decode {random legacySessionIdEcho : ByteArray}
    {group : NamedGroup} {keyExchange : ByteArray} {cipherSuite : UInt16}
    {msg : Message}
    (h : encodeServerHello random legacySessionIdEcho group keyExchange
      cipherSuite = .ok msg) : decode msg.encoded = .ok msg :=
  (encodeServerHello_frame h).elim fun _ hf => decode_frame hf

/-- HelloRetryRequest wire roundtrip with residual. -/
theorem encodeHelloRetryRequest_decodeOne {legacySessionIdEcho : ByteArray}
    {group : NamedGroup} {cipherSuite : UInt16} {msg : Message}
    (h : encodeHelloRetryRequest legacySessionIdEcho group cipherSuite
      = .ok msg) (rest : ByteArray) :
    decodeOne (msg.encoded ++ rest) = .ok (msg, rest) :=
  (encodeHelloRetryRequest_frame h).elim fun _ hf => decodeOne_frame hf rest

/-- HelloRetryRequest exact wire roundtrip. -/
theorem encodeHelloRetryRequest_decode {legacySessionIdEcho : ByteArray}
    {group : NamedGroup} {cipherSuite : UInt16} {msg : Message}
    (h : encodeHelloRetryRequest legacySessionIdEcho group cipherSuite
      = .ok msg) : decode msg.encoded = .ok msg :=
  (encodeHelloRetryRequest_frame h).elim fun _ hf => decode_frame hf

/-- EncryptedExtensions wire roundtrip with residual. -/
theorem encodeEncryptedExtensions_decodeOne {alpnSelected : Option String}
    {msg : Message} (h : encodeEncryptedExtensions alpnSelected = .ok msg)
    (rest : ByteArray) : decodeOne (msg.encoded ++ rest) = .ok (msg, rest) :=
  (encodeEncryptedExtensions_frame h).elim fun _ hf => decodeOne_frame hf rest

/-- EncryptedExtensions exact wire roundtrip. -/
theorem encodeEncryptedExtensions_decode {alpnSelected : Option String}
    {msg : Message} (h : encodeEncryptedExtensions alpnSelected = .ok msg) :
    decode msg.encoded = .ok msg :=
  (encodeEncryptedExtensions_frame h).elim fun _ hf => decode_frame hf

/-- Certificate wire roundtrip with residual. -/
theorem encodeCertificate_decodeOne {chain : Array ByteArray} {msg : Message}
    (h : encodeCertificate chain = .ok msg) (rest : ByteArray) :
    decodeOne (msg.encoded ++ rest) = .ok (msg, rest) :=
  (encodeCertificate_frame h).elim fun _ hf => decodeOne_frame hf rest

/-- Certificate exact wire roundtrip. -/
theorem encodeCertificate_decode {chain : Array ByteArray} {msg : Message}
    (h : encodeCertificate chain = .ok msg) : decode msg.encoded = .ok msg :=
  (encodeCertificate_frame h).elim fun _ hf => decode_frame hf

/-- CertificateVerify wire roundtrip with residual. -/
theorem encodeCertificateVerify_decodeOne {algorithm : UInt16}
    {signature : ByteArray} {msg : Message}
    (h : encodeCertificateVerify algorithm signature = .ok msg)
    (rest : ByteArray) : decodeOne (msg.encoded ++ rest) = .ok (msg, rest) :=
  (encodeCertificateVerify_frame h).elim fun _ hf => decodeOne_frame hf rest

/-- CertificateVerify exact wire roundtrip. -/
theorem encodeCertificateVerify_decode {algorithm : UInt16}
    {signature : ByteArray} {msg : Message}
    (h : encodeCertificateVerify algorithm signature = .ok msg) :
    decode msg.encoded = .ok msg :=
  (encodeCertificateVerify_frame h).elim fun _ hf => decode_frame hf

/-- Finished wire roundtrip with residual. -/
theorem encodeFinished_decodeOne {verifyData : ByteArray} {msg : Message}
    (h : encodeFinished verifyData = .ok msg) (rest : ByteArray) :
    decodeOne (msg.encoded ++ rest) = .ok (msg, rest) :=
  (encodeFinished_frame h).elim fun _ hf => decodeOne_frame hf rest

/-- Finished exact wire roundtrip. -/
theorem encodeFinished_decode {verifyData : ByteArray} {msg : Message}
    (h : encodeFinished verifyData = .ok msg) : decode msg.encoded = .ok msg :=
  (encodeFinished_frame h).elim fun _ hf => decode_frame hf

private theorem encodeNewSessionTicket_frame {ticketLifetime ticketAgeAdd : UInt32}
    {ticketNonce ticket : ByteArray} {msg : Message}
    (h : encodeNewSessionTicket ticketLifetime ticketAgeAdd ticketNonce ticket
      = .ok msg) :
    ∃ body, frame newSessionTicketType body = .ok msg := by
  unfold encodeNewSessionTicket at h
  split at h
  · cases h
  · split at h
    · cases h
    · split at h
      · cases h
      · split at h
        · cases h
        · split at h
          · cases h
          · exact ⟨_, h⟩

/-- NewSessionTicket wire roundtrip with residual. -/
theorem encodeNewSessionTicket_decodeOne {ticketLifetime ticketAgeAdd : UInt32}
    {ticketNonce ticket : ByteArray} {msg : Message}
    (h : encodeNewSessionTicket ticketLifetime ticketAgeAdd ticketNonce ticket
      = .ok msg) (rest : ByteArray) :
    decodeOne (msg.encoded ++ rest) = .ok (msg, rest) :=
  (encodeNewSessionTicket_frame h).elim fun _ hf => decodeOne_frame hf rest

/-- NewSessionTicket exact wire roundtrip. -/
theorem encodeNewSessionTicket_decode {ticketLifetime ticketAgeAdd : UInt32}
    {ticketNonce ticket : ByteArray} {msg : Message}
    (h : encodeNewSessionTicket ticketLifetime ticketAgeAdd ticketNonce ticket
      = .ok msg) : decode msg.encoded = .ok msg :=
  (encodeNewSessionTicket_frame h).elim fun _ hf => decode_frame hf

/-- KeyUpdate wire roundtrip with residual. -/
theorem encodeKeyUpdate_decodeOne {request : KeyUpdateRequest} {msg : Message}
    (h : encodeKeyUpdate request = .ok msg) (rest : ByteArray) :
    decodeOne (msg.encoded ++ rest) = .ok (msg, rest) :=
  (encodeKeyUpdate_frame h).elim fun _ hf => decodeOne_frame hf rest

/-- KeyUpdate exact wire roundtrip. -/
theorem encodeKeyUpdate_decode {request : KeyUpdateRequest} {msg : Message}
    (h : encodeKeyUpdate request = .ok msg) : decode msg.encoded = .ok msg :=
  (encodeKeyUpdate_frame h).elim fun _ hf => decode_frame hf

/-! ### Body-level parse inversion for the loop-free messages -/

/-- Parse inverts encode for Finished. -/
theorem encodeFinished_parse {verifyData : ByteArray} {msg : Message}
    (h : encodeFinished verifyData = .ok msg) :
    parseFinished msg = .ok { verifyData := verifyData,
                              encoded := msg.encoded } := by
  unfold encodeFinished at h
  obtain ⟨hsz, h⟩ | ⟨hsz, h⟩ := ite_ok_cases h
  · obtain ⟨_, _, h⟩ := bind_ok_ex h
    obtain ⟨hlt, hmsg⟩ := frame_spec h
    have hty : msg.msgType = finishedType := by rw [hmsg]
    have hbd : msg.body = verifyData := by rw [hmsg]
    unfold parseFinished
    rw [hty, hbd,
      if_pos (show (finishedType == finishedType) = true from rfl),
      if_pos hsz]
    rfl
  · obtain ⟨_, hu, _⟩ := bind_ok_ex h
    cases hu

/-- Parse inverts encode for KeyUpdate. -/
theorem encodeKeyUpdate_parse {request : KeyUpdateRequest} {msg : Message}
    (h : encodeKeyUpdate request = .ok msg) :
    parseKeyUpdate msg = .ok { request := request,
                               encoded := msg.encoded } := by
  obtain ⟨hlt, hmsg⟩ := frame_spec h
  have hty : msg.msgType = keyUpdateType := by rw [hmsg]
  have hbd : msg.body = ByteArray.empty.push request.toUInt8 := by rw [hmsg]
  unfold parseKeyUpdate
  rw [hty, hbd,
    if_pos (show (keyUpdateType == keyUpdateType) = true from rfl),
    if_pos (show ((ByteArray.empty.push request.toUInt8).size == 1) = true
      from rfl)]
  cases request <;> rfl

private theorem uint16_recompose (v : UInt16) :
    ((v >>> 8).toUInt8.toUInt16 <<< 8 ||| v.toUInt8.toUInt16) = v := by
  bv_decide

private theorem encodeLength16_ok {n : Nat} {out : ByteArray}
    (h : encodeLength16 n = .ok out) :
    n < 2 ^ 16 ∧ out = appendUInt16 ByteArray.empty (UInt16.ofNat n) := by
  unfold encodeLength16 at h
  obtain ⟨hc, h⟩ | ⟨hc, h⟩ := ite_ok_cases h
  · obtain ⟨_, hu, _⟩ := bind_ok_ex h
    cases hu
  · exact ⟨by omega, (pure_eq_ok h).symm⟩

private theorem encodeVector16_ok {b out : ByteArray}
    (h : encodeVector16 b = .ok out) :
    b.size < 2 ^ 16 ∧
    out = appendUInt16 ByteArray.empty (UInt16.ofNat b.size) ++ b := by
  unfold encodeVector16 at h
  obtain ⟨len, hlen, h⟩ := bind_ok_ex h
  obtain ⟨hsize, hbytes⟩ := encodeLength16_ok hlen
  refine ⟨hsize, ?_⟩
  rw [← pure_eq_ok h, hbytes]

private theorem readUInt16_eval {b : ByteArray} {off : Nat}
    (h : off + 2 ≤ b.size) :
    Reader.readUInt16 { bytes := b, offset := off } =
      .ok ((b.get! off).toUInt16 <<< 8 ||| (b.get! (off + 1)).toUInt16,
        { bytes := b, offset := off + 2 }) := by
  unfold Reader.readUInt16
  rw [take_eval (by omega)]
  show Except.ok (((b.extract off (off + 2)).get! 0).toUInt16 <<< 8 |||
      ((b.extract off (off + 2)).get! 1).toUInt16,
    ({ bytes := b, offset := off + 2 } : Reader)) = _
  rw [extract_get! (by omega) (by omega), extract_get! (by omega) (by omega)]
  rfl

private theorem readVector16_eval {b : ByteArray} {off L : Nat}
    (hL : ((b.get! off).toUInt16 <<< 8 |||
      (b.get! (off + 1)).toUInt16).toNat = L)
    (h : off + 2 + L ≤ b.size) :
    Reader.readVector16 { bytes := b, offset := off } =
      .ok (b.extract (off + 2) (off + 2 + L),
        { bytes := b, offset := off + 2 + L }) := by
  unfold Reader.readVector16
  rw [readUInt16_eval (by omega)]
  show ({ bytes := b, offset := off + 2 } : Reader).take
    ((b.get! off).toUInt16 <<< 8 ||| (b.get! (off + 1)).toUInt16).toNat = _
  rw [hL, take_eval (by omega)]

private theorem requireEnd_eval {b : ByteArray} {off : Nat} {context : String}
    (h : off = b.size) :
    Reader.requireEnd { bytes := b, offset := off } context = .ok () := by
  unfold Reader.requireEnd
  rw [if_pos]
  · rfl
  · show (off == b.size) = true
    rw [h]
    exact beq_self_eq_true b.size

/-- Parse inverts encode for CertificateVerify. -/
theorem encodeCertificateVerify_parse {algorithm : UInt16}
    {signature : ByteArray} {msg : Message}
    (h : encodeCertificateVerify algorithm signature = .ok msg) :
    parseCertificateVerify msg =
      .ok { algorithm := algorithm, signature := signature,
            encoded := msg.encoded } := by
  unfold encodeCertificateVerify at h
  obtain ⟨hemp, h⟩ | ⟨hemp, h⟩ := ite_ok_cases h
  · obtain ⟨_, hu, _⟩ := bind_ok_ex h
    cases hu
  obtain ⟨_, _, h⟩ := bind_ok_ex h
  obtain ⟨V, hV, h⟩ := bind_ok_ex h
  obtain ⟨hszlt, hVeq⟩ := encodeVector16_ok hV
  obtain ⟨hlt, hmsg⟩ := frame_spec h
  subst hVeq
  have hty : msg.msgType = certificateVerifyType := by rw [hmsg]
  have hbd : msg.body = appendUInt16 ByteArray.empty algorithm ++
      (appendUInt16 ByteArray.empty (UInt16.ofNat signature.size) ++
        signature) := by rw [hmsg]
  -- Facts about the assembled body bytes.
  have hA2 : (appendUInt16 ByteArray.empty algorithm).size = 2 := rfl
  have hL2 : (appendUInt16 ByteArray.empty
    (UInt16.ofNat signature.size)).size = 2 := rfl
  have hLS : (appendUInt16 ByteArray.empty (UInt16.ofNat signature.size) ++
      signature).size = 2 + signature.size := by
    rw [ByteArray.size_append, hL2]
  have hBsize : (appendUInt16 ByteArray.empty algorithm ++
      (appendUInt16 ByteArray.empty (UInt16.ofNat signature.size) ++
        signature)).size = 2 + (2 + signature.size) := by
    rw [ByteArray.size_append, hA2, ByteArray.size_append, hL2]
  have hb0 : (appendUInt16 ByteArray.empty algorithm ++
      (appendUInt16 ByteArray.empty (UInt16.ofNat signature.size) ++
        signature)).get! 0 = (algorithm >>> 8).toUInt8 := by
    rw [get!_append_left (by omega)]
    rfl
  have hb1 : (appendUInt16 ByteArray.empty algorithm ++
      (appendUInt16 ByteArray.empty (UInt16.ofNat signature.size) ++
        signature)).get! 1 = algorithm.toUInt8 := by
    rw [get!_append_left (by omega)]
    rfl
  have hb2 : (appendUInt16 ByteArray.empty algorithm ++
      (appendUInt16 ByteArray.empty (UInt16.ofNat signature.size) ++
        signature)).get! 2 = (UInt16.ofNat signature.size >>> 8).toUInt8 := by
    rw [get!_append_right (by omega) (by omega),
      show (2 : Nat) - (appendUInt16 ByteArray.empty algorithm).size = 0
        from rfl,
      get!_append_left (by omega)]
    rfl
  have hb3 : (appendUInt16 ByteArray.empty algorithm ++
      (appendUInt16 ByteArray.empty (UInt16.ofNat signature.size) ++
        signature)).get! 3 = (UInt16.ofNat signature.size).toUInt8 := by
    rw [get!_append_right (by omega) (by omega),
      show (3 : Nat) - (appendUInt16 ByteArray.empty algorithm).size = 1
        from rfl,
      get!_append_left (by omega)]
    rfl
  have hslice : (appendUInt16 ByteArray.empty algorithm ++
      (appendUInt16 ByteArray.empty (UInt16.ofNat signature.size) ++
        signature)).extract (2 + 2) (2 + 2 + signature.size) = signature := by
    rw [show appendUInt16 ByteArray.empty algorithm ++
        (appendUInt16 ByteArray.empty (UInt16.ofNat signature.size) ++
          signature) =
        (appendUInt16 ByteArray.empty algorithm ++
          appendUInt16 ByteArray.empty (UInt16.ofNat signature.size)) ++
          signature from ByteArray.append_assoc.symm]
    exact ByteArray.extract_append_eq_right
      (by rw [ByteArray.size_append, hA2, hL2])
      (by rw [ByteArray.size_append, hA2, hL2])
  -- Evaluate the parser.
  unfold parseCertificateVerify
  rw [hty,
    if_pos (show (certificateVerifyType == certificateVerifyType) = true
      from rfl), hbd]
  generalize hB : appendUInt16 ByteArray.empty algorithm ++
    (appendUInt16 ByteArray.empty (UInt16.ofNat signature.size) ++
      signature) = B at hBsize hb0 hb1 hb2 hb3 hslice ⊢
  have hr16 : Reader.readUInt16 { bytes := B } =
      .ok (algorithm, { bytes := B, offset := 2 }) := by
    rw [readUInt16_eval (off := 0) (by omega), hb0,
      show B.get! (0 + 1) = algorithm.toUInt8 from hb1, uint16_recompose]
  have hL : ((B.get! 2).toUInt16 <<< 8 |||
      (B.get! (2 + 1)).toUInt16).toNat = signature.size := by
    rw [hb2, show B.get! (2 + 1) = (UInt16.ofNat signature.size).toUInt8
      from hb3, uint16_recompose, UInt16.toNat_ofNat']
    exact Nat.mod_eq_of_lt hszlt
  have hv16 : Reader.readVector16 { bytes := B, offset := 2 } =
      .ok (signature, { bytes := B, offset := 2 + 2 + signature.size }) := by
    rw [readVector16_eval hL (by omega), hslice]
  have hend : Reader.requireEnd
      { bytes := B, offset := 2 + 2 + signature.size } "CertificateVerify" =
      .ok () := requireEnd_eval (by omega)
  simp only [hr16, hv16, hend]
  rw [if_neg hemp]

/-! ### Reading an encoded field out of an assembled message body

Message bodies are concatenations of encoded fields. Each lemma below reads
one field sitting between an arbitrary prefix `P` (already consumed) and an
arbitrary suffix `S` (not yet consumed), so a body proof is just a walk down
the field list. -/

/-- Reading inside a sandwiched middle segment. -/
private theorem get!_mid {P M S : ByteArray} {k : Nat} (h : k < M.size) :
    (P ++ (M ++ S)).get! (P.size + k) = M.get! k := by
  rw [get!_append_right (by omega) (by rw [ByteArray.size_append]; omega),
    show P.size + k - P.size = k from by omega, get!_append_left h]

/-- Slicing out a sandwiched middle segment. -/
private theorem extract_mid (P M S : ByteArray) :
    (P ++ (M ++ S)).extract P.size (P.size + M.size) = M := by
  have h := ByteArray.extract_append_size_add (a := P) (b := M ++ S) (i := 0)
    (j := M.size)
  rw [Nat.add_zero] at h
  rw [h]
  exact ByteArray.extract_append_eq_left rfl

/-- A fixed-size field read. -/
private theorem take_at {P X S : ByteArray} {n : Nat} (hn : X.size = n) :
    Reader.take { bytes := P ++ (X ++ S), offset := P.size } n =
      .ok (X, { bytes := P ++ (X ++ S), offset := P.size + n }) := by
  subst hn
  rw [take_eval (by rw [ByteArray.size_append, ByteArray.size_append]; omega),
    extract_mid]

private theorem readUInt8_at {P S : ByteArray} {b : UInt8} :
    Reader.readUInt8 (Reader.mk (P ++ (ByteArray.empty.push b ++ S)) P.size) =
      .ok (b, Reader.mk (P ++ (ByteArray.empty.push b ++ S)) (P.size + 1)) := by
  have h0 : (P ++ (ByteArray.empty.push b ++ S)).get! P.size = b := by
    have h := get!_mid (P := P) (M := ByteArray.empty.push b) (S := S) (k := 0)
      (by show 0 < 1; omega)
    rw [Nat.add_zero] at h
    rw [h]
    rfl
  have hbound : P.size < (P ++ (ByteArray.empty.push b ++ S)).size := by
    rw [ByteArray.size_append, ByteArray.size_append]
    show P.size < P.size + (1 + S.size)
    omega
  rw [readUInt8_eval hbound, h0]

private theorem readUInt16_at {P S : ByteArray} {v : UInt16} :
    Reader.readUInt16
        (Reader.mk (P ++ (appendUInt16 ByteArray.empty v ++ S)) P.size) =
      .ok (v, Reader.mk (P ++ (appendUInt16 ByteArray.empty v ++ S))
        (P.size + 2)) := by
  have hA : (appendUInt16 ByteArray.empty v).size = 2 := rfl
  have h0 : (P ++ (appendUInt16 ByteArray.empty v ++ S)).get! P.size =
      (v >>> 8).toUInt8 := by
    have h := get!_mid (P := P) (M := appendUInt16 ByteArray.empty v) (S := S)
      (k := 0) (by rw [hA]; omega)
    rw [Nat.add_zero] at h
    rw [h]
    rfl
  have h1 : (P ++ (appendUInt16 ByteArray.empty v ++ S)).get! (P.size + 1) =
      v.toUInt8 := by
    rw [get!_mid (by rw [hA]; omega)]
    rfl
  have hbound : P.size + 2 ≤ (P ++ (appendUInt16 ByteArray.empty v ++ S)).size := by
    rw [ByteArray.size_append, ByteArray.size_append, hA]
    omega
  rw [readUInt16_eval hbound, h0, h1, uint16_recompose]

private theorem readUInt32_at {P S : ByteArray} {v : UInt32} :
    Reader.readUInt32
        (Reader.mk (P ++ (appendUInt32 ByteArray.empty v ++ S)) P.size) =
      .ok (v, Reader.mk (P ++ (appendUInt32 ByteArray.empty v ++ S))
        (P.size + 4)) := by
  have hA : (appendUInt32 ByteArray.empty v).size = 4 := rfl
  have h0 : (P ++ (appendUInt32 ByteArray.empty v ++ S)).get! P.size =
      (v >>> 24).toUInt8 := by
    have h := get!_mid (P := P) (M := appendUInt32 ByteArray.empty v) (S := S)
      (k := 0) (by rw [hA]; omega)
    rw [Nat.add_zero] at h
    rw [h]
    rfl
  have h1 : (P ++ (appendUInt32 ByteArray.empty v ++ S)).get! (P.size + 1) =
      (v >>> 16).toUInt8 := by
    rw [get!_mid (by rw [hA]; omega)]
    rfl
  have h2 : (P ++ (appendUInt32 ByteArray.empty v ++ S)).get! (P.size + 2) =
      (v >>> 8).toUInt8 := by
    rw [get!_mid (by rw [hA]; omega)]
    rfl
  have h3 : (P ++ (appendUInt32 ByteArray.empty v ++ S)).get! (P.size + 3) =
      v.toUInt8 := by
    rw [get!_mid (by rw [hA]; omega)]
    rfl
  have hbound : P.size + 4 ≤ (P ++ (appendUInt32 ByteArray.empty v ++ S)).size := by
    rw [ByteArray.size_append, ByteArray.size_append, hA]
    omega
  rw [readUInt32_eval hbound, h0, h1, h2, h3, uint32_recompose]

private theorem readUInt24_at {P S : ByteArray} {n : Nat} (h : n < 2 ^ 24) :
    Reader.readUInt24 (Reader.mk (P ++ (length24Bytes n ++ S)) P.size) =
      .ok (n, Reader.mk (P ++ (length24Bytes n ++ S)) (P.size + 3)) := by
  have hA : (length24Bytes n).size = 3 := rfl
  have h0 : (P ++ (length24Bytes n ++ S)).get! P.size =
      UInt8.ofNat (n >>> 16) := by
    have h := get!_mid (P := P) (M := length24Bytes n) (S := S) (k := 0)
      (by rw [hA]; omega)
    rw [Nat.add_zero] at h
    rw [h]
    rfl
  have h1 : (P ++ (length24Bytes n ++ S)).get! (P.size + 1) =
      UInt8.ofNat (n >>> 8) := by
    rw [get!_mid (by rw [hA]; omega)]
    rfl
  have h2 : (P ++ (length24Bytes n ++ S)).get! (P.size + 2) = UInt8.ofNat n := by
    rw [get!_mid (by rw [hA]; omega)]
    rfl
  have hbound : P.size + 3 ≤ (P ++ (length24Bytes n ++ S)).size := by
    rw [ByteArray.size_append, ByteArray.size_append, hA]
    omega
  rw [readUInt24_eval hbound, h0, h1, h2, uint24_recompose h]

private theorem readVector8_at {P X S : ByteArray} (hsz : X.size < 2 ^ 8) :
    Reader.readVector8 (Reader.mk
        (P ++ (ByteArray.empty.push (UInt8.ofNat X.size) ++ (X ++ S)))
        P.size) =
      .ok (X, Reader.mk
        (P ++ (ByteArray.empty.push (UInt8.ofNat X.size) ++ (X ++ S)))
        (P.size + 1 + X.size)) := by
  unfold Reader.readVector8
  rw [readUInt8_at]
  show Reader.take (Reader.mk
    (P ++ (ByteArray.empty.push (UInt8.ofNat X.size) ++ (X ++ S)))
    (P.size + 1)) (UInt8.ofNat X.size).toNat = _
  rw [UInt8.toNat_ofNat', Nat.mod_eq_of_lt hsz,
    show P ++ (ByteArray.empty.push (UInt8.ofNat X.size) ++ (X ++ S)) =
      (P ++ ByteArray.empty.push (UInt8.ofNat X.size)) ++ (X ++ S) from
        ByteArray.append_assoc.symm,
    show P.size + 1 = (P ++ ByteArray.empty.push (UInt8.ofNat X.size)).size from
      by rw [ByteArray.size_append]; rfl,
    take_at rfl]

private theorem readVector16_at {P X S : ByteArray} (hsz : X.size < 2 ^ 16) :
    Reader.readVector16 (Reader.mk
        (P ++ (appendUInt16 ByteArray.empty (UInt16.ofNat X.size) ++ (X ++ S)))
        P.size) =
      .ok (X, Reader.mk
        (P ++ (appendUInt16 ByteArray.empty (UInt16.ofNat X.size) ++ (X ++ S)))
        (P.size + 2 + X.size)) := by
  unfold Reader.readVector16
  rw [readUInt16_at]
  show Reader.take (Reader.mk
    (P ++ (appendUInt16 ByteArray.empty (UInt16.ofNat X.size) ++ (X ++ S)))
    (P.size + 2)) (UInt16.ofNat X.size).toNat = _
  rw [UInt16.toNat_ofNat', Nat.mod_eq_of_lt hsz,
    show P ++ (appendUInt16 ByteArray.empty (UInt16.ofNat X.size) ++ (X ++ S)) =
      (P ++ appendUInt16 ByteArray.empty (UInt16.ofNat X.size)) ++ (X ++ S) from
        ByteArray.append_assoc.symm,
    show P.size + 2 =
      (P ++ appendUInt16 ByteArray.empty (UInt16.ofNat X.size)).size from by
        rw [ByteArray.size_append]; rfl,
    take_at rfl]

private theorem readVector24_at {P X S : ByteArray} (hsz : X.size < 2 ^ 24) :
    Reader.readVector24
        (Reader.mk (P ++ (length24Bytes X.size ++ (X ++ S))) P.size) =
      .ok (X, Reader.mk (P ++ (length24Bytes X.size ++ (X ++ S)))
        (P.size + 3 + X.size)) := by
  unfold Reader.readVector24
  rw [readUInt24_at hsz]
  show Reader.take (Reader.mk (P ++ (length24Bytes X.size ++ (X ++ S)))
    (P.size + 3)) X.size = _
  rw [show P ++ (length24Bytes X.size ++ (X ++ S)) =
      (P ++ length24Bytes X.size) ++ (X ++ S) from ByteArray.append_assoc.symm,
    show P.size + 3 = (P ++ length24Bytes X.size).size from by
      rw [ByteArray.size_append]; rfl,
    take_at rfl]

/-! Offset-explicit forms: a field read at a stated offset of a buffer that
decomposes as `prefix ‖ field ‖ suffix`. These are what a message-body walk
rewrites with, keeping the body itself opaque. -/

private theorem take_at' {W P X S : ByteArray} {off n : Nat}
    (hW : W = P ++ (X ++ S)) (hoff : off = P.size) (hn : X.size = n) :
    Reader.take (Reader.mk W off) n = .ok (X, Reader.mk W (off + n)) := by
  subst hW; subst hn; subst hoff
  exact take_at rfl

private theorem readUInt8_at' {W P S : ByteArray} {off : Nat} {b : UInt8}
    (hW : W = P ++ (ByteArray.empty.push b ++ S)) (hoff : off = P.size) :
    Reader.readUInt8 (Reader.mk W off) = .ok (b, Reader.mk W (off + 1)) := by
  subst hW; subst hoff
  exact readUInt8_at

private theorem readUInt16_at' {W P S : ByteArray} {off : Nat} {v : UInt16}
    (hW : W = P ++ (appendUInt16 ByteArray.empty v ++ S)) (hoff : off = P.size) :
    Reader.readUInt16 (Reader.mk W off) = .ok (v, Reader.mk W (off + 2)) := by
  subst hW; subst hoff
  exact readUInt16_at

private theorem readUInt32_at' {W P S : ByteArray} {off : Nat} {v : UInt32}
    (hW : W = P ++ (appendUInt32 ByteArray.empty v ++ S)) (hoff : off = P.size) :
    Reader.readUInt32 (Reader.mk W off) = .ok (v, Reader.mk W (off + 4)) := by
  subst hW; subst hoff
  exact readUInt32_at

private theorem readUInt24_at' {W P S : ByteArray} {off n : Nat}
    (hW : W = P ++ (length24Bytes n ++ S)) (hoff : off = P.size) (h : n < 2 ^ 24) :
    Reader.readUInt24 (Reader.mk W off) = .ok (n, Reader.mk W (off + 3)) := by
  subst hW; subst hoff
  exact readUInt24_at h

private theorem readVector8_at' {W P X S : ByteArray} {off : Nat}
    (hW : W = P ++ (ByteArray.empty.push (UInt8.ofNat X.size) ++ (X ++ S)))
    (hoff : off = P.size) (hsz : X.size < 2 ^ 8) :
    Reader.readVector8 (Reader.mk W off) =
      .ok (X, Reader.mk W (off + 1 + X.size)) := by
  subst hW; subst hoff
  exact readVector8_at hsz

private theorem readVector16_at' {W P X S : ByteArray} {off : Nat}
    (hW : W = P ++ (appendUInt16 ByteArray.empty (UInt16.ofNat X.size) ++ (X ++ S)))
    (hoff : off = P.size) (hsz : X.size < 2 ^ 16) :
    Reader.readVector16 (Reader.mk W off) =
      .ok (X, Reader.mk W (off + 2 + X.size)) := by
  subst hW; subst hoff
  exact readVector16_at hsz

private theorem readVector24_at' {W P X S : ByteArray} {off : Nat}
    (hW : W = P ++ (length24Bytes X.size ++ (X ++ S))) (hoff : off = P.size)
    (hsz : X.size < 2 ^ 24) :
    Reader.readVector24 (Reader.mk W off) =
      .ok (X, Reader.mk W (off + 3 + X.size)) := by
  subst hW; subst hoff
  exact readVector24_at hsz

private theorem size_extensionBytes (e : Extension) :
    (extensionBytes e).size = 4 + e.data.size := by
  unfold extensionBytes
  rw [ByteArray.size_append, ByteArray.size_append,
    show (appendUInt16 ByteArray.empty e.extensionType).size = 2 from rfl,
    show (appendUInt16 ByteArray.empty (UInt16.ofNat e.data.size)).size = 2
      from rfl]
  omega

/-- `encodeExtension` emits exactly `extensionBytes`. -/
private theorem encodeExtension_eq {t : UInt16} {d out : ByteArray}
    (h : encodeExtension t d = .ok out) :
    d.size < 2 ^ 16 ∧ out = extensionBytes { extensionType := t, data := d } := by
  unfold encodeExtension at h
  obtain ⟨V, hV, h⟩ := bind_ok_ex h
  obtain ⟨hszlt, hVeq⟩ := encodeVector16_ok hV
  refine ⟨hszlt, ?_⟩
  rw [← pure_eq_ok h, hVeq]
  rfl

/-- An exhausted cursor ends the loop with the extensions accumulated so far. -/
private theorem parseExtensionsLoop_end {E : ByteArray} {off : Nat}
    {out : Array Extension} (h : off = E.size) :
    parseExtensionsLoop { bytes := E, offset := off } out = .ok out := by
  unfold parseExtensionsLoop
  rw [if_pos]
  show (off == E.size) = true
  rw [h]
  exact beq_self_eq_true E.size

/-- One correctly-encoded extension at the cursor advances the loop by exactly
its wire size and appends it to the accumulator. -/
private theorem parseExtensionsLoop_cons {P S : ByteArray} {e : Extension}
    {out : Array Extension} (hsz : e.data.size < 2 ^ 16)
    (hfresh : out.any (fun x => x.extensionType == e.extensionType) = false) :
    parseExtensionsLoop
        { bytes := P ++ (extensionBytes e ++ S), offset := P.size } out =
      parseExtensionsLoop
        { bytes := P ++ (extensionBytes e ++ S),
          offset := (P ++ extensionBytes e).size } (out.push e) := by
  have hM : (extensionBytes e).size = 4 + e.data.size := size_extensionBytes e
  have hA : (appendUInt16 ByteArray.empty e.extensionType).size = 2 := rfl
  have hL : (appendUInt16 ByteArray.empty (UInt16.ofNat e.data.size)).size = 2 :=
    rfl
  have hWsize : (P ++ (extensionBytes e ++ S)).size =
      P.size + ((4 + e.data.size) + S.size) := by
    rw [ByteArray.size_append, ByteArray.size_append, hM]
  -- The four header bytes and the payload slice.
  have hb0 : (P ++ (extensionBytes e ++ S)).get! (P.size + 0) =
      (e.extensionType >>> 8).toUInt8 := by
    rw [get!_mid (by omega)]
    show (appendUInt16 ByteArray.empty e.extensionType ++
      (appendUInt16 ByteArray.empty (UInt16.ofNat e.data.size) ++
        e.data)).get! 0 = _
    rw [get!_append_left (by omega)]
    rfl
  have hb1 : (P ++ (extensionBytes e ++ S)).get! (P.size + 1) =
      e.extensionType.toUInt8 := by
    rw [get!_mid (by omega)]
    show (appendUInt16 ByteArray.empty e.extensionType ++
      (appendUInt16 ByteArray.empty (UInt16.ofNat e.data.size) ++
        e.data)).get! 1 = _
    rw [get!_append_left (by omega)]
    rfl
  have hb2 : (P ++ (extensionBytes e ++ S)).get! (P.size + 2) =
      (UInt16.ofNat e.data.size >>> 8).toUInt8 := by
    rw [get!_mid (by omega)]
    show (appendUInt16 ByteArray.empty e.extensionType ++
      (appendUInt16 ByteArray.empty (UInt16.ofNat e.data.size) ++
        e.data)).get! 2 = _
    rw [get!_append_right (by omega) (by rw [ByteArray.size_append]; omega),
      show 2 - (appendUInt16 ByteArray.empty e.extensionType).size = 0 from rfl,
      get!_append_left (by omega)]
    rfl
  have hb3 : (P ++ (extensionBytes e ++ S)).get! (P.size + 3) =
      (UInt16.ofNat e.data.size).toUInt8 := by
    rw [get!_mid (by omega)]
    show (appendUInt16 ByteArray.empty e.extensionType ++
      (appendUInt16 ByteArray.empty (UInt16.ofNat e.data.size) ++
        e.data)).get! 3 = _
    rw [get!_append_right (by omega) (by rw [ByteArray.size_append]; omega),
      show 3 - (appendUInt16 ByteArray.empty e.extensionType).size = 1 from rfl,
      get!_append_left (by omega)]
    rfl
  have hdata : (P ++ (extensionBytes e ++ S)).extract (P.size + 2 + 2)
      (P.size + 2 + 2 + e.data.size) = e.data := by
    rw [show P ++ (extensionBytes e ++ S) =
        (P ++ appendUInt16 ByteArray.empty e.extensionType ++
          appendUInt16 ByteArray.empty (UInt16.ofNat e.data.size)) ++
          (e.data ++ S) from by
      unfold extensionBytes
      rw [ByteArray.append_assoc, ByteArray.append_assoc, ByteArray.append_assoc,
        ByteArray.append_assoc]]
    rw [show P.size + 2 + 2 =
        (P ++ appendUInt16 ByteArray.empty e.extensionType ++
          appendUInt16 ByteArray.empty (UInt16.ofNat e.data.size)).size from by
      rw [ByteArray.size_append, ByteArray.size_append, hA, hL]]
    exact extract_mid _ _ _
  -- Evaluate one iteration against the assembled buffer.
  rw [show (P ++ extensionBytes e).size = P.size + 2 + 2 + e.data.size from by
    rw [ByteArray.size_append, hM]; omega]
  generalize hW : P ++ (extensionBytes e ++ S) = W at hWsize hb0 hb1 hb2 hb3 hdata ⊢
  have hne : ¬(({ bytes := W, offset := P.size } : Reader).atEnd = true) := by
    show ¬(P.size == W.size) = true
    rw [beq_iff_eq]
    omega
  have hr16 : Reader.readUInt16 { bytes := W, offset := P.size } =
      .ok (e.extensionType, { bytes := W, offset := P.size + 2 }) := by
    rw [readUInt16_eval (by omega),
      show W.get! P.size = (e.extensionType >>> 8).toUInt8 from by
        rw [show P.size = P.size + 0 from by omega]; exact hb0,
      hb1, uint16_recompose]
  have hLen : ((W.get! (P.size + 2)).toUInt16 <<< 8 |||
      (W.get! (P.size + 2 + 1)).toUInt16).toNat = e.data.size := by
    rw [show P.size + 2 + 1 = P.size + 3 from by omega, hb2, hb3,
      uint16_recompose, UInt16.toNat_ofNat']
    exact Nat.mod_eq_of_lt hsz
  have hv16 : Reader.readVector16 { bytes := W, offset := P.size + 2 } =
      .ok (e.data, { bytes := W, offset := P.size + 2 + 2 + e.data.size }) := by
    rw [readVector16_eval hLen (by omega), hdata]
  have hdup :
      ¬(out.any (fun ext => ext.extensionType == e.extensionType) = true) := by
    rw [hfresh]
    exact Bool.false_ne_true
  rw [parseExtensionsLoop.eq_def]
  rw [if_neg hne]
  -- The loop matches on its reads with equation binders (needed for the
  -- termination argument), so peel them with `split` rather than `rw`.
  split
  · rename_i err heq
    rw [hr16] at heq
    cases heq
  · rename_i t r₁ heq
    rw [hr16] at heq
    simp only [Except.ok.injEq, Prod.mk.injEq] at heq
    obtain ⟨rfl, rfl⟩ := heq
    split
    · rename_i err heq
      rw [hv16] at heq
      cases heq
    · rename_i d r₂ heq
      rw [hv16] at heq
      simp only [Except.ok.injEq, Prod.mk.injEq] at heq
      obtain ⟨rfl, rfl⟩ := heq
      rw [if_neg hdup]

/-- The extension loop consumes a whole encoded extension list, appending
every member — of *any* extension type — to the accumulator in order. -/
private theorem parseExtensionsLoop_extensionsBytes : ∀ (l : List Extension)
    (P : ByteArray) (out : Array Extension),
    (∀ e ∈ l, e.data.size < 2 ^ 16) →
    (∀ e ∈ l, out.any (fun x => x.extensionType == e.extensionType) = false) →
    l.Pairwise (fun a b => (a.extensionType == b.extensionType) = false) →
    parseExtensionsLoop { bytes := P ++ extensionsBytes l, offset := P.size }
        out = .ok (out.toList ++ l).toArray := by
  intro l
  induction l with
  | nil =>
    intro P out _ _ _
    rw [show extensionsBytes ([] : List Extension) = ByteArray.empty from rfl,
      ByteArray.append_empty, parseExtensionsLoop_end rfl, List.append_nil,
      Array.toArray_toList]
  | cons e rest ih =>
    intro P out hsz hfresh hpw
    rw [List.pairwise_cons] at hpw
    rw [show extensionsBytes (e :: rest) = extensionBytes e ++ extensionsBytes rest
      from rfl]
    rw [parseExtensionsLoop_cons (hsz e (List.mem_cons_self ..))
      (hfresh e (List.mem_cons_self ..))]
    rw [show P ++ (extensionBytes e ++ extensionsBytes rest) =
      (P ++ extensionBytes e) ++ extensionsBytes rest from
        ByteArray.append_assoc.symm]
    rw [ih (P ++ extensionBytes e) (out.push e)
      (fun e' he' => hsz e' (List.mem_cons_of_mem e he'))
      (fun e' he' => by
        rw [Array.any_push, hfresh e' (List.mem_cons_of_mem e he'),
          hpw.1 e' he']
        rfl)
      hpw.2]
    rw [Array.toList_push, List.append_assoc]
    rfl

/-- **Extension-list roundtrip (GREASE tolerance)**: parsing the wire image of
any extension list returns exactly that list, in order. The extension *types*
are arbitrary — unknown, reserved, or GREASE values are carried through
unchanged, never dropped or reordered — so re-encoding the parse result
reproduces the original bytes (`extensionsBytes l`). -/
theorem parseExtensions_extensionsBytes (l : List Extension)
    (hsz : ∀ e ∈ l, e.data.size < 2 ^ 16)
    (hdistinct :
      l.Pairwise (fun a b => (a.extensionType == b.extensionType) = false)) :
    parseExtensions (extensionsBytes l) = .ok l.toArray := by
  unfold parseExtensions
  rw [show ({ bytes := extensionsBytes l } : Reader) =
    { bytes := ByteArray.empty ++ extensionsBytes l,
      offset := ByteArray.empty.size } from by
    rw [ByteArray.empty_append]
    rfl]
  rw [parseExtensionsLoop_extensionsBytes l ByteArray.empty #[] hsz
    (fun _ _ => Array.any_empty) hdistinct]
  rfl

/-! ### EncryptedExtensions -/

/-- A body that is exactly one `uint16`-prefixed vector reads back as that
vector, leaving the cursor at the end. -/
private theorem readVector16_body {X : ByteArray} (hsz : X.size < 2 ^ 16) :
    Reader.readVector16
        (Reader.mk (appendUInt16 ByteArray.empty (UInt16.ofNat X.size) ++ X) 0) =
      .ok (X, Reader.mk (appendUInt16 ByteArray.empty (UInt16.ofNat X.size) ++ X)
        (2 + X.size)) := by
  have h := readVector16_at (P := ByteArray.empty) (X := X) (S := ByteArray.empty)
    hsz
  rw [ByteArray.append_empty, ByteArray.empty_append] at h
  exact h

/-- EncryptedExtensions with a known extension list parses back to that list. -/
private theorem parseEncryptedExtensions_of_body {msg : Message}
    {l : List Extension} (hty : msg.msgType = encryptedExtensionsType)
    (hbody : msg.body = appendUInt16 ByteArray.empty
      (UInt16.ofNat (extensionsBytes l).size) ++ extensionsBytes l)
    (hsz : (extensionsBytes l).size < 2 ^ 16)
    (hesz : ∀ e ∈ l, e.data.size < 2 ^ 16)
    (hdist :
      l.Pairwise (fun a b => (a.extensionType == b.extensionType) = false)) :
    parseEncryptedExtensions msg =
      .ok { extensions := l.toArray, encoded := msg.encoded } := by
  unfold parseEncryptedExtensions
  rw [hty, if_pos (show (encryptedExtensionsType == encryptedExtensionsType) = true
    from rfl), hbody]
  rw [readVector16_body hsz]
  simp only [requireEnd_eval (b := appendUInt16 ByteArray.empty
    (UInt16.ofNat (extensionsBytes l).size) ++ extensionsBytes l)
    (off := 2 + (extensionsBytes l).size) (context := "EncryptedExtensions")
    (by rw [ByteArray.size_append]; rfl)]
  simp only [parseExtensions_extensionsBytes l hesz hdist]

/-- **Parse inverts encode for EncryptedExtensions** with no ALPN selection:
the message carries an empty extension list. -/
theorem encodeEncryptedExtensions_parse_none {msg : Message}
    (h : encodeEncryptedExtensions none = .ok msg) :
    parseEncryptedExtensions msg =
      .ok { extensions := #[], encoded := msg.encoded } := by
  unfold encodeEncryptedExtensions at h
  obtain ⟨u, hu, h⟩ := bind_ok_ex h
  obtain ⟨V, hV, h⟩ := bind_ok_ex h
  obtain ⟨hszlt, hVeq⟩ := encodeVector16_ok hV
  obtain ⟨hlt, hmsg⟩ := frame_spec h
  exact parseEncryptedExtensions_of_body (l := [])
    (by rw [hmsg]) (by rw [hmsg]; exact hVeq) hszlt (by simp) List.Pairwise.nil

/-- **Parse inverts encode for EncryptedExtensions** with an ALPN selection:
the message carries exactly one extension, the ALPN one. -/
theorem encodeEncryptedExtensions_parse_some {protocol : String} {msg : Message}
    (h : encodeEncryptedExtensions (some protocol) = .ok msg) :
    ∃ alpnData, parseEncryptedExtensions msg =
      .ok { extensions := #[{ extensionType := alpnExtension, data := alpnData }],
            encoded := msg.encoded } := by
  unfold encodeEncryptedExtensions at h
  obtain ⟨A, hA, h⟩ := bind_ok_ex h
  obtain ⟨u, hu, h⟩ := bind_ok_ex h
  obtain ⟨V, hV, h⟩ := bind_ok_ex h
  obtain ⟨hszlt, hVeq⟩ := encodeVector16_ok hV
  obtain ⟨hlt, hmsg⟩ := frame_spec h
  unfold encodeAlpnServerExtension at hA
  obtain ⟨hemp, hA⟩ | ⟨hemp, hA⟩ := ite_ok_cases hA
  · obtain ⟨_, hu', _⟩ := bind_ok_ex hA
    cases hu'
  obtain ⟨V8, _, hA⟩ := bind_ok_ex hA
  obtain ⟨V16, _, hA⟩ := bind_ok_ex hA
  obtain ⟨D, _, hA⟩ := bind_ok_ex hA
  obtain ⟨hDsz, hAeq⟩ := encodeExtension_eq hA
  refine ⟨D, ?_⟩
  have hbytes : extensionsBytes [{ extensionType := alpnExtension, data := D }] =
      ByteArray.empty ++ A := by
    rw [hAeq, ByteArray.empty_append]
    show extensionBytes { extensionType := alpnExtension, data := D } ++
      extensionsBytes [] = _
    rw [show extensionsBytes ([] : List Extension) = ByteArray.empty from rfl,
      ByteArray.append_empty]
  exact parseEncryptedExtensions_of_body
    (l := [{ extensionType := alpnExtension, data := D }])
    (by rw [hmsg]) (by rw [hmsg, hbytes]; exact hVeq) (by rw [hbytes]; exact hszlt)
    (by intro e he; rw [List.mem_singleton] at he; subst he; exact hDsz)
    (List.pairwise_singleton ..)

/-! ### HelloRetryRequest discrimination

An HRR is a ServerHello whose random field is the fixed RFC 8446 sentinel.
These laws pin that down on both sides: the sentinel is where the
discriminator looks, and each parser rejects the other message. -/

/-- A six-segment body has its second segment right after the first. -/
private theorem append_head6 (a b x1 x2 x3 x4 : ByteArray) :
    ∃ T, a ++ b ++ x1 ++ x2 ++ x3 ++ x4 = a ++ (b ++ T) :=
  ⟨x1 ++ x2 ++ x3 ++ x4, by simp only [ByteArray.append_assoc]⟩

/-- The random field of an encoded ServerHello-shaped body is at offset 2. -/
private theorem serverHelloRandom {R T : ByteArray} (hR : R.size = 32) :
    (appendUInt16 ByteArray.empty legacyTls12Version ++ (R ++ T)).extract 2 34
      = R := by
  have h := extract_mid (appendUInt16 ByteArray.empty legacyTls12Version) R T
  rw [show (appendUInt16 ByteArray.empty legacyTls12Version).size = 2 from rfl,
    hR] at h
  exact h

/-- A HelloRetryRequest body starts with `legacy_version ‖ sentinel random`. -/
private theorem encodeHelloRetryRequest_body {legacySessionIdEcho : ByteArray}
    {group : NamedGroup} {cipherSuite : UInt16} {msg : Message}
    (h : encodeHelloRetryRequest legacySessionIdEcho group cipherSuite = .ok msg) :
    msg.msgType = serverHelloType ∧
    ∃ T, msg.body = appendUInt16 ByteArray.empty legacyTls12Version ++
      (helloRetryRequestRandom ++ T) := by
  unfold encodeHelloRetryRequest at h
  obtain ⟨hc, h⟩ | ⟨hc, h⟩ := ite_ok_cases h
  · obtain ⟨_, hu, _⟩ := bind_ok_ex h
    cases hu
  obtain ⟨_, _, h⟩ := bind_ok_ex h
  obtain ⟨_, _, h⟩ := bind_ok_ex h
  obtain ⟨_, _, h⟩ := bind_ok_ex h
  obtain ⟨_, _, h⟩ := bind_ok_ex h
  obtain ⟨_, _, h⟩ := bind_ok_ex h
  obtain ⟨hlt, hmsg⟩ := frame_spec h
  refine ⟨by rw [hmsg], ?_⟩
  simp only [hmsg]
  exact append_head6 ..

/-- A ServerHello body starts with `legacy_version ‖ random`. -/
private theorem encodeServerHello_body {random legacySessionIdEcho : ByteArray}
    {group : NamedGroup} {keyExchange : ByteArray} {cipherSuite : UInt16}
    {msg : Message}
    (h : encodeServerHello random legacySessionIdEcho group keyExchange
      cipherSuite = .ok msg) :
    msg.msgType = serverHelloType ∧ random.size = 32 ∧
    ∃ T, msg.body = appendUInt16 ByteArray.empty legacyTls12Version ++
      (random ++ T) := by
  unfold encodeServerHello at h
  obtain ⟨hc, h⟩ | ⟨hc, h⟩ := ite_ok_cases h
  · obtain ⟨hc2, h⟩ | ⟨hc2, h⟩ := ite_ok_cases h
    · obtain ⟨_, hu, _⟩ := bind_ok_ex h
      cases hu
    obtain ⟨_, _, h⟩ := bind_ok_ex h
    obtain ⟨_, _, h⟩ := bind_ok_ex h
    obtain ⟨_, _, h⟩ := bind_ok_ex h
    obtain ⟨_, _, h⟩ := bind_ok_ex h
    obtain ⟨_, _, h⟩ := bind_ok_ex h
    obtain ⟨_, _, h⟩ := bind_ok_ex h
    obtain ⟨hlt, hmsg⟩ := frame_spec h
    refine ⟨by rw [hmsg], by simpa using hc, ?_⟩
    simp only [hmsg]
    exact append_head6 ..
  · obtain ⟨_, hu, _⟩ := bind_ok_ex h
    cases hu

/-- **HRR discrimination**: an encoded HelloRetryRequest is recognised by the
sentinel random. -/
theorem encodeHelloRetryRequest_isHelloRetryRequest {legacySessionIdEcho : ByteArray}
    {group : NamedGroup} {cipherSuite : UInt16} {msg : Message}
    (h : encodeHelloRetryRequest legacySessionIdEcho group cipherSuite = .ok msg) :
    isHelloRetryRequest msg = true := by
  obtain ⟨hty, T, hbody⟩ := encodeHelloRetryRequest_body h
  have hsize : 34 ≤ msg.body.size := by
    rw [hbody, ByteArray.size_append, ByteArray.size_append,
      show (appendUInt16 ByteArray.empty legacyTls12Version).size = 2 from rfl,
      show helloRetryRequestRandom.size = 32 from rfl]
    omega
  unfold isHelloRetryRequest
  rw [hty, hbody, serverHelloRandom rfl,
    show (serverHelloType == serverHelloType) = true from rfl,
    beq_self helloRetryRequestRandom]
  rw [hbody] at hsize
  simp only [Bool.true_and, Bool.and_true, decide_eq_true_eq]
  omega

/-- **HRR discrimination**: an encoded ServerHello whose random is not the
sentinel is not mistaken for a HelloRetryRequest. -/
theorem encodeServerHello_not_isHelloRetryRequest {random legacySessionIdEcho : ByteArray}
    {group : NamedGroup} {keyExchange : ByteArray} {cipherSuite : UInt16}
    {msg : Message}
    (h : encodeServerHello random legacySessionIdEcho group keyExchange
      cipherSuite = .ok msg)
    (hrand : (random == helloRetryRequestRandom) = false) :
    isHelloRetryRequest msg = false := by
  obtain ⟨hty, hR, T, hbody⟩ := encodeServerHello_body h
  unfold isHelloRetryRequest
  rw [hty, hbody, serverHelloRandom hR, hrand]
  simp

/-- **HRR discrimination**: the ServerHello parser refuses a HelloRetryRequest
rather than mis-parsing it. -/
theorem encodeHelloRetryRequest_parseServerHello {legacySessionIdEcho : ByteArray}
    {group : NamedGroup} {cipherSuite : UInt16} {msg : Message}
    (h : encodeHelloRetryRequest legacySessionIdEcho group cipherSuite = .ok msg) :
    parseServerHello msg = .error "expected ServerHello, got HelloRetryRequest" := by
  obtain ⟨hty, T, hbody⟩ := encodeHelloRetryRequest_body h
  unfold parseServerHello
  rw [hty, if_pos (show (serverHelloType == serverHelloType) = true from rfl)]
  simp only [readUInt16_at' (W := msg.body) (off := 0) (v := legacyTls12Version)
    (P := ByteArray.empty) (S := helloRetryRequestRandom ++ T)
    (by rw [hbody, ByteArray.empty_append]) rfl]
  rw [if_pos (beq_self_eq_true legacyTls12Version)]
  simp only [take_at' (W := msg.body) (off := 0 + 2) (n := 32)
    (P := appendUInt16 ByteArray.empty legacyTls12Version)
    (X := helloRetryRequestRandom) (S := T) hbody rfl rfl]
  rw [if_pos (beq_self helloRetryRequestRandom)]

/-- **HRR discrimination**: the HelloRetryRequest parser refuses a ServerHello
whose random is not the sentinel. -/
theorem encodeServerHello_parseHelloRetryRequest {random legacySessionIdEcho : ByteArray}
    {group : NamedGroup} {keyExchange : ByteArray} {cipherSuite : UInt16}
    {msg : Message}
    (h : encodeServerHello random legacySessionIdEcho group keyExchange
      cipherSuite = .ok msg)
    (hrand : (random == helloRetryRequestRandom) = false) :
    parseHelloRetryRequest msg =
      .error "ServerHello random is not the HelloRetryRequest sentinel" := by
  obtain ⟨hty, hR, T, hbody⟩ := encodeServerHello_body h
  unfold parseHelloRetryRequest
  rw [hty, if_pos (show (serverHelloType == serverHelloType) = true from rfl)]
  simp only [readUInt16_at' (W := msg.body) (off := 0) (v := legacyTls12Version)
    (P := ByteArray.empty) (S := random ++ T)
    (by rw [hbody, ByteArray.empty_append]) rfl]
  rw [if_pos (beq_self_eq_true legacyTls12Version)]
  simp only [take_at' (W := msg.body) (off := 0 + 2) (n := 32)
    (P := appendUInt16 ByteArray.empty legacyTls12Version)
    (X := random) (S := T) hbody rfl hR]
  rw [if_neg (by rw [hrand]; exact Bool.false_ne_true)]

/-! ### Certificate -/

private theorem encodeLength8_ok {n : Nat} {out : ByteArray}
    (h : encodeLength8 n = .ok out) :
    n < 2 ^ 8 ∧ out = ByteArray.empty.push (UInt8.ofNat n) := by
  unfold encodeLength8 at h
  obtain ⟨hc, h⟩ | ⟨hc, h⟩ := ite_ok_cases h
  · obtain ⟨_, hu, _⟩ := bind_ok_ex h
    cases hu
  · exact ⟨by omega, (pure_eq_ok h).symm⟩

private theorem encodeVector8_ok {b out : ByteArray}
    (h : encodeVector8 b = .ok out) :
    b.size < 2 ^ 8 ∧ out = ByteArray.empty.push (UInt8.ofNat b.size) ++ b := by
  unfold encodeVector8 at h
  obtain ⟨len, hlen, h⟩ := bind_ok_ex h
  obtain ⟨hsize, hbytes⟩ := encodeLength8_ok hlen
  refine ⟨hsize, ?_⟩
  rw [← pure_eq_ok h, hbytes]

private theorem encodeVector24_ok {b out : ByteArray}
    (h : encodeVector24 b = .ok out) :
    b.size < 2 ^ 24 ∧ out = length24Bytes b.size ++ b := by
  unfold encodeVector24 at h
  obtain ⟨len, hlen, h⟩ := bind_ok_ex h
  obtain ⟨hsize, hbytes⟩ := encodeLength24_ok hlen
  refine ⟨hsize, ?_⟩
  rw [← pure_eq_ok h, hbytes]

/-- The wire image of one certificate_list entry: the DER, then an empty
extensions vector. -/
private def certificateEntryBytes (der : ByteArray) : ByteArray :=
  length24Bytes der.size ++ (der ++
    (appendUInt16 ByteArray.empty (UInt16.ofNat ByteArray.empty.size) ++
      ByteArray.empty))

/-- The wire image of a whole certificate_list. -/
private def certificateListBytes : List ByteArray → ByteArray
  | [] => ByteArray.empty
  | der :: rest => certificateEntryBytes der ++ certificateListBytes rest

private theorem encodeCertificateList_eq : ∀ {l : List ByteArray} {B : ByteArray},
    encodeCertificateList l = .ok B →
    B = certificateListBytes l ∧ (∀ der ∈ l, der.size < 2 ^ 24) ∧
      (∀ der ∈ l, der.isEmpty = false) := by
  intro l
  induction l with
  | nil =>
    intro B h
    refine ⟨?_, by simp, by simp⟩
    unfold encodeCertificateList at h
    cases h
    rfl
  | cons der rest ih =>
    intro B h
    unfold encodeCertificateList at h
    split at h
    · cases h
    · rename_i hne
      split at h
      · cases h
      · rename_i entry h24
        split at h
        · cases h
        · rename_i noExt h16
          split at h
          · cases h
          · rename_i tail htail
            obtain ⟨hszder, hentry⟩ := encodeVector24_ok h24
            obtain ⟨_, hnoext⟩ := encodeVector16_ok h16
            obtain ⟨htailEq, htailSz, htailNe⟩ := ih htail
            cases h
            refine ⟨?_, ?_, ?_⟩
            · rw [hentry, hnoext, htailEq]
              show _ = certificateEntryBytes der ++ certificateListBytes rest
              unfold certificateEntryBytes
              simp only [ByteArray.append_assoc]
            · intro d hd
              rcases List.mem_cons.mp hd with rfl | hd
              · exact hszder
              · exact htailSz d hd
            · intro d hd
              rcases List.mem_cons.mp hd with rfl | hd
              · exact Bool.eq_false_iff.mpr hne
              · exact htailNe d hd

private theorem size_certificateEntryBytes (der : ByteArray) :
    (certificateEntryBytes der).size = 5 + der.size := by
  unfold certificateEntryBytes
  rw [ByteArray.size_append, ByteArray.size_append, ByteArray.size_append,
    show (length24Bytes der.size).size = 3 from rfl,
    show (appendUInt16 ByteArray.empty
      (UInt16.ofNat ByteArray.empty.size)).size = 2 from rfl,
    show ByteArray.empty.size = 0 from rfl]
  omega

private theorem parseExtensions_empty : parseExtensions ByteArray.empty = .ok #[] :=
  parseExtensions_extensionsBytes [] (by simp) List.Pairwise.nil

/-- One correctly-encoded certificate entry at the cursor advances the
certificate_list loop by exactly its wire size. -/
private theorem parseCertificateEntries_cons {P S der : ByteArray}
    {entries : Array CertificateEntry}
    (hsz : der.size < 2 ^ 24) (hne : der.isEmpty = false) :
    parseCertificateEntries
        (Reader.mk (P ++ (certificateEntryBytes der ++ S)) P.size) entries =
      parseCertificateEntries
        (Reader.mk (P ++ (certificateEntryBytes der ++ S))
          (P ++ certificateEntryBytes der).size)
        (entries.push { der := der, extensions := #[] }) := by
  have hA : Reader.readVector24
      (Reader.mk (P ++ (certificateEntryBytes der ++ S)) P.size) =
      .ok (der, Reader.mk (P ++ (certificateEntryBytes der ++ S))
        (P.size + 3 + der.size)) :=
    readVector24_at' (W := P ++ (certificateEntryBytes der ++ S)) (off := P.size)
      (P := P) (X := der)
      (S := (appendUInt16 ByteArray.empty (UInt16.ofNat ByteArray.empty.size) ++
        ByteArray.empty) ++ S)
      (by unfold certificateEntryBytes; simp only [ByteArray.append_assoc]) rfl hsz
  have hB : Reader.readVector16
      (Reader.mk (P ++ (certificateEntryBytes der ++ S))
        (P.size + 3 + der.size)) =
      .ok (ByteArray.empty, Reader.mk (P ++ (certificateEntryBytes der ++ S))
        (P.size + 3 + der.size + 2 + ByteArray.empty.size)) :=
    readVector16_at' (W := P ++ (certificateEntryBytes der ++ S))
      (off := P.size + 3 + der.size) (P := P ++ length24Bytes der.size ++ der)
      (X := ByteArray.empty) (S := S)
      (by unfold certificateEntryBytes; simp only [ByteArray.append_assoc])
      (by rw [ByteArray.size_append, ByteArray.size_append,
        show (length24Bytes der.size).size = 3 from rfl]) (by simp)
  have hoff : (P ++ certificateEntryBytes der).size =
      P.size + 3 + der.size + 2 + ByteArray.empty.size := by
    rw [ByteArray.size_append, size_certificateEntryBytes,
      show ByteArray.empty.size = 0 from rfl]
    omega
  have hnotend : ¬((Reader.mk (P ++ (certificateEntryBytes der ++ S))
      P.size).atEnd = true) := by
    show ¬(P.size == (P ++ (certificateEntryBytes der ++ S)).size) = true
    rw [beq_iff_eq, ByteArray.size_append, ByteArray.size_append,
      size_certificateEntryBytes]
    omega
  rw [hoff, parseCertificateEntries.eq_def, if_neg hnotend]
  split
  · rename_i err heq
    rw [hA] at heq
    cases heq
  · rename_i d r₁ heq
    rw [hA] at heq
    simp only [Except.ok.injEq, Prod.mk.injEq] at heq
    obtain ⟨rfl, rfl⟩ := heq
    rw [if_neg (by rw [hne]; exact Bool.false_ne_true)]
    split
    · rename_i err heq
      rw [hB] at heq
      cases heq
    · rename_i eb r₂ heq
      rw [hB] at heq
      simp only [Except.ok.injEq, Prod.mk.injEq] at heq
      obtain ⟨rfl, rfl⟩ := heq
      simp only [parseExtensions_empty]

private theorem parseCertificateEntries_end {E : ByteArray} {off : Nat}
    {entries : Array CertificateEntry} (h : off = E.size) :
    parseCertificateEntries (Reader.mk E off) entries = .ok entries := by
  unfold parseCertificateEntries
  rw [if_pos]
  show (off == E.size) = true
  rw [h]
  exact beq_self_eq_true E.size

/-- The certificate_list loop consumes a whole encoded list, in order. -/
private theorem parseCertificateEntries_listBytes : ∀ (l : List ByteArray)
    (P : ByteArray) (entries : Array CertificateEntry),
    (∀ der ∈ l, der.size < 2 ^ 24) → (∀ der ∈ l, der.isEmpty = false) →
    parseCertificateEntries (Reader.mk (P ++ certificateListBytes l) P.size)
        entries =
      .ok (entries.toList ++ l.map (fun der =>
        ({ der := der, extensions := #[] } : CertificateEntry))).toArray := by
  intro l
  induction l with
  | nil =>
    intro P entries _ _
    rw [show certificateListBytes ([] : List ByteArray) = ByteArray.empty from rfl,
      ByteArray.append_empty, parseCertificateEntries_end rfl, List.map_nil,
      List.append_nil, Array.toArray_toList]
  | cons der rest ih =>
    intro P entries hsz hne
    rw [show certificateListBytes (der :: rest) =
      certificateEntryBytes der ++ certificateListBytes rest from rfl]
    rw [parseCertificateEntries_cons (hsz der (List.mem_cons_self ..))
      (hne der (List.mem_cons_self ..))]
    rw [show P ++ (certificateEntryBytes der ++ certificateListBytes rest) =
      (P ++ certificateEntryBytes der) ++ certificateListBytes rest from
        ByteArray.append_assoc.symm]
    rw [ih (P ++ certificateEntryBytes der)
      (entries.push { der := der, extensions := #[] })
      (fun d hd => hsz d (List.mem_cons_of_mem der hd))
      (fun d hd => hne d (List.mem_cons_of_mem der hd))]
    rw [Array.toList_push, List.append_assoc, List.map_cons]
    rfl

/-- **Parse inverts encode for Certificate**: every DER of the chain comes back
in order, with the empty request context and empty per-entry extensions the
encoder emitted, and the leaf first. -/
theorem encodeCertificate_parse {leaf : ByteArray} {rest : List ByteArray}
    {msg : Message} (h : encodeCertificate (leaf :: rest).toArray = .ok msg) :
    parseCertificate msg = .ok
      { requestContext := ByteArray.empty,
        entries :=
          ((leaf :: rest).map fun der => { der := der, extensions := #[] }).toArray,
        leafDer := leaf, encoded := msg.encoded } := by
  unfold encodeCertificate at h
  split at h
  · cases h
  · split at h
    · cases h
    · rename_i list hlist
      split at h
      · cases h
      · rename_i ctx hctx
        split at h
        · cases h
        · rename_i v24 hv24
          rw [List.toList_toArray] at hlist
          obtain ⟨hlistEq, hlistSz, hlistNe⟩ := encodeCertificateList_eq hlist
          obtain ⟨_, hctxEq⟩ := encodeVector8_ok hctx
          obtain ⟨hv24Sz, hv24Eq⟩ := encodeVector24_ok hv24
          obtain ⟨hlt, hmsg⟩ := frame_spec h
          have hty : msg.msgType = certificateType := by rw [hmsg]
          have hbody : msg.body =
              (ByteArray.empty.push (UInt8.ofNat ByteArray.empty.size) ++
                ByteArray.empty) ++ (length24Bytes list.size ++ list) := by
            rw [hmsg]
            show ctx ++ v24 = _
            rw [hctxEq, hv24Eq]
          have hA : Reader.readVector8 (Reader.mk msg.body 0) =
              .ok (ByteArray.empty,
                Reader.mk msg.body (0 + 1 + ByteArray.empty.size)) :=
            readVector8_at' (W := msg.body) (off := 0) (P := ByteArray.empty)
              (X := ByteArray.empty) (S := length24Bytes list.size ++ list)
              (by rw [hbody]; simp only [ByteArray.append_assoc,
                ByteArray.empty_append]) rfl (by simp)
          have hB : Reader.readVector24
              (Reader.mk msg.body (0 + 1 + ByteArray.empty.size)) =
              .ok (list, Reader.mk msg.body
                (0 + 1 + ByteArray.empty.size + 3 + list.size)) :=
            readVector24_at' (W := msg.body) (off := 0 + 1 + ByteArray.empty.size)
              (P := ByteArray.empty.push (UInt8.ofNat ByteArray.empty.size) ++
                ByteArray.empty)
              (X := list) (S := ByteArray.empty)
              (by rw [hbody]; simp only [ByteArray.append_empty]) rfl hv24Sz
          have hend : 0 + 1 + ByteArray.empty.size + 3 + list.size =
              msg.body.size := by
            rw [hbody, ByteArray.size_append, ByteArray.size_append,
              ByteArray.size_append,
              show (ByteArray.empty.push (UInt8.ofNat ByteArray.empty.size)).size
                = 1 from rfl,
              show (length24Bytes list.size).size = 3 from rfl,
              show ByteArray.empty.size = 0 from rfl]
            omega
          have hloop : parseCertificateEntries (Reader.mk list 0) #[] =
              .ok ((leaf :: rest).map
                fun der => { der := der, extensions := #[] }).toArray := by
            rw [hlistEq]
            have := parseCertificateEntries_listBytes (leaf :: rest)
              ByteArray.empty #[] hlistSz hlistNe
            rw [ByteArray.empty_append] at this
            rw [show (0 : Nat) = ByteArray.empty.size from rfl]
            rw [this]
            rfl
          unfold parseCertificate
          rw [hty, if_pos (show (certificateType == certificateType) = true from rfl)]
          simp only [hA]
          rw [if_pos (show ByteArray.empty.isEmpty = true from rfl)]
          simp only [hB]
          simp only [requireEnd_eval (context := "Certificate") hend]
          simp only [hloop]
          rw [if_neg (by simp)]
          rfl

/-! ### NewSessionTicket -/

/-- **Parse inverts encode for NewSessionTicket**: every field comes back, and
the ticket carries no extensions. -/
theorem encodeNewSessionTicket_parse {ticketLifetime ticketAgeAdd : UInt32}
    {ticketNonce ticket : ByteArray} {msg : Message}
    (h : encodeNewSessionTicket ticketLifetime ticketAgeAdd ticketNonce ticket
      = .ok msg) :
    parseNewSessionTicket msg = .ok
      { ticketLifetime := ticketLifetime, ticketAgeAdd := ticketAgeAdd,
        ticketNonce := ticketNonce, ticket := ticket, extensions := #[],
        encoded := msg.encoded } := by
  unfold encodeNewSessionTicket at h
  split at h
  · cases h
  · rename_i hlife
    split at h
    · cases h
    · rename_i hticket
      split at h
      · cases h
      · rename_i nonceVector hnonce
        split at h
        · cases h
        · rename_i ticketVector hticketVec
          split at h
          · cases h
          · rename_i extensionsVector hextVec
            obtain ⟨hnonceSz, hnonceEq⟩ := encodeVector8_ok hnonce
            obtain ⟨hticketSz, hticketEq⟩ := encodeVector16_ok hticketVec
            obtain ⟨_, hextEq⟩ := encodeVector16_ok hextVec
            obtain ⟨hlt, hmsg⟩ := frame_spec h
            have hty : msg.msgType = newSessionTicketType := by rw [hmsg]
            have hbody : msg.body =
                appendUInt32 ByteArray.empty ticketLifetime ++
                  appendUInt32 ByteArray.empty ticketAgeAdd ++
                  (ByteArray.empty.push (UInt8.ofNat ticketNonce.size) ++
                    ticketNonce) ++
                  (appendUInt16 ByteArray.empty (UInt16.ofNat ticket.size) ++
                    ticket) ++
                  (appendUInt16 ByteArray.empty
                    (UInt16.ofNat ByteArray.empty.size) ++ ByteArray.empty) := by
              rw [hmsg]
              show _ ++ _ ++ nonceVector ++ ticketVector ++ extensionsVector = _
              rw [hnonceEq, hticketEq, hextEq]
            -- The five field reads.
            have h1 : Reader.readUInt32 (Reader.mk msg.body 0) =
                .ok (ticketLifetime, Reader.mk msg.body (0 + 4)) :=
              readUInt32_at' (W := msg.body) (off := 0) (P := ByteArray.empty)
                (by rw [hbody]; simp only [ByteArray.append_assoc,
                  ByteArray.empty_append]; rfl) rfl
            have h2 : Reader.readUInt32 (Reader.mk msg.body (0 + 4)) =
                .ok (ticketAgeAdd, Reader.mk msg.body (0 + 4 + 4)) :=
              readUInt32_at' (W := msg.body) (off := 0 + 4)
                (P := appendUInt32 ByteArray.empty ticketLifetime)
                (by rw [hbody]; simp only [ByteArray.append_assoc]; rfl) rfl
            have h3 : Reader.readVector8 (Reader.mk msg.body (0 + 4 + 4)) =
                .ok (ticketNonce,
                  Reader.mk msg.body (0 + 4 + 4 + 1 + ticketNonce.size)) :=
              readVector8_at' (W := msg.body) (off := 0 + 4 + 4)
                (P := appendUInt32 ByteArray.empty ticketLifetime ++
                  appendUInt32 ByteArray.empty ticketAgeAdd)
                (X := ticketNonce)
                (by rw [hbody]; simp only [ByteArray.append_assoc]; rfl)
                (by rw [ByteArray.size_append, show (appendUInt32 ByteArray.empty ticketLifetime).size = 4 from rfl,
                  show (appendUInt32 ByteArray.empty ticketAgeAdd).size = 4 from rfl,
                  ]) hnonceSz
            have h4 : Reader.readVector16
                (Reader.mk msg.body (0 + 4 + 4 + 1 + ticketNonce.size)) =
                .ok (ticket, Reader.mk msg.body
                  (0 + 4 + 4 + 1 + ticketNonce.size + 2 + ticket.size)) :=
              readVector16_at' (W := msg.body)
                (off := 0 + 4 + 4 + 1 + ticketNonce.size)
                (P := appendUInt32 ByteArray.empty ticketLifetime ++
                  appendUInt32 ByteArray.empty ticketAgeAdd ++
                  (ByteArray.empty.push (UInt8.ofNat ticketNonce.size) ++
                    ticketNonce))
                (X := ticket)
                (by rw [hbody]; simp only [ByteArray.append_assoc]; rfl)
                (by rw [ByteArray.size_append, ByteArray.size_append,
                  ByteArray.size_append, show (appendUInt32 ByteArray.empty ticketLifetime).size = 4 from rfl,
                  show (appendUInt32 ByteArray.empty ticketAgeAdd).size = 4 from rfl,
                  show (ByteArray.empty.push
                    (UInt8.ofNat ticketNonce.size)).size = 1 from rfl]; omega)
                hticketSz
            have h5 : Reader.readVector16 (Reader.mk msg.body
                (0 + 4 + 4 + 1 + ticketNonce.size + 2 + ticket.size)) =
                .ok (ByteArray.empty, Reader.mk msg.body
                  (0 + 4 + 4 + 1 + ticketNonce.size + 2 + ticket.size + 2 +
                    ByteArray.empty.size)) :=
              readVector16_at' (W := msg.body)
                (off := 0 + 4 + 4 + 1 + ticketNonce.size + 2 + ticket.size)
                (P := appendUInt32 ByteArray.empty ticketLifetime ++
                  appendUInt32 ByteArray.empty ticketAgeAdd ++
                  (ByteArray.empty.push (UInt8.ofNat ticketNonce.size) ++
                    ticketNonce) ++
                  (appendUInt16 ByteArray.empty (UInt16.ofNat ticket.size) ++
                    ticket))
                (X := ByteArray.empty) (S := ByteArray.empty)
                (by rw [hbody]; simp only [ByteArray.append_assoc,
                  ByteArray.append_empty])
                (by rw [ByteArray.size_append, ByteArray.size_append,
                  ByteArray.size_append, ByteArray.size_append,
                  ByteArray.size_append, show (appendUInt32 ByteArray.empty ticketLifetime).size = 4 from rfl,
                  show (appendUInt32 ByteArray.empty ticketAgeAdd).size = 4 from rfl,
                  show (ByteArray.empty.push
                    (UInt8.ofNat ticketNonce.size)).size = 1 from rfl,
                  show (appendUInt16 ByteArray.empty
                    (UInt16.ofNat ticket.size)).size = 2 from rfl]; omega)
                (by simp)
            have hend : 0 + 4 + 4 + 1 + ticketNonce.size + 2 + ticket.size + 2 +
                ByteArray.empty.size = msg.body.size := by
              rw [hbody, ByteArray.size_append, ByteArray.size_append,
                ByteArray.size_append, ByteArray.size_append,
                ByteArray.size_append, ByteArray.size_append,
                ByteArray.size_append,
                show (appendUInt32 ByteArray.empty ticketLifetime).size = 4
                  from rfl,
                show (appendUInt32 ByteArray.empty ticketAgeAdd).size = 4 from rfl,
                show (ByteArray.empty.push (UInt8.ofNat ticketNonce.size)).size
                  = 1 from rfl,
                show (appendUInt16 ByteArray.empty
                  (UInt16.ofNat ticket.size)).size = 2 from rfl,
                show (appendUInt16 ByteArray.empty
                  (UInt16.ofNat ByteArray.empty.size)).size = 2 from rfl,
                show ByteArray.empty.size = 0 from rfl]
              omega
            unfold parseNewSessionTicket
            rw [hty, if_pos (show (newSessionTicketType == newSessionTicketType)
              = true from rfl)]
            simp only [h1]
            rw [if_neg hlife]
            simp only [h2, h3, h4]
            rw [if_neg hticket]
            simp only [h5]
            simp only [requireEnd_eval (context := "NewSessionTicket") hend]
            simp only [parseExtensions_empty]
            rfl

end Handshake
end Tls
