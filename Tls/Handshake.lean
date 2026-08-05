module

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

/-- The big-endian `uint24` length field of a handshake frame header, read at
offset 1 of a buffer that is at least four bytes long. -/
def uint24AtOne (bytes : ByteArray) : Nat :=
  (bytes.get! 1).toNat <<< 16 |||
    (bytes.get! 2).toNat <<< 8 |||
    (bytes.get! 3).toNat

/-- Take one complete framed handshake message out of a transport buffer,
returning `none` — not an error — while the buffer still holds only a prefix of
a message. This is the reassembly step both state machines run on the bytes the
record layer hands up; its laws are `takeMessage?_frame`,
`takeMessage?_prefix_none`, `takeMessage?_append` and
`takeMessage?_conservation`. -/
def takeMessage? (buffered : ByteArray) :
    Except String (Option (Message × ByteArray)) :=
  if buffered.size < 4 then
    .ok none
  else if buffered.size < 4 + uint24AtOne buffered then
    .ok none
  else
    match decode (buffered.extract 0 (4 + uint24AtOne buffered)) with
    | .error e => .error e
    | .ok message =>
        .ok (some (message,
          buffered.extract (4 + uint24AtOne buffered) buffered.size))

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

private theorem readVector8_ok {r r' : Reader} {b : ByteArray}
    (h : r.readVector8 = .ok (b, r')) :
    r'.bytes = r.bytes ∧ r.offset + 1 ≤ r'.offset ∧ r'.offset ≤ r.bytes.size := by
  unfold Reader.readVector8 at h
  split at h
  · cases h
  · rename_i len r₁ h8
    obtain ⟨hb1, ho1, hle1⟩ := readUInt8_ok h8
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
its laws: an x25519 share is 32 bytes, a P-256 share is a 65-byte SEC1
uncompressed point. Public (and exposed) because the ServerHello inversion law
below takes it as a hypothesis. -/
@[expose] def checkKeyShareSize : NamedGroup → ByteArray → Except String Unit
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
Split out so `parseServerHello` stays a flat `if`/`match` chain. -/
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
ServerHello laws below can evaluate it.) `encodeServerHello_parse` proves this
inverts `encodeServerHello` field by field, and
`encodeHelloRetryRequest_parseServerHello` that it refuses a
HelloRetryRequest. -/
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
Split out so `parseHelloRetryRequest` stays a flat `if`/`match` chain. -/
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
HelloRetryRequest laws below can evaluate it.) `encodeHelloRetryRequest_parse`
proves this inverts `encodeHelloRetryRequest` field by field, and
`encodeServerHello_parseHelloRetryRequest` that it refuses a ServerHello. -/
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
`encodeEncryptedExtensions_parse_none`/`_some` below can evaluate it.) -/
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

/-- One step of uint16-vector parsing. Explicit well-founded recursion over
the unconsumed bytes (not a `while` loop) so the list laws below can evaluate
it. -/
private def parseUInt16ListLoop (r : Reader) (out : Array UInt16) :
    Except String (Array UInt16) :=
  if r.atEnd then
    .ok out
  else
    match h16 : r.readUInt16 with
    | .error e => .error e
    | .ok (value, r') =>
      have hlt : r'.bytes.size - r'.offset < r.bytes.size - r.offset := by
        obtain ⟨hb, ho, hle⟩ := readUInt16_ok h16
        rw [hb]
        omega
      parseUInt16ListLoop r' (out.push value)
  termination_by r.bytes.size - r.offset
  decreasing_by exact hlt

/-- Parse a `uint16` vector body (cipher suites, supported groups, supported
versions, signature algorithms). Values are not interpreted, so unknown
(including GREASE) values are kept verbatim and in order. -/
def parseUInt16List (bytes : ByteArray) : Except String (Array UInt16) :=
  if bytes.size % 2 != 0 then
    .error "uint16 list has an odd byte length"
  else
    parseUInt16ListLoop { bytes } #[]

/-- The wire image of a `uint16` vector body. -/
def uint16ListBytes : List UInt16 → ByteArray
  | [] => ByteArray.empty
  | v :: rest => appendUInt16 ByteArray.empty v ++ uint16ListBytes rest

/-- Keep the group identifiers this implementation knows, in wire order.
Explicit recursion (not a `for` loop) so the ClientHello laws below can
evaluate it. -/
@[expose] def knownGroupsLoop : List UInt16 → Array NamedGroup → Array NamedGroup
  | [], known => known
  | id :: rest, known =>
      match NamedGroup.ofUInt16? id with
      | some group => knownGroupsLoop rest (known.push group)
      | none => knownGroupsLoop rest known

/-- The supported groups this implementation knows, in wire order. -/
@[expose] def knownGroups (ids : List UInt16) : Array NamedGroup :=
  knownGroupsLoop ids #[]

private def parseSupportedGroups (bytes : ByteArray) :
    Except String (Array UInt16 × Array NamedGroup) :=
  match parseUInt16List bytes with
  | .error e => .error e
  | .ok ids =>
    if ids.isEmpty then
      .error "supported_groups list must not be empty"
    else
      .ok (ids, knownGroups ids.toList)

/-- Record a client key share when its group is one this implementation
offers. Unknown (including GREASE) groups are skipped here, but their
identifiers are still retained in the group-id list. -/
@[expose] def pushKnownKeyShare (groupId : UInt16) (keyExchange : ByteArray)
    (out : Array ClientKeyShare) : Array ClientKeyShare :=
  match NamedGroup.ofUInt16? groupId with
  | some group => out.push { group, keyExchange }
  | none => out

/-- One step of key_share entry parsing: read `group ‖ uint16 key_exchange`
until the cursor is exhausted, rejecting empty keys and duplicate groups and
ignoring groups this implementation does not offer.

Written as explicit well-founded recursion over the unconsumed bytes rather
than a `while` loop (whose `Loop.forIn` is a `partial def`, hence opaque to
the kernel) so the key-share laws at the end of this file can evaluate it. -/
private def parseKeyShareEntriesLoop (r : Reader) (seenGroupIds : Array UInt16)
    (out : Array ClientKeyShare) :
    Except String (Array UInt16 × Array ClientKeyShare) :=
  if r.atEnd then
    .ok (seenGroupIds, out)
  else
    match h16 : r.readUInt16 with
    | .error e => .error e
    | .ok (groupId, r₁) =>
      match hv : r₁.readVector16 with
      | .error e => .error e
      | .ok (keyExchange, r₂) =>
        if keyExchange.isEmpty then
          .error s!"key_share entry for group {groupId} has an empty key_exchange"
        else if seenGroupIds.contains groupId then
          .error s!"duplicate key_share entry for group {groupId}"
        else
          have hlt : r₂.bytes.size - r₂.offset < r.bytes.size - r.offset := by
            obtain ⟨hb1, ho1, hle1⟩ := readUInt16_ok h16
            obtain ⟨hb2, ho2, hle2⟩ := readVector16_ok hv
            rw [hb2, hb1]
            rw [hb1] at hle2
            omega
          parseKeyShareEntriesLoop r₂ (seenGroupIds.push groupId)
            (pushKnownKeyShare groupId keyExchange out)
  termination_by r.bytes.size - r.offset
  decreasing_by exact hlt

/-- Parse a client key_share list: `group ‖ uint16 key_exchange` repeated until
the block is exhausted. Every group identifier offered is retained, including
ones this implementation does not know (and therefore GREASE values). -/
def parseKeyShareEntries (bytes : ByteArray) :
    Except String (Array UInt16 × Array ClientKeyShare) :=
  parseKeyShareEntriesLoop { bytes } #[] #[]

/-- The wire image of one client key_share entry:
`group ‖ uint16 length ‖ key_exchange`. -/
def keyShareEntryBytes (groupId : UInt16) (keyExchange : ByteArray) : ByteArray :=
  appendUInt16 ByteArray.empty groupId ++
    (appendUInt16 ByteArray.empty (UInt16.ofNat keyExchange.size) ++ keyExchange)

/-- The wire image of a client key_share list: its entries' images
concatenated in order. -/
def keyShareEntriesBytes : List (UInt16 × ByteArray) → ByteArray
  | [] => ByteArray.empty
  | e :: rest => keyShareEntryBytes e.1 e.2 ++ keyShareEntriesBytes rest

/-- The key shares of an offered list whose groups this implementation knows,
in wire order. -/
@[expose] def knownKeySharesLoop :
    List (UInt16 × ByteArray) → Array ClientKeyShare → Array ClientKeyShare
  | [], out => out
  | e :: rest, out => knownKeySharesLoop rest (pushKnownKeyShare e.1 e.2 out)

/-- The key shares of an offered list whose groups this implementation knows. -/
@[expose] def knownKeyShares (l : List (UInt16 × ByteArray)) : Array ClientKeyShare :=
  knownKeySharesLoop l #[]

/-- The supported_versions extension a client sends: a `uint8`-prefixed vector
of version identifiers, in preference order. -/
def clientSupportedVersionsExtension (versions : List UInt16) : Extension :=
  { extensionType := supportedVersionsExtension,
    data := ByteArray.empty.push (UInt8.ofNat (uint16ListBytes versions).size) ++
      uint16ListBytes versions }

/-- The supported_groups extension a client sends. -/
def clientSupportedGroupsExtension (groups : List UInt16) : Extension :=
  { extensionType := supportedGroupsExtension,
    data := appendUInt16 ByteArray.empty
        (UInt16.ofNat (uint16ListBytes groups).size) ++ uint16ListBytes groups }

/-- The key_share extension a client sends. -/
def clientKeyShareExtension (shares : List (UInt16 × ByteArray)) : Extension :=
  { extensionType := keyShareExtension,
    data := appendUInt16 ByteArray.empty
        (UInt16.ofNat (keyShareEntriesBytes shares).size) ++
      keyShareEntriesBytes shares }

/-- The signature_algorithms extension a client sends. -/
def clientSignatureAlgorithmsExtension (algorithms : List UInt16) : Extension :=
  { extensionType := signatureAlgorithmsExtension,
    data := appendUInt16 ByteArray.empty
        (UInt16.ofNat (uint16ListBytes algorithms).size) ++
      uint16ListBytes algorithms }

/-- Whether `subset` occurs as a subsequence of `superset`. Explicit structural
recursion (not the nested `while` scan it replaces) so the ClientHello laws
below can evaluate it. -/
@[expose] def isOrderedSubsetLoop : List UInt16 → List UInt16 → Bool
  | [], _ => true
  | _ :: _, [] => false
  | v :: vs, s :: ss =>
      if s == v then isOrderedSubsetLoop vs ss else isOrderedSubsetLoop (v :: vs) ss

/-- The key_share groups must occur in supported_groups order. Public because
the ClientHello inversion law below takes it as a hypothesis. -/
@[expose] def isOrderedSubset (subset superset : Array UInt16) : Bool :=
  isOrderedSubsetLoop subset.toList superset.toList

/-- One step of SNI server_name_list parsing: read `name_type ‖ uint16 name`
until the cursor is exhausted. Unknown name types are structurally
length-delimited and ignored. Explicit well-founded recursion, not a `while`
loop, for the same reason as `parseExtensionsLoop`. -/
private def parseServerNameListLoop (r : Reader) (seenNameTypes : Array UInt8)
    (result : Option String) : Except String (Option String) :=
  if r.atEnd then
    .ok result
  else
    match h8 : r.readUInt8 with
    | .error e => .error e
    | .ok (nameType, r₁) =>
      match hv : r₁.readVector16 with
      | .error e => .error e
      | .ok (name, r₂) =>
        if name.isEmpty then
          .error s!"SNI name of type {nameType} must not be empty"
        else if seenNameTypes.contains nameType then
          .error s!"duplicate SNI name type {nameType}"
        else
          have hlt : r₂.bytes.size - r₂.offset < r.bytes.size - r.offset := by
            obtain ⟨hb1, ho1, hle1⟩ := readUInt8_ok h8
            obtain ⟨hb2, ho2, hle2⟩ := readVector16_ok hv
            rw [hb2, hb1]
            rw [hb1] at hle2
            omega
          if nameType == 0 then
            if name.foldl (fun found b => found || b == 0) false then
              .error "SNI host_name must not contain NUL"
            else
              match String.fromUTF8? name with
              | some hostName =>
                  parseServerNameListLoop r₂ (seenNameTypes.push nameType)
                    (some hostName)
              | none => .error "SNI host_name is not valid UTF-8"
          else
            parseServerNameListLoop r₂ (seenNameTypes.push nameType) result
  termination_by r.bytes.size - r.offset
  decreasing_by
    · exact hlt
    · exact hlt

private def parseServerNameList (bytes : ByteArray) :
    Except String (Option String) :=
  if bytes.isEmpty then
    .error "SNI server_name list must not be empty"
  else
    parseServerNameListLoop { bytes } #[] none

/-- One step of ALPN ProtocolNameList parsing: read one length-prefixed name
until the cursor is exhausted. Explicit well-founded recursion, not a `while`
loop, for the same reason as `parseExtensionsLoop`. -/
private def parseAlpnProtocolListLoop (r : Reader) (out : Array String) :
    Except String (Array String) :=
  if r.atEnd then
    .ok out
  else
    match hv : r.readVector8 with
    | .error e => .error e
    | .ok (name, r₁) =>
      if name.isEmpty then
        .error "ALPN protocol name must not be empty"
      else
        have hlt : r₁.bytes.size - r₁.offset < r.bytes.size - r.offset := by
          obtain ⟨hb, ho, hle⟩ := readVector8_ok hv
          rw [hb]
          omega
        match String.fromUTF8? name with
        | some s => parseAlpnProtocolListLoop r₁ (out.push s)
        | none =>
            -- ProtocolName is an opaque byte string, not text. This server's
            -- application-facing API uses String protocol IDs, so retain the
            -- UTF-8 offers it can negotiate and ignore other well-formed IDs.
            parseAlpnProtocolListLoop r₁ out
  termination_by r.bytes.size - r.offset
  decreasing_by
    · exact hlt
    · exact hlt

private def parseAlpnProtocolList (bytes : ByteArray) :
    Except String (Array String) :=
  if bytes.isEmpty then
    .error "ALPN protocol list must not be empty"
  else
    parseAlpnProtocolListLoop { bytes } #[]

/-- The wire image of a ClientHello body: `legacy_version ‖ random ‖
legacy_session_id ‖ cipher_suites ‖ legacy_compression_methods ‖ extensions`,
with the single null compression method RFC 8446 requires. -/
def clientHelloBody (random legacySessionId : ByteArray)
    (cipherSuites : List UInt16) (extensions : List Extension) : ByteArray :=
  appendUInt16 ByteArray.empty legacyTls12Version ++ random ++
      (ByteArray.empty.push (UInt8.ofNat legacySessionId.size) ++ legacySessionId) ++
      (appendUInt16 ByteArray.empty
          (UInt16.ofNat (uint16ListBytes cipherSuites).size) ++
        uint16ListBytes cipherSuites) ++
      (ByteArray.empty.push 1 ++ ByteArray.empty.push 0) ++
    (appendUInt16 ByteArray.empty
        (UInt16.ofNat (extensionsBytes extensions).size) ++
      extensionsBytes extensions)

/-- The ClientHello extension block, absent in pre-extension ClientHellos.
Split out (like the extension-body parsers below) so `parseClientHello` stays a
flat `if`/`match` chain. -/
private def parseClientExtensionBlock (r : Reader) :
    Except String (Array Extension) :=
  if r.atEnd then
    -- The extension block was optional in pre-extension ClientHellos. Such
    -- a message cannot negotiate TLS 1.3, but is structurally decodable.
    .ok #[]
  else
    match r.readVector16 with
    | .error e => .error e
    | .ok (extensionBytes, r) =>
      match r.requireEnd "ClientHello" with
      | .error e => .error e
      | .ok () => parseExtensions extensionBytes

/-- RFC 8446 requires pre_shared_key to be the last extension and to come with
psk_key_exchange_modes. -/
private def checkClientPsk (extensions : Array Extension) : Except String Unit :=
  match findExtension? extensions preSharedKeyExtension with
  | none => .ok ()
  | some _ =>
    if !extensions.isEmpty &&
        extensions[extensions.size - 1]!.extensionType == preSharedKeyExtension then
      match findExtension? extensions pskKeyExchangeModesExtension with
      | none =>
          .error "ClientHello offered pre_shared_key without psk_key_exchange_modes"
      | some modes =>
        match ({ bytes := modes.data } : Reader).readVector8 with
        | .error e => .error e
        | .ok (values, mr) =>
          match mr.requireEnd "ClientHello psk_key_exchange_modes" with
          | .error e => .error e
          | .ok () =>
            if values.isEmpty then
              .error "ClientHello psk_key_exchange_modes must not be empty"
            else
              .ok ()
    else
      .error "ClientHello pre_shared_key must be the final extension"

/-- The supported_versions extension body a client sends: a `uint8`-prefixed
vector of version identifiers, kept verbatim. -/
private def parseClientVersions (data : ByteArray) : Except String (Array UInt16) :=
  match ({ bytes := data } : Reader).readVector8 with
  | .error e => .error e
  | .ok (list, vr) =>
    match vr.requireEnd "ClientHello supported_versions" with
    | .error e => .error e
    | .ok () =>
      if list.isEmpty then
        .error "ClientHello supported_versions list must not be empty"
      else
        parseUInt16List list

/-- The supported_groups extension body. -/
private def parseClientGroups (data : ByteArray) :
    Except String (Array UInt16 × Array NamedGroup) :=
  match ({ bytes := data } : Reader).readVector16 with
  | .error e => .error e
  | .ok (list, gr) =>
    match gr.requireEnd "ClientHello supported_groups" with
    | .error e => .error e
    | .ok () => parseSupportedGroups list

/-- The client key_share extension body. -/
private def parseClientKeyShare (data : ByteArray) :
    Except String (Array UInt16 × Array ClientKeyShare) :=
  match ({ bytes := data } : Reader).readVector16 with
  | .error e => .error e
  | .ok (entries, kr) =>
    match kr.requireEnd "ClientHello key_share" with
    | .error e => .error e
    | .ok () => parseKeyShareEntries entries

/-- The signature_algorithms extension body. -/
private def parseClientSignatureAlgorithms (data : ByteArray) :
    Except String (Array UInt16) :=
  match ({ bytes := data } : Reader).readVector16 with
  | .error e => .error e
  | .ok (list, sr) =>
    match sr.requireEnd "ClientHello signature_algorithms" with
    | .error e => .error e
    | .ok () =>
      if list.isEmpty then
        .error "ClientHello signature_algorithms list must not be empty"
      else
        parseUInt16List list

/-- The server_name extension body. -/
private def parseClientServerName (data : ByteArray) :
    Except String (Option String) :=
  match ({ bytes := data } : Reader).readVector16 with
  | .error e => .error e
  | .ok (list, sr) =>
    match sr.requireEnd "ClientHello server_name" with
    | .error e => .error e
    | .ok () => parseServerNameList list

/-- The ALPN extension body. -/
private def parseClientAlpn (data : ByteArray) : Except String (Array String) :=
  match ({ bytes := data } : Reader).readVector16 with
  | .error e => .error e
  | .ok (list, ar) =>
    match ar.requireEnd "ClientHello ALPN" with
    | .error e => .error e
    | .ok () => parseAlpnProtocolList list

/-- Look up an optional extension and parse its body, defaulting when absent. -/
private def parseOptionalExtension {α : Type} (extensions : Array Extension)
    (extensionType : UInt16) (dflt : α) (parse : ByteArray → Except String α) :
    Except String α :=
  match findExtension? extensions extensionType with
  | none => .ok dflt
  | some ext => parse ext.data

/-- Parse a ClientHello for the server flow. Extracts the fields the server needs
to select a key-exchange group, verify TLS 1.3 support, and negotiate ALPN/SNI.
(Written as a pure `if`/`match` chain so the ClientHello laws below can evaluate
it.) `parseClientHello_clientHelloBody_mem` proves it inverts `clientHelloBody`:
cipher suites, versions, supported groups, key-share groups, signature schemes
and the whole extension list come back verbatim and in order, whatever the
values are and wherever the interpreted extensions sit in the list
(`parseClientHello_clientHelloBody_opaque` is the special case of a ClientHello
whose extensions are all uninterpreted, `parseClientHello_clientHelloBody` the
one where the interpreted ones come last, and
`parseClientHello_clientHelloBody_psk` the resumption shape).
`parseClientHello_canonical` proves the converse direction: a ClientHello this
accepts re-encodes to exactly the body it was parsed from. -/
def parseClientHello (msg : Message) : Except String ClientHello :=
  if msg.msgType == clientHelloType then
    match ({ bytes := msg.body } : Reader).readUInt16 with
    | .error e => .error e
    | .ok (legacyVersion, r) =>
      if legacyVersion == legacyTls12Version then
        match r.take 32 with
        | .error e => .error e
        | .ok (random, r) =>
          match r.readVector8 with
          | .error e => .error e
          | .ok (sessionId, r) =>
            if sessionId.size ≤ 32 then
              match r.readVector16 with
              | .error e => .error e
              | .ok (cipherSuitesBytes, r) =>
                match parseUInt16List cipherSuitesBytes with
                | .error e => .error e
                | .ok cipherSuites =>
                  if cipherSuites.isEmpty then
                    .error "ClientHello cipher_suites must not be empty"
                  else
                    match r.readVector8 with
                    | .error e => .error e
                    | .ok (compression, r) =>
                      if compression.size == 1 && compression.get! 0 == 0 then
                        match parseClientExtensionBlock r with
                        | .error e => .error e
                        | .ok extensions =>
                          match checkClientPsk extensions with
                          | .error e => .error e
                          | .ok () =>
                            match parseOptionalExtension extensions
                                supportedVersionsExtension #[]
                                parseClientVersions with
                            | .error e => .error e
                            | .ok supportedVersionIds =>
                              match parseOptionalExtension extensions
                                  supportedGroupsExtension (#[], #[])
                                  parseClientGroups with
                              | .error e => .error e
                              | .ok (supportedGroupIds, supportedGroups) =>
                                match parseOptionalExtension extensions
                                    keyShareExtension (#[], #[])
                                    parseClientKeyShare with
                                | .error e => .error e
                                | .ok (keyShareGroupIds, keyShares) =>
                                  -- Keep missing-extension policy at the
                                  -- connection layer so it can emit the TLS 1.3
                                  -- `missing_extension` alert. When
                                  -- supported_groups is present, its ordering
                                  -- constraint on key_share entries is still a
                                  -- wire-codec invariant.
                                  if (findExtension? extensions
                                        supportedGroupsExtension).isSome &&
                                      !isOrderedSubset keyShareGroupIds
                                        supportedGroupIds then
                                    .error "ClientHello key_share groups must occur in supported_groups order"
                                  else
                                    match parseOptionalExtension extensions
                                        signatureAlgorithmsExtension #[]
                                        parseClientSignatureAlgorithms with
                                    | .error e => .error e
                                    | .ok signatureAlgorithms =>
                                      match parseOptionalExtension extensions
                                          serverNameExtension none
                                          parseClientServerName with
                                      | .error e => .error e
                                      | .ok serverName =>
                                        match parseOptionalExtension extensions
                                            alpnExtension #[]
                                            parseClientAlpn with
                                        | .error e => .error e
                                        | .ok alpnProtocols =>
                                          .ok {
                                            random,
                                            legacySessionId := sessionId,
                                            cipherSuites,
                                            supportedVersionIds,
                                            supportedGroupIds, supportedGroups,
                                            keyShareGroupIds, keyShares,
                                            signatureAlgorithms, serverName,
                                            alpnProtocols, extensions,
                                            offersTls13 :=
                                              supportedVersionIds.contains
                                                tls13Version,
                                            encoded := msg.encoded }
                      else
                        .error "ClientHello legacy_compression_methods must contain exactly null compression"
            else
              .error s!"ClientHello legacy session id exceeds 32 bytes ({sessionId.size})"
      else
        .error s!"ClientHello legacy_version must be 0x0303, got {legacyVersion}"
  else
    .error s!"expected ClientHello ({clientHelloType}), got handshake type {msg.msgType}"

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

Kernel-checked encode/parse inversion for the handshake codecs.

* Framing: `frame` output is accepted byte-for-byte by `decodeOne` with an
  explicit residual (`decodeOne_frame`), so every message encoder roundtrips
  through the wire decoder (`encode*_decodeOne`, `encode*_decode`).
* Reassembly: the outcome depends only on the reassembled byte stream, not on
  where the record layer split it (`decodeOne_frame_split`), back-to-back
  messages are peeled in order (`decodeOne_frame_concat`), and no strict
  prefix of a frame ever decodes (`decodeOne_prefix_error`).
* Message bodies invert semantically: `encodeFinished_parse`,
  `encodeKeyUpdate_parse`, `encodeCertificateVerify_parse`,
  `encodeEncryptedExtensions_parse_none`/`_some`, `encodeCertificate_parse`,
  and `encodeNewSessionTicket_parse`.
* Tolerance: an extension list (`parseExtensions_extensionsBytes`) and a
  `uint16` vector (`parseUInt16List_uint16ListBytes`) both roundtrip for
  *arbitrary* types and values, so unknown, reserved and GREASE extensions,
  cipher suites, groups, versions and signature schemes survive a
  parse/re-encode cycle unchanged and in order.
* HelloRetryRequest is discriminated from ServerHello by the RFC 8446
  sentinel random (`encodeHelloRetryRequest_isHelloRetryRequest`,
  `encodeServerHello_not_isHelloRetryRequest`), and each parser rejects the
  other message (`encodeHelloRetryRequest_parseServerHello`,
  `encodeServerHello_parseHelloRetryRequest`). -/

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

/-! ### Byte (de)composition

Big-endian recomposition, proved *arithmetically*:
`Nat.shiftLeft_add_eq_or_of_lt` rewrites a disjoint `|||` as `+` (see
`or_add_lt`), and `omega` finishes. Doing it this way rather than with
`bv_decide` keeps the LRAT certificate checker out of the trusted computing
base — nothing in this repository depends on a generated axiom. -/

/-- Disjoint `|||` is `+`: the low `i` bits of the left operand are clear. -/
private theorem or_add_lt {a b i : Nat} (hb : b < 2 ^ i) :
    a * 2 ^ i ||| b = a * 2 ^ i + b := by
  rw [show a * 2 ^ i = a <<< i from (Nat.shiftLeft_eq a i).symm,
    ← Nat.shiftLeft_add_eq_or_of_lt hb]

private theorem uint32_recompose (v : UInt32) :
    ((v >>> 24).toUInt8.toUInt32 <<< 24 ||| (v >>> 16).toUInt8.toUInt32 <<< 16 |||
      (v >>> 8).toUInt8.toUInt32 <<< 8 ||| v.toUInt8.toUInt32) = v := by
  apply UInt32.toNat_inj.mp
  have hv := v.toNat_lt
  simp only [UInt32.toNat_or, UInt32.toNat_shiftLeft, UInt8.toNat_toUInt32,
    UInt32.toNat_toUInt8, UInt32.toNat_shiftRight,
    show UInt32.toNat 24 % 32 = 24 from rfl,
    show UInt32.toNat 16 % 32 = 16 from rfl,
    show UInt32.toNat 8 % 32 = 8 from rfl,
    Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow]
  rw [show v.toNat / 2 ^ 24 % 2 ^ 8 * 2 ^ 24 % 2 ^ 32 = v.toNat / 2 ^ 24 * 2 ^ 24 from by
      omega,
    show v.toNat / 2 ^ 16 % 2 ^ 8 * 2 ^ 16 % 2 ^ 32 =
      v.toNat / 2 ^ 16 % 2 ^ 8 * 2 ^ 16 from by omega,
    show v.toNat / 2 ^ 8 % 2 ^ 8 * 2 ^ 8 % 2 ^ 32 =
      v.toNat / 2 ^ 8 % 2 ^ 8 * 2 ^ 8 from by omega,
    Nat.or_assoc, Nat.or_assoc, or_add_lt (i := 8), or_add_lt (i := 16),
    or_add_lt (i := 24)]
  all_goals omega

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
  apply UInt16.toNat_inj.mp
  have hv := v.toNat_lt
  simp only [UInt16.toNat_or, UInt16.toNat_shiftLeft, UInt8.toNat_toUInt16,
    UInt16.toNat_toUInt8, UInt16.toNat_shiftRight,
    show UInt16.toNat 8 % 16 = 8 from rfl, Nat.shiftLeft_eq,
    Nat.shiftRight_eq_div_pow]
  rw [show v.toNat / 2 ^ 8 % 2 ^ 8 * 2 ^ 8 % 2 ^ 16 = v.toNat / 2 ^ 8 * 2 ^ 8 from by
      omega,
    or_add_lt (i := 8)]
  all_goals omega

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

/-! ### Wire → list converse for extension lists

`parseExtensions_extensionsBytes` says every extension list is recovered from
its wire image. These laws say the opposite: every buffer the parser accepts
*is* the wire image of what it produced, so re-encoding a parsed extension list
reproduces the bytes it came from. -/

private theorem uint16_hi (b0 b1 : UInt8) :
    ((b0.toUInt16 <<< 8 ||| b1.toUInt16) >>> 8).toUInt8 = b0 := by
  apply UInt8.toNat_inj.mp
  have h0 := b0.toNat_lt
  have h1 := b1.toNat_lt
  simp only [UInt16.toNat_toUInt8, UInt16.toNat_shiftRight, UInt16.toNat_or,
    UInt16.toNat_shiftLeft, UInt8.toNat_toUInt16,
    show UInt16.toNat 8 % 16 = 8 from rfl, Nat.shiftLeft_eq,
    Nat.shiftRight_eq_div_pow]
  rw [show b0.toNat * 2 ^ 8 % 2 ^ 16 = b0.toNat * 2 ^ 8 from by omega,
    or_add_lt (i := 8)]
  all_goals omega

private theorem uint16_lo (b0 b1 : UInt8) :
    (b0.toUInt16 <<< 8 ||| b1.toUInt16).toUInt8 = b1 := by
  apply UInt8.toNat_inj.mp
  have h0 := b0.toNat_lt
  have h1 := b1.toNat_lt
  simp only [UInt16.toNat_toUInt8, UInt16.toNat_or, UInt16.toNat_shiftLeft,
    UInt8.toNat_toUInt16, show UInt16.toNat 8 % 16 = 8 from rfl,
    Nat.shiftLeft_eq]
  rw [show b0.toNat * 2 ^ 8 % 2 ^ 16 = b0.toNat * 2 ^ 8 from by omega,
    or_add_lt (i := 8)]
  all_goals omega

private theorem getElem_appendUInt16_zero (v : UInt16)
    (h : 0 < (appendUInt16 ByteArray.empty v).size) :
    (appendUInt16 ByteArray.empty v)[0] = (v >>> 8).toUInt8 := rfl

private theorem getElem_appendUInt16_one (v : UInt16)
    (h : 1 < (appendUInt16 ByteArray.empty v).size) :
    (appendUInt16 ByteArray.empty v)[1] = v.toUInt8 := rfl

/-- Two bytes of a buffer are the big-endian encoding of the `uint16` they
decode to. -/
private theorem extract_two {W : ByteArray} {off e : Nat} (he : e = off + 2)
    (h : off + 2 ≤ W.size) :
    W.extract off e = appendUInt16 ByteArray.empty
      ((W.get! off).toUInt16 <<< 8 ||| (W.get! (off + 1)).toUInt16) := by
  subst he
  apply ByteArray.ext_getElem
  · rw [ByteArray.size_extract, Nat.min_eq_left h]
    show off + 2 - off = 2
    omega
  · intro i hi hi'
    rw [ByteArray.size_extract, Nat.min_eq_left h] at hi
    rw [ByteArray.getElem_extract]
    match i, hi with
    | 0, _ =>
      rw [getElem_appendUInt16_zero, uint16_hi,
        get!_eq_getElem (show off < W.size by omega)]
      simp
    | 1, _ =>
      rw [getElem_appendUInt16_one, uint16_lo,
        get!_eq_getElem (show off + 1 < W.size by omega)]

/-- A `type ‖ uint16 length ‖ data` record read out of a buffer is exactly the
wire image of the extension it decodes to. -/
private theorem extract_extensionBytes {W : ByteArray} {off : Nat} {t Lv : UInt16}
    (ht : t = (W.get! off).toUInt16 <<< 8 ||| (W.get! (off + 1)).toUInt16)
    (hL : Lv = (W.get! (off + 2)).toUInt16 <<< 8 ||| (W.get! (off + 3)).toUInt16)
    (hle : off + 4 + Lv.toNat ≤ W.size) :
    W.extract off (off + 4 + Lv.toNat) =
      extensionBytes (Extension.mk t (W.extract (off + 4) (off + 4 + Lv.toNat))) := by
  have hdsize : (W.extract (off + 4) (off + 4 + Lv.toNat)).size = Lv.toNat := by
    rw [ByteArray.size_extract]
    omega
  have hofNat :
      UInt16.ofNat (W.extract (off + 4) (off + 4 + Lv.toNat)).size = Lv := by
    rw [hdsize, UInt16.ofNat_toNat]
  have hsplit1 : W.extract off (off + 2) ++
      W.extract (off + 2) (off + 4 + Lv.toNat)
      = W.extract off (off + 4 + Lv.toNat) := by
    rw [ByteArray.extract_append_extract, Nat.min_eq_left (by omega),
      Nat.max_eq_right (by omega)]
  have hsplit2 : W.extract (off + 2) (off + 4) ++
      W.extract (off + 4) (off + 4 + Lv.toNat)
      = W.extract (off + 2) (off + 4 + Lv.toNat) := by
    rw [ByteArray.extract_append_extract, Nat.min_eq_left (by omega),
      Nat.max_eq_right (by omega)]
  rw [← hsplit1, ← hsplit2,
    extract_two (W := W) (off := off) (e := off + 2) rfl (by omega),
    extract_two (W := W) (off := off + 2) (e := off + 4) (by omega) (by omega),
    ← ht]
  show _ = appendUInt16 ByteArray.empty t ++
    (appendUInt16 ByteArray.empty
        (UInt16.ofNat (W.extract (off + 4) (off + 4 + Lv.toNat)).size) ++
      W.extract (off + 4) (off + 4 + Lv.toNat))
  rw [hofNat, ← hL]

private theorem extract_self_empty (W : ByteArray) (k : Nat) :
    W.extract k k = ByteArray.empty := by
  apply ByteArray.ext_getElem
  · rw [ByteArray.size_extract]
    show min k W.size - k = 0
    omega
  · intro i hi hi'
    exact absurd hi' (by simp)

/-- Splitting a slice at an interior point. -/
private theorem extract_split {W : ByteArray} {i j k : Nat} (hij : i ≤ j)
    (hjk : j ≤ k) : W.extract i k = W.extract i j ++ W.extract j k := by
  rw [ByteArray.extract_append_extract, Nat.min_eq_left hij,
    Nat.max_eq_right hjk]

/-- Appending to a buffer does not change a slice that ends inside it. -/
private theorem extract_append_prefix {a x : ByteArray} {k : Nat}
    (hk : k ≤ a.size) : (a ++ x).extract 0 k = a.extract 0 k := by
  rw [ByteArray.extract_append, Nat.zero_sub, Nat.sub_eq_zero_of_le hk,
    extract_self_empty, ByteArray.append_empty]

/-- Appending to a buffer only extends the tail of a slice that starts inside
it. -/
private theorem extract_append_suffix {a x : ByteArray} {k : Nat}
    (hk : k ≤ a.size) :
    (a ++ x).extract k (a ++ x).size = a.extract k a.size ++ x := by
  rw [extract_split (W := a ++ x) (i := k) (j := a.size) hk
    (by rw [ByteArray.size_append]; omega),
    ByteArray.extract_append_eq_right rfl (by rw [ByteArray.size_append]),
    ByteArray.extract_append, Nat.sub_eq_zero_of_le hk, Nat.sub_self,
    extract_self_empty, ByteArray.append_empty]

/-- The wire image of an extension read out of a buffer, followed by the image
of what comes after it, is the whole remaining buffer. -/
private theorem extract_cons_image {W : ByteArray} {off : Nat}
    {rest : List Extension}
    (hle : off + 2 + 2 +
      ((W.get! (off + 2)).toUInt16 <<< 8 |||
        (W.get! (off + 2 + 1)).toUInt16).toNat ≤ W.size)
    (hext : W.extract (off + 2 + 2 +
        ((W.get! (off + 2)).toUInt16 <<< 8 |||
          (W.get! (off + 2 + 1)).toUInt16).toNat) W.size = extensionsBytes rest) :
    W.extract off W.size = extensionsBytes
      (Extension.mk ((W.get! off).toUInt16 <<< 8 ||| (W.get! (off + 1)).toUInt16)
        (W.extract (off + 2 + 2) (off + 2 + 2 +
          ((W.get! (off + 2)).toUInt16 <<< 8 |||
            (W.get! (off + 2 + 1)).toUInt16).toNat)) :: rest) := by
  have hidx : off + 2 + 1 = off + 3 := by omega
  have hidx2 : off + 2 + 2 = off + 4 := by omega
  rw [hidx, hidx2] at hle hext ⊢
  show W.extract off W.size = extensionBytes _ ++ extensionsBytes rest
  rw [← hext, ← extract_extensionBytes (W := W) (off := off) rfl rfl hle,
    ByteArray.extract_append_extract, Nat.min_eq_left (by omega),
    Nat.max_eq_right (by omega)]

/-- Everything the extension loop consumed is the wire image of what it
produced. -/
private theorem parseExtensionsLoop_image : ∀ (n : Nat) (W : ByteArray) (off : Nat)
    (out res : Array Extension),
    W.size - off ≤ n → off ≤ W.size →
    parseExtensionsLoop (Reader.mk W off) out = .ok res →
    ∃ rest, res.toList = out.toList ++ rest ∧
      W.extract off W.size = extensionsBytes rest := by
  intro n
  induction n with
  | zero =>
    intro W off out res hn hle h
    have hend : off = W.size := by omega
    rw [parseExtensionsLoop_end (E := W) (off := off) hend] at h
    cases h
    exact ⟨[], by simp, by rw [hend]; exact extract_self_empty ..⟩
  | succ n ih =>
    intro W off out res hn hle h
    by_cases hE : off = W.size
    · rw [parseExtensionsLoop_end (E := W) (off := off) hE] at h
      cases h
      exact ⟨[], by simp, by rw [hE]; exact extract_self_empty ..⟩
    have hlt : off < W.size := by omega
    rw [parseExtensionsLoop.eq_def, if_neg (show ¬((Reader.mk W off).atEnd = true) from by
      show ¬(off == W.size) = true
      rw [beq_iff_eq]
      exact hE)] at h
    split at h
    · cases h
    · rename_i t r₁ h16
      obtain ⟨hb1, ho1, hle1⟩ := readUInt16_ok h16
      have ho1' : r₁.offset = off + 2 := ho1
      have hle1' : r₁.offset ≤ W.size := hle1
      rw [readUInt16_eval (b := W) (off := off) (by omega)] at h16
      simp only [Except.ok.injEq, Prod.mk.injEq] at h16
      obtain ⟨rfl, rfl⟩ := h16
      split at h
      · cases h
      · rename_i d r₂ hv
        obtain ⟨hb2, hlo2, hle2⟩ := readVector16_ok hv
        have hlo2' : off + 2 + 2 ≤ r₂.offset := hlo2
        have hle2' : r₂.offset ≤ W.size := hle2
        unfold Reader.readVector16 at hv
        simp only [readUInt16_eval (b := W) (off := off + 2) (by omega)] at hv
        obtain ⟨hb3, ho3, hle3⟩ := take_ok hv
        have ho3' : r₂.offset = off + 2 + 2 +
            ((W.get! (off + 2)).toUInt16 <<< 8 |||
              (W.get! (off + 2 + 1)).toUInt16).toNat := ho3
        have hLbound : off + 2 + 2 +
            ((W.get! (off + 2)).toUInt16 <<< 8 |||
              (W.get! (off + 2 + 1)).toUInt16).toNat ≤ W.size := by omega
        rw [take_eval (b := W) (off := off + 2 + 2) hLbound] at hv
        simp only [Except.ok.injEq, Prod.mk.injEq] at hv
        obtain ⟨rfl, rfl⟩ := hv
        split at h
        · cases h
        · obtain ⟨rest, hres, hext⟩ := ih W (off + 2 + 2 +
            ((W.get! (off + 2)).toUInt16 <<< 8 |||
              (W.get! (off + 2 + 1)).toUInt16).toNat) _ _ (by omega) hLbound h
          refine ⟨_ :: rest, ?_, extract_cons_image hLbound hext⟩
          rw [hres, Array.toList_push, List.append_assoc]
          rfl

/-- **Wire → list converse**: every extension block the parser accepts is
exactly the wire image of the list it produced, so re-encoding a parsed
extension list reproduces the bytes it came from. Together with
`parseExtensions_extensionsBytes` this makes the extension codec a bijection
between accepted buffers and the lists they parse to. -/
theorem parseExtensions_image {E : ByteArray} {exts : Array Extension}
    (h : parseExtensions E = .ok exts) : E = extensionsBytes exts.toList := by
  unfold parseExtensions at h
  obtain ⟨rest, hres, hext⟩ :=
    parseExtensionsLoop_image E.size E 0 #[] exts (by omega) (by omega) h
  rw [ByteArray.extract_zero_size] at hext
  rw [hext, hres]
  rfl

/-- **Injectivity on accepted buffers**: two extension blocks that parse to the
same list are byte-identical. -/
theorem parseExtensions_injective {E₁ E₂ : ByteArray} {exts : Array Extension}
    (h₁ : parseExtensions E₁ = .ok exts) (h₂ : parseExtensions E₂ = .ok exts) :
    E₁ = E₂ := by
  rw [parseExtensions_image h₁, parseExtensions_image h₂]

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

/-! ### Reassembly independence

The record layer hands the handshake layer a byte stream that it may have
split at arbitrary points (`Tls.Record.Laws` proves the split is conserved).
These laws say the handshake decoder only ever sees that stream: where the
splits fell cannot change the outcome, an incomplete frame is never decoded,
and back-to-back messages are peeled in order. -/

/-- **Split independence**: however a framed message's bytes were divided
between records, decoding the reassembled buffer yields the message and
leaves the following bytes untouched. -/
theorem decodeOne_frame_split {msgType : UInt8} {body : ByteArray} {msg : Message}
    (h : frame msgType body = .ok msg) (a b rest : ByteArray)
    (hsplit : a ++ b = msg.encoded) :
    decodeOne (a ++ (b ++ rest)) = .ok (msg, rest) := by
  rw [← ByteArray.append_assoc, hsplit]
  exact decodeOne_frame h rest

/-- **In-order peeling**: two framed messages sharing a buffer are decoded one
at a time, each with the rest of the stream as residual. -/
theorem decodeOne_frame_concat {t₁ t₂ : UInt8} {b₁ b₂ : ByteArray}
    {m₁ m₂ : Message} (h₁ : frame t₁ b₁ = .ok m₁) (h₂ : frame t₂ b₂ = .ok m₂)
    (rest : ByteArray) :
    decodeOne (m₁.encoded ++ (m₂.encoded ++ rest)) = .ok (m₁, m₂.encoded ++ rest) ∧
    decodeOne (m₂.encoded ++ rest) = .ok (m₂, rest) :=
  ⟨decodeOne_frame h₁ (m₂.encoded ++ rest), decodeOne_frame h₂ rest⟩

/-- **Incomplete frames are never decoded**: any strict prefix of a framed
message is rejected, so a reassembler that waits for more bytes can never
have missed a message. -/
theorem decodeOne_prefix_error {msgType : UInt8} {body : ByteArray} {msg : Message}
    (h : frame msgType body = .ok msg) {k : Nat} (hk : k < msg.encoded.size) :
    ∃ e, decodeOne (msg.encoded.extract 0 k) = .error e := by
  obtain ⟨hlt, hmsg⟩ := frame_spec h
  have hP1 : (ByteArray.empty.push msgType).size = 1 := rfl
  have hPL : (ByteArray.empty.push msgType ++ length24Bytes body.size).size = 4 := by
    rw [ByteArray.size_append, hP1]
    rfl
  have hEsize : msg.encoded.size = 4 + body.size := by
    rw [hmsg]
    show (ByteArray.empty.push msgType ++ length24Bytes body.size ++ body).size = _
    rw [ByteArray.size_append, hPL]
  have hb : ∀ i, 1 ≤ i → i < 4 →
      msg.encoded.get! i = (length24Bytes body.size).get! (i - 1) := by
    intro i h1 h4
    rw [hmsg]
    show (ByteArray.empty.push msgType ++ length24Bytes body.size ++ body).get! i = _
    rw [get!_append_left (by rw [hPL]; omega),
      get!_append_right (by rw [hP1]; omega)
        (by rw [hP1, show (length24Bytes body.size).size = 3 from rfl]; omega),
      hP1]
  have hpsize : (msg.encoded.extract 0 k).size = k := by
    rw [ByteArray.size_extract]
    omega
  unfold decodeOne
  split
  · exact ⟨_, rfl⟩
  · rename_i mt r₁ h1
    split
    · exact ⟨_, rfl⟩
    · rename_i len r₂ h2
      split
      · exact ⟨_, rfl⟩
      · rename_i bodyBytes r₃ h3
        exfalso
        obtain ⟨hb1, ho1, hle1⟩ := readUInt8_ok h1
        obtain ⟨hb2, ho2, hle2⟩ := readUInt24_ok h2
        obtain ⟨hb3, ho3, hle3⟩ := take_ok h3
        have hr₁ : r₁ = { bytes := msg.encoded.extract 0 k, offset := 1 } := by
          rcases r₁ with ⟨bs, off⟩
          have hbs : bs = msg.encoded.extract 0 k := hb1
          have hoff : off = 1 := ho1
          rw [hbs, hoff]
        rw [hr₁] at h2 hb2 ho2 hle2
        have hoff2 : r₂.offset = 4 := by rw [ho2]
        have hbytes2 : r₂.bytes = msg.encoded.extract 0 k := hb2
        have hk4 : 4 ≤ k := by
          rw [hoff2] at hle2
          have hle2' : (4 : Nat) ≤ (msg.encoded.extract 0 k).size := hle2
          rw [hpsize] at hle2'
          exact hle2'
        -- Four header bytes are present, so the length field is the real one.
        have heval := readUInt24_eval (b := msg.encoded.extract 0 k) (off := 1)
          (by rw [hpsize]; omega)
        rw [h2] at heval
        simp only [Except.ok.injEq, Prod.mk.injEq] at heval
        have hlen : len = body.size := by
          rw [heval.1,
            extract_get! (s := 0) (k := 1) (by omega) (by omega),
            extract_get! (s := 0) (k := 2) (by omega) (by omega),
            extract_get! (s := 0) (k := 3) (by omega) (by omega),
            hb 1 (by omega) (by omega), hb 2 (by omega) (by omega),
            hb 3 (by omega) (by omega)]
          exact uint24_recompose hlt
        rw [hbytes2, hpsize] at hle3
        rw [ho3, hoff2, hlen] at hle3
        omega

/-! ### Buffered delivery

`takeMessage?` is the reassembly step a state machine runs on the bytes the
record layer has handed up so far. These laws say buffering is monotone and
exact: while a framed message is incomplete the buffer yields nothing (never an
error), and the instant its last byte arrives the whole message is delivered
with the bytes after it returned untouched. -/

private theorem size_encoded {msgType : UInt8} {body : ByteArray} {msg : Message}
    (h : frame msgType body = .ok msg) : msg.encoded.size = 4 + body.size := by
  obtain ⟨hlt, hmsg⟩ := frame_spec h
  rw [hmsg]
  show (ByteArray.empty.push msgType ++ length24Bytes body.size ++ body).size = _
  rw [ByteArray.size_append, ByteArray.size_append,
    show (ByteArray.empty.push msgType).size = 1 from rfl,
    show (length24Bytes body.size).size = 3 from rfl]

private theorem uint24AtOne_congr {a b : ByteArray}
    (h : ∀ i, i < 4 → a.get! i = b.get! i) : uint24AtOne a = uint24AtOne b := by
  unfold uint24AtOne
  rw [h 1 (by omega), h 2 (by omega), h 3 (by omega)]

private theorem uint24AtOne_encoded {msgType : UInt8} {body : ByteArray}
    {msg : Message} (h : frame msgType body = .ok msg) :
    uint24AtOne msg.encoded = body.size := by
  obtain ⟨hlt, hmsg⟩ := frame_spec h
  have hP1 : (ByteArray.empty.push msgType).size = 1 := rfl
  have hPL : (ByteArray.empty.push msgType ++ length24Bytes body.size).size = 4 := by
    rw [ByteArray.size_append, hP1]
    rfl
  have hb : ∀ i, 1 ≤ i → i < 4 →
      msg.encoded.get! i = (length24Bytes body.size).get! (i - 1) := by
    intro i h1 h4
    rw [hmsg]
    show (ByteArray.empty.push msgType ++ length24Bytes body.size ++ body).get! i = _
    rw [get!_append_left (by rw [hPL]; omega),
      get!_append_right (by rw [hP1]; omega)
        (by rw [hP1, show (length24Bytes body.size).size = 3 from rfl]; omega),
      hP1]
  unfold uint24AtOne
  rw [hb 1 (by omega) (by omega), hb 2 (by omega) (by omega),
    hb 3 (by omega) (by omega)]
  show (UInt8.ofNat (body.size >>> 16)).toNat <<< 16 |||
    (UInt8.ofNat (body.size >>> 8)).toNat <<< 8 |||
    (UInt8.ofNat body.size).toNat = body.size
  exact uint24_recompose hlt

/-- **Delivery**: once a framed message's last byte is in the buffer the whole
message is taken out, and the bytes after it are returned untouched. -/
theorem takeMessage?_frame {msgType : UInt8} {body : ByteArray} {msg : Message}
    (h : frame msgType body = .ok msg) (rest : ByteArray) :
    takeMessage? (msg.encoded ++ rest) = .ok (some (msg, rest)) := by
  have hEsize : msg.encoded.size = 4 + body.size := size_encoded h
  have hL : uint24AtOne (msg.encoded ++ rest) = body.size := by
    rw [uint24AtOne_congr (b := msg.encoded)
      (fun i hi => get!_append_left (by omega))]
    exact uint24AtOne_encoded h
  unfold takeMessage?
  rw [if_neg (by rw [ByteArray.size_append]; omega), hL,
    if_neg (by rw [ByteArray.size_append]; omega),
    show (msg.encoded ++ rest).extract 0 (4 + body.size) = msg.encoded from by
      rw [← hEsize]
      exact ByteArray.extract_append_eq_left rfl,
    decode_frame h,
    show (msg.encoded ++ rest).extract (4 + body.size)
        (msg.encoded ++ rest).size = rest from by
      rw [← hEsize]
      have h2 := ByteArray.extract_append_size_add (a := msg.encoded) (b := rest)
        (i := 0) (j := rest.size)
      rw [Nat.add_zero] at h2
      rw [ByteArray.size_append, h2, ByteArray.extract_zero_size]]

/-- **No early delivery**: a strict prefix of a framed message yields nothing —
and never an error — so a state machine that waits for more bytes can never
have skipped a message. -/
theorem takeMessage?_prefix_none {msgType : UInt8} {body : ByteArray}
    {msg : Message} (h : frame msgType body = .ok msg) {a c : ByteArray}
    (hsplit : a ++ c = msg.encoded) (hc : 0 < c.size) :
    takeMessage? a = .ok none := by
  have hEsize : msg.encoded.size = 4 + body.size := size_encoded h
  have hasize : a.size + c.size = msg.encoded.size := by
    rw [← hsplit, ByteArray.size_append]
  unfold takeMessage?
  by_cases h4 : a.size < 4
  · rw [if_pos h4]
  · rw [if_neg h4]
    have hL : uint24AtOne a = body.size := by
      rw [uint24AtOne_congr (b := msg.encoded)
        (fun i hi => by
          rw [← hsplit]
          exact (get!_append_left (by omega)).symm)]
      exact uint24AtOne_encoded h
    rw [hL, if_pos (by omega)]

/-- **Buffering is monotone and exact**: however the record layer split a framed
message, every proper prefix of it leaves the buffer empty-handed, and the
arrival of its last byte delivers the whole message together with whatever
followed it. -/
theorem takeMessage?_frame_split {msgType : UInt8} {body : ByteArray}
    {msg : Message} (h : frame msgType body = .ok msg) (a c rest : ByteArray)
    (hsplit : a ++ c = msg.encoded) :
    (0 < c.size → takeMessage? a = .ok none) ∧
    takeMessage? (a ++ (c ++ rest)) = .ok (some (msg, rest)) :=
  ⟨fun hc => takeMessage?_prefix_none h hsplit hc, by
    rw [← ByteArray.append_assoc, hsplit]
    exact takeMessage?_frame h rest⟩

/-- **Monotone on any buffer**: bytes that arrive after a message was already
complete cannot change what is delivered. Whatever buffer `takeMessage?`
succeeded on, appending more bytes returns the same message with those bytes
appended to the residual — no framing hypothesis needed, so this covers
buffers a state machine assembled from arbitrary record boundaries. -/
theorem takeMessage?_append {buffered rest x : ByteArray} {msg : Message}
    (h : takeMessage? buffered = .ok (some (msg, rest))) :
    takeMessage? (buffered ++ x) = .ok (some (msg, rest ++ x)) := by
  unfold takeMessage? at h ⊢
  split at h
  · cases h
  · rename_i h4
    split at h
    · cases h
    · rename_i hcomplete
      have hc' : 4 + uint24AtOne buffered ≤ buffered.size := by omega
      have hL : uint24AtOne (buffered ++ x) = uint24AtOne buffered :=
        uint24AtOne_congr (fun i hi => get!_append_left (by omega))
      split at h
      · cases h
      · rename_i message hdec
        simp only [Except.ok.injEq, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        rw [if_neg (by rw [ByteArray.size_append]; omega), hL,
          if_neg (by rw [ByteArray.size_append]; omega),
          extract_append_prefix hc', hdec, extract_append_suffix hc']

/-- **Conservation**: what `takeMessage?` delivers, followed by what it leaves
behind, is exactly the buffer it was given — the handshake-layer mirror of
`Tls.Record.Laws.decodeStep_conservation`. -/
theorem takeMessage?_conservation {buffered rest : ByteArray} {msg : Message}
    (h : takeMessage? buffered = .ok (some (msg, rest))) :
    msg.encoded ++ rest = buffered := by
  unfold takeMessage? at h
  split at h
  · cases h
  · rename_i h4
    split at h
    · cases h
    · rename_i hcomplete
      split at h
      · cases h
      · rename_i message hdec
        simp only [Except.ok.injEq, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        rw [decode_encoded hdec, ByteArray.extract_append_extract,
          Nat.min_eq_left (Nat.zero_le _),
          Nat.max_eq_right (by omega : 4 + uint24AtOne buffered ≤ buffered.size),
          ByteArray.extract_zero_size]

/-- A successful `takeMessage?` consumes the four-byte header plus the body, so
the buffer strictly shrinks and a reassembly loop terminates. -/
theorem takeMessage?_size {buffered rest : ByteArray} {msg : Message}
    (h : takeMessage? buffered = .ok (some (msg, rest))) :
    rest.size < buffered.size := by
  unfold takeMessage? at h
  split at h
  · cases h
  · split at h
    · cases h
    · split at h
      · cases h
      · simp only [Except.ok.injEq, Option.some.injEq, Prod.mk.injEq] at h
        rw [← h.2, ByteArray.size_extract]
        omega


/-! ### `uint16` vectors (cipher suites, groups, versions, algorithms) -/

private theorem size_uint16ListBytes : ∀ l : List UInt16,
    (uint16ListBytes l).size = 2 * l.length := by
  intro l
  induction l with
  | nil => rfl
  | cons v rest ih =>
    show (appendUInt16 ByteArray.empty v ++ uint16ListBytes rest).size = _
    rw [ByteArray.size_append,
      show (appendUInt16 ByteArray.empty v).size = 2 from rfl, ih]
    simp [Nat.mul_succ]
    omega

private theorem parseUInt16ListLoop_end {E : ByteArray} {off : Nat}
    {out : Array UInt16} (h : off = E.size) :
    parseUInt16ListLoop (Reader.mk E off) out = .ok out := by
  unfold parseUInt16ListLoop
  rw [if_pos]
  show (off == E.size) = true
  rw [h]
  exact beq_self_eq_true E.size

private theorem parseUInt16ListLoop_cons {P S : ByteArray} {v : UInt16}
    {out : Array UInt16} :
    parseUInt16ListLoop
        (Reader.mk (P ++ (appendUInt16 ByteArray.empty v ++ S)) P.size) out =
      parseUInt16ListLoop (Reader.mk (P ++ (appendUInt16 ByteArray.empty v ++ S))
        (P ++ appendUInt16 ByteArray.empty v).size) (out.push v) := by
  have hA : (appendUInt16 ByteArray.empty v).size = 2 := rfl
  have hread := readUInt16_at (P := P) (S := S) (v := v)
  have hnotend : ¬((Reader.mk (P ++ (appendUInt16 ByteArray.empty v ++ S))
      P.size).atEnd = true) := by
    show ¬(P.size == (P ++ (appendUInt16 ByteArray.empty v ++ S)).size) = true
    rw [beq_iff_eq, ByteArray.size_append, ByteArray.size_append, hA]
    omega
  rw [show (P ++ appendUInt16 ByteArray.empty v).size = P.size + 2 from by
    rw [ByteArray.size_append, hA]]
  rw [parseUInt16ListLoop.eq_def, if_neg hnotend]
  split
  · rename_i err heq
    rw [hread] at heq
    cases heq
  · rename_i x r' heq
    rw [hread] at heq
    simp only [Except.ok.injEq, Prod.mk.injEq] at heq
    obtain ⟨rfl, rfl⟩ := heq
    rfl

private theorem parseUInt16ListLoop_uint16ListBytes : ∀ (l : List UInt16)
    (P : ByteArray) (out : Array UInt16),
    parseUInt16ListLoop (Reader.mk (P ++ uint16ListBytes l) P.size) out =
      .ok (out.toList ++ l).toArray := by
  intro l
  induction l with
  | nil =>
    intro P out
    rw [show uint16ListBytes ([] : List UInt16) = ByteArray.empty from rfl,
      ByteArray.append_empty, parseUInt16ListLoop_end rfl, List.append_nil,
      Array.toArray_toList]
  | cons v rest ih =>
    intro P out
    rw [show uint16ListBytes (v :: rest) =
      appendUInt16 ByteArray.empty v ++ uint16ListBytes rest from rfl]
    rw [parseUInt16ListLoop_cons]
    rw [show P ++ (appendUInt16 ByteArray.empty v ++ uint16ListBytes rest) =
      (P ++ appendUInt16 ByteArray.empty v) ++ uint16ListBytes rest from
        ByteArray.append_assoc.symm]
    rw [ih (P ++ appendUInt16 ByteArray.empty v) (out.push v)]
    rw [Array.toList_push, List.append_assoc]
    rfl

/-- **`uint16`-vector roundtrip (GREASE tolerance)**: parsing the wire image of
any `uint16` list returns exactly that list, in order. The values are
arbitrary, so unknown cipher suites, unknown/GREASE named groups, versions and
signature schemes are all carried through unchanged — re-encoding the parse
result reproduces the original bytes (`uint16ListBytes l`). -/
theorem parseUInt16List_uint16ListBytes (l : List UInt16) :
    parseUInt16List (uint16ListBytes l) = .ok l.toArray := by
  unfold parseUInt16List
  rw [if_neg (by
    rw [size_uint16ListBytes]
    simp [Nat.mul_mod_right])]
  rw [show ({ bytes := uint16ListBytes l } : Reader) =
    Reader.mk (ByteArray.empty ++ uint16ListBytes l) ByteArray.empty.size from by
    rw [ByteArray.empty_append]
    rfl]
  rw [parseUInt16ListLoop_uint16ListBytes l ByteArray.empty #[]]
  rfl

/-! ### Wire → list converse for `uint16` vectors -/

/-- The wire image of a `uint16` read out of a buffer, followed by the image of
what comes after it, is the whole remaining buffer. -/
private theorem extract_cons_uint16 {W : ByteArray} {off : Nat} {rest : List UInt16}
    (hle : off + 2 ≤ W.size)
    (hext : W.extract (off + 2) W.size = uint16ListBytes rest) :
    W.extract off W.size = uint16ListBytes
      (((W.get! off).toUInt16 <<< 8 ||| (W.get! (off + 1)).toUInt16) :: rest) := by
  show W.extract off W.size =
    appendUInt16 ByteArray.empty _ ++ uint16ListBytes rest
  rw [← hext, ← extract_two (W := W) (off := off) (e := off + 2) rfl hle,
    ByteArray.extract_append_extract, Nat.min_eq_left (by omega),
    Nat.max_eq_right hle]

/-- Everything the `uint16`-vector loop consumed is the wire image of what it
produced. -/
private theorem parseUInt16ListLoop_image : ∀ (n : Nat) (W : ByteArray) (off : Nat)
    (out res : Array UInt16),
    W.size - off ≤ n → off ≤ W.size →
    parseUInt16ListLoop (Reader.mk W off) out = .ok res →
    ∃ rest, res.toList = out.toList ++ rest ∧
      W.extract off W.size = uint16ListBytes rest := by
  intro n
  induction n with
  | zero =>
    intro W off out res hn hle h
    have hend : off = W.size := by omega
    rw [parseUInt16ListLoop_end (E := W) (off := off) hend] at h
    cases h
    exact ⟨[], by simp, by rw [hend]; exact extract_self_empty ..⟩
  | succ n ih =>
    intro W off out res hn hle h
    by_cases hE : off = W.size
    · rw [parseUInt16ListLoop_end (E := W) (off := off) hE] at h
      cases h
      exact ⟨[], by simp, by rw [hE]; exact extract_self_empty ..⟩
    have hlt : off < W.size := by omega
    rw [parseUInt16ListLoop.eq_def, if_neg (show ¬((Reader.mk W off).atEnd = true) from by
      show ¬(off == W.size) = true
      rw [beq_iff_eq]
      exact hE)] at h
    split at h
    · cases h
    · rename_i v r₁ h16
      obtain ⟨hb1, ho1, hle1⟩ := readUInt16_ok h16
      have ho1' : r₁.offset = off + 2 := ho1
      have hle1' : r₁.offset ≤ W.size := hle1
      rw [readUInt16_eval (b := W) (off := off) (by omega)] at h16
      simp only [Except.ok.injEq, Prod.mk.injEq] at h16
      obtain ⟨rfl, rfl⟩ := h16
      obtain ⟨rest, hres, hext⟩ := ih W (off + 2) _ _ (by omega) (by omega) h
      refine ⟨_ :: rest, ?_, extract_cons_uint16 (by omega) hext⟩
      rw [hres, Array.toList_push, List.append_assoc]
      rfl

/-- **Wire → list converse**: every `uint16` vector body the parser accepts is
exactly the wire image of the list it produced, so re-encoding a parsed vector
reproduces the bytes it came from. Together with
`parseUInt16List_uint16ListBytes` this makes the `uint16`-vector codec a
bijection between accepted buffers and the lists they parse to. -/
theorem parseUInt16List_image {E : ByteArray} {vs : Array UInt16}
    (h : parseUInt16List E = .ok vs) : E = uint16ListBytes vs.toList := by
  unfold parseUInt16List at h
  split at h
  · cases h
  · obtain ⟨rest, hres, hext⟩ :=
      parseUInt16ListLoop_image E.size E 0 #[] vs (by omega) (by omega) h
    rw [ByteArray.extract_zero_size] at hext
    rw [hext, hres]
    rfl

/-- **Injectivity on accepted buffers**: two `uint16` vector bodies that parse
to the same list are byte-identical. -/
theorem parseUInt16List_injective {E₁ E₂ : ByteArray} {vs : Array UInt16}
    (h₁ : parseUInt16List E₁ = .ok vs) (h₂ : parseUInt16List E₂ = .ok vs) :
    E₁ = E₂ := by
  rw [parseUInt16List_image h₁, parseUInt16List_image h₂]

/-! ### ClientHello -/

private theorem except_bind_ok {α β : Type} (a : α) (f : α → Except String β) :
    (Except.ok a >>= f) = f a := rfl

private theorem except_pure_bind {α β : Type} (a : α) (f : α → Except String β) :
    ((pure a : Except String α) >>= f) = f a := rfl

private theorem parseOptionalExtension_none {α : Type}
    {extensions : Array Extension} {t : UInt16} {dflt : α}
    {parse : ByteArray → Except String α}
    (h : findExtension? extensions t = none) :
    parseOptionalExtension extensions t dflt parse = .ok dflt := by
  unfold parseOptionalExtension
  rw [h]

private theorem parseOptionalExtension_some {α : Type}
    {extensions : Array Extension} {t : UInt16} {dflt : α}
    {parse : ByteArray → Except String α} {ext : Extension}
    (h : findExtension? extensions t = some ext) :
    parseOptionalExtension extensions t dflt parse = parse ext.data := by
  unfold parseOptionalExtension
  rw [h]

private theorem checkClientPsk_none {extensions : Array Extension}
    (h : findExtension? extensions preSharedKeyExtension = none) :
    checkClientPsk extensions = .ok () := by
  unfold checkClientPsk
  rw [h]

private theorem findExtension?_eq_none {l : List Extension} {t : UInt16}
    (h : ∀ e ∈ l, (e.extensionType == t) = false) :
    findExtension? l.toArray t = none := by
  unfold findExtension?
  rw [List.find?_toArray, List.find?_eq_none]
  intro x hx
  rw [h x hx]
  exact Bool.false_ne_true

/-- **ClientHello preservation (GREASE tolerance)**: a ClientHello whose
extensions this implementation does not interpret parses with its cipher-suite
list and its *whole* extension list returned verbatim — in wire order, nothing
dropped or reordered, whatever the extension types and cipher-suite values are.
That is exactly what a GREASE-sending client requires of a server. -/
theorem parseClientHello_clientHelloBody_opaque {msg : Message}
    {random legacySessionId : ByteArray} {cipherSuites : List UInt16}
    {l : List Extension}
    (hty : msg.msgType = clientHelloType)
    (hbody : msg.body = clientHelloBody random legacySessionId cipherSuites l)
    (hR : random.size = 32) (hsid : legacySessionId.size < 2 ^ 8)
    (hsid32 : legacySessionId.size ≤ 32)
    (hcs : (uint16ListBytes cipherSuites).size < 2 ^ 16)
    (hcsne : cipherSuites ≠ [])
    (hE : (extensionsBytes l).size < 2 ^ 16)
    (hesz : ∀ e ∈ l, e.data.size < 2 ^ 16)
    (hedist : l.Pairwise (fun a b => (a.extensionType == b.extensionType) = false))
    (hopaque : ∀ e ∈ l,
      (e.extensionType == preSharedKeyExtension) = false ∧
      (e.extensionType == supportedVersionsExtension) = false ∧
      (e.extensionType == supportedGroupsExtension) = false ∧
      (e.extensionType == keyShareExtension) = false ∧
      (e.extensionType == signatureAlgorithmsExtension) = false ∧
      (e.extensionType == serverNameExtension) = false ∧
      (e.extensionType == alpnExtension) = false) :
    parseClientHello msg = .ok
      { random := random, legacySessionId := legacySessionId,
        cipherSuites := cipherSuites.toArray,
        supportedVersionIds := #[], supportedGroupIds := #[],
        supportedGroups := #[], keyShareGroupIds := #[], keyShares := #[],
        signatureAlgorithms := #[], serverName := none, alpnProtocols := #[],
        extensions := l.toArray, offersTls13 := false,
        encoded := msg.encoded } := by
  have s2 : (appendUInt16 ByteArray.empty legacyTls12Version).size = 2 := rfl
  have s1 : ∀ b : UInt8, (ByteArray.empty.push b).size = 1 := fun _ => rfl
  have se : ∀ n : Nat, (appendUInt16 ByteArray.empty (UInt16.ofNat n)).size = 2 :=
    fun _ => rfl
  have r1 : Reader.readUInt16 (Reader.mk msg.body 0) =
      .ok (legacyTls12Version, Reader.mk msg.body (0 + 2)) :=
    readUInt16_at' (W := msg.body) (off := 0) (P := ByteArray.empty)
      (by rw [hbody]; unfold clientHelloBody
          simp only [ByteArray.append_assoc, ByteArray.empty_append]; rfl) rfl
  have r2 : Reader.take (Reader.mk msg.body (0 + 2)) 32 =
      .ok (random, Reader.mk msg.body (0 + 2 + 32)) :=
    take_at' (W := msg.body) (off := 0 + 2) (n := 32)
      (P := appendUInt16 ByteArray.empty legacyTls12Version) (X := random)
      (by rw [hbody]; unfold clientHelloBody
          simp only [ByteArray.append_assoc]; rfl) rfl hR
  have r3 : Reader.readVector8 (Reader.mk msg.body (0 + 2 + 32)) =
      .ok (legacySessionId,
        Reader.mk msg.body (0 + 2 + 32 + 1 + legacySessionId.size)) :=
    readVector8_at' (W := msg.body) (off := 0 + 2 + 32)
      (P := appendUInt16 ByteArray.empty legacyTls12Version ++ random)
      (X := legacySessionId)
      (by rw [hbody]; unfold clientHelloBody
          simp only [ByteArray.append_assoc]; rfl)
      (by rw [ByteArray.size_append, s2, hR]) hsid
  have r4 : Reader.readVector16
      (Reader.mk msg.body (0 + 2 + 32 + 1 + legacySessionId.size)) =
      .ok (uint16ListBytes cipherSuites, Reader.mk msg.body
        (0 + 2 + 32 + 1 + legacySessionId.size + 2 +
          (uint16ListBytes cipherSuites).size)) :=
    readVector16_at' (W := msg.body)
      (off := 0 + 2 + 32 + 1 + legacySessionId.size)
      (P := appendUInt16 ByteArray.empty legacyTls12Version ++ random ++
        (ByteArray.empty.push (UInt8.ofNat legacySessionId.size) ++
          legacySessionId))
      (X := uint16ListBytes cipherSuites)
      (by rw [hbody]; unfold clientHelloBody
          simp only [ByteArray.append_assoc]; rfl)
      (by rw [ByteArray.size_append, ByteArray.size_append,
        ByteArray.size_append, s2, hR, s1]; omega) hcs
  have r5 : Reader.readVector8 (Reader.mk msg.body
      (0 + 2 + 32 + 1 + legacySessionId.size + 2 +
        (uint16ListBytes cipherSuites).size)) =
      .ok (ByteArray.empty.push 0, Reader.mk msg.body
        (0 + 2 + 32 + 1 + legacySessionId.size + 2 +
          (uint16ListBytes cipherSuites).size + 1 + 1)) :=
    readVector8_at' (W := msg.body)
      (off := 0 + 2 + 32 + 1 + legacySessionId.size + 2 +
        (uint16ListBytes cipherSuites).size)
      (P := appendUInt16 ByteArray.empty legacyTls12Version ++ random ++
        (ByteArray.empty.push (UInt8.ofNat legacySessionId.size) ++
          legacySessionId) ++
        (appendUInt16 ByteArray.empty
            (UInt16.ofNat (uint16ListBytes cipherSuites).size) ++
          uint16ListBytes cipherSuites))
      (X := ByteArray.empty.push 0)
      (by rw [hbody]; unfold clientHelloBody
          simp only [ByteArray.append_assoc]; rfl)
      (by rw [ByteArray.size_append, ByteArray.size_append,
        ByteArray.size_append, ByteArray.size_append, ByteArray.size_append,
        s2, hR, s1, se]; omega) (by decide)
  have r6 : Reader.readVector16 (Reader.mk msg.body
      (0 + 2 + 32 + 1 + legacySessionId.size + 2 +
        (uint16ListBytes cipherSuites).size + 1 + 1)) =
      .ok (extensionsBytes l, Reader.mk msg.body
        (0 + 2 + 32 + 1 + legacySessionId.size + 2 +
          (uint16ListBytes cipherSuites).size + 1 + 1 + 2 +
          (extensionsBytes l).size)) :=
    readVector16_at' (W := msg.body)
      (off := 0 + 2 + 32 + 1 + legacySessionId.size + 2 +
        (uint16ListBytes cipherSuites).size + 1 + 1)
      (P := appendUInt16 ByteArray.empty legacyTls12Version ++ random ++
        (ByteArray.empty.push (UInt8.ofNat legacySessionId.size) ++
          legacySessionId) ++
        (appendUInt16 ByteArray.empty
            (UInt16.ofNat (uint16ListBytes cipherSuites).size) ++
          uint16ListBytes cipherSuites) ++
        (ByteArray.empty.push 1 ++ ByteArray.empty.push 0))
      (X := extensionsBytes l) (S := ByteArray.empty)
      (by rw [hbody]; unfold clientHelloBody
          simp only [ByteArray.append_assoc, ByteArray.append_empty])
      (by simp only [ByteArray.size_append, s2, hR, s1, se]; omega) hE
  have hbsize : msg.body.size = 0 + 2 + 32 + 1 + legacySessionId.size + 2 +
      (uint16ListBytes cipherSuites).size + 1 + 1 + 2 + (extensionsBytes l).size := by
    rw [hbody]
    unfold clientHelloBody
    simp only [ByteArray.size_append, s2, hR, s1, se]
    omega
  have hAtEnd : ¬((Reader.mk msg.body (0 + 2 + 32 + 1 + legacySessionId.size + 2 +
      (uint16ListBytes cipherSuites).size + 1 + 1)).atEnd = true) := by
    show ¬(0 + 2 + 32 + 1 + legacySessionId.size + 2 +
      (uint16ListBytes cipherSuites).size + 1 + 1 == msg.body.size) = true
    rw [beq_iff_eq, hbsize]
    omega
  have hend : 0 + 2 + 32 + 1 + legacySessionId.size + 2 +
      (uint16ListBytes cipherSuites).size + 1 + 1 + 2 + (extensionsBytes l).size
      = msg.body.size := hbsize.symm
  have hcsEmpty : ¬(cipherSuites.toArray.isEmpty = true) := by
    cases cipherSuites with
    | nil => exact absurd rfl hcsne
    | cons a t => simp
  have hf : ∀ t : UInt16, (∀ e ∈ l, (e.extensionType == t) = false) →
      findExtension? l.toArray t = none := fun _ h => findExtension?_eq_none h
  unfold parseClientHello
  rw [hty, if_pos (show (clientHelloType == clientHelloType) = true from rfl)]
  simp only [r1]
  rw [if_pos (beq_self_eq_true legacyTls12Version)]
  simp only [r2, r3]
  rw [if_pos hsid32]
  simp only [r4, parseUInt16List_uint16ListBytes cipherSuites]
  rw [if_neg hcsEmpty]
  simp only [r5]
  rw [if_pos (show ((ByteArray.empty.push 0).size == 1 &&
    (ByteArray.empty.push 0).get! 0 == 0) = true from rfl)]
  unfold parseClientExtensionBlock
  rw [if_neg hAtEnd]
  simp only [r6, requireEnd_eval (context := "ClientHello") hend,
    parseExtensions_extensionsBytes l hesz hedist,
    checkClientPsk_none (hf preSharedKeyExtension (fun e he => (hopaque e he).1)),
    parseOptionalExtension_none
      (hf supportedVersionsExtension (fun e he => (hopaque e he).2.1)),
    parseOptionalExtension_none
      (hf supportedGroupsExtension (fun e he => (hopaque e he).2.2.1)),
    parseOptionalExtension_none
      (hf keyShareExtension (fun e he => (hopaque e he).2.2.2.1)),
    parseOptionalExtension_none
      (hf signatureAlgorithmsExtension (fun e he => (hopaque e he).2.2.2.2.1)),
    parseOptionalExtension_none
      (hf serverNameExtension (fun e he => (hopaque e he).2.2.2.2.2.1)),
    parseOptionalExtension_none
      (hf alpnExtension (fun e he => (hopaque e he).2.2.2.2.2.2)),
    hf supportedGroupsExtension (fun e he => (hopaque e he).2.2.1),
    Option.isSome_none, Bool.false_and]
  rw [if_neg Bool.false_ne_true,
    show ((#[] : Array UInt16).contains tls13Version) = false from by simp]

/-! ### Client key shares

The key_share block a client offers is a list of `group ‖ uint16 key_exchange`
entries. Groups this implementation does not offer must not be dropped from the
group-id list (a retry has to be able to see them), so the law below is stated
for arbitrary group identifiers, GREASE values included. -/

private theorem size_keyShareEntryBytes (g : UInt16) (k : ByteArray) :
    (keyShareEntryBytes g k).size = 4 + k.size := by
  unfold keyShareEntryBytes
  rw [ByteArray.size_append, ByteArray.size_append,
    show (appendUInt16 ByteArray.empty g).size = 2 from rfl,
    show (appendUInt16 ByteArray.empty (UInt16.ofNat k.size)).size = 2 from rfl]
  omega

private theorem contains_push_false {a : Array UInt16} {g x : UInt16}
    (h : a.contains x = false) (hne : (g == x) = false) :
    (a.push g).contains x = false := by
  have hx : ¬(x = g) := fun hxg => by
    rw [hxg, beq_self_eq_true] at hne
    exact Bool.true_eq_false.mp hne
  simp only [Array.contains, Array.any_push] at *
  simp [h, hx]

/-- An exhausted cursor ends the key_share loop with what it has. -/
private theorem parseKeyShareEntriesLoop_end {E : ByteArray} {off : Nat}
    {seen : Array UInt16} {out : Array ClientKeyShare} (h : off = E.size) :
    parseKeyShareEntriesLoop { bytes := E, offset := off } seen out =
      .ok (seen, out) := by
  unfold parseKeyShareEntriesLoop
  rw [if_pos]
  show (off == E.size) = true
  rw [h]
  exact beq_self_eq_true E.size

/-- One correctly-encoded key_share entry at the cursor advances the loop by
exactly its wire size, recording the group identifier and (when the group is
known) the share itself. -/
private theorem parseKeyShareEntriesLoop_cons {P S : ByteArray} {g : UInt16}
    {k : ByteArray} {seen : Array UInt16} {out : Array ClientKeyShare}
    (hsz : k.size < 2 ^ 16) (hne : k.isEmpty = false)
    (hfresh : seen.contains g = false) :
    parseKeyShareEntriesLoop
        { bytes := P ++ (keyShareEntryBytes g k ++ S), offset := P.size } seen out =
      parseKeyShareEntriesLoop
        { bytes := P ++ (keyShareEntryBytes g k ++ S),
          offset := (P ++ keyShareEntryBytes g k).size } (seen.push g)
        (pushKnownKeyShare g k out) := by
  have hr16 : Reader.readUInt16
      { bytes := P ++ (keyShareEntryBytes g k ++ S), offset := P.size } =
      .ok (g, { bytes := P ++ (keyShareEntryBytes g k ++ S),
                offset := P.size + 2 }) :=
    readUInt16_at' (W := P ++ (keyShareEntryBytes g k ++ S)) (off := P.size)
      (v := g) (P := P)
      (by unfold keyShareEntryBytes; simp only [ByteArray.append_assoc]; rfl) rfl
  have hv16 : Reader.readVector16
      { bytes := P ++ (keyShareEntryBytes g k ++ S), offset := P.size + 2 } =
      .ok (k, { bytes := P ++ (keyShareEntryBytes g k ++ S),
                offset := P.size + 2 + 2 + k.size }) :=
    readVector16_at' (W := P ++ (keyShareEntryBytes g k ++ S))
      (off := P.size + 2) (P := P ++ appendUInt16 ByteArray.empty g) (X := k)
      (by unfold keyShareEntryBytes; simp only [ByteArray.append_assoc]; rfl)
      (by rw [ByteArray.size_append,
        show (appendUInt16 ByteArray.empty g).size = 2 from rfl]) hsz
  have hnotEnd : ¬((Reader.mk (P ++ (keyShareEntryBytes g k ++ S))
      P.size).atEnd = true) := by
    show ¬(P.size == (P ++ (keyShareEntryBytes g k ++ S)).size) = true
    rw [beq_iff_eq, ByteArray.size_append, ByteArray.size_append,
      size_keyShareEntryBytes]
    omega
  rw [show (P ++ keyShareEntryBytes g k).size = P.size + 2 + 2 + k.size from by
    rw [ByteArray.size_append, size_keyShareEntryBytes]; omega]
  rw [parseKeyShareEntriesLoop.eq_def]
  rw [if_neg hnotEnd]
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
      rw [if_neg (by rw [hne]; exact Bool.false_ne_true),
        if_neg (by rw [hfresh]; exact Bool.false_ne_true)]

/-- The key_share loop consumes a whole encoded entry list, keeping every
group identifier in order. -/
private theorem parseKeyShareEntriesLoop_entriesBytes :
    ∀ (l : List (UInt16 × ByteArray)) (P : ByteArray) (seen : Array UInt16)
      (out : Array ClientKeyShare),
    (∀ e ∈ l, e.2.size < 2 ^ 16) → (∀ e ∈ l, e.2.isEmpty = false) →
    (∀ e ∈ l, seen.contains e.1 = false) →
    l.Pairwise (fun a b => (a.1 == b.1) = false) →
    parseKeyShareEntriesLoop
        { bytes := P ++ keyShareEntriesBytes l, offset := P.size } seen out =
      .ok ((seen.toList ++ l.map Prod.fst).toArray, knownKeySharesLoop l out) := by
  intro l
  induction l with
  | nil =>
    intro P seen out _ _ _ _
    rw [show keyShareEntriesBytes ([] : List (UInt16 × ByteArray)) =
        ByteArray.empty from rfl,
      ByteArray.append_empty, parseKeyShareEntriesLoop_end rfl, List.map_nil,
      List.append_nil, Array.toArray_toList]
    rfl
  | cons e rest ih =>
    intro P seen out hsz hne hfresh hpw
    rw [List.pairwise_cons] at hpw
    rw [show keyShareEntriesBytes (e :: rest) =
      keyShareEntryBytes e.1 e.2 ++ keyShareEntriesBytes rest from rfl]
    rw [parseKeyShareEntriesLoop_cons (hsz e (List.mem_cons_self ..))
      (hne e (List.mem_cons_self ..)) (hfresh e (List.mem_cons_self ..))]
    rw [show P ++ (keyShareEntryBytes e.1 e.2 ++ keyShareEntriesBytes rest) =
      (P ++ keyShareEntryBytes e.1 e.2) ++ keyShareEntriesBytes rest from
        ByteArray.append_assoc.symm]
    rw [ih (P ++ keyShareEntryBytes e.1 e.2) (seen.push e.1)
      (pushKnownKeyShare e.1 e.2 out)
      (fun e' he' => hsz e' (List.mem_cons_of_mem e he'))
      (fun e' he' => hne e' (List.mem_cons_of_mem e he'))
      (fun e' he' => contains_push_false
        (hfresh e' (List.mem_cons_of_mem e he')) (hpw.1 e' he'))
      hpw.2]
    rw [Array.toList_push, List.append_assoc]
    rfl

/-- **Client key_share roundtrip (GREASE tolerance)**: parsing the wire image of
any list of key_share entries returns every offered group identifier, in order
and undropped — the identifiers are arbitrary, so unknown and GREASE groups
survive — together with the shares whose groups this implementation knows. -/
theorem parseKeyShareEntries_keyShareEntriesBytes (l : List (UInt16 × ByteArray))
    (hsz : ∀ e ∈ l, e.2.size < 2 ^ 16) (hne : ∀ e ∈ l, e.2.isEmpty = false)
    (hdistinct : l.Pairwise (fun a b => (a.1 == b.1) = false)) :
    parseKeyShareEntries (keyShareEntriesBytes l) =
      .ok ((l.map Prod.fst).toArray, knownKeyShares l) := by
  unfold parseKeyShareEntries
  rw [show ({ bytes := keyShareEntriesBytes l } : Reader) =
    { bytes := ByteArray.empty ++ keyShareEntriesBytes l,
      offset := ByteArray.empty.size } from by
    rw [ByteArray.empty_append]
    rfl]
  rw [parseKeyShareEntriesLoop_entriesBytes l ByteArray.empty #[] #[] hsz hne
    (fun _ _ => by simp) hdistinct]
  rfl

/-! ### Wire → list converse for client key_share lists

A key_share entry has the same wire shape as an extension — a `uint16` tag, a
`uint16` length and that many bytes — so the extension retention lemma
`extract_extensionBytes` carries over unchanged. -/

private theorem extensionBytes_mk (t : UInt16) (d : ByteArray) :
    extensionBytes (Extension.mk t d) = keyShareEntryBytes t d := rfl

/-- The wire image of one key_share entry read out of a buffer, followed by the
image of what comes after it, is the whole remaining buffer. -/
private theorem extract_cons_keyShare {W : ByteArray} {off : Nat}
    {rest : List (UInt16 × ByteArray)}
    (hle : off + 2 + 2 +
      ((W.get! (off + 2)).toUInt16 <<< 8 |||
        (W.get! (off + 2 + 1)).toUInt16).toNat ≤ W.size)
    (hext : W.extract (off + 2 + 2 +
        ((W.get! (off + 2)).toUInt16 <<< 8 |||
          (W.get! (off + 2 + 1)).toUInt16).toNat) W.size =
      keyShareEntriesBytes rest) :
    W.extract off W.size = keyShareEntriesBytes
      (((W.get! off).toUInt16 <<< 8 ||| (W.get! (off + 1)).toUInt16,
        W.extract (off + 2 + 2) (off + 2 + 2 +
          ((W.get! (off + 2)).toUInt16 <<< 8 |||
            (W.get! (off + 2 + 1)).toUInt16).toNat)) :: rest) := by
  have hidx : off + 2 + 1 = off + 3 := by omega
  have hidx2 : off + 2 + 2 = off + 4 := by omega
  rw [hidx, hidx2] at hle hext ⊢
  show W.extract off W.size = keyShareEntryBytes _ _ ++ keyShareEntriesBytes rest
  rw [← hext, ← extensionBytes_mk,
    ← extract_extensionBytes (W := W) (off := off) rfl rfl hle,
    ByteArray.extract_append_extract, Nat.min_eq_left (by omega),
    Nat.max_eq_right (by omega)]

/-- Everything the key_share loop consumed is the wire image of the entry list
it produced. -/
private theorem parseKeyShareEntriesLoop_image : ∀ (n : Nat) (W : ByteArray)
    (off : Nat) (seen ids : Array UInt16) (out shares : Array ClientKeyShare),
    W.size - off ≤ n → off ≤ W.size →
    parseKeyShareEntriesLoop (Reader.mk W off) seen out = .ok (ids, shares) →
    ∃ l : List (UInt16 × ByteArray),
      ids.toList = seen.toList ++ l.map Prod.fst ∧
      shares = knownKeySharesLoop l out ∧
      W.extract off W.size = keyShareEntriesBytes l := by
  intro n
  induction n with
  | zero =>
    intro W off seen ids out shares hn hle h
    have hend : off = W.size := by omega
    rw [parseKeyShareEntriesLoop_end (E := W) (off := off) hend] at h
    simp only [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨[], by simp, rfl, by rw [hend]; exact extract_self_empty ..⟩
  | succ n ih =>
    intro W off seen ids out shares hn hle h
    by_cases hE : off = W.size
    · rw [parseKeyShareEntriesLoop_end (E := W) (off := off) hE] at h
      simp only [Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨[], by simp, rfl, by rw [hE]; exact extract_self_empty ..⟩
    have hlt : off < W.size := by omega
    rw [parseKeyShareEntriesLoop.eq_def,
      if_neg (show ¬((Reader.mk W off).atEnd = true) from by
        show ¬(off == W.size) = true
        rw [beq_iff_eq]
        exact hE)] at h
    split at h
    · cases h
    · rename_i g r₁ h16
      obtain ⟨hb1, ho1, hle1⟩ := readUInt16_ok h16
      have ho1' : r₁.offset = off + 2 := ho1
      have hle1' : r₁.offset ≤ W.size := hle1
      rw [readUInt16_eval (b := W) (off := off) (by omega)] at h16
      simp only [Except.ok.injEq, Prod.mk.injEq] at h16
      obtain ⟨rfl, rfl⟩ := h16
      split at h
      · cases h
      · rename_i k r₂ hv
        obtain ⟨hb2, hlo2, hle2⟩ := readVector16_ok hv
        have hlo2' : off + 2 + 2 ≤ r₂.offset := hlo2
        have hle2' : r₂.offset ≤ W.size := hle2
        unfold Reader.readVector16 at hv
        simp only [readUInt16_eval (b := W) (off := off + 2) (by omega)] at hv
        obtain ⟨hb3, ho3, hle3⟩ := take_ok hv
        have ho3' : r₂.offset = off + 2 + 2 +
            ((W.get! (off + 2)).toUInt16 <<< 8 |||
              (W.get! (off + 2 + 1)).toUInt16).toNat := ho3
        have hLbound : off + 2 + 2 +
            ((W.get! (off + 2)).toUInt16 <<< 8 |||
              (W.get! (off + 2 + 1)).toUInt16).toNat ≤ W.size := by omega
        rw [take_eval (b := W) (off := off + 2 + 2) hLbound] at hv
        simp only [Except.ok.injEq, Prod.mk.injEq] at hv
        obtain ⟨rfl, rfl⟩ := hv
        split at h
        · cases h
        · split at h
          · cases h
          · obtain ⟨l, hids, hshares, hext⟩ := ih W (off + 2 + 2 +
              ((W.get! (off + 2)).toUInt16 <<< 8 |||
                (W.get! (off + 2 + 1)).toUInt16).toNat) _ _ _ _
              (by omega) hLbound h
            refine ⟨_ :: l, ?_, ?_, extract_cons_keyShare hLbound hext⟩
            · rw [hids, Array.toList_push, List.append_assoc]
              rfl
            · exact hshares

/-- **Wire decomposition**: every key_share block the parser accepts is the
wire image of some full entry list whose identifiers are exactly the returned
identifiers and whose known-group entries are exactly the returned shares.

The full list is an existential witness, not parser output: unknown/GREASE key
bytes are deliberately discarded. Consequently this theorem does not support
re-encoding from the parse result or an injectivity corollary. -/
theorem parseKeyShareEntries_image {E : ByteArray} {ids : Array UInt16}
    {shares : Array ClientKeyShare}
    (h : parseKeyShareEntries E = .ok (ids, shares)) :
    ∃ l : List (UInt16 × ByteArray),
      ids = (l.map Prod.fst).toArray ∧ shares = knownKeyShares l ∧
      E = keyShareEntriesBytes l := by
  unfold parseKeyShareEntries at h
  obtain ⟨l, hids, hshares, hext⟩ :=
    parseKeyShareEntriesLoop_image E.size E 0 #[] ids #[] shares (by omega)
      (by omega) h
  rw [ByteArray.extract_zero_size] at hext
  refine ⟨l, ?_, hshares, hext⟩
  have hids' : ids.toList = l.map Prod.fst := by simpa using hids
  rw [← hids', Array.toArray_toList]

-- No injectivity companion: the parse result keeps only the group identifiers
-- and the shares of groups this implementation knows, so two buffers offering
-- the same identifiers with different key bytes for an *unknown* group parse
-- to the same pair. The `l` returned above is what pins the bytes down.


/-! ### ClientHello with the extensions this implementation interprets -/

private theorem readVector8_body {X : ByteArray} (hsz : X.size < 2 ^ 8) :
    Reader.readVector8
        (Reader.mk (ByteArray.empty.push (UInt8.ofNat X.size) ++ X) 0) =
      .ok (X, Reader.mk (ByteArray.empty.push (UInt8.ofNat X.size) ++ X)
        (0 + 1 + X.size)) :=
  readVector8_at' (W := ByteArray.empty.push (UInt8.ofNat X.size) ++ X)
    (P := ByteArray.empty) (X := X) (S := ByteArray.empty)
    (by rw [ByteArray.append_empty, ByteArray.empty_append]) rfl hsz

private theorem readVector16_body' {X : ByteArray} (hsz : X.size < 2 ^ 16) :
    Reader.readVector16
        (Reader.mk (appendUInt16 ByteArray.empty (UInt16.ofNat X.size) ++ X) 0) =
      .ok (X, Reader.mk (appendUInt16 ByteArray.empty (UInt16.ofNat X.size) ++ X)
        (0 + 2 + X.size)) :=
  readVector16_at' (W := appendUInt16 ByteArray.empty (UInt16.ofNat X.size) ++ X)
    (P := ByteArray.empty) (X := X) (S := ByteArray.empty)
    (by rw [ByteArray.append_empty, ByteArray.empty_append]) rfl hsz

private theorem uint16ListBytes_ne_empty {l : List UInt16} (h : l ≠ []) :
    ¬((uint16ListBytes l).isEmpty = true) := by
  cases l with
  | nil => exact absurd rfl h
  | cons a t =>
    simp only [ByteArray.isEmpty, size_uint16ListBytes]
    simp

/-- The client supported_versions extension body parses back to the offered
version identifiers, whatever they are. -/
private theorem parseClientVersions_body {versions : List UInt16}
    (hsz : (uint16ListBytes versions).size < 2 ^ 8) (hne : versions ≠ []) :
    parseClientVersions (clientSupportedVersionsExtension versions).data =
      .ok versions.toArray := by
  show parseClientVersions (ByteArray.empty.push
      (UInt8.ofNat (uint16ListBytes versions).size) ++ uint16ListBytes versions)
    = _
  unfold parseClientVersions
  simp only [readVector8_body hsz,
    requireEnd_eval (b := ByteArray.empty.push
        (UInt8.ofNat (uint16ListBytes versions).size) ++ uint16ListBytes versions)
      (off := 0 + 1 + (uint16ListBytes versions).size)
      (context := "ClientHello supported_versions")
      (by rw [ByteArray.size_append]; rfl)]
  rw [if_neg (uint16ListBytes_ne_empty hne), parseUInt16List_uint16ListBytes]

/-- The client supported_groups extension body parses back to the offered group
identifiers, whatever they are, plus the ones this implementation knows. -/
private theorem parseClientGroups_body {groups : List UInt16}
    (hsz : (uint16ListBytes groups).size < 2 ^ 16) (hne : groups ≠ []) :
    parseClientGroups (clientSupportedGroupsExtension groups).data =
      .ok (groups.toArray, knownGroups groups) := by
  show parseClientGroups (appendUInt16 ByteArray.empty
      (UInt16.ofNat (uint16ListBytes groups).size) ++ uint16ListBytes groups) = _
  unfold parseClientGroups parseSupportedGroups
  simp only [readVector16_body' hsz,
    requireEnd_eval (b := appendUInt16 ByteArray.empty
        (UInt16.ofNat (uint16ListBytes groups).size) ++ uint16ListBytes groups)
      (off := 0 + 2 + (uint16ListBytes groups).size)
      (context := "ClientHello supported_groups")
      (by rw [ByteArray.size_append]; rfl),
    parseUInt16List_uint16ListBytes]
  rw [if_neg (by
    cases groups with
    | nil => exact absurd rfl hne
    | cons a t => simp)]

/-- The client key_share extension body parses back to every offered group
identifier, GREASE included, plus the shares this implementation can use. -/
private theorem parseClientKeyShare_body {shares : List (UInt16 × ByteArray)}
    (hsz : (keyShareEntriesBytes shares).size < 2 ^ 16)
    (hesz : ∀ e ∈ shares, e.2.size < 2 ^ 16)
    (hene : ∀ e ∈ shares, e.2.isEmpty = false)
    (hdistinct : shares.Pairwise (fun a b => (a.1 == b.1) = false)) :
    parseClientKeyShare (clientKeyShareExtension shares).data =
      .ok ((shares.map Prod.fst).toArray, knownKeyShares shares) := by
  show parseClientKeyShare (appendUInt16 ByteArray.empty
      (UInt16.ofNat (keyShareEntriesBytes shares).size) ++
    keyShareEntriesBytes shares) = _
  unfold parseClientKeyShare
  simp only [readVector16_body' hsz,
    requireEnd_eval (b := appendUInt16 ByteArray.empty
        (UInt16.ofNat (keyShareEntriesBytes shares).size) ++
      keyShareEntriesBytes shares)
      (off := 0 + 2 + (keyShareEntriesBytes shares).size)
      (context := "ClientHello key_share")
      (by rw [ByteArray.size_append]; rfl),
    parseKeyShareEntries_keyShareEntriesBytes shares hesz hene hdistinct]

/-- The client signature_algorithms extension body parses back to the offered
identifiers, whatever they are. -/
private theorem parseClientSignatureAlgorithms_body {algorithms : List UInt16}
    (hsz : (uint16ListBytes algorithms).size < 2 ^ 16) (hne : algorithms ≠ []) :
    parseClientSignatureAlgorithms
        (clientSignatureAlgorithmsExtension algorithms).data =
      .ok algorithms.toArray := by
  show parseClientSignatureAlgorithms (appendUInt16 ByteArray.empty
      (UInt16.ofNat (uint16ListBytes algorithms).size) ++
    uint16ListBytes algorithms) = _
  unfold parseClientSignatureAlgorithms
  simp only [readVector16_body' hsz,
    requireEnd_eval (b := appendUInt16 ByteArray.empty
        (UInt16.ofNat (uint16ListBytes algorithms).size) ++
      uint16ListBytes algorithms)
      (off := 0 + 2 + (uint16ListBytes algorithms).size)
      (context := "ClientHello signature_algorithms")
      (by rw [ByteArray.size_append]; rfl)]
  rw [if_neg (uint16ListBytes_ne_empty hne), parseUInt16List_uint16ListBytes]

/-- First-match lookup finds a member as soon as no two members of the list
share an extension type — RFC 8446 forbids duplicate extensions, so a parsed
ClientHello always satisfies this (`parseExtensions` rejects duplicates). -/
private theorem find?_of_mem_of_pairwise : ∀ {l : List Extension} {e : Extension},
    l.Pairwise (fun a b => (a.extensionType == b.extensionType) = false) →
    e ∈ l → l.find? (fun ext => ext.extensionType == e.extensionType) = some e := by
  intro l
  induction l with
  | nil => intro e _ hmem; cases hmem
  | cons a t ih =>
    intro e hdist hmem
    rw [List.pairwise_cons] at hdist
    rcases List.mem_cons.mp hmem with rfl | hmem'
    · exact List.find?_cons_of_pos (beq_self_eq_true _)
    · rw [List.find?_cons_of_neg (by rw [hdist.1 e hmem']; exact Bool.false_ne_true)]
      exact ih hdist.2 hmem'

/-- Lookup by type finds exactly the extension of that type a duplicate-free
list carries, wherever in the list it sits. -/
private theorem findExtension?_of_mem {l : List Extension} {e : Extension}
    (hdist : l.Pairwise (fun a b => (a.extensionType == b.extensionType) = false))
    (hmem : e ∈ l) : findExtension? l.toArray e.extensionType = some e := by
  unfold findExtension?
  rw [List.find?_toArray]
  exact find?_of_mem_of_pairwise hdist hmem



/-- The workhorse behind the ClientHello preservation laws: it takes the
`pre_shared_key` precondition as an abstract hypothesis, so both the
PSK-free (`parseClientHello_clientHelloBody_mem`) and the PSK-offering
(`parseClientHello_clientHelloBody_psk`) statements share this proof. -/
private theorem parseClientHello_clientHelloBody_core {msg : Message}
    {random legacySessionId : ByteArray} {cipherSuites : List UInt16}
    {versions groups algorithms : List UInt16}
    {shares : List (UInt16 × ByteArray)} {extensions : List Extension}
    (hty : msg.msgType = clientHelloType)
    (hbody : msg.body =
      clientHelloBody random legacySessionId cipherSuites extensions)
    (hR : random.size = 32) (hsid : legacySessionId.size < 2 ^ 8)
    (hsid32 : legacySessionId.size ≤ 32)
    (hcs : (uint16ListBytes cipherSuites).size < 2 ^ 16)
    (hcsne : cipherSuites ≠ [])
    (hE : (extensionsBytes extensions).size < 2 ^ 16)
    (hesz : ∀ e ∈ extensions, e.data.size < 2 ^ 16)
    (hedist : extensions.Pairwise
      (fun a b => (a.extensionType == b.extensionType) = false))
    (hSVmem : clientSupportedVersionsExtension versions ∈ extensions)
    (hSGmem : clientSupportedGroupsExtension groups ∈ extensions)
    (hKSmem : clientKeyShareExtension shares ∈ extensions)
    (hSAmem : clientSignatureAlgorithmsExtension algorithms ∈ extensions)
    (hpsk : checkClientPsk extensions.toArray = .ok ())
    (hnone : ∀ e ∈ extensions,
      (e.extensionType == serverNameExtension) = false ∧
      (e.extensionType == alpnExtension) = false)
    (hv8 : (uint16ListBytes versions).size < 2 ^ 8) (hvne : versions ≠ [])
    (hg16 : (uint16ListBytes groups).size < 2 ^ 16) (hgne : groups ≠ [])
    (hk16 : (keyShareEntriesBytes shares).size < 2 ^ 16)
    (hksz : ∀ e ∈ shares, e.2.size < 2 ^ 16)
    (hkne : ∀ e ∈ shares, e.2.isEmpty = false)
    (hkdist : shares.Pairwise (fun a b => (a.1 == b.1) = false))
    (ha16 : (uint16ListBytes algorithms).size < 2 ^ 16) (hane : algorithms ≠ [])
    (horder :
      isOrderedSubset (shares.map Prod.fst).toArray groups.toArray = true) :
    parseClientHello msg = .ok
      { random := random, legacySessionId := legacySessionId,
        cipherSuites := cipherSuites.toArray,
        supportedVersionIds := versions.toArray,
        supportedGroupIds := groups.toArray,
        supportedGroups := knownGroups groups,
        keyShareGroupIds := (shares.map Prod.fst).toArray,
        keyShares := knownKeyShares shares,
        signatureAlgorithms := algorithms.toArray,
        serverName := none, alpnProtocols := #[],
        extensions := extensions.toArray,
        offersTls13 := versions.toArray.contains tls13Version,
        encoded := msg.encoded } := by
  have s2 : (appendUInt16 ByteArray.empty legacyTls12Version).size = 2 := rfl
  have s1 : ∀ b : UInt8, (ByteArray.empty.push b).size = 1 := fun _ => rfl
  have se : ∀ n : Nat, (appendUInt16 ByteArray.empty (UInt16.ofNat n)).size = 2 :=
    fun _ => rfl
  have r1 : Reader.readUInt16 (Reader.mk msg.body 0) =
      .ok (legacyTls12Version, Reader.mk msg.body (0 + 2)) :=
    readUInt16_at' (W := msg.body) (off := 0) (P := ByteArray.empty)
      (by rw [hbody]; unfold clientHelloBody
          simp only [ByteArray.append_assoc, ByteArray.empty_append]; rfl) rfl
  have r2 : Reader.take (Reader.mk msg.body (0 + 2)) 32 =
      .ok (random, Reader.mk msg.body (0 + 2 + 32)) :=
    take_at' (W := msg.body) (off := 0 + 2) (n := 32)
      (P := appendUInt16 ByteArray.empty legacyTls12Version) (X := random)
      (by rw [hbody]; unfold clientHelloBody
          simp only [ByteArray.append_assoc]; rfl) rfl hR
  have r3 : Reader.readVector8 (Reader.mk msg.body (0 + 2 + 32)) =
      .ok (legacySessionId,
        Reader.mk msg.body (0 + 2 + 32 + 1 + legacySessionId.size)) :=
    readVector8_at' (W := msg.body) (off := 0 + 2 + 32)
      (P := appendUInt16 ByteArray.empty legacyTls12Version ++ random)
      (X := legacySessionId)
      (by rw [hbody]; unfold clientHelloBody
          simp only [ByteArray.append_assoc]; rfl)
      (by rw [ByteArray.size_append, s2, hR]) hsid
  have r4 : Reader.readVector16
      (Reader.mk msg.body (0 + 2 + 32 + 1 + legacySessionId.size)) =
      .ok (uint16ListBytes cipherSuites, Reader.mk msg.body
        (0 + 2 + 32 + 1 + legacySessionId.size + 2 +
          (uint16ListBytes cipherSuites).size)) :=
    readVector16_at' (W := msg.body)
      (off := 0 + 2 + 32 + 1 + legacySessionId.size)
      (P := appendUInt16 ByteArray.empty legacyTls12Version ++ random ++
        (ByteArray.empty.push (UInt8.ofNat legacySessionId.size) ++
          legacySessionId))
      (X := uint16ListBytes cipherSuites)
      (by rw [hbody]; unfold clientHelloBody
          simp only [ByteArray.append_assoc]; rfl)
      (by rw [ByteArray.size_append, ByteArray.size_append,
        ByteArray.size_append, s2, hR, s1]; omega) hcs
  have r5 : Reader.readVector8 (Reader.mk msg.body
      (0 + 2 + 32 + 1 + legacySessionId.size + 2 +
        (uint16ListBytes cipherSuites).size)) =
      .ok (ByteArray.empty.push 0, Reader.mk msg.body
        (0 + 2 + 32 + 1 + legacySessionId.size + 2 +
          (uint16ListBytes cipherSuites).size + 1 + 1)) :=
    readVector8_at' (W := msg.body)
      (off := 0 + 2 + 32 + 1 + legacySessionId.size + 2 +
        (uint16ListBytes cipherSuites).size)
      (P := appendUInt16 ByteArray.empty legacyTls12Version ++ random ++
        (ByteArray.empty.push (UInt8.ofNat legacySessionId.size) ++
          legacySessionId) ++
        (appendUInt16 ByteArray.empty
            (UInt16.ofNat (uint16ListBytes cipherSuites).size) ++
          uint16ListBytes cipherSuites))
      (X := ByteArray.empty.push 0)
      (by rw [hbody]; unfold clientHelloBody
          simp only [ByteArray.append_assoc]; rfl)
      (by rw [ByteArray.size_append, ByteArray.size_append,
        ByteArray.size_append, ByteArray.size_append, ByteArray.size_append,
        s2, hR, s1, se]; omega) (by decide)
  have r6 : Reader.readVector16 (Reader.mk msg.body
      (0 + 2 + 32 + 1 + legacySessionId.size + 2 +
        (uint16ListBytes cipherSuites).size + 1 + 1)) =
      .ok (extensionsBytes extensions, Reader.mk msg.body
        (0 + 2 + 32 + 1 + legacySessionId.size + 2 +
          (uint16ListBytes cipherSuites).size + 1 + 1 + 2 +
          (extensionsBytes extensions).size)) :=
    readVector16_at' (W := msg.body)
      (off := 0 + 2 + 32 + 1 + legacySessionId.size + 2 +
        (uint16ListBytes cipherSuites).size + 1 + 1)
      (P := appendUInt16 ByteArray.empty legacyTls12Version ++ random ++
        (ByteArray.empty.push (UInt8.ofNat legacySessionId.size) ++
          legacySessionId) ++
        (appendUInt16 ByteArray.empty
            (UInt16.ofNat (uint16ListBytes cipherSuites).size) ++
          uint16ListBytes cipherSuites) ++
        (ByteArray.empty.push 1 ++ ByteArray.empty.push 0))
      (X := extensionsBytes extensions) (S := ByteArray.empty)
      (by rw [hbody]; unfold clientHelloBody
          simp only [ByteArray.append_assoc, ByteArray.append_empty])
      (by simp only [ByteArray.size_append, s2, hR, s1, se]; omega) hE
  have hbsize : msg.body.size = 0 + 2 + 32 + 1 + legacySessionId.size + 2 +
      (uint16ListBytes cipherSuites).size + 1 + 1 + 2 +
      (extensionsBytes extensions).size := by
    rw [hbody]
    unfold clientHelloBody
    simp only [ByteArray.size_append, s2, hR, s1, se]
    omega
  have hAtEnd : ¬((Reader.mk msg.body (0 + 2 + 32 + 1 + legacySessionId.size + 2 +
      (uint16ListBytes cipherSuites).size + 1 + 1)).atEnd = true) := by
    show ¬(0 + 2 + 32 + 1 + legacySessionId.size + 2 +
      (uint16ListBytes cipherSuites).size + 1 + 1 == msg.body.size) = true
    rw [beq_iff_eq, hbsize]
    omega
  have hend : 0 + 2 + 32 + 1 + legacySessionId.size + 2 +
      (uint16ListBytes cipherSuites).size + 1 + 1 + 2 +
      (extensionsBytes extensions).size = msg.body.size := hbsize.symm
  have hcsEmpty : ¬(cipherSuites.toArray.isEmpty = true) := by
    cases cipherSuites with
    | nil => exact absurd rfl hcsne
    | cons a t => simp
  have hSN : findExtension? extensions.toArray serverNameExtension = none :=
    findExtension?_eq_none (fun e he => (hnone e he).1)
  have hAL : findExtension? extensions.toArray alpnExtension = none :=
    findExtension?_eq_none (fun e he => (hnone e he).2)
  have hSV : findExtension? extensions.toArray supportedVersionsExtension =
      some (clientSupportedVersionsExtension versions) :=
    findExtension?_of_mem hedist hSVmem
  have hSG : findExtension? extensions.toArray supportedGroupsExtension =
      some (clientSupportedGroupsExtension groups) :=
    findExtension?_of_mem hedist hSGmem
  have hKS : findExtension? extensions.toArray keyShareExtension =
      some (clientKeyShareExtension shares) :=
    findExtension?_of_mem hedist hKSmem
  have hSA : findExtension? extensions.toArray signatureAlgorithmsExtension =
      some (clientSignatureAlgorithmsExtension algorithms) :=
    findExtension?_of_mem hedist hSAmem
  unfold parseClientHello
  rw [hty, if_pos (show (clientHelloType == clientHelloType) = true from rfl)]
  simp only [r1]
  rw [if_pos (beq_self_eq_true legacyTls12Version)]
  simp only [r2, r3]
  rw [if_pos hsid32]
  simp only [r4, parseUInt16List_uint16ListBytes cipherSuites]
  rw [if_neg hcsEmpty]
  simp only [r5]
  rw [if_pos (show ((ByteArray.empty.push 0).size == 1 &&
    (ByteArray.empty.push 0).get! 0 == 0) = true from rfl)]
  unfold parseClientExtensionBlock
  rw [if_neg hAtEnd]
  simp only [r6, requireEnd_eval (context := "ClientHello") hend,
    parseExtensions_extensionsBytes extensions hesz hedist,
    hpsk,
    parseOptionalExtension_some hSV, parseClientVersions_body hv8 hvne,
    parseOptionalExtension_some hSG, parseClientGroups_body hg16 hgne,
    parseOptionalExtension_some hKS,
    parseClientKeyShare_body hk16 hksz hkne hkdist,
    parseOptionalExtension_some hSA,
    parseClientSignatureAlgorithms_body ha16 hane,
    parseOptionalExtension_none hSN, parseOptionalExtension_none hAL,
    hSG, Option.isSome_some, Bool.true_and, horder, Bool.not_true]
  rw [if_neg Bool.false_ne_true]

/-- **ClientHello preservation (GREASE tolerance)**: a ClientHello whose
extension list carries the four extensions this implementation interprets
(`supported_versions`, `supported_groups`, `key_share`,
`signature_algorithms`) *anywhere in it*, interleaved in any order with any
number of extensions it does not interpret, parses with *every* offered list
returned verbatim: the cipher suites, the version identifiers, the
supported-group identifiers, the key-share group identifiers and the
signature-scheme identifiers all come back in wire order with nothing dropped,
whatever the values are, and the whole extension list — unknown entries
included — is retained as sent. Only the derived views (`supportedGroups`,
`keyShares`) narrow to what this implementation knows. This is what a
GREASE-sending client requires of a server.

The only ordering-flavoured hypothesis left is `hedist`: no two extensions may
share a type. RFC 8446 forbids duplicate extensions, and `parseExtensions`
rejects them, so every ClientHello this implementation would accept satisfies
it. -/
theorem parseClientHello_clientHelloBody_mem {msg : Message}
    {random legacySessionId : ByteArray} {cipherSuites : List UInt16}
    {versions groups algorithms : List UInt16}
    {shares : List (UInt16 × ByteArray)} {extensions : List Extension}
    (hty : msg.msgType = clientHelloType)
    (hbody : msg.body =
      clientHelloBody random legacySessionId cipherSuites extensions)
    (hR : random.size = 32) (hsid : legacySessionId.size < 2 ^ 8)
    (hsid32 : legacySessionId.size ≤ 32)
    (hcs : (uint16ListBytes cipherSuites).size < 2 ^ 16)
    (hcsne : cipherSuites ≠ [])
    (hE : (extensionsBytes extensions).size < 2 ^ 16)
    (hesz : ∀ e ∈ extensions, e.data.size < 2 ^ 16)
    (hedist : extensions.Pairwise
      (fun a b => (a.extensionType == b.extensionType) = false))
    (hSVmem : clientSupportedVersionsExtension versions ∈ extensions)
    (hSGmem : clientSupportedGroupsExtension groups ∈ extensions)
    (hKSmem : clientKeyShareExtension shares ∈ extensions)
    (hSAmem : clientSignatureAlgorithmsExtension algorithms ∈ extensions)
    (hnone : ∀ e ∈ extensions,
      (e.extensionType == preSharedKeyExtension) = false ∧
      (e.extensionType == serverNameExtension) = false ∧
      (e.extensionType == alpnExtension) = false)
    (hv8 : (uint16ListBytes versions).size < 2 ^ 8) (hvne : versions ≠ [])
    (hg16 : (uint16ListBytes groups).size < 2 ^ 16) (hgne : groups ≠ [])
    (hk16 : (keyShareEntriesBytes shares).size < 2 ^ 16)
    (hksz : ∀ e ∈ shares, e.2.size < 2 ^ 16)
    (hkne : ∀ e ∈ shares, e.2.isEmpty = false)
    (hkdist : shares.Pairwise (fun a b => (a.1 == b.1) = false))
    (ha16 : (uint16ListBytes algorithms).size < 2 ^ 16) (hane : algorithms ≠ [])
    (horder :
      isOrderedSubset (shares.map Prod.fst).toArray groups.toArray = true) :
    parseClientHello msg = .ok
      { random := random, legacySessionId := legacySessionId,
        cipherSuites := cipherSuites.toArray,
        supportedVersionIds := versions.toArray,
        supportedGroupIds := groups.toArray,
        supportedGroups := knownGroups groups,
        keyShareGroupIds := (shares.map Prod.fst).toArray,
        keyShares := knownKeyShares shares,
        signatureAlgorithms := algorithms.toArray,
        serverName := none, alpnProtocols := #[],
        extensions := extensions.toArray,
        offersTls13 := versions.toArray.contains tls13Version,
        encoded := msg.encoded } :=
  parseClientHello_clientHelloBody_core hty hbody hR hsid hsid32 hcs hcsne hE
    hesz hedist hSVmem hSGmem hKSmem hSAmem
    (checkClientPsk_none (findExtension?_eq_none (fun e he => (hnone e he).1)))
    (fun e he => ⟨(hnone e he).2.1, (hnone e he).2.2⟩)
    hv8 hvne hg16 hgne hk16 hksz hkne hkdist ha16 hane horder

/-- `checkClientPsk` accepts a ClientHello that offers `pre_shared_key` as its
final extension and carries a non-empty `psk_key_exchange_modes` vector — the
two conditions RFC 8446 section 4.2.11 attaches to a PSK offer.

Phrased with `List.getLast?`, which is how "the PSK offer comes last" reads when
the extension list is not already in `front ++ [psk]` form; `checkClientPsk_ok`
below is the split-form corollary. -/
private theorem checkClientPsk_ok_getLast {l : List Extension}
    {pskData pskModes : ByteArray}
    (hlast : l.getLast? = some (Extension.mk preSharedKeyExtension pskData))
    (hdist : l.Pairwise (fun a b => (a.extensionType == b.extensionType) = false))
    (hmodes : Extension.mk pskKeyExchangeModesExtension
        (ByteArray.empty.push (UInt8.ofNat pskModes.size) ++ pskModes) ∈ l)
    (hsz : pskModes.size < 2 ^ 8) (hne : pskModes.isEmpty = false) :
    checkClientPsk l.toArray = .ok () := by
  obtain ⟨front, rfl⟩ := List.getLast?_eq_some_iff.mp hlast
  have hpsk : findExtension?
      (front ++ [Extension.mk preSharedKeyExtension pskData]).toArray
      preSharedKeyExtension = some (Extension.mk preSharedKeyExtension pskData) :=
    findExtension?_of_mem (e := Extension.mk preSharedKeyExtension pskData) hdist
      (by simp)
  have hmodes' : findExtension?
      (front ++ [Extension.mk preSharedKeyExtension pskData]).toArray
      pskKeyExchangeModesExtension =
      some (Extension.mk pskKeyExchangeModesExtension
        (ByteArray.empty.push (UInt8.ofNat pskModes.size) ++ pskModes)) :=
    findExtension?_of_mem hdist hmodes
  unfold checkClientPsk
  rw [hpsk, if_pos (by simp), hmodes']
  simp only [readVector8_body hsz,
    requireEnd_eval (b := ByteArray.empty.push (UInt8.ofNat pskModes.size) ++
        pskModes)
      (off := 0 + 1 + pskModes.size)
      (context := "ClientHello psk_key_exchange_modes")
      (by rw [ByteArray.size_append]; rfl)]
  rw [if_neg (by rw [hne]; exact Bool.false_ne_true)]

/-- The split-form corollary of `checkClientPsk_ok_getLast`, which is the shape
`parseClientHello_clientHelloBody_psk` needs. -/
private theorem checkClientPsk_ok {front : List Extension}
    {pskData pskModes : ByteArray}
    (hdist : (front ++ [Extension.mk preSharedKeyExtension pskData]).Pairwise
      (fun a b => (a.extensionType == b.extensionType) = false))
    (hmodes : Extension.mk pskKeyExchangeModesExtension
        (ByteArray.empty.push (UInt8.ofNat pskModes.size) ++ pskModes) ∈
      front ++ [Extension.mk preSharedKeyExtension pskData])
    (hsz : pskModes.size < 2 ^ 8) (hne : pskModes.isEmpty = false) :
    checkClientPsk (front ++ [Extension.mk preSharedKeyExtension pskData]).toArray =
      .ok () :=
  checkClientPsk_ok_getLast (List.getLast?_eq_some_iff.mpr ⟨front, rfl⟩) hdist
    hmodes hsz hne

/-- **ClientHello preservation with a PSK offer**: the same law for a
ClientHello that resumes. RFC 8446 requires `pre_shared_key` to be the last
extension and to travel with a non-empty `psk_key_exchange_modes`; given that
shape the parser accepts the message and still returns every offered list
verbatim. The PSK identities and binders themselves stay opaque (`pskData` is
arbitrary) — this codec does not interpret them, and the extension list retains
them byte for byte. -/
theorem parseClientHello_clientHelloBody_psk {msg : Message}
    {random legacySessionId : ByteArray} {cipherSuites : List UInt16}
    {versions groups algorithms : List UInt16}
    {shares : List (UInt16 × ByteArray)} {front : List Extension}
    {pskData pskModes : ByteArray}
    (hty : msg.msgType = clientHelloType)
    (hbody : msg.body = clientHelloBody random legacySessionId cipherSuites
      (front ++ [Extension.mk preSharedKeyExtension pskData]))
    (hR : random.size = 32) (hsid : legacySessionId.size < 2 ^ 8)
    (hsid32 : legacySessionId.size ≤ 32)
    (hcs : (uint16ListBytes cipherSuites).size < 2 ^ 16)
    (hcsne : cipherSuites ≠ [])
    (hE : (extensionsBytes
      (front ++ [Extension.mk preSharedKeyExtension pskData])).size < 2 ^ 16)
    (hesz : ∀ e ∈ front ++ [Extension.mk preSharedKeyExtension pskData],
      e.data.size < 2 ^ 16)
    (hedist : (front ++ [Extension.mk preSharedKeyExtension pskData]).Pairwise
      (fun a b => (a.extensionType == b.extensionType) = false))
    (hSVmem : clientSupportedVersionsExtension versions ∈
      front ++ [Extension.mk preSharedKeyExtension pskData])
    (hSGmem : clientSupportedGroupsExtension groups ∈
      front ++ [Extension.mk preSharedKeyExtension pskData])
    (hKSmem : clientKeyShareExtension shares ∈
      front ++ [Extension.mk preSharedKeyExtension pskData])
    (hSAmem : clientSignatureAlgorithmsExtension algorithms ∈
      front ++ [Extension.mk preSharedKeyExtension pskData])
    (hmodesMem : Extension.mk pskKeyExchangeModesExtension
        (ByteArray.empty.push (UInt8.ofNat pskModes.size) ++ pskModes) ∈
      front ++ [Extension.mk preSharedKeyExtension pskData])
    (hmodes8 : pskModes.size < 2 ^ 8) (hmodesne : pskModes.isEmpty = false)
    (hnone : ∀ e ∈ front ++ [Extension.mk preSharedKeyExtension pskData],
      (e.extensionType == serverNameExtension) = false ∧
      (e.extensionType == alpnExtension) = false)
    (hv8 : (uint16ListBytes versions).size < 2 ^ 8) (hvne : versions ≠ [])
    (hg16 : (uint16ListBytes groups).size < 2 ^ 16) (hgne : groups ≠ [])
    (hk16 : (keyShareEntriesBytes shares).size < 2 ^ 16)
    (hksz : ∀ e ∈ shares, e.2.size < 2 ^ 16)
    (hkne : ∀ e ∈ shares, e.2.isEmpty = false)
    (hkdist : shares.Pairwise (fun a b => (a.1 == b.1) = false))
    (ha16 : (uint16ListBytes algorithms).size < 2 ^ 16) (hane : algorithms ≠ [])
    (horder :
      isOrderedSubset (shares.map Prod.fst).toArray groups.toArray = true) :
    parseClientHello msg = .ok
      { random := random, legacySessionId := legacySessionId,
        cipherSuites := cipherSuites.toArray,
        supportedVersionIds := versions.toArray,
        supportedGroupIds := groups.toArray,
        supportedGroups := knownGroups groups,
        keyShareGroupIds := (shares.map Prod.fst).toArray,
        keyShares := knownKeyShares shares,
        signatureAlgorithms := algorithms.toArray,
        serverName := none, alpnProtocols := #[],
        extensions := (front ++
          [Extension.mk preSharedKeyExtension pskData]).toArray,
        offersTls13 := versions.toArray.contains tls13Version,
        encoded := msg.encoded } :=
  parseClientHello_clientHelloBody_core hty hbody hR hsid hsid32 hcs hcsne hE
    hesz hedist hSVmem hSGmem hKSmem hSAmem
    (checkClientPsk_ok hedist hmodesMem hmodes8 hmodesne) hnone
    hv8 hvne hg16 hgne hk16 hksz hkne hkdist ha16 hane horder

/-- **ClientHello preservation, ordered special case**: the same law when the
four interpreted extensions come last, after the uninterpreted ones. Kept as
the shape most encoders emit; `parseClientHello_clientHelloBody_mem` allows any
interleaving. -/
theorem parseClientHello_clientHelloBody {msg : Message}
    {random legacySessionId : ByteArray} {cipherSuites : List UInt16}
    {other : List Extension} {versions groups algorithms : List UInt16}
    {shares : List (UInt16 × ByteArray)} {extensions : List Extension}
    (hexts : extensions = other ++
      [clientSupportedVersionsExtension versions,
        clientSupportedGroupsExtension groups,
        clientKeyShareExtension shares,
        clientSignatureAlgorithmsExtension algorithms])
    (hty : msg.msgType = clientHelloType)
    (hbody : msg.body =
      clientHelloBody random legacySessionId cipherSuites extensions)
    (hR : random.size = 32) (hsid : legacySessionId.size < 2 ^ 8)
    (hsid32 : legacySessionId.size ≤ 32)
    (hcs : (uint16ListBytes cipherSuites).size < 2 ^ 16)
    (hcsne : cipherSuites ≠ [])
    (hE : (extensionsBytes extensions).size < 2 ^ 16)
    (hesz : ∀ e ∈ extensions, e.data.size < 2 ^ 16)
    (hedist : extensions.Pairwise
      (fun a b => (a.extensionType == b.extensionType) = false))
    (hother : ∀ e ∈ other,
      (e.extensionType == preSharedKeyExtension) = false ∧
      (e.extensionType == supportedVersionsExtension) = false ∧
      (e.extensionType == supportedGroupsExtension) = false ∧
      (e.extensionType == keyShareExtension) = false ∧
      (e.extensionType == signatureAlgorithmsExtension) = false ∧
      (e.extensionType == serverNameExtension) = false ∧
      (e.extensionType == alpnExtension) = false)
    (hv8 : (uint16ListBytes versions).size < 2 ^ 8) (hvne : versions ≠ [])
    (hg16 : (uint16ListBytes groups).size < 2 ^ 16) (hgne : groups ≠ [])
    (hk16 : (keyShareEntriesBytes shares).size < 2 ^ 16)
    (hksz : ∀ e ∈ shares, e.2.size < 2 ^ 16)
    (hkne : ∀ e ∈ shares, e.2.isEmpty = false)
    (hkdist : shares.Pairwise (fun a b => (a.1 == b.1) = false))
    (ha16 : (uint16ListBytes algorithms).size < 2 ^ 16) (hane : algorithms ≠ [])
    (horder :
      isOrderedSubset (shares.map Prod.fst).toArray groups.toArray = true) :
    parseClientHello msg = .ok
      { random := random, legacySessionId := legacySessionId,
        cipherSuites := cipherSuites.toArray,
        supportedVersionIds := versions.toArray,
        supportedGroupIds := groups.toArray,
        supportedGroups := knownGroups groups,
        keyShareGroupIds := (shares.map Prod.fst).toArray,
        keyShares := knownKeyShares shares,
        signatureAlgorithms := algorithms.toArray,
        serverName := none, alpnProtocols := #[],
        extensions := extensions.toArray,
        offersTls13 := versions.toArray.contains tls13Version,
        encoded := msg.encoded } :=
  parseClientHello_clientHelloBody_mem hty hbody hR hsid hsid32 hcs hcsne hE
    hesz hedist
    (by rw [hexts]; simp) (by rw [hexts]; simp) (by rw [hexts]; simp)
    (by rw [hexts]; simp)
    (by
      intro e he
      rw [hexts] at he
      rcases List.mem_append.mp he with hu | hf
      · exact ⟨(hother e hu).1, (hother e hu).2.2.2.2.2.1,
          (hother e hu).2.2.2.2.2.2⟩
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
        rcases hf with rfl | rfl | rfl | rfl <;> exact ⟨rfl, rfl, rfl⟩)
    hv8 hvne hg16 hgne hk16 hksz hkne hkdist ha16 hane horder


/-! ### ClientHello canonicity

`parseClientHello_clientHelloBody` runs encode-then-parse. These laws run it
the other way: the body a parse accepted is *exactly* the wire image of the
fields it produced, so re-encoding a parsed ClientHello reproduces the bytes it
came from. That is what the HelloRetryRequest flow needs — the second
ClientHello must match the first except for the permitted changes, and the
transcript is hashed over the original bytes (which `decode_encoded` retains).
-/

private theorem getElem_push_empty (b : UInt8)
    (h : 0 < (ByteArray.empty.push b).size) :
    (ByteArray.empty.push b)[0] = b := rfl

/-- A single byte read out of a buffer is that buffer's one-byte slice. -/
private theorem extract_one {W : ByteArray} {off : Nat} (h : off < W.size) :
    W.extract off (off + 1) = ByteArray.empty.push (W.get! off) := by
  apply ByteArray.ext_getElem
  · rw [ByteArray.size_extract, Nat.min_eq_left (by omega)]
    show off + 1 - off = 1
    omega
  · intro i hi hi'
    rw [ByteArray.size_extract, Nat.min_eq_left (by omega)] at hi
    have hi0 : i = 0 := by omega
    subst hi0
    rw [ByteArray.getElem_extract, getElem_push_empty,
      get!_eq_getElem (show off < W.size by omega)]
    simp

/-- A one-byte buffer is the push of its only byte. -/
private theorem eq_push_of_size_one {X : ByteArray} (hsz : X.size = 1) :
    X = ByteArray.empty.push (X.get! 0) := by
  apply ByteArray.ext_getElem
  · rw [hsz]
    rfl
  · intro i hi hi'
    rw [hsz] at hi
    have hi0 : i = 0 := by omega
    subst hi0
    rw [getElem_push_empty, get!_eq_getElem (by omega)]

/-- A successful `take` returns exactly the slice at the cursor. -/
private theorem take_extract {W : ByteArray} {off n : Nat} {X : ByteArray}
    {r' : Reader} (h : Reader.take (Reader.mk W off) n = .ok (X, r')) :
    X = W.extract off (off + n) ∧ r' = Reader.mk W (off + n) ∧
      off + n ≤ W.size := by
  unfold Reader.take at h
  split at h
  · cases h
  · rename_i hle
    have hle' : ¬(off + n > W.size) := hle
    simp only [Except.ok.injEq, Prod.mk.injEq] at h
    exact ⟨h.1.symm, h.2.symm, by omega⟩

/-- A successful `readUInt16` means the two bytes at the cursor are the
big-endian encoding of the value it returned. -/
private theorem readUInt16_extract {W : ByteArray} {off : Nat} {v : UInt16}
    {r' : Reader} (h : Reader.readUInt16 (Reader.mk W off) = .ok (v, r')) :
    W.extract off (off + 2) = appendUInt16 ByteArray.empty v ∧
      r' = Reader.mk W (off + 2) ∧ off + 2 ≤ W.size := by
  obtain ⟨hb, ho, hle⟩ := readUInt16_ok h
  have hle' : off + 2 ≤ W.size := by
    have h1 : r'.offset = off + 2 := ho
    have h2 : r'.offset ≤ W.size := hle
    omega
  rw [readUInt16_eval (b := W) (off := off) hle'] at h
  simp only [Except.ok.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  exact ⟨extract_two rfl hle', rfl, hle'⟩

/-- A successful `readVector8` means the cursor held a one-byte length followed
by exactly the bytes it returned. -/
private theorem readVector8_extract {W : ByteArray} {off : Nat} {X : ByteArray}
    {r' : Reader} (h : Reader.readVector8 (Reader.mk W off) = .ok (X, r')) :
    W.extract off (off + 1 + X.size) =
        ByteArray.empty.push (UInt8.ofNat X.size) ++ X ∧
      r' = Reader.mk W (off + 1 + X.size) ∧ off + 1 + X.size ≤ W.size ∧
      X.size < 2 ^ 8 := by
  unfold Reader.readVector8 at h
  split at h
  · cases h
  · rename_i len r₁ h8
    obtain ⟨hb1, ho1, hle1⟩ := readUInt8_ok h8
    have hlt : off < W.size := by
      have h1 : r₁.offset = off + 1 := ho1
      have h2 : r₁.offset ≤ W.size := hle1
      omega
    rw [readUInt8_eval (b := W) (off := off) hlt] at h8
    simp only [Except.ok.injEq, Prod.mk.injEq] at h8
    obtain ⟨rfl, rfl⟩ := h8
    obtain ⟨hX, hr', hb⟩ := take_extract h
    have hXsize : X.size = (W.get! off).toNat := by
      rw [hX, ByteArray.size_extract]
      omega
    refine ⟨?_, by rw [hXsize]; exact hr', by omega, by
      rw [hXsize]; exact UInt8.toNat_lt _⟩
    rw [hXsize, UInt8.ofNat_toNat, ← extract_one hlt, hX,
      ByteArray.extract_append_extract, Nat.min_eq_left (by omega),
      Nat.max_eq_right (by omega)]

/-- A successful `readVector16` means the cursor held a two-byte length
followed by exactly the bytes it returned. -/
private theorem readVector16_extract {W : ByteArray} {off : Nat} {X : ByteArray}
    {r' : Reader} (h : Reader.readVector16 (Reader.mk W off) = .ok (X, r')) :
    W.extract off (off + 2 + X.size) =
        appendUInt16 ByteArray.empty (UInt16.ofNat X.size) ++ X ∧
      r' = Reader.mk W (off + 2 + X.size) ∧ off + 2 + X.size ≤ W.size ∧
      X.size < 2 ^ 16 := by
  unfold Reader.readVector16 at h
  split at h
  · cases h
  · rename_i len r₁ h16
    obtain ⟨hb1, ho1, hle1⟩ := readUInt16_ok h16
    have hlt : off + 2 ≤ W.size := by
      have h1 : r₁.offset = off + 2 := ho1
      have h2 : r₁.offset ≤ W.size := hle1
      omega
    rw [readUInt16_eval (b := W) (off := off) hlt] at h16
    simp only [Except.ok.injEq, Prod.mk.injEq] at h16
    obtain ⟨rfl, rfl⟩ := h16
    obtain ⟨hX, hr', hb⟩ := take_extract h
    have hXsize : X.size =
        ((W.get! off).toUInt16 <<< 8 ||| (W.get! (off + 1)).toUInt16).toNat := by
      rw [hX, ByteArray.size_extract]
      omega
    refine ⟨?_, by rw [hXsize]; exact hr', by omega, by
      rw [hXsize]; exact UInt16.toNat_lt _⟩
    rw [hXsize, UInt16.ofNat_toNat, ← extract_two (e := off + 2) rfl (by omega),
      hX, ByteArray.extract_append_extract, Nat.min_eq_left (by omega),
      Nat.max_eq_right (by omega)]

/-- `requireEnd` succeeds only at the end of the buffer. -/
private theorem requireEnd_end {W : ByteArray} {off : Nat} {context : String}
    (h : Reader.requireEnd (Reader.mk W off) context = .ok ()) : off = W.size := by
  unfold Reader.requireEnd at h
  split at h
  · rename_i hend
    have hend' : (off == W.size) = true := hend
    exact beq_iff_eq.mp hend'
  · cases h

/-- The two halves of ClientHello canonicity, proved by one walk over the
parser: a ClientHello with no extensions at all cannot have offered TLS 1.3,
and one that carried an extension block re-encodes to the body it was parsed
from. -/
private theorem parseClientHello_spec {msg : Message} {ch : ClientHello}
    (h : parseClientHello msg = .ok ch) :
    (ch.extensions.isEmpty = true → ch.offersTls13 = false) ∧
    (ch.extensions.isEmpty = false →
      msg.body = clientHelloBody ch.random ch.legacySessionId
        ch.cipherSuites.toList ch.extensions.toList) := by
  unfold parseClientHello at h
  repeat' first | split at h | cases h
  rename_i hty _ legacyVersion r1 h1 hlv _ random r2 h2 _ sessionId r3 h3 hsid
    _ csBytes r4 h4 _ cipherSuites h5 hcsne _ compression r5 h6 hcomp
    _ extensions h7 _ hpsk _ versionIds h8 _ groupIds groups h9
    _ ksIds shares h10 horder _ algorithms h11 _ serverName h12
    _ alpn h13
  dsimp only
  refine ⟨fun hempty => ?_, fun hnonempty => ?_⟩
  · have hemp : extensions = #[] := by simpa using hempty
    subst hemp
    rw [parseOptionalExtension_none (t := supportedVersionsExtension)
      (dflt := #[]) (parse := parseClientVersions) rfl] at h8
    cases h8
    simp
  · have hlv' : legacyVersion = legacyTls12Version := by
      simpa using hlv
    subst hlv'
    have hc1 : compression.size = 1 := by
      have h' := (Bool.and_eq_true _ _).mp hcomp
      simpa using h'.1
    have hc0 : compression.get! 0 = 0 := by
      have h' := (Bool.and_eq_true _ _).mp hcomp
      simpa using h'.2
    have hcompeq : compression = ByteArray.empty.push 0 := by
      rw [eq_push_of_size_one hc1, hc0]
    have hcs : csBytes = uint16ListBytes cipherSuites.toList :=
      parseUInt16List_image h5
    obtain ⟨e1, hr1, hb1⟩ := readUInt16_extract h1
    subst hr1
    obtain ⟨e2, hr2, hb2⟩ := take_extract h2
    subst hr2
    obtain ⟨e3, hr3, hb3, hsz3⟩ := readVector8_extract h3
    subst hr3
    obtain ⟨e4, hr4, hb4, hsz4⟩ := readVector16_extract h4
    subst hr4
    obtain ⟨e5, hr5, hb5, hsz5⟩ := readVector8_extract h6
    subst hr5
    rw [hc1] at e5 hb5 h7
    unfold parseClientExtensionBlock at h7
    split at h7
    · cases h7
      simp at hnonempty
    · split at h7
      · cases h7
      · rename_i extBytes r6 h14
        split at h7
        · cases h7
        · rename_i hreq
          obtain ⟨e6, hr6, hb6, hsz6⟩ := readVector16_extract h14
          subst hr6
          have hend : 0 + 2 + 32 + 1 + sessionId.size + 2 + csBytes.size + 1 + 1 +
              2 + extBytes.size = msg.body.size := requireEnd_end hreq
          have hexts : extBytes = extensionsBytes extensions.toList :=
            parseExtensions_image h7
          have a2 : msg.body.extract 0 (0 + 2 + 32) =
              appendUInt16 ByteArray.empty legacyTls12Version ++ random := by
            rw [extract_split (W := msg.body) (i := 0) (j := 0 + 2)
              (by omega) (by omega), e1, e2]
          have a3 : msg.body.extract 0 (0 + 2 + 32 + 1 + sessionId.size) =
              appendUInt16 ByteArray.empty legacyTls12Version ++ random ++
                (ByteArray.empty.push (UInt8.ofNat sessionId.size) ++
                  sessionId) := by
            rw [extract_split (W := msg.body) (i := 0) (j := 0 + 2 + 32)
              (by omega) (by omega), a2, e3]
          have a4 : msg.body.extract 0
              (0 + 2 + 32 + 1 + sessionId.size + 2 + csBytes.size) =
              appendUInt16 ByteArray.empty legacyTls12Version ++ random ++
                (ByteArray.empty.push (UInt8.ofNat sessionId.size) ++
                  sessionId) ++
                (appendUInt16 ByteArray.empty (UInt16.ofNat csBytes.size) ++
                  csBytes) := by
            rw [extract_split (W := msg.body) (i := 0)
              (j := 0 + 2 + 32 + 1 + sessionId.size) (by omega) (by omega),
              a3, e4]
          have a5 : msg.body.extract 0
              (0 + 2 + 32 + 1 + sessionId.size + 2 + csBytes.size + 1 + 1) =
              appendUInt16 ByteArray.empty legacyTls12Version ++ random ++
                (ByteArray.empty.push (UInt8.ofNat sessionId.size) ++
                  sessionId) ++
                (appendUInt16 ByteArray.empty (UInt16.ofNat csBytes.size) ++
                  csBytes) ++
                (ByteArray.empty.push (UInt8.ofNat 1) ++ compression) := by
            rw [extract_split (W := msg.body) (i := 0)
              (j := 0 + 2 + 32 + 1 + sessionId.size + 2 + csBytes.size)
              (by omega) (by omega), a4, e5]
          have a6 : msg.body.extract 0
              (0 + 2 + 32 + 1 + sessionId.size + 2 + csBytes.size + 1 + 1 + 2 +
                extBytes.size) =
              appendUInt16 ByteArray.empty legacyTls12Version ++ random ++
                (ByteArray.empty.push (UInt8.ofNat sessionId.size) ++
                  sessionId) ++
                (appendUInt16 ByteArray.empty (UInt16.ofNat csBytes.size) ++
                  csBytes) ++
                (ByteArray.empty.push (UInt8.ofNat 1) ++ compression) ++
                (appendUInt16 ByteArray.empty (UInt16.ofNat extBytes.size) ++
                  extBytes) := by
            rw [extract_split (W := msg.body) (i := 0)
              (j := 0 + 2 + 32 + 1 + sessionId.size + 2 + csBytes.size + 1 + 1)
              (by omega) (by omega), a5, e6]
          rw [hend, ByteArray.extract_zero_size, hcs, hexts, hcompeq] at a6
          rw [a6]
          unfold clientHelloBody
          rfl

/-- **ClientHello canonicity**: the body a `parseClientHello` accepted is
exactly `clientHelloBody` of the fields it returned — the random, the legacy
session id, the cipher-suite list and the whole extension list, in wire order,
with the null compression method RFC 8446 mandates. Re-encoding a parsed
ClientHello therefore reproduces the bytes it came from, and `decode_encoded`
retains the framed message on top of that.

The hypothesis excludes only the pre-extension ClientHello shape, which carries
no extension block at all and so is two bytes shorter than `clientHelloBody` of
an empty extension list. Every TLS 1.3 ClientHello has extensions:
`parseClientHello_canonical_of_offersTls13` discharges the hypothesis from
`offersTls13`. -/
theorem parseClientHello_canonical {msg : Message} {ch : ClientHello}
    (h : parseClientHello msg = .ok ch) (hexts : ch.extensions.isEmpty = false) :
    msg.body = clientHelloBody ch.random ch.legacySessionId
      ch.cipherSuites.toList ch.extensions.toList :=
  (parseClientHello_spec h).2 hexts

/-- **ClientHello canonicity for TLS 1.3 clients**: a ClientHello that offered
TLS 1.3 carried an extension block (that is where supported_versions lives), so
it re-encodes to exactly the body it was parsed from. -/
theorem parseClientHello_canonical_of_offersTls13 {msg : Message}
    {ch : ClientHello} (h : parseClientHello msg = .ok ch)
    (h13 : ch.offersTls13 = true) :
    msg.body = clientHelloBody ch.random ch.legacySessionId
      ch.cipherSuites.toList ch.extensions.toList := by
  refine (parseClientHello_spec h).2 ?_
  cases hE : ch.extensions.isEmpty with
  | false => rfl
  | true =>
    rw [(parseClientHello_spec h).1 hE] at h13
    exact absurd h13 Bool.false_ne_true

/-- A ClientHello that offered TLS 1.3 carried an extension block: that is where
`supported_versions` lives. This is the side condition every canonicity
consumer needs, discharged from a field the parser returns. -/
theorem parseClientHello_extensions_of_offersTls13 {msg : Message}
    {ch : ClientHello} (h : parseClientHello msg = .ok ch)
    (h13 : ch.offersTls13 = true) : ch.extensions.isEmpty = false := by
  cases hE : ch.extensions.isEmpty with
  | false => rfl
  | true =>
    rw [(parseClientHello_spec h).1 hE] at h13
    exact absurd h13 Bool.false_ne_true

/-- **Retry comparison**: two ClientHellos whose parses agree on the random, the
legacy session id, the cipher suites and the whole extension list have
byte-identical bodies. This is the check RFC 8446 section 4.1.2 demands of a
second ClientHello after a HelloRetryRequest: comparing the *parsed* fields is
as strong as comparing the bytes. -/
theorem parseClientHello_body_injective {msg₁ msg₂ : Message}
    {ch₁ ch₂ : ClientHello} (h₁ : parseClientHello msg₁ = .ok ch₁)
    (h₂ : parseClientHello msg₂ = .ok ch₂)
    (hexts : ch₁.extensions.isEmpty = false)
    (hrandom : ch₁.random = ch₂.random)
    (hsid : ch₁.legacySessionId = ch₂.legacySessionId)
    (hcs : ch₁.cipherSuites = ch₂.cipherSuites)
    (hext : ch₁.extensions = ch₂.extensions) : msg₁.body = msg₂.body := by
  rw [parseClientHello_canonical h₁ hexts,
    parseClientHello_canonical h₂ (by rw [← hext]; exact hexts),
    hrandom, hsid, hcs, hext]

/-! ### ServerHello and HelloRetryRequest body inversion

The framing laws recover the `Message`; these laws take its body apart. Every
field an encoder wrote comes back unchanged, and the two extensions a server
sends — `supported_versions` selecting TLS 1.3, then `key_share` — are
recovered in order with their exact wire data. -/

/-- Named-group codes roundtrip: a group encodes to a code that parses back to
the same group. -/
theorem NamedGroup.ofUInt16?_toUInt16 (g : NamedGroup) :
    NamedGroup.ofUInt16? g.toUInt16 = some g := by
  cases g <;> rfl

/-- A buffer that is exactly one `uint16` reads back as that value. -/
private theorem readUInt16_solo (v : UInt16) :
    Reader.readUInt16 (Reader.mk (appendUInt16 ByteArray.empty v) 0) =
      .ok (v, Reader.mk (appendUInt16 ByteArray.empty v) (0 + 2)) :=
  readUInt16_at' (W := appendUInt16 ByteArray.empty v) (P := ByteArray.empty)
    (S := ByteArray.empty)
    (by rw [ByteArray.append_empty, ByteArray.empty_append]) rfl

/-- The HelloRetryRequest key_share body (a bare group code) parses back to
that group. -/
private theorem parseHrrKeyShare_eq (g : NamedGroup) :
    parseHrrKeyShare (appendUInt16 ByteArray.empty g.toUInt16) = .ok g := by
  unfold parseHrrKeyShare
  simp only [readUInt16_solo,
    requireEnd_eval (b := appendUInt16 ByteArray.empty g.toUInt16)
      (off := 0 + 2) (context := "HelloRetryRequest key_share") rfl,
    NamedGroup.ofUInt16?_toUInt16]

/-- The ServerHello key_share body (`group ‖ uint16 key`) parses back to the
group and key it was built from, provided the key has the size the parser
requires for that group. -/
private theorem parseServerKeyShare_eq {g : NamedGroup} {k : ByteArray}
    (hsz : k.size < 2 ^ 16) (hcheck : checkKeyShareSize g k = .ok ()) :
    parseServerKeyShare (appendUInt16 ByteArray.empty g.toUInt16 ++
        (appendUInt16 ByteArray.empty (UInt16.ofNat k.size) ++ k)) = .ok (g, k) := by
  unfold parseServerKeyShare
  simp only [readUInt16_at' (W := appendUInt16 ByteArray.empty g.toUInt16 ++
        (appendUInt16 ByteArray.empty (UInt16.ofNat k.size) ++ k))
      (off := 0) (v := g.toUInt16) (P := ByteArray.empty)
      (S := appendUInt16 ByteArray.empty (UInt16.ofNat k.size) ++ k)
      (by rw [ByteArray.empty_append]) rfl,
    NamedGroup.ofUInt16?_toUInt16,
    readVector16_at' (W := appendUInt16 ByteArray.empty g.toUInt16 ++
        (appendUInt16 ByteArray.empty (UInt16.ofNat k.size) ++ k))
      (off := 0 + 2) (P := appendUInt16 ByteArray.empty g.toUInt16)
      (X := k) (S := ByteArray.empty) (by rw [ByteArray.append_empty]) rfl hsz,
    requireEnd_eval (b := appendUInt16 ByteArray.empty g.toUInt16 ++
        (appendUInt16 ByteArray.empty (UInt16.ofNat k.size) ++ k))
      (off := 0 + 2 + 2 + k.size) (context := "ServerHello key_share")
      (by rw [ByteArray.size_append, ByteArray.size_append,
        show (appendUInt16 ByteArray.empty g.toUInt16).size = 2 from rfl,
        show (appendUInt16 ByteArray.empty (UInt16.ofNat k.size)).size = 2
          from rfl]; omega),
    hcheck]


/-- **Parse inverts encode for HelloRetryRequest**: the echoed session id,
cipher suite and selected group come back, together with the two extensions
the encoder wrote, in order. -/
theorem encodeHelloRetryRequest_parse {legacySessionIdEcho : ByteArray}
    {group : NamedGroup} {cipherSuite : UInt16} {msg : Message}
    (h : encodeHelloRetryRequest legacySessionIdEcho group cipherSuite = .ok msg) :
    parseHelloRetryRequest msg = .ok
      { legacySessionIdEcho := legacySessionIdEcho, cipherSuite := cipherSuite,
        selectedGroup := group,
        extensions :=
          #[{ extensionType := supportedVersionsExtension,
              data := appendUInt16 ByteArray.empty tls13Version },
            { extensionType := keyShareExtension,
              data := appendUInt16 ByteArray.empty group.toUInt16 }],
        encoded := msg.encoded } := by
  unfold encodeHelloRetryRequest at h
  obtain ⟨hc, h⟩ | ⟨hc, h⟩ := ite_ok_cases h
  · obtain ⟨_, hu, _⟩ := bind_ok_ex h
    cases hu
  obtain ⟨_, _, h⟩ := bind_ok_ex h
  obtain ⟨SV, hSV, h⟩ := bind_ok_ex h
  obtain ⟨KS, hKS, h⟩ := bind_ok_ex h
  obtain ⟨SIDV, hSIDV, h⟩ := bind_ok_ex h
  obtain ⟨EXTV, hEXTV, h⟩ := bind_ok_ex h
  obtain ⟨hSVsz, hSVeq⟩ := encodeExtension_eq hSV
  obtain ⟨hKSsz, hKSeq⟩ := encodeExtension_eq hKS
  obtain ⟨hSIDsz, hSIDeq⟩ := encodeVector8_ok hSIDV
  obtain ⟨hEXTsz, hEXTeq⟩ := encodeVector16_ok hEXTV
  obtain ⟨hlt, hmsg⟩ := frame_spec h
  have hty : msg.msgType = serverHelloType := by rw [hmsg]
  have hexts : extensionsBytes
      [{ extensionType := supportedVersionsExtension,
         data := appendUInt16 ByteArray.empty tls13Version },
       { extensionType := keyShareExtension,
         data := appendUInt16 ByteArray.empty group.toUInt16 }] = SV ++ KS := by
    show extensionBytes _ ++ (extensionBytes _ ++ extensionsBytes []) = _
    rw [← hSVeq, ← hKSeq,
      show extensionsBytes ([] : List Extension) = ByteArray.empty from rfl,
      ByteArray.append_empty]
  have hbody : msg.body =
      appendUInt16 ByteArray.empty legacyTls12Version ++ helloRetryRequestRandom ++
          (ByteArray.empty.push (UInt8.ofNat legacySessionIdEcho.size) ++
            legacySessionIdEcho) ++
          appendUInt16 ByteArray.empty cipherSuite ++ ByteArray.empty.push 0 ++
        (appendUInt16 ByteArray.empty (UInt16.ofNat (SV ++ KS).size) ++
          (SV ++ KS)) := by
    rw [hmsg]
    show _ ++ _ ++ SIDV ++ _ ++ _ ++ EXTV = _
    rw [hSIDeq, hEXTeq]
  have s2 : (appendUInt16 ByteArray.empty legacyTls12Version).size = 2 := rfl
  have sR : helloRetryRequestRandom.size = 32 := rfl
  have s1 : (ByteArray.empty.push (UInt8.ofNat legacySessionIdEcho.size)).size = 1 :=
    rfl
  have sc : (appendUInt16 ByteArray.empty cipherSuite).size = 2 := rfl
  have sz : (ByteArray.empty.push (0 : UInt8)).size = 1 := rfl
  have se : ∀ n : Nat, (appendUInt16 ByteArray.empty (UInt16.ofNat n)).size = 2 :=
    fun _ => rfl
  have r1 : Reader.readUInt16 (Reader.mk msg.body 0) =
      .ok (legacyTls12Version, Reader.mk msg.body (0 + 2)) :=
    readUInt16_at' (W := msg.body) (off := 0) (P := ByteArray.empty)
      (by rw [hbody]; simp only [ByteArray.append_assoc, ByteArray.empty_append]; rfl)
      rfl
  have r2 : Reader.take (Reader.mk msg.body (0 + 2)) 32 =
      .ok (helloRetryRequestRandom, Reader.mk msg.body (0 + 2 + 32)) :=
    take_at' (W := msg.body) (off := 0 + 2) (n := 32)
      (P := appendUInt16 ByteArray.empty legacyTls12Version)
      (X := helloRetryRequestRandom)
      (by rw [hbody]; simp only [ByteArray.append_assoc]; rfl) rfl sR
  have r3 : Reader.readVector8 (Reader.mk msg.body (0 + 2 + 32)) =
      .ok (legacySessionIdEcho,
        Reader.mk msg.body (0 + 2 + 32 + 1 + legacySessionIdEcho.size)) :=
    readVector8_at' (W := msg.body) (off := 0 + 2 + 32)
      (P := appendUInt16 ByteArray.empty legacyTls12Version ++
        helloRetryRequestRandom)
      (X := legacySessionIdEcho)
      (by rw [hbody]; simp only [ByteArray.append_assoc]; rfl)
      (by rw [ByteArray.size_append, s2, sR]) hSIDsz
  have r4 : Reader.readUInt16
      (Reader.mk msg.body (0 + 2 + 32 + 1 + legacySessionIdEcho.size)) =
      .ok (cipherSuite,
        Reader.mk msg.body (0 + 2 + 32 + 1 + legacySessionIdEcho.size + 2)) :=
    readUInt16_at' (W := msg.body)
      (off := 0 + 2 + 32 + 1 + legacySessionIdEcho.size)
      (P := appendUInt16 ByteArray.empty legacyTls12Version ++
        helloRetryRequestRandom ++
        (ByteArray.empty.push (UInt8.ofNat legacySessionIdEcho.size) ++
          legacySessionIdEcho))
      (by rw [hbody]; simp only [ByteArray.append_assoc]; rfl)
      (by rw [ByteArray.size_append, ByteArray.size_append,
        ByteArray.size_append, s2, sR, s1]; omega)
  have r5 : Reader.readUInt8
      (Reader.mk msg.body (0 + 2 + 32 + 1 + legacySessionIdEcho.size + 2)) =
      .ok (0,
        Reader.mk msg.body (0 + 2 + 32 + 1 + legacySessionIdEcho.size + 2 + 1)) :=
    readUInt8_at' (W := msg.body)
      (off := 0 + 2 + 32 + 1 + legacySessionIdEcho.size + 2)
      (P := appendUInt16 ByteArray.empty legacyTls12Version ++
        helloRetryRequestRandom ++
        (ByteArray.empty.push (UInt8.ofNat legacySessionIdEcho.size) ++
          legacySessionIdEcho) ++ appendUInt16 ByteArray.empty cipherSuite)
      (by rw [hbody]; simp only [ByteArray.append_assoc]; rfl)
      (by rw [ByteArray.size_append, ByteArray.size_append,
        ByteArray.size_append, ByteArray.size_append, s2, sR, s1, sc]; omega)
  have r6 : Reader.readVector16
      (Reader.mk msg.body (0 + 2 + 32 + 1 + legacySessionIdEcho.size + 2 + 1)) =
      .ok (SV ++ KS, Reader.mk msg.body
        (0 + 2 + 32 + 1 + legacySessionIdEcho.size + 2 + 1 + 2 +
          (SV ++ KS).size)) :=
    readVector16_at' (W := msg.body)
      (off := 0 + 2 + 32 + 1 + legacySessionIdEcho.size + 2 + 1)
      (P := appendUInt16 ByteArray.empty legacyTls12Version ++
        helloRetryRequestRandom ++
        (ByteArray.empty.push (UInt8.ofNat legacySessionIdEcho.size) ++
          legacySessionIdEcho) ++ appendUInt16 ByteArray.empty cipherSuite ++
        ByteArray.empty.push 0)
      (X := SV ++ KS) (S := ByteArray.empty)
      (by rw [hbody]; simp only [ByteArray.append_assoc, ByteArray.append_empty])
      (by rw [ByteArray.size_append, ByteArray.size_append,
        ByteArray.size_append, ByteArray.size_append, ByteArray.size_append,
        s2, sR, s1, sc, sz]; omega) hEXTsz
  have hend : 0 + 2 + 32 + 1 + legacySessionIdEcho.size + 2 + 1 + 2 +
      (SV ++ KS).size = msg.body.size := by
    rw [hbody]
    simp only [ByteArray.size_append, s2, sR, s1, sc, sz, se]
    omega
  have hesz : ∀ e ∈ [Extension.mk supportedVersionsExtension
        (appendUInt16 ByteArray.empty tls13Version),
      Extension.mk keyShareExtension (appendUInt16 ByteArray.empty group.toUInt16)],
      e.data.size < 2 ^ 16 := by
    intro e he
    cases he with
    | head => exact (show (2 : Nat) < 2 ^ 16 by decide)
    | tail _ he => cases he with
      | head => exact (show (2 : Nat) < 2 ^ 16 by decide)
      | tail _ he => cases he
  have hedist : List.Pairwise
      (fun a b => (a.extensionType == b.extensionType) = false)
      [Extension.mk supportedVersionsExtension
          (appendUInt16 ByteArray.empty tls13Version),
        Extension.mk keyShareExtension
          (appendUInt16 ByteArray.empty group.toUInt16)] := by
    refine List.Pairwise.cons ?_ (List.pairwise_singleton ..)
    intro b hb
    cases hb with
    | head => rfl
    | tail _ hb => cases hb
  unfold parseHelloRetryRequest
  rw [hty, if_pos (show (serverHelloType == serverHelloType) = true from rfl)]
  simp only [r1]
  rw [if_pos (beq_self_eq_true legacyTls12Version)]
  simp only [r2]
  rw [if_pos (beq_self helloRetryRequestRandom)]
  simp only [r3]
  rw [if_neg hc]
  simp only [r4, r5]
  rw [if_pos (show ((0 : UInt8) == 0) = true from rfl)]
  simp only [r6, requireEnd_eval (context := "HelloRetryRequest") hend]
  rw [← hexts]
  simp only [parseExtensions_extensionsBytes _ hesz hedist,
    show requireExtension
      [Extension.mk supportedVersionsExtension
          (appendUInt16 ByteArray.empty tls13Version),
        Extension.mk keyShareExtension
          (appendUInt16 ByteArray.empty group.toUInt16)].toArray
      supportedVersionsExtension "supported_versions" =
      .ok (Extension.mk supportedVersionsExtension
        (appendUInt16 ByteArray.empty tls13Version)) from rfl]
  rw [if_pos (beq_self (appendUInt16 ByteArray.empty tls13Version))]
  simp only [show requireExtension
      [Extension.mk supportedVersionsExtension
          (appendUInt16 ByteArray.empty tls13Version),
        Extension.mk keyShareExtension
          (appendUInt16 ByteArray.empty group.toUInt16)].toArray
      keyShareExtension "key_share" =
      .ok (Extension.mk keyShareExtension
        (appendUInt16 ByteArray.empty group.toUInt16)) from rfl,
    parseHrrKeyShare_eq]


/-- **Parse inverts encode for ServerHello**: the random, echoed session id,
cipher suite, selected group and key share all come back, together with the two
extensions the encoder wrote, in order. The random must not be the
HelloRetryRequest sentinel (`encodeHelloRetryRequest_parseServerHello` covers
that case) and the key share must have the size the parser requires for the
selected group. -/
theorem encodeServerHello_parse {random legacySessionIdEcho : ByteArray}
    {group : NamedGroup} {keyExchange : ByteArray} {cipherSuite : UInt16}
    {msg : Message}
    (h : encodeServerHello random legacySessionIdEcho group keyExchange
      cipherSuite = .ok msg)
    (hrand : (random == helloRetryRequestRandom) = false)
    (hkey : checkKeyShareSize group keyExchange = .ok ()) :
    parseServerHello msg = .ok
      { random := random, legacySessionIdEcho := legacySessionIdEcho,
        cipherSuite := cipherSuite, selectedGroup := group,
        keyExchange := keyExchange,
        extensions :=
          #[{ extensionType := supportedVersionsExtension,
              data := appendUInt16 ByteArray.empty tls13Version },
            { extensionType := keyShareExtension,
              data := appendUInt16 ByteArray.empty group.toUInt16 ++
                (appendUInt16 ByteArray.empty (UInt16.ofNat keyExchange.size) ++
                  keyExchange) }],
        encoded := msg.encoded } := by
  unfold encodeServerHello at h
  obtain ⟨hc32, h⟩ | ⟨hc32, h⟩ := ite_ok_cases h
  case inr => obtain ⟨_, hu, _⟩ := bind_ok_ex h
              cases hu
  obtain ⟨hc, h⟩ | ⟨hc, h⟩ := ite_ok_cases h
  · obtain ⟨_, hu, _⟩ := bind_ok_ex h
    cases hu
  obtain ⟨_, _, h⟩ := bind_ok_ex h
  obtain ⟨SV, hSV, h⟩ := bind_ok_ex h
  obtain ⟨KX, hKX, h⟩ := bind_ok_ex h
  obtain ⟨hKXsz, rfl⟩ := encodeVector16_ok hKX
  obtain ⟨KS, hKS, h⟩ := bind_ok_ex h
  obtain ⟨SIDV, hSIDV, h⟩ := bind_ok_ex h
  obtain ⟨EXTV, hEXTV, h⟩ := bind_ok_ex h
  obtain ⟨hSVsz, hSVeq⟩ := encodeExtension_eq hSV
  obtain ⟨hKSsz, hKSeq⟩ := encodeExtension_eq hKS
  obtain ⟨hSIDsz, hSIDeq⟩ := encodeVector8_ok hSIDV
  obtain ⟨hEXTsz, hEXTeq⟩ := encodeVector16_ok hEXTV
  obtain ⟨hlt, hmsg⟩ := frame_spec h
  have hR : random.size = 32 := by simpa using hc32
  have hty : msg.msgType = serverHelloType := by rw [hmsg]
  have hexts : extensionsBytes
      [{ extensionType := supportedVersionsExtension,
         data := appendUInt16 ByteArray.empty tls13Version },
       { extensionType := keyShareExtension,
         data := appendUInt16 ByteArray.empty group.toUInt16 ++
           (appendUInt16 ByteArray.empty (UInt16.ofNat keyExchange.size) ++
             keyExchange) }] = SV ++ KS := by
    show extensionBytes _ ++ (extensionBytes _ ++ extensionsBytes []) = _
    rw [← hSVeq, ← hKSeq,
      show extensionsBytes ([] : List Extension) = ByteArray.empty from rfl,
      ByteArray.append_empty]
  have hbody : msg.body =
      appendUInt16 ByteArray.empty legacyTls12Version ++ random ++
          (ByteArray.empty.push (UInt8.ofNat legacySessionIdEcho.size) ++
            legacySessionIdEcho) ++
          appendUInt16 ByteArray.empty cipherSuite ++ ByteArray.empty.push 0 ++
        (appendUInt16 ByteArray.empty (UInt16.ofNat (SV ++ KS).size) ++
          (SV ++ KS)) := by
    rw [hmsg]
    show _ ++ _ ++ SIDV ++ _ ++ _ ++ EXTV = _
    rw [hSIDeq, hEXTeq]
  have s2 : (appendUInt16 ByteArray.empty legacyTls12Version).size = 2 := rfl
  have s1 : (ByteArray.empty.push (UInt8.ofNat legacySessionIdEcho.size)).size = 1 :=
    rfl
  have sc : (appendUInt16 ByteArray.empty cipherSuite).size = 2 := rfl
  have sz : (ByteArray.empty.push (0 : UInt8)).size = 1 := rfl
  have se : ∀ n : Nat, (appendUInt16 ByteArray.empty (UInt16.ofNat n)).size = 2 :=
    fun _ => rfl
  have r1 : Reader.readUInt16 (Reader.mk msg.body 0) =
      .ok (legacyTls12Version, Reader.mk msg.body (0 + 2)) :=
    readUInt16_at' (W := msg.body) (off := 0) (P := ByteArray.empty)
      (by rw [hbody]; simp only [ByteArray.append_assoc, ByteArray.empty_append]; rfl)
      rfl
  have r2 : Reader.take (Reader.mk msg.body (0 + 2)) 32 =
      .ok (random, Reader.mk msg.body (0 + 2 + 32)) :=
    take_at' (W := msg.body) (off := 0 + 2) (n := 32)
      (P := appendUInt16 ByteArray.empty legacyTls12Version) (X := random)
      (by rw [hbody]; simp only [ByteArray.append_assoc]; rfl) rfl hR
  have r3 : Reader.readVector8 (Reader.mk msg.body (0 + 2 + 32)) =
      .ok (legacySessionIdEcho,
        Reader.mk msg.body (0 + 2 + 32 + 1 + legacySessionIdEcho.size)) :=
    readVector8_at' (W := msg.body) (off := 0 + 2 + 32)
      (P := appendUInt16 ByteArray.empty legacyTls12Version ++ random)
      (X := legacySessionIdEcho)
      (by rw [hbody]; simp only [ByteArray.append_assoc]; rfl)
      (by rw [ByteArray.size_append, s2, hR]) hSIDsz
  have r4 : Reader.readUInt16
      (Reader.mk msg.body (0 + 2 + 32 + 1 + legacySessionIdEcho.size)) =
      .ok (cipherSuite,
        Reader.mk msg.body (0 + 2 + 32 + 1 + legacySessionIdEcho.size + 2)) :=
    readUInt16_at' (W := msg.body)
      (off := 0 + 2 + 32 + 1 + legacySessionIdEcho.size)
      (P := appendUInt16 ByteArray.empty legacyTls12Version ++ random ++
        (ByteArray.empty.push (UInt8.ofNat legacySessionIdEcho.size) ++
          legacySessionIdEcho))
      (by rw [hbody]; simp only [ByteArray.append_assoc]; rfl)
      (by rw [ByteArray.size_append, ByteArray.size_append,
        ByteArray.size_append, s2, hR, s1]; omega)
  have r5 : Reader.readUInt8
      (Reader.mk msg.body (0 + 2 + 32 + 1 + legacySessionIdEcho.size + 2)) =
      .ok (0,
        Reader.mk msg.body (0 + 2 + 32 + 1 + legacySessionIdEcho.size + 2 + 1)) :=
    readUInt8_at' (W := msg.body)
      (off := 0 + 2 + 32 + 1 + legacySessionIdEcho.size + 2)
      (P := appendUInt16 ByteArray.empty legacyTls12Version ++ random ++
        (ByteArray.empty.push (UInt8.ofNat legacySessionIdEcho.size) ++
          legacySessionIdEcho) ++ appendUInt16 ByteArray.empty cipherSuite)
      (by rw [hbody]; simp only [ByteArray.append_assoc]; rfl)
      (by rw [ByteArray.size_append, ByteArray.size_append,
        ByteArray.size_append, ByteArray.size_append, s2, hR, s1, sc]; omega)
  have r6 : Reader.readVector16
      (Reader.mk msg.body (0 + 2 + 32 + 1 + legacySessionIdEcho.size + 2 + 1)) =
      .ok (SV ++ KS, Reader.mk msg.body
        (0 + 2 + 32 + 1 + legacySessionIdEcho.size + 2 + 1 + 2 +
          (SV ++ KS).size)) :=
    readVector16_at' (W := msg.body)
      (off := 0 + 2 + 32 + 1 + legacySessionIdEcho.size + 2 + 1)
      (P := appendUInt16 ByteArray.empty legacyTls12Version ++ random ++
        (ByteArray.empty.push (UInt8.ofNat legacySessionIdEcho.size) ++
          legacySessionIdEcho) ++ appendUInt16 ByteArray.empty cipherSuite ++
        ByteArray.empty.push 0)
      (X := SV ++ KS) (S := ByteArray.empty)
      (by rw [hbody]; simp only [ByteArray.append_assoc, ByteArray.append_empty])
      (by rw [ByteArray.size_append, ByteArray.size_append,
        ByteArray.size_append, ByteArray.size_append, ByteArray.size_append,
        s2, hR, s1, sc, sz]; omega) hEXTsz
  have hend : 0 + 2 + 32 + 1 + legacySessionIdEcho.size + 2 + 1 + 2 +
      (SV ++ KS).size = msg.body.size := by
    rw [hbody]
    simp only [ByteArray.size_append, s2, hR, s1, sc, sz, se]
    omega
  have hesz : ∀ e ∈ [Extension.mk supportedVersionsExtension
        (appendUInt16 ByteArray.empty tls13Version),
      Extension.mk keyShareExtension (appendUInt16 ByteArray.empty group.toUInt16 ++
        (appendUInt16 ByteArray.empty (UInt16.ofNat keyExchange.size) ++
          keyExchange))],
      e.data.size < 2 ^ 16 := by
    intro e he
    cases he with
    | head => exact (show (2 : Nat) < 2 ^ 16 by decide)
    | tail _ he => cases he with
      | head => exact hKSsz
      | tail _ he => cases he
  have hedist : List.Pairwise
      (fun a b => (a.extensionType == b.extensionType) = false)
      [Extension.mk supportedVersionsExtension
          (appendUInt16 ByteArray.empty tls13Version),
        Extension.mk keyShareExtension
          (appendUInt16 ByteArray.empty group.toUInt16 ++
            (appendUInt16 ByteArray.empty (UInt16.ofNat keyExchange.size) ++
              keyExchange))] := by
    refine List.Pairwise.cons ?_ (List.pairwise_singleton ..)
    intro b hb
    cases hb with
    | head => rfl
    | tail _ hb => cases hb
  unfold parseServerHello
  rw [hty, if_pos (show (serverHelloType == serverHelloType) = true from rfl)]
  simp only [r1]
  rw [if_pos (beq_self_eq_true legacyTls12Version)]
  simp only [r2]
  rw [if_neg (by rw [hrand]; exact Bool.false_ne_true)]
  simp only [r3]
  rw [if_neg hc]
  simp only [r4, r5]
  rw [if_pos (show ((0 : UInt8) == 0) = true from rfl)]
  simp only [r6, requireEnd_eval (context := "ServerHello") hend]
  rw [← hexts]
  simp only [parseExtensions_extensionsBytes _ hesz hedist,
    show requireExtension
      [Extension.mk supportedVersionsExtension
          (appendUInt16 ByteArray.empty tls13Version),
        Extension.mk keyShareExtension
          (appendUInt16 ByteArray.empty group.toUInt16 ++
            (appendUInt16 ByteArray.empty (UInt16.ofNat keyExchange.size) ++
              keyExchange))].toArray
      supportedVersionsExtension "supported_versions" =
      .ok (Extension.mk supportedVersionsExtension
        (appendUInt16 ByteArray.empty tls13Version)) from rfl]
  rw [if_pos (beq_self (appendUInt16 ByteArray.empty tls13Version))]
  simp only [show requireExtension
      [Extension.mk supportedVersionsExtension
          (appendUInt16 ByteArray.empty tls13Version),
        Extension.mk keyShareExtension
          (appendUInt16 ByteArray.empty group.toUInt16 ++
            (appendUInt16 ByteArray.empty (UInt16.ofNat keyExchange.size) ++
              keyExchange))].toArray
      keyShareExtension "key_share" =
      .ok (Extension.mk keyShareExtension
        (appendUInt16 ByteArray.empty group.toUInt16 ++
          (appendUInt16 ByteArray.empty (UInt16.ofNat keyExchange.size) ++
            keyExchange))) from rfl,
    parseServerKeyShare_eq hKXsz hkey]

/-! ### End-to-end: encode, take off the wire with residual, parse

Each law below composes the framing roundtrip with the body inversion: the
encoded message is recovered from a buffer that carries arbitrary trailing
bytes, those bytes are returned untouched as the residual, and parsing the
recovered message reproduces the encoded fields. -/

/-- Finished: wire roundtrip with residual, then parse inversion. -/
theorem encodeFinished_decodeOne_parse {verifyData : ByteArray} {msg : Message}
    (h : encodeFinished verifyData = .ok msg) (rest : ByteArray) :
    decodeOne (msg.encoded ++ rest) = .ok (msg, rest) ∧
      parseFinished msg =
        .ok { verifyData := verifyData, encoded := msg.encoded } :=
  ⟨encodeFinished_decodeOne h rest, encodeFinished_parse h⟩

/-- KeyUpdate: wire roundtrip with residual, then parse inversion. -/
theorem encodeKeyUpdate_decodeOne_parse {request : KeyUpdateRequest}
    {msg : Message} (h : encodeKeyUpdate request = .ok msg) (rest : ByteArray) :
    decodeOne (msg.encoded ++ rest) = .ok (msg, rest) ∧
      parseKeyUpdate msg = .ok { request := request, encoded := msg.encoded } :=
  ⟨encodeKeyUpdate_decodeOne h rest, encodeKeyUpdate_parse h⟩

/-- CertificateVerify: wire roundtrip with residual, then parse inversion. -/
theorem encodeCertificateVerify_decodeOne_parse {algorithm : UInt16}
    {signature : ByteArray} {msg : Message}
    (h : encodeCertificateVerify algorithm signature = .ok msg)
    (rest : ByteArray) :
    decodeOne (msg.encoded ++ rest) = .ok (msg, rest) ∧
      parseCertificateVerify msg =
        .ok { algorithm := algorithm, signature := signature,
              encoded := msg.encoded } :=
  ⟨encodeCertificateVerify_decodeOne h rest, encodeCertificateVerify_parse h⟩

/-- EncryptedExtensions (no ALPN): wire roundtrip with residual, then parse
inversion. -/
theorem encodeEncryptedExtensions_decodeOne_parse_none {msg : Message}
    (h : encodeEncryptedExtensions none = .ok msg) (rest : ByteArray) :
    decodeOne (msg.encoded ++ rest) = .ok (msg, rest) ∧
      parseEncryptedExtensions msg =
        .ok { extensions := #[], encoded := msg.encoded } :=
  ⟨encodeEncryptedExtensions_decodeOne h rest,
    encodeEncryptedExtensions_parse_none h⟩

/-- Certificate: wire roundtrip with residual, then parse inversion. -/
theorem encodeCertificate_decodeOne_parse {leaf : ByteArray}
    {rest : List ByteArray} {msg : Message}
    (h : encodeCertificate (leaf :: rest).toArray = .ok msg)
    (trailing : ByteArray) :
    decodeOne (msg.encoded ++ trailing) = .ok (msg, trailing) ∧
      parseCertificate msg = .ok
        { requestContext := ByteArray.empty,
          entries :=
            ((leaf :: rest).map fun der =>
              ({ der := der, extensions := #[] } : CertificateEntry)).toArray,
          leafDer := leaf, encoded := msg.encoded } :=
  ⟨encodeCertificate_decodeOne h trailing, encodeCertificate_parse h⟩

/-- ServerHello: wire roundtrip with residual, then parse inversion. -/
theorem encodeServerHello_decodeOne_parse {random legacySessionIdEcho : ByteArray}
    {group : NamedGroup} {keyExchange : ByteArray} {cipherSuite : UInt16}
    {msg : Message}
    (h : encodeServerHello random legacySessionIdEcho group keyExchange
      cipherSuite = .ok msg)
    (hrand : (random == helloRetryRequestRandom) = false)
    (hkey : checkKeyShareSize group keyExchange = .ok ()) (rest : ByteArray) :
    decodeOne (msg.encoded ++ rest) = .ok (msg, rest) ∧
      parseServerHello msg = .ok
        { random := random, legacySessionIdEcho := legacySessionIdEcho,
          cipherSuite := cipherSuite, selectedGroup := group,
          keyExchange := keyExchange,
          extensions :=
            #[{ extensionType := supportedVersionsExtension,
                data := appendUInt16 ByteArray.empty tls13Version },
              { extensionType := keyShareExtension,
                data := appendUInt16 ByteArray.empty group.toUInt16 ++
                  (appendUInt16 ByteArray.empty (UInt16.ofNat keyExchange.size) ++
                    keyExchange) }],
          encoded := msg.encoded } :=
  ⟨encodeServerHello_decodeOne h rest, encodeServerHello_parse h hrand hkey⟩

/-- HelloRetryRequest: wire roundtrip with residual, then parse inversion. -/
theorem encodeHelloRetryRequest_decodeOne_parse {legacySessionIdEcho : ByteArray}
    {group : NamedGroup} {cipherSuite : UInt16} {msg : Message}
    (h : encodeHelloRetryRequest legacySessionIdEcho group cipherSuite = .ok msg)
    (rest : ByteArray) :
    decodeOne (msg.encoded ++ rest) = .ok (msg, rest) ∧
      parseHelloRetryRequest msg = .ok
        { legacySessionIdEcho := legacySessionIdEcho, cipherSuite := cipherSuite,
          selectedGroup := group,
          extensions :=
            #[{ extensionType := supportedVersionsExtension,
                data := appendUInt16 ByteArray.empty tls13Version },
              { extensionType := keyShareExtension,
                data := appendUInt16 ByteArray.empty group.toUInt16 }],
          encoded := msg.encoded } :=
  ⟨encodeHelloRetryRequest_decodeOne h rest, encodeHelloRetryRequest_parse h⟩

/-- NewSessionTicket: wire roundtrip with residual, then parse inversion. -/
theorem encodeNewSessionTicket_decodeOne_parse {ticketLifetime ticketAgeAdd : UInt32}
    {ticketNonce ticket : ByteArray} {msg : Message}
    (h : encodeNewSessionTicket ticketLifetime ticketAgeAdd ticketNonce ticket
      = .ok msg) (rest : ByteArray) :
    decodeOne (msg.encoded ++ rest) = .ok (msg, rest) ∧
      parseNewSessionTicket msg = .ok
        { ticketLifetime := ticketLifetime, ticketAgeAdd := ticketAgeAdd,
          ticketNonce := ticketNonce, ticket := ticket, extensions := #[],
          encoded := msg.encoded } :=
  ⟨encodeNewSessionTicket_decodeOne h rest, encodeNewSessionTicket_parse h⟩

/-! ### Frame canonicity

`decodeOne_frame` says the wire decoder accepts what `frame` produced. These are
the converse: everything the decoder produces *is* a frame. Re-framing a decoded
message's type and body reproduces the message, retained `encoded` bytes and
all, so comparing two decoded messages' `msgType` and `body` is exactly as
strong as comparing their wire bytes (`decodeOne_injective`) — the framing-layer
analogue of `parseClientHello_canonical` and `parseClientHello_body_injective`.

The missing ingredient was the converse of `uint24_recompose`: the three
big-endian length bytes are recovered from the length they encode. -/

private theorem uint24_value (b0 b1 b2 : UInt8) :
    b0.toNat <<< 16 ||| b1.toNat <<< 8 ||| b2.toNat =
      b0.toNat * 2 ^ 16 + b1.toNat * 2 ^ 8 + b2.toNat := by
  have h2 := UInt8.toNat_lt b2
  have h1 := UInt8.toNat_lt b1
  have e1 : b0.toNat <<< 16 ||| b1.toNat <<< 8 =
      (b0.toNat * 2 ^ 8 + b1.toNat) <<< 8 := by
    rw [← Nat.shiftLeft_add_eq_or_of_lt (i := 16) (by rw [Nat.shiftLeft_eq]; omega),
      Nat.shiftLeft_eq, Nat.shiftLeft_eq, Nat.shiftLeft_eq]
    omega
  rw [e1, ← Nat.shiftLeft_add_eq_or_of_lt (i := 8) (by omega), Nat.shiftLeft_eq]
  omega

private theorem uint24_lt (b0 b1 b2 : UInt8) :
    (b0.toNat <<< 16 ||| b1.toNat <<< 8 ||| b2.toNat) < 2 ^ 24 := by
  have h0 := UInt8.toNat_lt b0
  have h1 := UInt8.toNat_lt b1
  have h2 := UInt8.toNat_lt b2
  rw [uint24_value]; omega

private theorem uint24_decompose (b0 b1 b2 : UInt8) :
    length24Bytes (b0.toNat <<< 16 ||| b1.toNat <<< 8 ||| b2.toNat) =
      ((ByteArray.empty.push b0).push b1).push b2 := by
  have h0 := UInt8.toNat_lt b0
  have h1 := UInt8.toNat_lt b1
  have h2 := UInt8.toNat_lt b2
  unfold length24Bytes
  rw [show UInt8.ofNat ((b0.toNat <<< 16 ||| b1.toNat <<< 8 ||| b2.toNat) >>> 16)
        = b0 from by
      rw [uint24_value, Nat.shiftRight_eq_div_pow,
        show (b0.toNat * 2 ^ 16 + b1.toNat * 2 ^ 8 + b2.toNat) / 2 ^ 16
          = b0.toNat from by omega, UInt8.ofNat_toNat],
    show UInt8.ofNat ((b0.toNat <<< 16 ||| b1.toNat <<< 8 ||| b2.toNat) >>> 8)
        = b1 from by
      apply UInt8.toNat_inj.mp
      rw [uint24_value, Nat.shiftRight_eq_div_pow, UInt8.toNat_ofNat']
      omega,
    show UInt8.ofNat (b0.toNat <<< 16 ||| b1.toNat <<< 8 ||| b2.toNat) = b2 from by
      apply UInt8.toNat_inj.mp
      rw [uint24_value, UInt8.toNat_ofNat']
      omega]

private theorem extract_three {W : ByteArray} {off e : Nat} (he : e = off + 3)
    (h : off + 3 ≤ W.size) :
    W.extract off e =
      ((ByteArray.empty.push (W.get! off)).push (W.get! (off + 1))).push
        (W.get! (off + 2)) := by
  subst he
  apply ByteArray.ext_getElem
  · rw [ByteArray.size_extract, Nat.min_eq_left h]
    show off + 3 - off = 3
    omega
  · intro i hi hi'
    rw [ByteArray.size_extract, Nat.min_eq_left h] at hi
    rw [ByteArray.getElem_extract]
    match i, hi with
    | 0, _ =>
      rw [show (((ByteArray.empty.push (W.get! off)).push (W.get! (off + 1))).push
          (W.get! (off + 2)))[0] = W.get! off from rfl,
        get!_eq_getElem (show off < W.size by omega)]
      simp
    | 1, _ =>
      rw [show (((ByteArray.empty.push (W.get! off)).push (W.get! (off + 1))).push
          (W.get! (off + 2)))[1] = W.get! (off + 1) from rfl,
        get!_eq_getElem (show off + 1 < W.size by omega)]
    | 2, _ =>
      rw [show (((ByteArray.empty.push (W.get! off)).push (W.get! (off + 1))).push
          (W.get! (off + 2)))[2] = W.get! (off + 2) from rfl,
        get!_eq_getElem (show off + 2 < W.size by omega)]

private theorem length24Bytes_extract {W : ByteArray} {off : Nat}
    (h : off + 3 ≤ W.size) :
    length24Bytes ((W.get! off).toNat <<< 16 ||| (W.get! (off + 1)).toNat <<< 8 |||
      (W.get! (off + 2)).toNat) = W.extract off (off + 3) := by
  rw [uint24_decompose, extract_three rfl h]

private theorem encodeLength24_eval {n : Nat} (h : n < 2 ^ 24) :
    encodeLength24 n = .ok (length24Bytes n) := by
  unfold encodeLength24
  rw [if_neg (show ¬(n > 0xffffff) by omega)]
  rfl

private theorem length24Bytes_extract_one {W : ByteArray} (h : 4 ≤ W.size) :
    length24Bytes ((W.get! 1).toNat <<< 16 ||| (W.get! 2).toNat <<< 8 |||
      (W.get! 3).toNat) = W.extract 1 4 :=
  length24Bytes_extract (W := W) (off := 1) (by omega)

private theorem frame_of_header {W : ByteArray} {n : Nat}
    (hn : (W.get! 1).toNat <<< 16 ||| (W.get! 2).toNat <<< 8 ||| (W.get! 3).toNat = n)
    (hbnd : 4 + n ≤ W.size) :
    frame (W.get! 0) (W.extract 4 (4 + n)) =
      .ok { msgType := W.get! 0, body := W.extract 4 (4 + n),
            encoded := W.extract 0 (4 + n) } := by
  have hlt : n < 2 ^ 24 := hn ▸ uint24_lt (W.get! 1) (W.get! 2) (W.get! 3)
  have hsz : (W.extract 4 (4 + n)).size = n := by
    rw [ByteArray.size_extract, Nat.min_eq_left (by omega)]
    omega
  have henc : ByteArray.empty.push (W.get! 0) ++ length24Bytes n ++
      W.extract 4 (4 + n) = W.extract 0 (4 + n) := by
    rw [extract_split (W := W) (i := 0) (j := 4) (k := 4 + n) (by omega) (by omega),
      extract_split (W := W) (i := 0) (j := 1) (k := 4) (by omega) (by omega),
      show W.extract 0 1 = ByteArray.empty.push (W.get! 0) from
        extract_one (by omega),
      ← hn, length24Bytes_extract_one (by omega)]
  unfold frame
  rw [hsz, encodeLength24_eval hlt]
  show Except.ok (Message.mk (W.get! 0) (W.extract 4 (4 + n))
    (ByteArray.empty.push (W.get! 0) ++ length24Bytes n ++
      W.extract 4 (4 + n))) = _
  rw [henc]

/-- **Frame canonicity**: every message the wire decoder produces *is* a frame.
Re-framing a decoded message's type and body reproduces the message, retained
`encoded` bytes and all — the converse of `decodeOne_frame`, and the
framing-layer analogue of `parseClientHello_canonical`. -/
theorem decodeOne_canonical {bytes : ByteArray} {msg : Message} {rest : ByteArray}
    (h : decodeOne bytes = .ok (msg, rest)) :
    frame msg.msgType msg.body = .ok msg := by
  unfold decodeOne at h
  split at h
  · cases h
  · rename_i msgType r0 h8
    split at h
    · cases h
    · rename_i len r1 h24
      split at h
      · cases h
      · rename_i body r2 htake
        cases h
        obtain ⟨-, ho0, hle0⟩ := readUInt8_ok h8
        have hb1 : (1 : Nat) ≤ bytes.size := by
          have h' : r0.offset ≤ bytes.size := hle0
          omega
        rw [show ({ bytes := bytes } : Reader) = Reader.mk bytes 0 from rfl,
          readUInt8_eval (show 0 < bytes.size by omega)] at h8
        simp only [Except.ok.injEq, Prod.mk.injEq] at h8
        obtain ⟨rfl, rfl⟩ := h8
        obtain ⟨-, ho1, hle1⟩ := readUInt24_ok h24
        have hb4 : (4 : Nat) ≤ bytes.size := by
          have h' : r1.offset ≤ bytes.size := hle1
          omega
        rw [readUInt24_eval (off := 0 + 1) (show 0 + 1 + 3 ≤ bytes.size by omega)] at h24
        simp only [Except.ok.injEq, Prod.mk.injEq] at h24
        obtain ⟨rfl, rfl⟩ := h24
        obtain ⟨rfl, rfl, hbnd⟩ := take_extract htake
        exact frame_of_header (W := bytes) rfl hbnd


theorem decode_canonical {bytes : ByteArray} {msg : Message}
    (h : decode bytes = .ok msg) : frame msg.msgType msg.body = .ok msg := by
  unfold decode at h
  split at h
  · cases h
  · rename_i m rest hd
    obtain ⟨-, h⟩ | ⟨-, h⟩ := ite_ok_cases h
    · cases h
      exact decodeOne_canonical hd
    · cases h

theorem takeMessage?_canonical {buffered rest : ByteArray} {msg : Message}
    (h : takeMessage? buffered = .ok (some (msg, rest))) :
    frame msg.msgType msg.body = .ok msg := by
  unfold takeMessage? at h
  split at h
  · cases h
  · split at h
    · cases h
    · split at h
      · cases h
      · rename_i message hdec
        simp only [Except.ok.injEq, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, -⟩ := h
        exact decode_canonical hdec

theorem decodeOne_injective {b₁ b₂ : ByteArray} {m₁ m₂ : Message}
    {r₁ r₂ : ByteArray} (h₁ : decodeOne b₁ = .ok (m₁, r₁))
    (h₂ : decodeOne b₂ = .ok (m₂, r₂)) (hty : m₁.msgType = m₂.msgType)
    (hbody : m₁.body = m₂.body) : m₁ = m₂ := by
  have e₁ := decodeOne_canonical h₁
  have e₂ := decodeOne_canonical h₂
  rw [hty, hbody] at e₁
  rw [e₂] at e₁
  exact (Except.ok.inj e₁).symm

end Handshake
end Tls
