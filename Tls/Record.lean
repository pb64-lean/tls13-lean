module

import HaclStar.Aead
import TLS13.KeySchedule

public section

namespace Tls
namespace Record

/-!
The TLS 1.3 record layer for `TLS_CHACHA20_POLY1305_SHA256`.

This module is sans-I/O. `Decoder.feed` incrementally frames bytes received
from a transport, while `seal` and `open` protect one record and return the
advanced directional traffic-key state. Handshake ordering, alerts, and key
update messages remain the responsibility of the TLS handshake machine.
-/

/-- TLS record content types supported by TLS 1.3. Heartbeat and unknown
content types are deliberately rejected. -/
inductive ContentType where
  | changeCipherSpec
  | alert
  | handshake
  | applicationData
  deriving Repr, BEq, DecidableEq, Inhabited

namespace ContentType

@[expose] def toUInt8 : ContentType → UInt8
  | .changeCipherSpec => 20
  | .alert => 21
  | .handshake => 22
  | .applicationData => 23

@[expose] def ofUInt8? : UInt8 → Option ContentType
  | 20 => some .changeCipherSpec
  | 21 => some .alert
  | 22 => some .handshake
  | 23 => some .applicationData
  | _ => none

end ContentType

/-- TLS 1.3 uses TLS 1.2's version number in every record-layer header. -/
@[expose] def legacyRecordVersion : UInt16 := 0x0303

/-- RFC 8446 §5.1 permits an initial ClientHello sender to use TLS 1.0's
record version for compatibility with old middleboxes. Receivers ignore the
legacy version on TLSPlaintext records; authenticated TLSCiphertext is still
checked by `open` because its header is AEAD additional data. -/
@[expose] def legacyClientHelloRecordVersion : UInt16 := 0x0301

@[expose] def headerLength : Nat := 5

/-- RFC 8446 §5.1: maximum `TLSPlaintext.fragment` length. -/
@[expose] def maxPlaintextLength : Nat := 1 <<< 14

/-- RFC 8446 §5.2: maximum `TLSCiphertext.encrypted_record` length. -/
@[expose] def maxCiphertextLength : Nat := (1 <<< 14) + 256

@[expose] def aeadKeyLength : Nat := 32

@[expose] def aeadIvLength : Nat := 12

@[expose] def aeadTagLength : Nat := 16

/-- RFC 9846 §5.2: `TLSInnerPlaintext.content` plus zero padding is at most
`2^14` bytes; the encoded value has one additional content-type byte. -/
@[expose] def maxInnerPlaintextLength : Nat := (1 <<< 14) + 1

inductive Error where
  | unsupportedContentType (value : UInt8)
  | invalidLegacyVersion (value : UInt16)
  | plaintextTooLong (length : Nat)
  | ciphertextTooLong (length : Nat)
  | ciphertextTooShort (length : Nat)
  | innerPlaintextTooLong (length : Nat)
  | invalidTrafficSecretLength (length : Nat)
  | invalidKeyLength (length : Nat)
  | invalidIvLength (length : Nat)
  | sequenceExhausted
  | authenticationFailed
  | missingInnerContentType
  | aeadOutputLengthMismatch (expected actual : Nat)
  deriving Repr, BEq, Inhabited

namespace Error

def toString : Error → String
  | .unsupportedContentType value => s!"unsupported TLS content type {value}"
  | .invalidLegacyVersion value => s!"invalid TLS record version {value}"
  | .plaintextTooLong length =>
    s!"TLS plaintext is {length} bytes (maximum {maxPlaintextLength})"
  | .ciphertextTooLong length =>
    s!"TLS ciphertext is {length} bytes (maximum {maxCiphertextLength})"
  | .ciphertextTooShort length =>
    s!"TLS ciphertext is {length} bytes (minimum {aeadTagLength + 1})"
  | .innerPlaintextTooLong length =>
    s!"TLS inner plaintext is {length} bytes (maximum {maxInnerPlaintextLength})"
  | .invalidTrafficSecretLength length =>
    s!"TLS traffic secret is {length} bytes (expected {TLS13.KeySchedule.hashLen})"
  | .invalidKeyLength length =>
    s!"TLS ChaCha20-Poly1305 key is {length} bytes (expected {aeadKeyLength})"
  | .invalidIvLength length =>
    s!"TLS ChaCha20-Poly1305 IV is {length} bytes (expected {aeadIvLength})"
  | .sequenceExhausted => "TLS record sequence number exhausted"
  | .authenticationFailed => "TLS record authentication failed"
  | .missingInnerContentType => "TLS inner plaintext has no content type"
  | .aeadOutputLengthMismatch expected actual =>
    s!"TLS AEAD returned {actual} bytes (expected {expected})"

end Error

instance : ToString Error := ⟨Error.toString⟩

/-- A strictly framed wire record. `fragment` excludes the five-byte header.
The decoder accepts the extended TLSCiphertext limit only for outer
`application_data` records. -/
structure RawRecord where
  contentType : ContentType
  legacyVersion : UInt16 := legacyRecordVersion
  fragment : ByteArray := ByteArray.empty
  deriving BEq, Inhabited

/-- Decrypted TLSInnerPlaintext, including the amount of stripped zero
padding. -/
structure Plaintext where
  contentType : ContentType
  fragment : ByteArray := ByteArray.empty
  paddingLength : Nat := 0
  deriving BEq, Inhabited

/-- Directional TLS traffic state. Client write and server write directions
must use distinct values. `seq` is reset whenever the secret is updated. -/
structure TrafficKeys where
  secret : ByteArray
  key : ByteArray
  iv : ByteArray
  seq : UInt64 := 0
  deriving BEq, Inhabited

/-- Append a big-endian 16-bit value. -/
@[expose] def putUInt16 (out : ByteArray) (value : UInt16) : ByteArray :=
  (out.push (value >>> 8).toUInt8).push value.toUInt8

/-- Read a big-endian 16-bit value at `offset`; the caller checks bounds. -/
@[expose] def getUInt16 (bytes : ByteArray) (offset : Nat) : UInt16 :=
  (bytes.get! offset).toUInt16 <<< 8 ||| (bytes.get! (offset + 1)).toUInt16

/-- Encode the five-byte record header. `fragmentLength` is truncated to
16 bits; encoders validate it beforehand. -/
@[expose] def encodeHeader (contentType : ContentType) (version : UInt16)
    (fragmentLength : Nat) : ByteArray :=
  let out := ByteArray.empty.push contentType.toUInt8
  let out := putUInt16 out version
  putUInt16 out (UInt16.ofNat fragmentLength)

@[expose] def RawRecord.header (record : RawRecord) : ByteArray :=
  encodeHeader record.contentType record.legacyVersion record.fragment.size

/-- Exact wire bytes of a raw record: the five-byte header followed by the
fragment. `Tls.Record.Laws` proves that decoding is a left inverse of this
encoding. -/
@[expose] def RawRecord.encode (record : RawRecord) : ByteArray :=
  record.header ++ record.fragment

/-- Concatenated wire encoding of framed records, in order. -/
@[expose] def encodeRawRecords (records : Array RawRecord) : ByteArray :=
  records.foldl (fun out record => out ++ record.encode) ByteArray.empty

/-- Encode an unprotected TLSPlaintext record. This is used for the initial
ClientHello and compatibility ChangeCipherSpec records; callers enforce the
handshake-state rules governing when those records are legal. -/
def encodePlaintext (contentType : ContentType) (fragment : ByteArray) :
    Except Error ByteArray := do
  if fragment.size > maxPlaintextLength then
    throw (.plaintextTooLong fragment.size)
  pure (encodeHeader contentType legacyRecordVersion fragment.size ++ fragment)

/-- Incremental record framer state. A successful call retains only an
incomplete trailing record in `buffered`. -/
structure Decoder where
  buffered : ByteArray := ByteArray.empty
  deriving BEq, Inhabited

/-- Validate a header's claimed fragment length as soon as the header is
available, without waiting for the fragment itself. The extended TLSCiphertext
limit applies only to outer `application_data` records. -/
@[expose] def checkFragmentLength (contentType : ContentType) (fragmentLength : Nat) :
    Except Error Unit :=
  if contentType == .applicationData then
    if fragmentLength > maxCiphertextLength then
      .error (.ciphertextTooLong fragmentLength)
    else if fragmentLength < aeadTagLength + 1 then
      .error (.ciphertextTooShort fragmentLength)
    else
      .ok ()
  else if fragmentLength > maxPlaintextLength then
    .error (.plaintextTooLong fragmentLength)
  else
    .ok ()

/-- Frame one record out of `buffered`. `some` carries the record and the
unconsumed remainder; `none` means the buffer holds no complete record yet. -/
@[expose] def decodeStep (buffered : ByteArray) :
    Except Error (Option (RawRecord × ByteArray)) :=
  if buffered.size < headerLength then
    .ok none
  else
    match ContentType.ofUInt8? (buffered.get! 0) with
    | none => .error (.unsupportedContentType (buffered.get! 0))
    | some contentType =>
      match checkFragmentLength contentType (getUInt16 buffered 3).toNat with
      | .error e => .error e
      | .ok () =>
        if buffered.size < headerLength + (getUInt16 buffered 3).toNat then
          .ok none
        else
          -- RFC 8446 §5.1 deprecates TLSPlaintext.legacy_record_version and
          -- requires receivers to ignore it. Preserve it in RawRecord for
          -- exact AEAD header handling; `open` enforces 0x0303 on
          -- TLSCiphertext.
          .ok (some (
            { contentType
              legacyVersion := getUInt16 buffered 1
              fragment :=
                buffered.extract headerLength
                  (headerLength + (getUInt16 buffered 3).toNat) },
            buffered.extract (headerLength + (getUInt16 buffered 3).toNat)
              buffered.size))

/-- A successful `decodeStep` strictly shrinks the buffer: it consumes the
five-byte header plus the fragment. -/
theorem decodeStep_size_lt {buffered rest : ByteArray} {record : RawRecord}
    (h : decodeStep buffered = .ok (some (record, rest))) :
    rest.size < buffered.size := by
  unfold decodeStep at h
  split at h
  · simp at h
  · split at h
    · simp at h
    · split at h
      · simp at h
      · split at h
        · simp at h
        · simp only [Except.ok.injEq, Option.some.injEq, Prod.mk.injEq] at h
          rw [← h.2, ByteArray.size_extract]
          simp only [headerLength] at *
          omega

-- The named scrutinee hypothesis is consumed by `decreasing_by`, which the
-- unused-variable linter does not see.
set_option linter.unusedVariables false in
def decodeBuffered (buffered : ByteArray) (records : Array RawRecord) :
    Except Error (ByteArray × Array RawRecord) :=
  match h : decodeStep buffered with
  | .error e => .error e
  | .ok none => .ok (buffered, records)
  | .ok (some (record, rest)) => decodeBuffered rest (records.push record)
  termination_by buffered.size
  decreasing_by exact decodeStep_size_lt h

/-- Feed an arbitrary transport chunk and return every complete record in wire
order. Header errors and oversized lengths are reported as soon as the header
is available, without waiting for the claimed fragment. -/
def Decoder.feed (decoder : Decoder) (chunk : ByteArray) :
    Except Error (Decoder × Array RawRecord) := do
  let (buffered, records) ← decodeBuffered (decoder.buffered ++ chunk) #[]
  pure ({ buffered }, records)

private def validateSecret (secret : ByteArray) : Except Error Unit := do
  unless secret.size == TLS13.KeySchedule.hashLen do
    throw (.invalidTrafficSecretLength secret.size)

private def validateKeyAndIv (keys : TrafficKeys) : Except Error Unit := do
  unless keys.key.size == aeadKeyLength do
    throw (.invalidKeyLength keys.key.size)
  unless keys.iv.size == aeadIvLength do
    throw (.invalidIvLength keys.iv.size)

/-- Check the derived key and IV widths and assemble the initial traffic
state, with the sequence number at zero. -/
private def mkTrafficKeys (secret key iv : ByteArray) :
    Except Error TrafficKeys :=
  if key.size == aeadKeyLength then
    if iv.size == aeadIvLength then
      .ok { secret, key, iv, seq := 0 }
    else
      .error (.invalidIvLength iv.size)
  else
    .error (.invalidKeyLength key.size)

/-- Derive the ChaCha20-Poly1305 key and static IV from a SHA-256 traffic
secret (RFC 8446 §7.3). -/
def deriveTrafficKeys (secret : ByteArray) : Except Error TrafficKeys := do
  validateSecret secret
  mkTrafficKeys secret
    (TLS13.KeySchedule.expandLabel secret "key" ByteArray.empty aeadKeyLength)
    (TLS13.KeySchedule.expandLabel secret "iv" ByteArray.empty aeadIvLength)

/-- RFC 8446 §7.2 application traffic-secret update. The context here is the
empty byte string, not the hash of an empty transcript. -/
def updateTrafficSecret (secret : ByteArray) : Except Error ByteArray := do
  validateSecret secret
  let next := TLS13.KeySchedule.expandLabel secret "traffic upd" ByteArray.empty
    TLS13.KeySchedule.hashLen
  unless next.size == TLS13.KeySchedule.hashLen do
    throw (.invalidTrafficSecretLength next.size)
  pure next

/-- Advance to the next traffic secret, derive a fresh key/IV, and reset the
record sequence number. -/
def TrafficKeys.update (keys : TrafficKeys) : Except Error TrafficKeys := do
  deriveTrafficKeys (← updateTrafficSecret keys.secret)

/-- The record sequence number left-zero-padded to the IV width, big endian
(RFC 8446 §5.3). -/
@[expose] def sequenceBytes (seq : UInt64) : ByteArray :=
  ByteArray.mk #[
    0, 0, 0, 0,
    (seq >>> 56).toUInt8,
    (seq >>> 48).toUInt8,
    (seq >>> 40).toUInt8,
    (seq >>> 32).toUInt8,
    (seq >>> 24).toUInt8,
    (seq >>> 16).toUInt8,
    (seq >>> 8).toUInt8,
    seq.toUInt8
  ]

/-- Pointwise XOR of the first `count` bytes of `a` and `b`; the callers
check bounds. -/
@[expose] def xorBytes (count : Nat) (a b : ByteArray) : ByteArray :=
  match count with
  | 0 => ByteArray.empty
  | n + 1 => (xorBytes n a b).push (a.get! n ^^^ b.get! n)

/-- Per-record nonce: the static IV XOR the left-zero-padded, big-endian
64-bit record sequence number (RFC 8446 §5.3). -/
def TrafficKeys.nonce (keys : TrafficKeys) : Except Error ByteArray := do
  unless keys.iv.size == aeadIvLength do
    throw (.invalidIvLength keys.iv.size)
  pure (xorBytes aeadIvLength keys.iv (sequenceBytes keys.seq))

/-- Advance the sequence number, rejecting wraparound. -/
def advance (keys : TrafficKeys) : Except Error TrafficKeys := do
  if keys.seq == (0xffffffffffffffff : UInt64) then
    throw .sequenceExhausted
  pure { keys with seq := keys.seq + 1 }

/-- `count` zero bytes. Structural recursion so proofs can compute with it. -/
@[expose] def zeroBytes : Nat → ByteArray
  | 0 => ByteArray.empty
  | count + 1 => (zeroBytes count).push 0

/-- The encoded TLSInnerPlaintext: content, inner content type, zero padding
(RFC 8446 §5.2). -/
@[expose] def innerPlaintext (contentType : ContentType) (fragment : ByteArray)
    (paddingLength : Nat) : ByteArray :=
  (fragment.push contentType.toUInt8) ++ zeroBytes paddingLength

/-- The AEAD output `seal` frames, named so `Tls.Record.Laws` can state the
open∘seal identity parametrically over the opaque HACL* binding. (Not
`@[expose]`d: the body mentions the privately imported HACL* binding.) -/
def sealedCiphertext (keys : TrafficKeys) (contentType : ContentType)
    (fragment : ByteArray) (paddingLength : Nat) (nonce : ByteArray) :
    ByteArray :=
  HaclStar.ChaCha20Poly1305.encrypt keys.key nonce
    (encodeHeader .applicationData legacyRecordVersion
      (fragment.size + 1 + paddingLength + aeadTagLength))
    (innerPlaintext contentType fragment paddingLength)

/-- Protect one TLSInnerPlaintext record. The returned traffic state has its
sequence number advanced exactly once. `paddingLength` counts zero bytes after
the inner content type. Written as a pure `match`/`if` chain so
`Tls.Record.Laws` can reason about it by case analysis. -/
def «seal» (keys : TrafficKeys) (contentType : ContentType) (fragment : ByteArray)
    (paddingLength : Nat := 0) : Except Error (TrafficKeys × ByteArray) :=
  match validateKeyAndIv keys with
  | .error e => .error e
  | .ok _ =>
    if fragment.size > maxPlaintextLength then
      .error (.plaintextTooLong fragment.size)
    else if fragment.size + 1 + paddingLength > maxInnerPlaintextLength then
      .error (.innerPlaintextTooLong (fragment.size + 1 + paddingLength))
    else
      -- Reject before encryption so a caller can never accidentally reuse the
      -- final sequence number after failing to represent its successor.
      match advance keys with
      | .error e => .error e
      | .ok nextKeys =>
        if fragment.size + 1 + paddingLength + aeadTagLength >
            maxCiphertextLength then
          .error (.ciphertextTooLong
            (fragment.size + 1 + paddingLength + aeadTagLength))
        else
          match keys.nonce with
          | .error e => .error e
          | .ok nonce =>
            if (sealedCiphertext keys contentType fragment paddingLength
                  nonce).size ≠
                fragment.size + 1 + paddingLength + aeadTagLength then
              .error (.aeadOutputLengthMismatch
                (fragment.size + 1 + paddingLength + aeadTagLength)
                (sealedCiphertext keys contentType fragment paddingLength
                  nonce).size)
            else
              .ok (nextKeys,
                encodeHeader .applicationData legacyRecordVersion
                    (fragment.size + 1 + paddingLength + aeadTagLength) ++
                  sealedCiphertext keys contentType fragment paddingLength nonce)

/-- Index of the last nonzero byte strictly below `i`, scanning backward. -/
@[expose] def lastNonZero (inner : ByteArray) : Nat → Option Nat
  | 0 => none
  | i + 1 => if inner.get! i != 0 then some i else lastNonZero inner i

/-- Position of the TLSInnerPlaintext content-type byte: the last nonzero
byte, skipping the zero padding. -/
@[expose] def findInnerContentType (inner : ByteArray) : Option Nat :=
  lastNonZero inner inner.size

/-- Authenticate and decrypt one TLSCiphertext record. The exact encoded outer
header is supplied as AEAD additional data. Zero padding is stripped by
searching backward for the nonzero inner content-type byte. Written as a pure
`match`/`if` chain so `Tls.Record.Laws` can reason about it by case
analysis. -/
def «open» (keys : TrafficKeys) (record : RawRecord) :
    Except Error (TrafficKeys × Plaintext) :=
  match validateKeyAndIv keys with
  | .error e => .error e
  | .ok _ =>
    if record.contentType != .applicationData then
      .error (.unsupportedContentType record.contentType.toUInt8)
    else if record.legacyVersion != legacyRecordVersion then
      .error (.invalidLegacyVersion record.legacyVersion)
    else if record.fragment.size > maxCiphertextLength then
      .error (.ciphertextTooLong record.fragment.size)
    else if record.fragment.size < aeadTagLength + 1 then
      .error (.ciphertextTooShort record.fragment.size)
    else
      match advance keys with
      | .error e => .error e
      | .ok nextKeys =>
        match keys.nonce with
        | .error e => .error e
        | .ok nonce =>
          match HaclStar.ChaCha20Poly1305.decrypt keys.key nonce record.header
              record.fragment with
          | none => .error .authenticationFailed
          | some inner =>
            if inner.size ≠ record.fragment.size - aeadTagLength then
              .error (.aeadOutputLengthMismatch
                (record.fragment.size - aeadTagLength) inner.size)
            else if inner.size > maxInnerPlaintextLength then
              .error (.innerPlaintextTooLong inner.size)
            else
              match findInnerContentType inner with
              | none => .error .missingInnerContentType
              | some typePos =>
                match ContentType.ofUInt8? (inner.get! typePos) with
                | none => .error (.unsupportedContentType (inner.get! typePos))
                | some contentType =>
                  if (inner.extract 0 typePos).size > maxPlaintextLength then
                    .error (.plaintextTooLong (inner.extract 0 typePos).size)
                  else
                    .ok (nextKeys, {
                      contentType
                      fragment := inner.extract 0 typePos
                      paddingLength := inner.size - typePos - 1 })

end Record
end Tls
