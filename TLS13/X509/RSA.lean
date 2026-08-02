module

public import HaclStar.Sha256
public import TLS13.X509.Certificate

public section

/-!
Pure-Lean RSA signature verification for SHA-256.

All operands are public, so these routines deliberately optimize for clear,
exact RFC 8017 validation rather than constant-time execution. Lean `Nat`
arithmetic uses the runtime's big-integer backend; modular exponentiation keeps
every intermediate reduced instead of constructing `signature ^ exponent`.
-/

namespace TLS13
namespace X509
namespace RSA

inductive Scheme where
  | pkcs1v15Sha256
  | pssSha256 (saltLength : Nat)
  deriving Repr, BEq, DecidableEq

/-- RFC 8017 OS2IP: big-endian octets to a nonnegative integer. -/
def os2ip (bytes : ByteArray) : Nat :=
  bytes.foldl (fun value octet => value * 256 + octet.toNat) 0

/-- RFC 8017 I2OSP with an exact output length. -/
def i2osp (value size : Nat) : Except String ByteArray := do
  let mut remainder := value
  let mut output := ByteArray.mk (Array.replicate size 0)
  for offset in [0:size] do
    let index := size - offset - 1
    output := output.set! index (UInt8.ofNat (remainder % 256))
    remainder := remainder / 256
  if remainder != 0 then
    throw s!"integer does not fit in {size} octets"
  pure output

/-- Square-and-multiply modular exponentiation with reduced intermediates. -/
def modPow (base exponent modulus : Nat) : Nat := Id.run do
  if modulus == 0 then
    return 0
  let mut factor := base % modulus
  let mut power := exponent
  let mut result := 1 % modulus
  while power != 0 do
    if power % 2 == 1 then
      result := (result * factor) % modulus
    power := power >>> 1
    if power != 0 then
      factor := (factor * factor) % modulus
  return result

private def validPublicKey (key : RSAPublicKey) : Bool :=
  key.modulus > 1 && key.modulus % 2 == 1 &&
    key.exponent ≥ 3 && key.exponent % 2 == 1 &&
    key.exponent < key.modulus

private structure Representative where
  modulusBits : Nat
  modulusOctets : Nat
  value : Nat

/-- Apply RSAVP1 after checking the exact signature width and representative
range. -/
private def recoverRepresentative (key : RSAPublicKey) (signature : ByteArray) :
    Option Representative := do
  if !validPublicKey key then
    none
  else
    let modulusBits := key.modulus.log2 + 1
    let modulusOctets := (modulusBits + 7) / 8
    if signature.size != modulusOctets then
      none
    else
      let signatureRepresentative := os2ip signature
      if signatureRepresentative ≥ key.modulus then
        none
      else
        some {
          modulusBits
          modulusOctets
          value := modPow signatureRepresentative key.exponent key.modulus
        }

private def sha256DigestInfoPrefix : ByteArray :=
  ByteArray.mk #[
    0x30, 0x31, 0x30, 0x0d, 0x06, 0x09, 0x60, 0x86, 0x48, 0x01,
    0x65, 0x03, 0x04, 0x02, 0x01, 0x05, 0x00, 0x04, 0x20
  ]

/-- Construct the one canonical EMSA-PKCS1-v1_5 encoding for a SHA-256 digest.
The fixed DigestInfo includes the required NULL parameters. -/
def encodePKCS1v15Sha256 (digest : ByteArray) (encodedLength : Nat) :
    Except String ByteArray := do
  if digest.size != HaclStar.sha256DigestLen then
    throw "SHA-256 digest must contain exactly 32 bytes"
  let trailerLength := sha256DigestInfoPrefix.size + digest.size
  if encodedLength < trailerLength + 11 then
    throw "RSA modulus is too short for PKCS#1 v1.5 SHA-256"
  let paddingLength := encodedLength - trailerLength - 3
  if paddingLength < 8 then
    throw "PKCS#1 v1.5 padding must contain at least eight FF octets"
  let mut encoded := ByteArray.mk #[0x00, 0x01]
  for _ in [0:paddingLength] do
    encoded := encoded.push 0xff
  pure (((encoded.push 0x00) ++ sha256DigestInfoPrefix) ++ digest)

/-- Exact EMSA-PKCS1-v1_5 verification. No DigestInfo or padding bytes are
parsed loosely: the complete recovered block must equal the canonical block. -/
def emsaPKCS1v15Sha256 (digest encoded : ByteArray) : Bool :=
  match encodePKCS1v15Sha256 digest encoded.size with
  | .ok expected => encoded == expected
  | .error _ => false

/-- MGF1 with SHA-256. -/
def mgf1Sha256 (seed : ByteArray) (maskLength : Nat) :
    Except String ByteArray := do
  let maximumLength : Nat := 0x100000000 * HaclStar.sha256DigestLen
  if maskLength > maximumLength then
    throw "MGF1 mask length exceeds the four-octet counter space"
  let blockCount :=
    (maskLength + HaclStar.sha256DigestLen - 1) / HaclStar.sha256DigestLen
  let mut output := ByteArray.empty
  for counter in [0:blockCount] do
    let counterBytes ← i2osp counter 4
    let digest := HaclStar.sha256 (seed ++ counterBytes)
    if digest.size != HaclStar.sha256DigestLen then
      throw "HACL SHA-256 returned an unexpected digest length"
    output := output ++ digest
  pure (output.extract 0 maskLength)

private def xorBytes (left right : ByteArray) : Option ByteArray := Id.run do
  if left.size != right.size then
    return none
  let mut output := ByteArray.empty
  for index in [0:left.size] do
    output := output.push (left.get! index ^^^ right.get! index)
  return some output

/-- RFC 8017 EMSA-PSS-VERIFY specialized to SHA-256 and MGF1-SHA256.
`saltLength` is an explicit policy input; it is never inferred from the
encoded message. -/
def emsaPSSSha256
    (digest encoded : ByteArray) (encodedBits saltLength : Nat) : Bool := Id.run do
  if digest.size != HaclStar.sha256DigestLen then
    return false
  let encodedLength := (encodedBits + 7) / 8
  if encoded.size != encodedLength then
    return false
  if encodedLength < HaclStar.sha256DigestLen + saltLength + 2 then
    return false
  if encoded.get! (encodedLength - 1) != 0xbc then
    return false

  let dataBlockLength := encodedLength - HaclStar.sha256DigestLen - 1
  let maskedDataBlock := encoded.extract 0 dataBlockLength
  let encodedHash :=
    encoded.extract dataBlockLength (dataBlockLength + HaclStar.sha256DigestLen)
  let unusedTopBits := encodedLength * 8 - encodedBits
  if unusedTopBits > 7 then
    return false
  let allowedFirstOctet := UInt8.ofNat (0xff >>> unusedTopBits)
  if maskedDataBlock.get! 0 > allowedFirstOctet then
    return false

  let some dataBlockMask :=
    (match mgf1Sha256 encodedHash dataBlockLength with
    | .ok mask => some mask
    | .error _ => none)
    | return false
  let some dataBlock := xorBytes maskedDataBlock dataBlockMask
    | return false
  let dataBlock :=
    dataBlock.set! 0 (dataBlock.get! 0 &&& allowedFirstOctet)
  let paddingLength :=
    encodedLength - HaclStar.sha256DigestLen - saltLength - 2
  for index in [0:paddingLength] do
    if dataBlock.get! index != 0 then
      return false
  if dataBlock.get! paddingLength != 0x01 then
    return false
  let salt := dataBlock.extract (paddingLength + 1) dataBlock.size
  if salt.size != saltLength then
    return false

  let eightZeros := ByteArray.mk (Array.replicate 8 0)
  let recomputedHash := HaclStar.sha256 ((eightZeros ++ digest) ++ salt)
  return recomputedHash.size == HaclStar.sha256DigestLen &&
    recomputedHash == encodedHash

/-- Verify an RSA signature over an already computed SHA-256 digest. -/
def verifyDigest
    (key : RSAPublicKey) (scheme : Scheme)
    (digest signature : ByteArray) : Bool := Id.run do
  if digest.size != HaclStar.sha256DigestLen then
    return false
  let some representative := recoverRepresentative key signature
    | return false
  match scheme with
  | .pkcs1v15Sha256 =>
    let some encoded :=
      (match i2osp representative.value representative.modulusOctets with
      | .ok bytes => some bytes
      | .error _ => none)
      | return false
    return emsaPKCS1v15Sha256 digest encoded
  | .pssSha256 saltLength =>
    let encodedBits := representative.modulusBits - 1
    let encodedLength := (encodedBits + 7) / 8
    let some encoded :=
      (match i2osp representative.value encodedLength with
      | .ok bytes => some bytes
      | .error _ => none)
      | return false
    return emsaPSSSha256 digest encoded encodedBits saltLength

/-- Verify an RSA SHA-256 signature over `message`. -/
def verify
    (key : RSAPublicKey) (scheme : Scheme)
    (message signature : ByteArray) : Bool :=
  verifyDigest key scheme (HaclStar.sha256 message) signature

end RSA
end X509
end TLS13
