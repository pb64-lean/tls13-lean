import Tls.Record

/-!
Focused RFC 9846 §5.2 boundary checks for `TLSInnerPlaintext`. The outer
`TLSCiphertext` allowance is deliberately larger, so the oversized `open` case
constructs an authenticated record directly and verifies that the inner limit,
not outer framing or authentication, rejects it.
-/

open Tls

private def repeated (n : Nat) (byte : UInt8) : ByteArray :=
  ByteArray.mk (Array.replicate n byte)

private def keys : Record.TrafficKeys := {
  secret := repeated TLS13.KeySchedule.hashLen 0x00
  key := repeated Record.aeadKeyLength 0x11
  iv := repeated Record.aeadIvLength 0x22
}

private def check (label : String) (condition : Bool) : IO Unit := do
  unless condition do
    throw (IO.userError label)

private def unwrap (label : String) (result : Except Record.Error α) : IO α :=
  match result with
  | .ok value => pure value
  | .error error => throw (IO.userError s!"{label}: unexpected error: {error}")

private def expectInnerPlaintextTooLong (label : String) (expected : Nat)
    (result : Except Record.Error α) : IO Unit :=
  match result with
  | .error (.innerPlaintextTooLong actual) =>
      check s!"{label}: reported length {actual}, expected {expected}"
        (actual == expected)
  | .error error => throw (IO.userError s!"{label}: wrong error: {error}")
  | .ok _ => throw (IO.userError s!"{label}: unexpectedly succeeded")

/-- Build an authenticated record without using `seal`, so `open` is tested
independently of `seal`'s matching length guard. -/
private def authenticatedRecord (contentType : Record.ContentType)
    (fragment : ByteArray) (paddingLength : Nat) :
    Except Record.Error Record.RawRecord := do
  let nonce ← keys.nonce
  pure {
    contentType := .applicationData
    legacyVersion := Record.legacyRecordVersion
    fragment := Record.sealedCiphertext keys contentType fragment paddingLength nonce
  }

def main : IO Unit := do
  check "TLSInnerPlaintext maximum is not 2^14 + 1"
    (Record.maxInnerPlaintextLength == (1 <<< 14) + 1)

  let fullFragment := repeated Record.maxPlaintextLength 0x5a
  let rejectedInnerLength := Record.maxInnerPlaintextLength + 1

  let (sealedNext, wire) ← unwrap "seal at TLSInnerPlaintext maximum"
    (Record.seal keys .applicationData fullFragment 0)
  check "seal at maximum did not advance exactly once" (sealedNext.seq == 1)
  check "seal at maximum emitted the wrong wire length"
    (wire.size == Record.headerLength + Record.maxInnerPlaintextLength +
      Record.aeadTagLength)

  expectInnerPlaintextTooLong "seal above TLSInnerPlaintext maximum"
    rejectedInnerLength (Record.seal keys .applicationData fullFragment 1)

  -- Keep one padding byte in the accepted `open` case so the backward scan and
  -- recovered padding count are exercised at the boundary too.
  let paddedFragment := repeated (Record.maxPlaintextLength - 1) 0x6b
  let acceptedRecord ← unwrap "construct maximum authenticated record"
    (authenticatedRecord .applicationData paddedFragment 1)
  let (openedNext, plaintext) ← unwrap "open at TLSInnerPlaintext maximum"
    (Record.open keys acceptedRecord)
  check "open at maximum did not advance exactly once" (openedNext.seq == 1)
  check "open at maximum changed the fragment" (plaintext.fragment == paddedFragment)
  check "open at maximum changed the content type"
    (plaintext.contentType == .applicationData)
  check "open at maximum changed the padding" (plaintext.paddingLength == 1)

  let oversizedRecord ← unwrap "construct oversized authenticated record"
    (authenticatedRecord .applicationData fullFragment 1)
  expectInnerPlaintextTooLong "open above TLSInnerPlaintext maximum"
    rejectedInnerLength (Record.open keys oversizedRecord)
