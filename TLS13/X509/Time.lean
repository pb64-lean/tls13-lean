module

public import TLS13.X509.DER

public section

/-!
Strict RFC 5280 validity-time parsing.

Certificate times are kept both as their calendar fields and as signed Unix
seconds. The latter is deliberately a plain `Int`: path validation only needs
a stable, comparable UTC instant and does not need the platform time-zone
types.
-/

namespace TLS13
namespace X509

/-- A UTC calendar instant and its comparable Unix epoch value. -/
structure Timestamp where
  year : Nat
  month : Nat
  day : Nat
  hour : Nat
  minute : Nat
  second : Nat
  unixSeconds : Int
  deriving Repr, BEq, Inhabited

namespace Time

def isLeapYear (year : Nat) : Bool :=
  year % 4 == 0 && (year % 100 != 0 || year % 400 == 0)

def daysInMonth (year month : Nat) : Option Nat :=
  match month with
  | 1 | 3 | 5 | 7 | 8 | 10 | 12 => some 31
  | 4 | 6 | 9 | 11 => some 30
  | 2 => some (if isLeapYear year then 29 else 28)
  | _ => none

/-- Validate a UTC calendar value and compute signed Unix seconds.

Second 60 is accepted for ASN.1 leap-second notation and naturally normalizes
to the first Unix second of the following minute. -/
def ofComponents (year month day hour minute second : Nat) :
    Except String Timestamp := do
  let some monthDays := daysInMonth year month
    | throw s!"X.509 time has invalid month {month}"
  if day == 0 || day > monthDays then
    throw s!"X.509 time has invalid day {day} for {year}-{month}"
  if hour > 23 then
    throw s!"X.509 time has invalid hour {hour}"
  if minute > 59 then
    throw s!"X.509 time has invalid minute {minute}"
  if second > 60 then
    throw s!"X.509 time has invalid second {second}"
  -- Proleptic Gregorian days-from-civil calculation. It covers the complete
  -- four-digit GeneralizedTime range, including ASN.1 year 0000.
  let calendarYear : Int := Int.ofNat year
  let adjustedYear := if month > 2 then calendarYear else calendarYear - 1
  let era := (if adjustedYear ≥ 0 then adjustedYear else adjustedYear - 399).tdiv 400
  let yearOfEra := adjustedYear - era * 400
  let adjustedMonth : Int :=
    Int.ofNat month + (if month > 2 then -3 else 9)
  let dayOfYear := (153 * adjustedMonth + 2).tdiv 5 + Int.ofNat day - 1
  let dayOfEra :=
    yearOfEra * 365 + yearOfEra.tdiv 4 - yearOfEra.tdiv 100 + dayOfYear
  let days := era * 146097 + dayOfEra - 719468
  let unixSeconds :=
    days * 86400 + Int.ofNat hour * 3600 + Int.ofNat minute * 60 + Int.ofNat second
  pure { year, month, day, hour, minute, second, unixSeconds }

private def readDecimal (bytes : ByteArray) (start count : Nat) (field : String) :
    Except String Nat := do
  if start + count > bytes.size then
    throw s!"truncated X.509 time {field}"
  let mut value := 0
  for offset in [start:start + count] do
    let octet := bytes.get! offset
    if octet < 0x30 || octet > 0x39 then
      throw s!"X.509 time {field} contains a non-decimal byte"
    value := value * 10 + (octet.toNat - 0x30)
  pure value

private def parseFields (bytes : ByteArray) (yearDigits : Nat) :
    Except String Timestamp := do
  let expectedSize := yearDigits + 11
  if bytes.size != expectedSize then
    throw s!"X.509 time must contain exactly {expectedSize} bytes"
  if bytes.get! (bytes.size - 1) != 0x5a then
    throw "X.509 time must use uppercase Z (UTC)"
  let encodedYear ← readDecimal bytes 0 yearDigits "year"
  let year :=
    if yearDigits == 2 then
      if encodedYear ≥ 50 then 1900 + encodedYear else 2000 + encodedYear
    else
      encodedYear
  let month ← readDecimal bytes yearDigits 2 "month"
  let day ← readDecimal bytes (yearDigits + 2) 2 "day"
  let hour ← readDecimal bytes (yearDigits + 4) 2 "hour"
  let minute ← readDecimal bytes (yearDigits + 6) 2 "minute"
  let second ← readDecimal bytes (yearDigits + 8) 2 "second"
  ofComponents year month day hour minute second

/-- Parse an RFC 5280 `Time` choice. UTCTime uses the mandated 1950/2050
pivot; both forms require seconds and uppercase `Z`, and reject offsets and
fractional seconds. -/
def parse (value : DER.TLV) : Except String Timestamp := do
  if value.tag == DER.Tag.utcTime then
    parseFields value.contents 2
  else if value.tag == DER.Tag.generalizedTime then
    parseFields value.contents 4
  else
    throw s!"validity value has an unexpected tag at offset {value.offset}"

end Time
end X509
end TLS13
