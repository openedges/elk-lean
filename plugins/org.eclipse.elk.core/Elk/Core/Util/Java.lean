import Elk.Core.Util.Ffi
import Elk.Core.Util.FastFloat
/-!
# Java / Rust numeric semantics helpers

Thin helpers that give Lean `Float`, `Int` and `String` the exact semantics the
reference implementations rely on. The oracle for parity is elk-rs, so where
Java and Rust differ (e.g. `f64::min` vs `Math.min` on NaN) the Rust behaviour
is the default and the Java variant carries a `java` prefix.
-/
/-! Float literals as global constants (FL): inside branches, loops and specialised code the compiler
shares a literal's `Nat`/`Bool` arguments with unrelated variables (CSE) and then parses it on every
evaluation (`FastFloat.ofScientificImpl`); a top-level constant is a load (PLAN §7.1 items 17, 22). -/
private def fl0p0 : Float := 0.0
private def fl1e16 : Float := 1e16
private def fl180p0 : Float := 180.0
private def fl3p141592653589793 : Float := 3.141592653589793

namespace Elk.Core.Util

/-- Positive infinity (`Double.POSITIVE_INFINITY`). -/
def Float.posInf : Float := 1.0 / 0.0
/-- Negative infinity (`Double.NEGATIVE_INFINITY`). -/
def Float.negInf : Float := -1.0 / 0.0
/-- Quiet NaN (`Double.NaN`). -/
def Float.nan : Float := 0.0 / 0.0
/-- `Double.MAX_VALUE` = `f64::MAX`. -/
def Float.maxValue : Float := Float.ofBits 0x7FEFFFFFFFFFFFFF
/-- `-Double.MAX_VALUE` = `f64::MIN`. -/
def Float.minValue : Float := Float.ofBits 0xFFEFFFFFFFFFFFFF
/-- `Double.MIN_VALUE` (smallest positive subnormal, `4.9e-324`). -/
def Float.minPositive : Float := Float.ofBits 1
/-- `f64::EPSILON` / `Math.ulp(1.0)`. -/
def Float.epsilon : Float := Float.ofBits 0x3CB0000000000000

/-- Rust `f64::min` (IEEE minNum: ignores a NaN operand). -/
@[inline] def fmin (a b : Float) : Float :=
  if a.isNaN then b else if b.isNaN then a else if a < b then a else b

/-- Rust `f64::max` (IEEE maxNum: ignores a NaN operand). -/
@[inline] def fmax (a b : Float) : Float :=
  if a.isNaN then b else if b.isNaN then a else if a > b then a else b

/-- Java `Math.min(double, double)`: NaN propagates, `-0.0 < 0.0`. -/
def javaMin (a b : Float) : Float :=
  if a.isNaN || b.isNaN then Float.nan
  else if a == 0.0 && b == 0.0 then (if a.toBits == 0x8000000000000000 then a else b)
  else if a <= b then a else b

/-- Java `Math.max(double, double)`: NaN propagates, `0.0 > -0.0`. -/
def javaMax (a b : Float) : Float :=
  if a.isNaN || b.isNaN then Float.nan
  else if a == 0.0 && b == 0.0 then (if a.toBits == 0 then a else b)
  else if a >= b then a else b

/-- Rust `x as i64` / Java `(long) x`: truncation toward zero, saturating, NaN → 0. -/
@[inline] def Float.toIntTrunc (x : Float) : Int := x.toInt64.toInt

/-- Rust `x.round() as i64`: round half away from zero, then truncate/saturate. -/
@[inline] def Float.roundToInt (x : Float) : Int := x.round.toInt64.toInt

/-- Rust `x.floor() as i64`. -/
@[inline] def Float.floorToInt (x : Float) : Int := x.floor.toInt64.toInt

/-- Rust `x.ceil() as i64`. -/
@[inline] def Float.ceilToInt (x : Float) : Int := x.ceil.toInt64.toInt

/-- Java `Math.round(double)` (`floor(x + 0.5)` with correct handling of
`0.49999999999999994`, NaN → 0, saturating). Only use where the reference
explicitly emulates Java rounding; elk-rs normally uses `f64::round`. -/
def Float.javaRound (x : Float) : Int :=
  if x.isNaN then 0
  else
    let r := x.floor
    let diff := x - r
    (if diff >= 0.5 then r + 1.0 else r).toInt64.toInt

/-- Rust `x as f32 as f64` / Java `(float)` arithmetic emulation. -/
@[inline] def Float.toF32 (x : Float) : Float := x.toFloat32.toFloat

/-- `Float.ofInt`-style conversion used everywhere (`i as f64`). -/
@[inline] def Int.toFloat (i : Int) : Float :=
  -- `FastFloat.ofInt` (not `Float.ofInt`): the compiler inlines this abbreviation after the `csimp`
  -- pass, so a plain `Float.ofInt` here would call the core (GMP) conversion at every call site
  FastFloat.ofInt i

/-- Signed interpretation of the raw bits (Java `long`). Built from `UInt64` operations: the
literal `2^64` and the intermediate `Nat`s of `b.toNat - 2^64` are GMP numbers. -/
private def bitsSigned (b : UInt64) : Int :=
  if b ≥ 0x8000000000000000 then Int.negSucc (~~~b).toNat else Int.ofNat b.toNat

/-- `compare (bitsSigned a) (bitsSigned b)` without building the `Int`s (most bit patterns of
doubles are beyond the small-`Int` range): signed order is unsigned order with the sign bit flipped. -/
@[inline] private def compareBitsSigned (a b : UInt64) : Ordering :=
  compare (a ^^^ 0x8000000000000000) (b ^^^ 0x8000000000000000)

/-- Java `Double.compare` / Rust `f64::total_cmp`-like ordering:
`-0.0 < 0.0`, every NaN is equal to every NaN and greater than everything else. -/
def Float.compareJava (a b : Float) : Ordering :=
  if a < b then .lt
  else if a > b then .gt
  else
    let ba := if a.isNaN then 0x7ff8000000000000 else a.toBits
    let bb := if b.isNaN then 0x7ff8000000000000 else b.toBits
    compareBitsSigned ba bb

/-- Rust `partial_cmp(..).unwrap_or(Equal)`: NaN compares equal to everything. -/
@[inline] def Float.comparePartial (a b : Float) : Ordering :=
  if a < b then .lt else if a > b then .gt else .eq

/-- Rust `f64::total_cmp`. -/
def Float.compareTotal (a b : Float) : Ordering :=
  let key (x : Float) : UInt64 :=
    let bits := x.toBits
    if bits ≥ 0x8000000000000000 then bits ^^^ 0x7FFFFFFFFFFFFFFF else bits
  compareBitsSigned (key a) (key b)

/-- Java `Double.doubleToLongBits` equality (`equals`): NaN == NaN, `-0.0 != 0.0`. -/
def Float.equalsJava (a b : Float) : Bool :=
  (a.isNaN && b.isNaN) || a.toBits == b.toBits

/-- Java `Math.signum` for doubles as an `Int`. -/
def Float.signumInt (x : Float) : Int := if x < 0.0 then -1 else if x > 0.0 then 1 else 0

/-- Java `Math.signum(double)` (keeps NaN and signed zero). -/
def Float.signum (x : Float) : Float := if x < 0.0 then -1.0 else if x > 0.0 then 1.0 else x

/-- `Math.toRadians`. -/
@[inline] def Float.toRadians (deg : Float) : Float := deg / fl180p0 * fl3p141592653589793

/-- `Math.toDegrees`. -/
@[inline] def Float.toDegrees (rad : Float) : Float := rad * fl180p0 / fl3p141592653589793

/-- `Math.PI`. -/
def Float.pi : Float := 3.141592653589793
/-- `Math.E`. -/
def Float.e : Float := 2.718281828459045

/-- Java integer division (truncates toward zero). -/
@[inline] def Int.jdiv (a b : Int) : Int := Int.tdiv a b
/-- Java integer remainder (sign of the dividend). -/
@[inline] def Int.jmod (a b : Int) : Int := Int.tmod a b

/-- Two's complement bit pattern of an `Int` as `UInt64` (Rust `as u64`). -/
def Int.toUInt64Wrap (i : Int) : UInt64 :=
  -- `-(n + 1)` is `~~~n` in two's complement (no `2^64` literal, no GMP for small values)
  match i with
  | .ofNat n => UInt64.ofNat n
  | .negSucc n => ~~~(UInt64.ofNat n)

/-- Rust `i64 as i32` / Java `(int) long`: wrap to 32 bits. -/
def Int.wrap32 (i : Int) : Int := (Int32.ofInt i).toInt

/-- `Int` from a `UInt32` interpreted as Java `int` (two's complement). -/
def UInt32.toIntSigned (u : UInt32) : Int :=
  if u ≥ 0x80000000 then Int.negSucc (~~~u).toNat else Int.ofNat u.toNat

/-- `Int` from a `UInt64` interpreted as Java `long`. -/
def UInt64.toIntSigned (u : UInt64) : Int := bitsSigned u

/-! ## Number parsing (Rust `str::parse` grammar, correctly rounded via `strtod`) -/

private def isDigitList : List Char → Bool
  | [] => true
  | c :: cs => c.isDigit && isDigitList cs

/-- Validates the Rust `f64::from_str` grammar:
`[+-]? (digits [. digits*]? | . digits) ([eE] [+-]? digits)?` or `inf`,
`infinity`, `nan` (case-insensitive). No surrounding whitespace. -/
def isRustFloatLexeme (s : String) : Bool := Id.run do
  let cs := s.toList
  let cs := match cs with
    | '+' :: rest => rest
    | '-' :: rest => rest
    | rest => rest
  if cs.isEmpty then return false
  let lower := String.ofList (cs.map Char.toLower)
  if lower == "inf" || lower == "infinity" || lower == "nan" then return true
  -- mantissa
  let (intPart, rest) := cs.span Char.isDigit
  let (fracPart, rest, hadDot) := match rest with
    | '.' :: r => let (f, r2) := r.span Char.isDigit; (f, r2, true)
    | r => ([], r, false)
  if intPart.isEmpty && fracPart.isEmpty then return false
  let _ := hadDot
  match rest with
  | [] => return true
  | 'e' :: r | 'E' :: r =>
    let r := match r with
      | '+' :: r2 => r2
      | '-' :: r2 => r2
      | r2 => r2
    return !r.isEmpty && isDigitList r
  | _ => return false

/-- Rust `s.parse::<f64>()` (also the behaviour of elk-rs option parsing). -/
def parseFloat? (s : String) : Option Float :=
  if isRustFloatLexeme s then some (strtodUnchecked s) else none

/-- Rust `s.parse::<i32>()`: optional sign, decimal digits, within `i32`. -/
def parseInt32? (s : String) : Option Int := Id.run do
  let cs := s.toList
  let (neg, digits) := match cs with
    | '+' :: rest => (false, rest)
    | '-' :: rest => (true, rest)
    | rest => (false, rest)
  if digits.isEmpty || !isDigitList digits then return none
  let n : Nat := digits.foldl (fun acc c => acc * 10 + (c.toNat - '0'.toNat)) 0
  let v : Int := if neg then -(n : Int) else (n : Int)
  if v < -2147483648 || v > 2147483647 then return none
  return some v

/-- Rust `s.parse::<i64>()`. -/
def parseInt64? (s : String) : Option Int := Id.run do
  let cs := s.toList
  let (neg, digits) := match cs with
    | '+' :: rest => (false, rest)
    | '-' :: rest => (true, rest)
    | rest => (false, rest)
  if digits.isEmpty || !isDigitList digits then return none
  let n : Nat := digits.foldl (fun acc c => acc * 10 + (c.toNat - '0'.toNat)) 0
  let v : Int := if neg then -(n : Int) else (n : Int)
  if v < -9223372036854775808 || v > 9223372036854775807 then return none
  return some v

/-- Rust `f64` `Display`: shortest digits, never exponent notation, `12` for `12.0`. -/
def Float.toRustDisplay (x : Float) : String :=
  if x.isNaN then "NaN"
  else if x.isInf then (if x > fl0p0 then "inf" else "-inf")
  else if x == x.floor && x.abs < fl1e16 then
    -- integral: print without fraction
    let s := Float.toShortest x
    if s.endsWith ".0" then (s.dropEnd 2).toString else s
  else
    Float.toShortest x

/-- The shortest round-trip decimal digits of a finite, non-zero `x` (no leading or trailing zeros)
and the exponent `e` with `|x| = 0.d₁d₂…dₙ × 10^e`, from `Float.toShortest` (`12.0`, `0.1`, `1e21`,
`1.5e-7`). -/
private def shortestDigits (x : Float) : String × Int := Id.run do
  let s := Float.toShortest x.abs
  let (mant, exp) := match s.splitOn "e" with
    | [m, e] => (m, (e.toInt?).getD (((e.drop 1).toString.toInt?).getD 0))
    | _ => (s, 0)
  let (intPart, fracPart) := match mant.splitOn "." with
    | [i, f] => (i, f)
    | _ => (mant, "")
  let all := intPart ++ fracPart
  let lead := (all.toList.takeWhile (· == '0')).length
  let digits := String.ofList ((all.toList.drop lead).reverse.dropWhile (· == '0')).reverse
  -- 0.d₁… × 10^e: the decimal point sits after `intPart`, minus the leading zeros
  return (digits, exp + (intPart.length : Int) - (lead : Int))

/-- Java `Double.toString(d)` / `StringBuilder.append(double)` (JDK 19+: shortest round-trip
digits): `NaN`, `Infinity`, `-0.0`; for `10⁻³ ≤ |d| < 10⁷` plain decimal with at least one fraction
digit (`12.0`, `0.001`, `50.5`), otherwise computerized scientific notation (`1.0E7`, `1.5E-7`). -/
def Float.toJavaString (x : Float) : String := Id.run do
  if x.isNaN then return "NaN"
  if x.isInf then return if x > 0.0 then "Infinity" else "-Infinity"
  let sign := if x < 0.0 || (x == 0.0 && x.toBits == 0x8000000000000000) then "-" else ""
  if x == 0.0 then return sign ++ "0.0"
  let (digits, e) := shortestDigits x
  let ds := digits.toList
  let ax := x.abs
  if ax >= 1e-3 && ax < 1e7 then
    if e <= 0 then
      return sign ++ "0." ++ String.ofList (List.replicate e.natAbs '0') ++ digits
    else
      let k := e.toNat
      let intDigits := String.ofList (ds.take k) ++ String.ofList (List.replicate (k - min k ds.length) '0')
      let frac := String.ofList (ds.drop k)
      return sign ++ intDigits ++ "." ++ (if frac.isEmpty then "0" else frac)
  else
    let first := String.ofList (ds.take 1)
    let rest := String.ofList (ds.drop 1)
    return sign ++ first ++ "." ++ (if rest.isEmpty then "0" else rest) ++ "E" ++ toString (e - 1)

/-! ## Strings -/

/-- Java `String.trim()` (ASCII whitespace). -/
@[inline] def String.jtrim (s : String) : String := s.trimAscii.toString

/-- Java `String.isEmpty()` after trim, i.e. blank. -/
@[inline] def String.isBlank (s : String) : Bool := s.trimAscii.toString.isEmpty

end Elk.Core.Util
