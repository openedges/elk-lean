import Elk.Core.Util.Java
/-!
# elk-rs `p3order/random_trace.rs` (no Java counterpart)

Shared tracing of the random draws of the crossing minimisation, enabled with the environment
variable `CROSSMIN_RANDOM_TRACE` (read once at startup, Rust `LazyLock`). Every traced draw prints

    [random #N] method() = value @ location

to stderr; the counter `N` is process-wide (Rust `static COUNTER: AtomicUsize`) and is reset by
`LayerSweepCrossingMinimizer.initialize` (`resetCounter`). The tracing never changes a value, so
it has no influence on the layout.

Value formats as in Rust: `next_long`/`next_int` decimal, `next_boolean` `true`/`false`,
`next_float`/`next_double` `format!("{value:.7}")` (`formatFixed 7`).
-/
namespace Elk.Alg.Layered.P3Order

namespace RandomTrace

/-- `CROSSMIN_RANDOM_TRACE` is set in the environment (Rust `static CROSSMIN_RANDOM_TRACE`). -/
builtin_initialize enabledFlag : Bool ← return (← IO.getEnv "CROSSMIN_RANDOM_TRACE").isSome

/-- The process-wide draw counter (Rust `static COUNTER`). -/
builtin_initialize counter : IO.Ref Nat ← IO.mkRef 0

/-- `is_enabled()`. -/
@[inline] def isEnabled : Bool := enabledFlag

/-- `reset_counter()`: back to zero (once per graph layout). -/
def resetCounter : BaseIO Unit := counter.set 0

/-- The decimal digits of `x = m * 2^e` scaled by `10^digits`, rounded half to even. -/
private def scaledHalfEven (m : Nat) (e : Int) (digits : Nat) : Nat :=
  let scale := 10 ^ digits
  if e >= 0 then m * scale * 2 ^ e.toNat
  else
    let den := 2 ^ (-e).toNat
    let num := m * scale
    let quo := num / den
    let rem := num % den
    if 2 * rem > den then quo + 1
    else if 2 * rem == den then (if quo % 2 == 1 then quo + 1 else quo)
    else quo

/-- Rust `format!("{:.N}", x)` for an `f64`: the exact binary value rounded half to even to
`digits` decimals; `NaN`, `inf`, `-inf`; the minus sign is kept for negative values and `-0.0`. -/
def formatFixed (digits : Nat) (x : Float) : String :=
  if x.isNaN then "NaN"
  else if x.isInf then (if x > 0.0 then "inf" else "-inf")
  else
    let bits := x.toBits
    let negative := (bits >>> 63) == 1
    let expBits := ((bits >>> 52) &&& 0x7FF).toNat
    let frac := (bits &&& 0xFFFFFFFFFFFFF).toNat
    let q := if expBits == 0 then scaledHalfEven frac (-1074) digits
      else scaledHalfEven (frac + 4503599627370496) ((expBits : Int) - 1075) digits
    let scale := 10 ^ digits
    let fracStr := toString (q % scale)
    let body := if digits == 0 then toString (q / scale)
      else s!"{q / scale}." ++ ("".pushn '0' (digits - fracStr.length)) ++ fracStr
    if negative then "-" ++ body else body

/-- `trace(method, value, location)`: prints one line and advances the counter. -/
def trace (method value location : String) : IO Unit := do
  let n ← counter.modifyGet fun n => (n, n + 1)
  IO.eprintln s!"[random #{n}] {method}() = {value} @ {location}"

/-- `trace_next_long(value, location)`: traces (when enabled) and returns `value`. -/
def traceNextLong (value : Int) (location : String) : IO Int := do
  if isEnabled then trace "next_long" (toString value) location
  return value

/-- `trace_next_boolean(value, location)`. -/
def traceNextBoolean (value : Bool) (location : String) : IO Bool := do
  if isEnabled then trace "next_boolean" (toString value) location
  return value

/-- `trace_next_float(value, location)` (the value is the `f64` carrying the `f32` draw). -/
def traceNextFloat (value : Float) (location : String) : IO Float := do
  if isEnabled then trace "next_float" (formatFixed 7 value) location
  return value

/-- `trace_next_double(value, location)`. -/
def traceNextDouble (value : Float) (location : String) : IO Float := do
  if isEnabled then trace "next_double" (formatFixed 7 value) location
  return value

/-- `trace_next_int(value, location)`. -/
def traceNextInt (value : Int) (location : String) : IO Int := do
  if isEnabled then trace "next_int" (toString value) location
  return value

end RandomTrace

end Elk.Alg.Layered.P3Order
