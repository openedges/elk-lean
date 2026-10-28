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

/-- Order key of Java `Double.compare`: `compare a.javaOrderKey b.javaOrderKey = Float.compareJava a b`
(`-0.0 < 0.0`, every NaN equal and above `+∞`). Sorting by these keys with any stable sort gives
the result of a Java `List.sort`/`Collections.sort` with a `Double.compare` comparator on the same
keys (a consistent total order, so TimSort's result is the unique stable order). -/
@[inline] def Float.javaOrderKey (x : Float) : UInt64 :=
  let b := if x.isNaN then 0x7ff8000000000000 else x.toBits
  if b ≥ 0x8000000000000000 then ~~~b else b ^^^ 0x8000000000000000

/-- `a` before `b` in `Double.compare` order (the keys of an unboxed `FloatArray`). -/
@[inline] private def javaKeyLt (a b : Float) : Bool := Float.javaOrderKey a < Float.javaOrderKey b

/-- Whether the keys are in non-decreasing `Double.compare` order. -/
private def javaKeysSorted (keys : FloatArray) (i : Nat) : Bool :=
  if h : i + 1 < keys.size then
    if javaKeyLt keys[i + 1] keys[i] then false else javaKeysSorted keys (i + 1)
  else true
  termination_by keys.size - i

/-- Merges the sorted index runs `src[i..iEnd)` and `src[j..jEnd)` into `dst` from `k` on; an
element of the right run goes first only if its key is strictly smaller (stable). -/
private partial def javaKeyMergeRuns (keys : FloatArray) (src dst : Array Nat) (i iEnd j jEnd k : Nat) :
    Array Nat :=
  if i < iEnd then
    if j < jEnd then
      let a := src[i]!
      let b := src[j]!
      if javaKeyLt (keys.get! b) (keys.get! a) then
        javaKeyMergeRuns keys src (dst.set! k b) i iEnd (j + 1) jEnd (k + 1)
      else
        javaKeyMergeRuns keys src (dst.set! k a) (i + 1) iEnd j jEnd (k + 1)
    else javaKeyMergeRuns keys src (dst.set! k src[i]!) (i + 1) iEnd j jEnd (k + 1)
  else if j < jEnd then javaKeyMergeRuns keys src (dst.set! k src[j]!) i iEnd (j + 1) jEnd (k + 1)
  else dst

/-- One bottom-up merge pass with run width `w`, from `lo` on. -/
private partial def javaKeyMergePass (keys : FloatArray) (src dst : Array Nat) (w lo : Nat) : Array Nat :=
  let n := src.size
  if lo < n then
    let mid := min (lo + w) n
    let hi := min (lo + 2 * w) n
    javaKeyMergePass keys src (javaKeyMergeRuns keys src dst lo mid mid hi lo) w (lo + 2 * w)
  else dst

/-- Bottom-up merge passes until one run covers everything. -/
private partial def javaKeyMergeAll (keys : FloatArray) (src dst : Array Nat) (w : Nat) : Array Nat :=
  if w < src.size then
    let merged := javaKeyMergePass keys src dst w 0
    javaKeyMergeAll keys merged src (2 * w)
  else src

/-- The elements stably sorted by the Java order of their keys (`List.sort` with
`Double.compare(key x, key y)`: a consistent comparator, so the unique stable order). Returns the
input when it is already sorted (no comparison for fewer than two elements). -/
def javaSortByDoubleKeys {α : Type} [Inhabited α] (xs : Array α) (keys : FloatArray) : Array α :=
  if xs.size < 2 then xs else
  if javaKeysSorted keys 0 then xs
  else (javaKeyMergeAll keys (Array.range keys.size) (Array.replicate keys.size 0) 1).map fun i => xs[i]!

/-- `javaSortByDoubleKeys` with a key function. -/
@[inline] def javaSortByDouble {α : Type} [Inhabited α] (xs : Array α) (key : α → Float) : Array α :=
  if xs.size < 2 then xs else
  javaSortByDoubleKeys xs (xs.foldl (init := FloatArray.emptyWithCapacity xs.size) fun ks x => ks.push (key x))

/-- Java `DoubleStream.average()` of a sequential stream (JDK 21 `DoublePipeline.average`): Kahan
summation (`Collectors.sumWithCompensation`) plus the simple sum, final value
`Collectors.computeFinalSum` (`sum - compensation`, or the simple sum when that is NaN and the simple
sum infinite) divided by the count; `none` for no element (`OptionalDouble.empty()`). -/
def javaDoubleAverage (xs : Array Float) : Option Float := Id.run do
  if xs.isEmpty then return none
  let mut sum := fl0p0
  let mut comp := fl0p0
  let mut simple := fl0p0
  for v in xs do
    let tmp := v - comp
    let velvel := sum + tmp
    comp := (velvel - sum) - tmp
    sum := velvel
    simple := simple + v
  let total := sum - comp
  let total := if total.isNaN && simple.isInf then simple else total
  return some (total / Float.ofNat xs.size)

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

/-- Constants of fdlibm's `__ieee754_log` (`e_log.c`), by bit pattern. -/
private def logLn2Hi : Float := Float.ofBits 0x3fe62e42fee00000
private def logLn2Lo : Float := Float.ofBits 0x3dea39ef35793c76
private def logTwo54 : Float := Float.ofBits 0x4350000000000000
private def logLg1 : Float := Float.ofBits 0x3FE5555555555593
private def logLg2 : Float := Float.ofBits 0x3FD999999997FA04
private def logLg3 : Float := Float.ofBits 0x3FD2492494229359
private def logLg4 : Float := Float.ofBits 0x3FCC71C51D8E78AF
private def logLg5 : Float := Float.ofBits 0x3FC7466496CB03DE
private def logLg6 : Float := Float.ofBits 0x3FC39A09D078C69F
private def logLg7 : Float := Float.ofBits 0x3FC2F112DF3E5244
private def logHalf : Float := 0.5
private def logThird : Float := 0.33333333333333333
private def logOne : Float := 1.0
private def logTwo : Float := 2.0

/-- Java `StrictMath.log` (fdlibm `__ieee754_log`, JDK `FdLibm.Log`). The reference JVM's `Math.log`
(HotSpot on aarch64, the machine of the ELK Java baselines) returns the same values (200,000 random
arguments: 0 differences), while the C library's `log` (`Float.log`) differs by one ulp for about
1% of the arguments. Used where ELK Java calls `Math.log` and the result must equal Java's
(the Eades model of `org.eclipse.elk.alg.force`). -/
def javaLog (x : Float) : Float := Id.run do
  let bits := x.toBits
  let hxU : UInt32 := (bits >>> 32).toUInt32
  let mut hx : Int := hxU.toInt32.toInt
  let lx : UInt64 := bits &&& 0xffffffff
  let mut x := x
  let mut k : Int := 0
  if hx < 0x00100000 then
    -- zero, negative or subnormal: log(±0) = -inf, log(negative) = NaN
    if (hxU &&& 0x7fffffff) == 0 && lx == 0 then return Float.negInf
    if hx < 0 then return Float.nan
    k := k - 54
    x := x * logTwo54
    hx := (x.toBits >>> 32).toUInt32.toInt32.toInt
  if hx ≥ 0x7ff00000 then return x + x
  let hxN : Nat := hx.toNat
  k := k + (Int.ofNat (hxN >>> 20) - 1023)
  let hxM : Nat := hxN &&& 0x000fffff
  let i : Nat := (hxM + 0x95f64) &&& 0x100000
  let hi : Nat := hxM ||| (i ^^^ 0x3ff00000)
  x := Float.ofBits ((hi.toUInt64 <<< 32) ||| (x.toBits &&& 0xffffffff))
  k := k + Int.ofNat (i >>> 20)
  let f := x - logOne
  if (0x000fffff &&& (2 + hxM)) < 3 then
    -- |f| < 2^-20
    if f == 0.0 then
      if k == 0 then return 0.0
      let dk := Float.ofInt k
      return dk * logLn2Hi + dk * logLn2Lo
    let r := f * f * (logHalf - logThird * f)
    if k == 0 then return f - r
    let dk := Float.ofInt k
    return dk * logLn2Hi - ((r - dk * logLn2Lo) - f)
  let s := f / (logTwo + f)
  let dk := Float.ofInt k
  let z := s * s
  let ii : Int := Int.ofNat hxM - 0x6147a
  let w := z * z
  let jj : Int := 0x6b851 - Int.ofNat hxM
  let t1 := w * (logLg2 + w * (logLg4 + w * logLg6))
  let t2 := z * (logLg1 + w * (logLg3 + w * (logLg5 + w * logLg7)))
  let r := t2 + t1
  -- C `i |= j; if (i > 0)` on 32-bit ints
  if ii ≥ 0 && jj ≥ 0 && (ii > 0 || jj > 0) then
    let hfsq := logHalf * f * f
    if k == 0 then return f - (hfsq - s * (hfsq + r))
    return dk * logLn2Hi - ((hfsq - (s * (hfsq + r) + dk * logLn2Lo)) - f)
  else
    if k == 0 then return f - s * (f - r)
    return dk * logLn2Hi - ((s * (f - r) - dk * logLn2Lo) - f)

/-! ### `Math.sin`/`Math.cos`/`Math.atan2`/`Math.acos` of the reference JVM

The ELK Java baselines run on HotSpot (Temurin 21, aarch64). There `Math.atan2`, `Math.atan`,
`Math.acos` and `Math.asin` are not intrinsified and equal `StrictMath` (fdlibm, JDK `FdLibm`), while
`Math.sin`/`Math.cos` are the HotSpot stubs of `macroAssembler_aarch64_trig.cpp`: fdlibm's algorithm
with fused multiply-adds (`fmadd`/`fmsub`/`fnmsub`) in the polynomials and the medium argument
reduction, and `__kernel_cos` reading the high word of the *unreduced* argument (so a reduced
argument always takes the `qx = 0.28125` branch). They differ from `StrictMath` for about 5% and
from the C library (`Float.sin`/`Float.cos`) for about 7% of the arguments; `atan2`/`acos` of the C
library differ from fdlibm for about 16%. The ports below were checked bit for bit against the JVM
(1,000,000 random arguments each for typical, near-`k·π/2` and up to `2^19·π/2` magnitudes: 0
differences); the large-argument reduction of the stubs (`|x| > 2^19·π/2`, vectorised
`__kernel_rem_pio2` with fused operations) is not ported — such arguments use the C library. -/

private def trigS1 : Float := Float.ofBits 0xBFC5555555555549
private def trigS2 : Float := Float.ofBits 0x3F8111111110F8A6
private def trigS3 : Float := Float.ofBits 0xBF2A01A019C161D5
private def trigS4 : Float := Float.ofBits 0x3EC71DE357B1FE7D
private def trigS5 : Float := Float.ofBits 0xBE5AE5E68A2B9CEB
private def trigS6 : Float := Float.ofBits 0x3DE5D93A5ACFD57C
private def trigC1 : Float := Float.ofBits 0x3FA555555555554C
private def trigC2 : Float := Float.ofBits 0xBF56C16C16C15177
private def trigC3 : Float := Float.ofBits 0x3EFA01A019CB1590
private def trigC4 : Float := Float.ofBits 0xBE927E4F809C52AD
private def trigC5 : Float := Float.ofBits 0x3E21EE9EBDB4B1C4
private def trigC6 : Float := Float.ofBits 0xBDA8FAE9BE8838D4
private def trigHalf : Float := 0.5
private def trigOne : Float := 1.0
private def trigQx : Float := 0.28125
private def trigInvPio2 : Float := Float.ofBits 0x3FE45F306DC9C883
private def trigPio2_1 : Float := Float.ofBits 0x3FF921FB54400000
private def trigPio2_1t : Float := Float.ofBits 0x3DD0B4611A626331
private def trigPio2_2 : Float := Float.ofBits 0x3DD0B4611A600000
private def trigPio2_2t : Float := Float.ofBits 0x3BA3198A2E037073
private def trigPio2_3 : Float := Float.ofBits 0x3BA3198A2E000000
private def trigPio2_3t : Float := Float.ofBits 0x397B839A252049C1

/-- fdlibm `npio2_hw` (the high words of `n·π/2`, `n = 1 .. 32`). -/
private def trigNpio2Hw : Array UInt32 := #[
  0x3FF921FB, 0x400921FB, 0x4012D97C, 0x401921FB, 0x401F6A7A, 0x4022D97C,
  0x4025FDBB, 0x402921FB, 0x402C463A, 0x402F6A7A, 0x4031475C, 0x4032D97C,
  0x40346B9C, 0x4035FDBB, 0x40378FDB, 0x403921FB, 0x403AB41B, 0x403C463A,
  0x403DD85A, 0x403F6A7A, 0x40407E4C, 0x4041475C, 0x4042106C, 0x4042D97C,
  0x4043A28C, 0x40446B9C, 0x404534AC, 0x4045FDBB, 0x4046C6CB, 0x40478FDB,
  0x404858EB, 0x404921FB]

/-- HotSpot aarch64 `generate_kernel_sin` (`iyIsOne`: with the tail `y`). -/
private def hsKernelSin (x y : Float) (iyIsOne : Bool) : Float :=
  let z := x * x
  let v := z * x
  let r := Float.fma z trigS6 trigS5
  let r := Float.fma z r trigS4
  let r := Float.fma z r trigS3
  let r := Float.fma z r trigS2
  if !iyIsOne then
    Float.fma v (Float.fma z r trigS1) x
  else
    let t := trigHalf * y
    let t := Float.fma (-v) r t
    let t := Float.fma (-z) t y
    let t := Float.fma v trigS1 t
    x + t

/-- HotSpot aarch64 `generate_kernel_cos`; `ix` is the high word of `|x|` of the *original* argument
(the register of `generate_dsin_dcos`, not recomputed after the reduction). -/
private def hsKernelCos (x y : Float) (ix : UInt32) : Float :=
  let z := x * x
  let r := Float.fma z trigC6 trigC5
  let r := Float.fma z r trigC4
  let xy := x * y
  let r := Float.fma z r trigC3
  let r := Float.fma z r trigC2
  let zz := z * z
  let r := Float.fma z r trigC1
  if ix ≤ 0x3FD33333 then
    trigOne - Float.fma trigHalf z (Float.fma (-zz) r xy)
  else
    let qx := if ix > 0x3fe90000 then trigQx else Float.ofBits ((ix - 0x00200000).toUInt64 <<< 32)
    let c := Float.fma zz r (-xy)
    let h := Float.fma trigHalf z (-qx)
    (trigOne - qx) - (h - c)

/-- The biased exponent of a double. -/
@[inline] private def trigExp (x : Float) : UInt32 := ((x.toBits >>> 52) &&& 0x7ff).toUInt32

/-- HotSpot aarch64 `generate__ieee754_rem_pio2` for `|x| ≤ 2^19·π/2` (`ix ≤ 0x413921fb`):
`(n, y0, y1)`; `none` for larger arguments. -/
private def hsRemPio2 (x : Float) (ix : UInt32) : Option (Int × Float × Float) := Id.run do
  let negative := x.toBits ≥ 0x8000000000000000
  if ix < 0x4002d97c then
    if !negative then
      let z := x - trigPio2_1
      if ix == 0x3ff921fb then
        let z := z - trigPio2_2
        let y0 := z - trigPio2_2t
        return some (1, y0, (z - y0) - trigPio2_2t)
      let y0 := z - trigPio2_1t
      return some (1, y0, (z - y0) - trigPio2_1t)
    else
      let z := x + trigPio2_1
      if ix == 0x3ff921fb then
        let z := z + trigPio2_2
        let y0 := z + trigPio2_2t
        return some (-1, y0, (z - y0) + trigPio2_2t)
      let y0 := z + trigPio2_1t
      return some (-1, y0, (z - y0) + trigPio2_1t)
  if ix > 0x413921fb then return none
  let t := x.abs
  let v2 := Float.fma t trigInvPio2 trigHalf
  -- `fcvtzdw`: `t < 2^20`, so the truncation fits an `int`
  let n : Nat := v2.toUInt64.toNat
  let fn := v2.floor
  let mut r := Float.fma (-fn) trigPio2_1 t
  let mut w := fn * trigPio2_1t
  let mut y0 := r - w
  let quick := n ≤ 32 && ix != trigNpio2Hw[n - 1]!
  if !quick then
    let j := ix >>> 20
    let i : Int := (j.toNat : Int) - (trigExp y0).toNat
    if i > 16 then
      let tt := r
      let ww := fn * trigPio2_2
      r := tt - ww
      w := Float.fma fn trigPio2_2t (ww - (tt - r))
      y0 := r - w
      let i : Int := (j.toNat : Int) - (trigExp y0).toNat
      if i > 49 then
        let tt := r
        let ww := fn * trigPio2_3
        r := tt - ww
        w := Float.fma fn trigPio2_3t (ww - (tt - r))
        y0 := r - w
  let y1 := (r - y0) - w
  -- `cmp(X, zr); br(GT, done)`: a non-positive `X` (as `long`) negates
  if !negative then return some ((n : Int), y0, y1)
  return some (-(n : Int), -y0, -y1)

/-- HotSpot aarch64 `generate_dsin_dcos(isCos)`. -/
private def hsSinCos (x : Float) (isCos : Bool) : Float :=
  let absX := x.toBits &&& 0x7fffffffffffffff
  let ix : UInt32 := (absX >>> 32).toUInt32
  if ix < 0x3e400000 then (if isCos then trigOne else x)
  else if ix ≤ 0x3fe921fb then (if isCos then hsKernelCos x 0.0 ix else hsKernelSin x 0.0 false)
  else if absX ≥ 0x7ff0000000000000 then Float.nan
  else match hsRemPio2 x ix with
    | none => if isCos then x.cos else x.sin
    | some (n, y0, y1) =>
      -- `n & 3` of the two's complement `int` (`Int.emod`)
      let low := n % 4
      let odd := low % 2 == 1
      if isCos then
        -- negated iff bit 0 of `n ^ (n >>> 1)` is set
        let v := if odd then hsKernelSin y0 y1 true else hsKernelCos y0 y1 ix
        if low == 1 || low == 2 then -v else v
      else
        let v := if odd then hsKernelCos y0 y1 ix else hsKernelSin y0 y1 true
        if low ≥ 2 then -v else v

/-- Java `Math.sin` on the reference JVM (HotSpot aarch64 intrinsic, see above). -/
def javaSin (x : Float) : Float := hsSinCos x false

/-- Java `Math.cos` on the reference JVM (HotSpot aarch64 intrinsic, see above). -/
def javaCos (x : Float) : Float := hsSinCos x true

private def atanHi : Array Float := #[Float.ofBits 0x3FDDAC670561BB4F, Float.ofBits 0x3FE921FB54442D18,
  Float.ofBits 0x3FEF730BD281F69B, Float.ofBits 0x3FF921FB54442D18]
private def atanLo : Array Float := #[Float.ofBits 0x3C7A2B7F222F65E2, Float.ofBits 0x3C81A62633145C07,
  Float.ofBits 0x3C7007887AF0CBBD, Float.ofBits 0x3C91A62633145C07]
private def atanT : Array Float := #[Float.ofBits 0x3FD555555555550D, Float.ofBits 0xBFC999999998EBC4,
  Float.ofBits 0x3FC24924920083FF, Float.ofBits 0xBFBC71C6FE231671, Float.ofBits 0x3FB745CDC54C206E,
  Float.ofBits 0xBFB3B0F2AF749A6D, Float.ofBits 0x3FB10D66A0D03D51, Float.ofBits 0xBFADDE2D52DEFD9A,
  Float.ofBits 0x3FA97B4B24760DEB, Float.ofBits 0xBFA2B4442C6A6C2F, Float.ofBits 0x3F90AD3AE322DA11]
private def atanHuge : Float := 1.0e300
private def trigTwo : Float := 2.0
private def trigOneHalf : Float := 1.5

/-- Java `StrictMath.atan` (= `Math.atan` on HotSpot; JDK `FdLibm.Atan`). -/
def javaAtan (x : Float) : Float := Id.run do
  let hx : Int32 := (x.toBits >>> 32).toUInt32.toInt32
  let ix : UInt32 := hx.toUInt32 &&& 0x7fffffff
  let mut x := x
  if ix ≥ 0x44100000 then
    -- |x| ≥ 2^66
    if ix > 0x7ff00000 || (ix == 0x7ff00000 && (x.toBits &&& 0xffffffff) != 0) then return x + x
    if hx > 0 then return atanHi[3]! + atanLo[3]! else return -atanHi[3]! - atanLo[3]!
  let mut id : Int := -1
  if ix < 0x3fdc0000 then
    -- |x| < 0.4375
    if ix < 0x3e200000 then
      if atanHuge + x > trigOne then return x
    id := -1
  else
    x := x.abs
    if ix < 0x3ff30000 then
      if ix < 0x3fe60000 then
        id := 0
        x := (trigTwo * x - trigOne) / (trigTwo + x)
      else
        id := 1
        x := (x - trigOne) / (x + trigOne)
    else
      if ix < 0x40038000 then
        id := 2
        x := (x - trigOneHalf) / (trigOne + trigOneHalf * x)
      else
        id := 3
        x := -trigOne / x
  let z := x * x
  let w := z * z
  let s1 := z * (atanT[0]! + w * (atanT[2]! + w * (atanT[4]! + w * (atanT[6]! + w * (atanT[8]! + w * atanT[10]!)))))
  let s2 := w * (atanT[1]! + w * (atanT[3]! + w * (atanT[5]! + w * (atanT[7]! + w * atanT[9]!))))
  if id < 0 then return x - x * (s1 + s2)
  let i := id.toNat
  let z := atanHi[i]! - ((x * (s1 + s2) - atanLo[i]!) - x)
  return if hx < 0 then -z else z

private def atan2Tiny : Float := 1.0e-300
private def atan2PiO4 : Float := Float.ofBits 0x3FE921FB54442D18
private def atan2PiO2 : Float := Float.ofBits 0x3FF921FB54442D18
private def atan2PiLo : Float := Float.ofBits 0x3CA1A62633145C07
private def atan2Three : Float := 3.0
private def atan2Zero : Float := 0.0

/-- Java `StrictMath.atan2(y, x)` (= `Math.atan2` on HotSpot; JDK `FdLibm.Atan2`). -/
def javaAtan2 (y x : Float) : Float := Id.run do
  let hx : Int32 := (x.toBits >>> 32).toUInt32.toInt32
  let ix : UInt32 := hx.toUInt32 &&& 0x7fffffff
  let lx : UInt32 := (x.toBits &&& 0xffffffff).toUInt32
  let hy : Int32 := (y.toBits >>> 32).toUInt32.toInt32
  let iy : UInt32 := hy.toUInt32 &&& 0x7fffffff
  let ly : UInt32 := (y.toBits &&& 0xffffffff).toUInt32
  if x.isNaN || y.isNaN then return x + y
  if ix == 0x3ff00000 && lx == 0 && hx ≥ 0 then return javaAtan y
  -- `m = ((hy >> 31) & 1) | ((hx >> 30) & 2)`: 2·sign(x) + sign(y)
  let m : Nat := (if hy < 0 then 1 else 0) + (if hx < 0 then 2 else 0)
  if iy == 0 && ly == 0 then
    match m with
    | 0 | 1 => return y
    | 2 => return Float.pi + atan2Tiny
    | _ => return -Float.pi - atan2Tiny
  if ix == 0 && lx == 0 then
    return if hy < 0 then -atan2PiO2 - atan2Tiny else atan2PiO2 + atan2Tiny
  if ix == 0x7ff00000 then
    if iy == 0x7ff00000 then
      match m with
      | 0 => return atan2PiO4 + atan2Tiny
      | 1 => return -atan2PiO4 - atan2Tiny
      | 2 => return atan2Three * atan2PiO4 + atan2Tiny
      | _ => return -atan2Three * atan2PiO4 - atan2Tiny
    else
      match m with
      | 0 => return atan2Zero
      | 1 => return -atan2Zero
      | 2 => return Float.pi + atan2Tiny
      | _ => return -Float.pi - atan2Tiny
  if iy == 0x7ff00000 then
    return if hy < 0 then -atan2PiO2 - atan2Tiny else atan2PiO2 + atan2Tiny
  -- `k = (iy - ix) >> 20` on `int`s
  let k : Int := Int.fdiv ((iy.toNat : Int) - ix.toNat) 1048576
  let z : Float :=
    if k > 60 then atan2PiO2 + trigHalf * atan2PiLo
    else if hx < 0 && k < -60 then atan2Zero
    else javaAtan (y / x).abs
  match m with
  | 0 => return z
  | 1 => return -z
  | 2 => return Float.pi - (z - atan2PiLo)
  | _ => return (z - atan2PiLo) - Float.pi

private def acosPio2Hi : Float := Float.ofBits 0x3FF921FB54442D18
private def acosPio2Lo : Float := Float.ofBits 0x3C91A62633145C07
private def acosPS0 : Float := Float.ofBits 0x3FC5555555555555
private def acosPS1 : Float := Float.ofBits 0xBFD4D61203EB6F7D
private def acosPS2 : Float := Float.ofBits 0x3FC9C1550E884455
private def acosPS3 : Float := Float.ofBits 0xBFA48228B5688F3B
private def acosPS4 : Float := Float.ofBits 0x3F49EFE07501B288
private def acosPS5 : Float := Float.ofBits 0x3F023DE10DFDF709
private def acosQS1 : Float := Float.ofBits 0xC0033A271C8A2D4B
private def acosQS2 : Float := Float.ofBits 0x40002AE59C598AC8
private def acosQS3 : Float := Float.ofBits 0xBFE6066C1B8D0159
private def acosQS4 : Float := Float.ofBits 0x3FB3B8C5B12E9282

/-- Java `StrictMath.acos` (= `Math.acos` on HotSpot; JDK `FdLibm.Acos`). -/
def javaAcos (x : Float) : Float := Id.run do
  let hx : Int32 := (x.toBits >>> 32).toUInt32.toInt32
  let ix : UInt32 := hx.toUInt32 &&& 0x7fffffff
  let lx : UInt32 := (x.toBits &&& 0xffffffff).toUInt32
  let poly (z : Float) : Float × Float :=
    (z * (acosPS0 + z * (acosPS1 + z * (acosPS2 + z * (acosPS3 + z * (acosPS4 + z * acosPS5))))),
     trigOne + z * (acosQS1 + z * (acosQS2 + z * (acosQS3 + z * acosQS4))))
  if ix ≥ 0x3ff00000 then
    if ix == 0x3ff00000 && lx == 0 then
      return if hx > 0 then 0.0 else Float.pi + trigTwo * acosPio2Lo
    return (x - x) / (x - x)
  if ix < 0x3fe00000 then
    if ix ≤ 0x3c600000 then return acosPio2Hi + acosPio2Lo
    let z := x * x
    let (p, q) := poly z
    let r := p / q
    return acosPio2Hi - (x - (acosPio2Lo - x * r))
  else if hx < 0 then
    let z := (trigOne + x) * trigHalf
    let (p, q) := poly z
    let s := z.sqrt
    let r := p / q
    let w := r * s - acosPio2Lo
    return Float.pi - trigTwo * (s + w)
  else
    let z := (trigOne - x) * trigHalf
    let s := z.sqrt
    let df := Float.ofBits (s.toBits &&& 0xffffffff00000000)
    let c := (z - df * df) / (s + df)
    let (p, q) := poly z
    let r := p / q
    let w := r * s + c
    return trigTwo * (df + w)

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
