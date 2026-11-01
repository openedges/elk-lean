import Elk.Core.Util.Java
/-!
# `java.util.Random`

Exact port of the 48-bit linear congruential generator used by ELK
(`elk.randomSeed`). The generator is a pure value: every operation returns the
drawn value together with the advanced generator. Mirrors elk-rs
`org.eclipse.elk.core.util::Random`.
-/
namespace Elk.Core.Util

structure Random where
  /-- Scrambled 48-bit state. -/
  seed : UInt64 := 0
  /-- Test mock (elk-rs `set_mock_next_boolean`): fixed `nextBoolean` result. -/
  mockNextBoolean : Option Bool := none
  /-- Test mock (elk-rs `set_mock_double_sequence`): `(current, step)`; `nextDouble` returns
  `current + step` and advances. -/
  mockDoubleSequence : Option (Float × Float) := none
  deriving Repr, Inhabited, BEq

namespace Random

def multiplier : UInt64 := 0x5DEECE66D
def addend : UInt64 := 0xB
def mask : UInt64 := ((1 : UInt64) <<< 48) - 1

/-- `new Random(seed)` for a Java `long` seed given as `Int` (sign-extended like `(long) intSeed`). -/
def ofInt (seed : Int) : Random := { seed := (Int.toUInt64Wrap seed ^^^ multiplier) &&& mask }

/-- `new Random(seed)` with a raw 64-bit seed (Rust `Random::new(u64)`). -/
def ofUInt64 (seed : UInt64) : Random := { seed := (seed ^^^ multiplier) &&& mask }

/-- `setSeed` (keeps the test mocks). -/
def setSeed (r : Random) (seed : Int) : Random := { r with seed := (ofInt seed).seed }

/-- elk-rs `set_mock_next_boolean(value)`. -/
def setMockNextBoolean (r : Random) (value : Bool) : Random := { r with mockNextBoolean := some value }
/-- elk-rs `clear_mock_next_boolean()`. -/
def clearMockNextBoolean (r : Random) : Random := { r with mockNextBoolean := none }
/-- elk-rs `set_mock_double_sequence(start, step)`. -/
def setMockDoubleSequence (r : Random) (start step : Float) : Random := { r with mockDoubleSequence := some (start, step) }
/-- elk-rs `clear_mock_double_sequence()`. -/
def clearMockDoubleSequence (r : Random) : Random := { r with mockDoubleSequence := none }

/-- `next(bits)`: advances the state and returns the top `bits` bits. -/
@[inline] def next (r : Random) (bits : Nat) : UInt32 × Random :=
  let s := (r.seed * multiplier + addend) &&& mask
  ((s >>> (48 - bits).toUInt64).toUInt32, { r with seed := s })

/-- `nextInt()`: uniformly distributed Java `int`. -/
def nextIntUnbounded (r : Random) : Int × Random :=
  let (v, r) := r.next 32
  (UInt32.toIntSigned v, r)

/-- `nextInt(bound)`: uniform in `[0, bound)`. `bound` must be positive; a
non-positive bound returns `0` (Java throws `IllegalArgumentException`). -/
def nextInt (r : Random) (bound : Int) : Int × Random :=
  if bound <= 0 then (0, r)
  else
    let b32 := Int32.ofInt bound
    -- power of two: (bound * next(31)) >> 31
    let n := bound.toNat
    if (n &&& (n - 1)) == 0 then
      let (bits, r) := r.next 31
      (Int.tdiv (bound * (bits.toNat : Int)) 2147483648, r)
    else
      let rec loop (r : Random) (fuel : Nat) : Int × Random :=
        match fuel with
        | 0 => (0, r)
        | fuel + 1 =>
          let (bitsU, r) := r.next 31
          let bits := Int32.ofInt (bitsU.toNat : Int)
          let val := bits % b32
          -- Java: `u - r + m < 0` with int overflow; Int32 arithmetic wraps the same way
          if bits - val + (b32 - 1) >= 0 then (val.toInt, r) else loop r fuel
      loop r 1000000

/-- `nextLong()`. -/
def nextLong (r : Random) : Int × Random :=
  let (hi, r) := r.next 32
  let (lo, r) := r.next 32
  let v : Int64 := (Int64.ofInt (UInt32.toIntSigned hi) <<< 32) + Int64.ofInt (UInt32.toIntSigned lo)
  (v.toInt, r)

/-- `nextLong()` as its two's complement bit pattern (`(nextLong r).1` is `Int64.toInt` of it): no
`Int` result, which for most draws lies outside the small-`Int` range and costs a GMP number. -/
def nextLongBits (r : Random) : UInt64 × Random :=
  let (hi, r) := r.next 32
  let (lo, r) := r.next 32
  -- `((long) hi << 32) + (long) lo` with both halves sign-extended, wrapping
  let hi64 : UInt64 := (Int32.toInt64 hi.toInt32).toUInt64
  let lo64 : UInt64 := (Int32.toInt64 lo.toInt32).toUInt64
  ((hi64 <<< 32) + lo64, r)

/-- `setSeed(seed)` for a `long` seed given as its bit pattern (`setSeed r (Int64.toInt b)`). -/
def setSeedBits (r : Random) (seed : UInt64) : Random := { r with seed := (seed ^^^ multiplier) &&& mask }

/-- `nextBoolean()` (honours the test mock). -/
def nextBoolean (r : Random) : Bool × Random :=
  match r.mockNextBoolean with
  | some value => (value, r)
  | none =>
    let (v, r) := r.next 1
    (v != 0, r)

/-- `2^53` as an exact bit pattern (the literal `9007199254740992.0` lies outside the fast
`Float.ofScientific` domain and is not always hoisted by the compiler). -/
def TWO_POW_53 : Float := Float.ofBits 0x4340000000000000

/-- `nextDouble()`: `((next(26) << 27) + next(27)) * 2^-53` (honours the mock sequence). -/
def nextDouble (r : Random) : Float × Random :=
  match r.mockDoubleSequence with
  | some (current, step) =>
    let value := current + step
    (value, { r with mockDoubleSequence := some (value, step) })
  | none =>
    let (hi, r) := r.next 26
    let (lo, r) := r.next 27
    let n : UInt64 := (hi.toUInt64 <<< 27) + lo.toUInt64
    (n.toFloat / TWO_POW_53, r)

/-- `nextFloat()` as a double carrying only single precision (`next(24) / 2^24` in `float`);
with the mock sequence it is the mocked double rounded to single precision. -/
def nextFloat (r : Random) : Float × Random :=
  match r.mockDoubleSequence with
  | some _ =>
    let (v, r) := r.nextDouble
    (Float.toF32 v, r)
  | none =>
    let (v, r) := r.next 24
    (Float.toF32 (v.toNat.toFloat / 16777216.0), r)

end Random

end Elk.Core.Util
