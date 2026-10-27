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
  deriving Repr, Inhabited, BEq

namespace Random

def multiplier : UInt64 := 0x5DEECE66D
def addend : UInt64 := 0xB
def mask : UInt64 := ((1 : UInt64) <<< 48) - 1

/-- `new Random(seed)` for a Java `long` seed given as `Int` (sign-extended like `(long) intSeed`). -/
def ofInt (seed : Int) : Random := ⟨(Int.toUInt64Wrap seed ^^^ multiplier) &&& mask⟩

/-- `new Random(seed)` with a raw 64-bit seed (Rust `Random::new(u64)`). -/
def ofUInt64 (seed : UInt64) : Random := ⟨(seed ^^^ multiplier) &&& mask⟩

/-- `setSeed`. -/
def setSeed (_ : Random) (seed : Int) : Random := ofInt seed

/-- `next(bits)`: advances the state and returns the top `bits` bits. -/
@[inline] def next (r : Random) (bits : Nat) : UInt32 × Random :=
  let s := (r.seed * multiplier + addend) &&& mask
  ((s >>> (48 - bits).toUInt64).toUInt32, ⟨s⟩)

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

/-- `nextBoolean()`. -/
def nextBoolean (r : Random) : Bool × Random :=
  let (v, r) := r.next 1
  (v != 0, r)

/-- `nextDouble()`: `((next(26) << 27) + next(27)) * 2^-53`. -/
def nextDouble (r : Random) : Float × Random :=
  let (hi, r) := r.next 26
  let (lo, r) := r.next 27
  let n : UInt64 := (hi.toUInt64 <<< 27) + lo.toUInt64
  (n.toFloat / 9007199254740992.0, r)

/-- `nextFloat()` as a double carrying only single precision (`next(24) / 2^24` in `float`). -/
def nextFloat (r : Random) : Float × Random :=
  let (v, r) := r.next 24
  (Float.toF32 (v.toNat.toFloat / 16777216.0), r)

end Random

end Elk.Core.Util
