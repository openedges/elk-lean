import Tests.Framework
import Elk.Core.Util.FastFloat
import Elk.Core.Util.Random
/-!
Test suite for `Elk.Core.Util.FastFloat`: the run-time implementations behind the `csimp`
redirections must be bit-identical to the core functions (`coreOf*`, compiled before the
redirection) on the fast-path domain, its borders and beyond (fallback).
-/
namespace Tests.Core.FastFloat

open Tests Elk.Core.Util Elk.Core.Util.FastFloat

private def bitsEq (a b : Float) : Bool := a.toBits == b.toBits

def suite : Suite := Tests.suite "core.util.FastFloat" do
  let mantissas : Array Nat := #[0, 1, 5, 12345, 999999, 2 ^ 32 - 1, 2 ^ 32, 2 ^ 53 - 1, 2 ^ 53, 2 ^ 53 + 1,
    2 ^ 62, 2 ^ 63 - 1, 2 ^ 63, 2 ^ 64 + 5, 10 ^ 30 + 7]
  let exps : Array Nat := #[0, 1, 2, 5, 15, 16, 22, 23, 30, 300, 330]
  let mut bad := 0
  let mut count := 0
  for m in mantissas do
    for e in exps do
      for s in [true, false] do
        count := count + 1
        if !bitsEq (ofScientificImpl m s e) (coreOfScientific m s e) then bad := bad + 1
  -- pseudo-random mantissas and exponents (mostly inside the fast-path domain)
  let mut r := Random.ofInt 42
  for _ in [0:20000] do
    let (a, r1) := r.nextInt 2147483647
    let (b, r2) := r1.nextInt 2147483647
    let (c, r3) := r2.nextInt 2147483647
    r := r3
    let m := (a.toNat % 1000000007) * (b.toNat % 9007199) % (2 ^ 54)
    let e := c.toNat % 26
    count := count + 1
    if !bitsEq (ofScientificImpl m (c % 2 == 0) e) (coreOfScientific m (c % 2 == 0) e) then bad := bad + 1
  checkEq s!"ofScientific bit-identical ({count} cases)" bad 0
  let nats : Array Nat := #[0, 1, 2, 3, 1000, 2 ^ 31, 2 ^ 32, 2 ^ 52 + 1, 2 ^ 53 - 1, 2 ^ 53, 2 ^ 53 + 1,
    2 ^ 62 + 3, 2 ^ 63 - 1, 2 ^ 63, 2 ^ 64, 10 ^ 30]
  checkEq "ofNat bit-identical" (nats.filter fun n => !bitsEq (ofNatImpl n) (coreOfNat n)).size 0
  let pos : Array Int := nats.map (fun (n : Nat) => Int.ofNat n)
  let ints : Array Int := pos ++ pos.map (fun (i : Int) => -i)
  checkEq "ofInt bit-identical" (ints.filter fun i => !bitsEq (ofIntImpl i) (coreOfInt i)).size 0
  let specials : Array Float := #[0.0, -0.0, 1.0, -1.0, 1.0 / 0.0, -1.0 / 0.0, 0.0 / 0.0,
    Float.ofBits 0x7FEFFFFFFFFFFFFF, Float.ofBits 0x0000000000000001, Float.ofBits 0x7FF8000000000001]
  checkEq "isNaN" (specials.filter fun x => isNaNImpl x != coreIsNaN x).size 0
  checkEq "isFinite" (specials.filter fun x => isFiniteImpl x != coreIsFinite x).size 0
  checkEq "isInf" (specials.filter fun x => isInfImpl x != coreIsInf x).size 0
  -- literals and conversions in compiled code go through the redirection
  checkEq "literal 0.1" (0.1 : Float).toBits (coreOfScientific 1 true 1).toBits
  checkEq "literal 2.5e10" (2.5e10 : Float).toBits (coreOfScientific 25 false 9).toBits
  checkEq "Nat.toFloat" (12345 : Nat).toFloat.toBits (coreOfNat 12345).toBits
  -- exact constants that replace literals outside the fast-path domain
  checkEq "Random.TWO_POW_53" Random.TWO_POW_53.toBits (coreOfScientific 90071992547409920 true 1).toBits
  checkEq "2^64 bits" (Float.ofBits 0x43F0000000000000).toBits (coreOfScientific 184467440737095516160 true 1).toBits
  checkEq "2^63 bits" (Float.ofBits 0x43E0000000000000).toBits (coreOfScientific 92233720368547758080 true 1).toBits

def suites : Array Suite := #[suite]

end Tests.Core.FastFloat
