/-!
Differential test of the Lean runtime's big-number paths (`lean_nat_big_*`, `lean_int_big_*`,
`lean_cstr_to_nat`, big `Nat.repr`, `Float` ↔ `Nat`/`Int` conversions).

Not part of `lake build` / `lake test`: `scripts/build_runtime_nogmp.sh --check` compiles this file
with `lean -c`, links it once against the toolchain runtime (GMP) and once against the runtime
rebuilt without GMP (Lean's own mpn bignums), runs both and requires byte-identical output.
Every printed line covers the operations on pseudo-random operands of up to 1,280 bits (both signs,
including 2^k and 2^k ± 1), so a difference points at the operations that disagree.
-/

/-- 64-bit LCG (Knuth MMIX constants); deterministic across runs and runtimes. -/
structure Rng where
  s : UInt64

def Rng.next (r : Rng) : UInt64 × Rng :=
  let s := r.s * 6364136223846793005 + 1442695040888963407
  (s ^^^ (s >>> 29), ⟨s⟩)

/-- A natural number of `0..maxLimbs` random 64-bit limbs, sometimes near a power of two. -/
def Rng.nat (r : Rng) (maxLimbs : Nat) : Nat × Rng := Id.run do
  let (k, r) := r.next
  let mut r := r
  let limbs := k.toNat % (maxLimbs + 1)
  let mut n := 0
  for _ in [0:limbs] do
    let (l, r') := r.next
    r := r'
    n := n * 18446744073709551616 + l.toNat
  -- edge shapes: 2^k, 2^k - 1, 2^k + 1
  match k.toNat / 7 % 8 with
  | 0 => return (2 ^ (64 * limbs), r)
  | 1 => return (2 ^ (64 * limbs) - 1, r)
  | 2 => return (2 ^ (64 * limbs) + 1, r)
  | _ => return (n, r)

def Rng.int (r : Rng) (maxLimbs : Nat) : Int × Rng :=
  let (n, r) := r.nat maxLimbs
  let (s, r) := r.next
  (if s % 2 == 0 then (n : Int) else -(n : Int), r)

def main : IO Unit := do
  let out ← IO.getStdout
  let mut r : Rng := ⟨0x0123456789abcdef⟩
  -- Nat
  for i in [0:3000] do
    let (a, r1) := r.nat 10
    let (b, r2) := r1.nat 6
    r := r2
    let b' := if b == 0 then 1 else b
    let sh := (a % 200)
    out.putStrLn s!"N{i} {a + b} {a * b} {a - b} {b - a} {a / b'} {a % b'} {Nat.gcd a b} {Nat.lcm a b'} {decide (a < b)} {decide (a = b)} {a &&& b} {a ||| b} {a ^^^ b} {a <<< sh} {a >>> sh} {Nat.log2 a} {a.testBit sh} {b ^ (sh % 7)}"
  -- Int
  for i in [0:3000] do
    let (a, r1) := r.int 10
    let (b, r2) := r1.int 6
    r := r2
    let b' := if b == 0 then 1 else b
    let sh := (a.natAbs % 200)
    out.putStrLn s!"I{i} {a + b} {a * b} {a - b} {Int.ediv a b'} {Int.emod a b'} {Int.tdiv a b'} {Int.tmod a b'} {Int.fdiv a b'} {Int.fmod a b'} {Int.bmod a b'.natAbs} {decide (a < b)} {a.toNat} {a.natAbs} {a >>> sh} {Int.gcd a b} {-a} {(a : Int) ^ (sh % 5)}"
  -- conversions and literals
  for i in [0:2000] do
    let (a, r1) := r.int 20
    let (e, r2) := r1.next
    r := r2
    let f := Float.ofInt a
    let g := Float.ofScientific a.natAbs (e % 2 == 0) (e.toNat % 400)
    out.putStrLn s!"F{i} {f.toBits} {f} {g.toBits} {g} {f.toUInt64} {g.toUInt64} {(Float.ofNat a.natAbs).toBits} {(toString a).toInt?} {(toString a.natAbs).toNat?} {(toString a).length}"
  -- large values
  let fact := (List.range 400).foldl (fun acc k => acc * (k + 1)) 1
  out.putStrLn s!"fact400 {fact}"
  out.putStrLn s!"fact400 / 3^200 {fact / 3 ^ 200} {fact % (3 ^ 200 + 7)}"
  let p := 2 ^ 4423 - 1
  out.putStrLn s!"mersenne {p % 1000000007} {(p * p) % (2 ^ 521 - 1)} {(toString p).length}"
  out.putStrLn s!"pow10 {(10 : Nat) ^ 1000 / 7} {Float.ofNat (10 ^ 308)} {Float.ofNat (10 ^ 309)} {(1e300 : Float).toUInt64} {Float.ofScientific (10 ^ 400) true 420}"
  out.putStrLn s!"lit {(340282366920938463463374607431768211457 : Nat) * 18446744073709551617} {(-170141183460469231731687303715884105728 : Int) / 3}"
