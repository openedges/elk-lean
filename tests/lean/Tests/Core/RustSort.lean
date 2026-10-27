import Tests.Framework
import Elk.Core.Util.RustSort
import Elk.Json.Parser
/-!
Test suites for `Elk.Core.Util.RustSort` (port of Rust 1.97.1 `slice::sort_by`, driftsort).

* `core.util.RustSort.fixtures`: every case of `tests/fixtures/rustsort/cases.json` was produced by
  real Rust 1.97.1 (`Vec::sort_by` on elements of `size_of::<T>() = elemSize` carrying the ids
  `0..n-1`). For consistent and deliberately inconsistent comparators the port must reproduce the
  resulting permutation (or the `panic_on_ord_violation` panic), the number of comparator calls and
  the FNV-1a hash of the comparator argument sequence.
* `core.util.RustSort.basics`: agreement with `stableSort` for consistent comparators,
  `rustSortByKey`, zero-sized elements.
-/
namespace Tests.Core.RustSort

open Tests Elk.Core.Util

/-- splitmix64 finaliser (the generator's `mix`). -/
def mix (z : UInt64) : UInt64 :=
  let z := z + 0x9E3779B97F4A7C15
  let z := (z ^^^ (z >>> 30)) * 0xBF58476D1CE4E5B9
  let z := (z ^^^ (z >>> 27)) * 0x94D049BB133111EB
  z ^^^ (z >>> 31)

/-- Deterministic pair hash of the generator (`h3`). -/
def h3 (seed a b : UInt64) : UInt64 := mix (seed ^^^ mix ((a * 1000003) ^^^ mix b))

/-- `Less`/`Equal`/`Greater` from a hash (`ord3`). -/
def ord3 (r : UInt64) : Ordering :=
  match r % 3 with
  | 0 => .lt
  | 1 => .eq
  | _ => .gt

/-- The generator's comparator kinds on element ids (see `cases.json` `kinds`). -/
def cmpIds (kind : Nat) (seed : UInt64) (keys : Array Int) (n : Nat) (a b : Nat) : Ordering :=
  let ka := keys[a]!
  let kb := keys[b]!
  let a64 := UInt64.ofNat a
  let b64 := UInt64.ofNat b
  match kind with
  | 0 => compare ka kb
  | 1 => ord3 (h3 seed a64 b64)
  | 2 | 3 => if ka < 0 || kb < 0 then .eq else compare ka kb
  | 4 =>
    if a == b then .eq
    else
      let (x, y) := if a < b then (a64, b64) else (b64, a64)
      let o : Ordering := if h3 seed x y % 2 == 0 then .lt else .gt
      if a < b then o else o.swap
  | 5 =>
    let r := h3 seed a64 b64
    if r % 16 == 0 then ord3 (r >>> 8) else compare ka kb
  | _ =>
    if ka ≥ 0 && kb ≥ 0 then compare ka kb
    else
      let sa := h3 seed a64 0 % (UInt64.ofNat n + 1)
      let sb := h3 seed b64 0 % (UInt64.ofNat n + 1)
      compare sa sb

/-- FNV-1a 64 step over one id. -/
def fnv (h : UInt64) (x : Nat) : UInt64 := (h ^^^ UInt64.ofNat x) * 0x100000001b3

private def natArr (v : Elk.Json.Value) : Array Nat :=
  (v.getArr?.getD #[]).map fun x => (x.getInt?.getD 0).toNat

private def intArr (v : Elk.Json.Value) : Array Int :=
  (v.getArr?.getD #[]).map fun x => x.getInt?.getD 0

/-- `core.util.RustSort.fixtures`. -/
def fixtureTests : Suite := suite "core.util.RustSort.fixtures" do
  let text ← IO.FS.readFile "tests/fixtures/rustsort/cases.json"
  match Elk.Json.parseString text with
  | .error e => report "parse cases.json" false e
  | .ok doc =>
    let cases := (doc.get? "cases").bind (·.getArr?) |>.getD #[]
    check "at least 200 cases" (cases.size ≥ 200)
    let mut idx := 0
    let mut inconsistent := 0
    let mut panics := 0
    for c in cases do
      let es := ((c.get? "elemSize").bind (·.getInt?)).getD 8 |>.toNat
      let kind := ((c.get? "kind").bind (·.getInt?)).getD 0 |>.toNat
      let seed := UInt64.ofNat (((c.get? "seed").bind (·.getStr?)).getD "0").toNat!
      let keys := intArr ((c.get? "keys").getD .null)
      let expPanic := ((c.get? "panics").bind (·.getBool?)).getD false
      let expPerm := natArr ((c.get? "perm").getD .null)
      let expCount := ((c.get? "comparisons").bind (·.getInt?)).getD 0 |>.toNat
      let expHash := UInt64.ofNat (((c.get? "cmpHash").bind (·.getStr?)).getD "0").toNat!
      let n := keys.size
      if kind != 0 then inconsistent := inconsistent + 1
      if expPanic then panics := panics + 1
      let name := s!"case {idx} (elemSize {es}, kind {kind}, n {n})"
      let cmpM : Nat → Nat → StateM (Nat × UInt64) Ordering := fun a b => do
        modify fun (k, h) => (k + 1, fnv (fnv h a) b)
        return cmpIds kind seed keys n a b
      let (res, (count, hash)) := (rustSortByM (Array.range n) cmpM es).run (0, 0xcbf29ce484222325)
      let pureRes := rustSortBy (Array.range n) (cmpIds kind seed keys n) es
      checkEq s!"{name}: comparisons" count expCount
      check s!"{name}: comparison sequence hash" (hash == expHash)
      match res, pureRes with
      | .ok p, .ok q =>
        check s!"{name}: no panic" (!expPanic)
        check s!"{name}: permutation" (!expPanic && p == expPerm)
        check s!"{name}: pure = monadic" (p == q)
      | .error e, .error e' =>
        check s!"{name}: panics" expPanic
        checkEq s!"{name}: panic message" e RustSort.ordViolationMessage
        check s!"{name}: pure panics too" (e == e')
      | _, _ => report s!"{name}: pure and monadic agree on panicking" false
      idx := idx + 1
    check "fixtures contain inconsistent comparators" (inconsistent ≥ 100)
    check "fixtures contain panics" (panics ≥ 50)

/-- Linear congruential generator for the property tests. -/
private def lcg (s : UInt64) : UInt64 := s * 6364136223846793005 + 1442695040888963407

/-- `core.util.RustSort.basics`. -/
def basicTests : Suite := suite "core.util.RustSort.basics" do
  -- consistent comparators: any stable sort gives the same result
  let mut s : UInt64 := 42
  let mut agree := true
  for n in [0, 1, 2, 5, 20, 21, 33, 64, 65, 100, 257, 513, 1000, 2000] do
    for modulus in [3, 50, 100000] do
      let mut a : Array (Nat × Nat) := #[]
      for i in [0:n] do
        s := lcg s
        a := a.push ((s >>> 33).toNat % modulus, i)
      let cmp := fun (x y : Nat × Nat) => compare x.1 y.1
      for es in [8, 16, 24] do
        match rustSortBy a cmp es with
        | .ok r => if r != stableSort a cmp then agree := false
        | .error _ => agree := false
  check "consistent comparators agree with stableSort" agree
  -- sort_by_key
  match rustSortByKey #[(3, "c"), (1, "a"), (2, "b"), (1, "a2")] (·.1) with
  | .ok r => checkEq "sortByKey" (r.map (·.2)) #["a", "a2", "b", "c"]
  | .error e => report "sortByKey" false e
  -- zero-sized types are left alone (`T::IS_ZST`)
  match rustSortBy #[3, 1, 2] (fun a b => compare a b) 0 with
  | .ok r => checkEq "zero-sized element type" r #[3, 1, 2]
  | .error e => report "zero-sized element type" false e
  -- descending input: reversed with n - 1 comparisons (`find_existing_run`)
  let desc := (Array.range 1000).reverse
  let (r, k) := (rustSortByM desc (fun a b => do
      modify (· + 1)
      return compare a b : Nat → Nat → StateM Nat Ordering)).run 0
  match r with
  | .ok r => do
    checkEq "descending input sorted" r (Array.range 1000)
    checkEq "descending input: n - 1 comparisons" k 999
  | .error e => report "descending input" false e

/-- All `RustSort` suites. -/
def suites : Array Suite := #[fixtureTests, basicTests]

end Tests.Core.RustSort
