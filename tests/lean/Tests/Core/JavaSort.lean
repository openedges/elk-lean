import Tests.Framework
import Elk.Core.Util.JavaSort
import Elk.Json.Parser
/-!
Test suites for `Elk.Core.Util.JavaSort` (port of OpenJDK 21 `java.util.TimSort`).

* `core.util.JavaSort.fixtures`: every line of `tests/fixtures/timsort/cases.jsonl` was produced by
  a real JDK 21 (`scripts/java/TimSortTrace.java gen <out> fixture`: `Collections.sort` of an
  `ArrayList` of elements carrying their index `0..n-1` and a generated key). The keys are
  regenerated here with the same generator (`genKeys`, checked against `keysHash`), and the port
  must reproduce the outcome (sorted / `IllegalArgumentException` "Comparison method violates its
  general contract!" / the comparator's own exception), the number of comparator calls, the FNV-1a
  hash of the comparator call sequence (ids and result of every call) and the permutation.
* `core.util.JavaSort.full`: the same over the full differential set (13,767 cases, sizes up to
  5,000) when `ELK_TIMSORT_CASES` names a file written by `TimSortTrace gen <out> full`
  (`scripts/run_timsort_diff.sh`); skipped otherwise.
* `core.util.JavaSort.basics`: agreement with `stableSort` for consistent comparators,
  `javaSortByKey`, `javaSortByIO`, `minRunLength`, the run-detection asymmetry.
* `core.util.JavaSort.bench` (`ELK_TIMSORT_BENCH=1`): `javaSortBy` vs `stableSort` timings.
-/
namespace Tests.Core.JavaSort

open Tests Elk.Core.Util

/-- splitmix64 finaliser after adding the golden gamma (`TimSortTrace.mix`). -/
def mix (z : UInt64) : UInt64 :=
  let z := z + 0x9E3779B97F4A7C15
  let z := (z ^^^ (z >>> 30)) * 0xBF58476D1CE4E5B9
  let z := (z ^^^ (z >>> 27)) * 0x94D049BB133111EB
  z ^^^ (z >>> 31)

/-- `TimSortTrace.h3`. -/
def h3 (seed a b : UInt64) : UInt64 := mix (seed ^^^ mix ((a * 1000003) ^^^ mix b))

/-- FNV-1a 64 step (`TimSortTrace.fnv`). -/
def fnv (h x : UInt64) : UInt64 := (h ^^^ x) * 0x100000001b3

/-- FNV-1a 64 offset basis. -/
def fnvOffset : UInt64 := 0xcbf29ce484222325

/-- Java `long` → two's complement `UInt64`. -/
def ofLong (x : Int) : UInt64 := if x < 0 then 0 - UInt64.ofNat (-x).toNat else UInt64.ofNat x.toNat

/-- `TimSortTrace.keys`: key kinds 0 random `% mod`, 1 ascending with duplicates, 2 descending,
3 random ascending/descending/constant runs, 4 all equal, 5 sawtooth `i % mod`, 6 nearly sorted;
then every key with `h3(seed, i, 99) % neg == 0` (`neg > 0`) becomes `-1` ("undefined"). -/
def genKeys (n keyKind : Nat) (mod neg seed : UInt64) : Array Int := Id.run do
  let mut k : Array Int := Array.replicate n 0
  let mut i := 0
  let mut seg : UInt64 := 0
  while i < n do
    match keyKind with
    | 0 =>
      k := k.set! i (h3 seed (UInt64.ofNat i) 1 % mod).toNat
      i := i + 1
    | 1 =>
      k := k.set! i (i * mod.toNat / n)
      i := i + 1
    | 2 =>
      k := k.set! i ((n - 1 - i) * mod.toNat / n)
      i := i + 1
    | 3 =>
      let r := h3 seed seg 3
      seg := seg + 1
      let len := ((1 : UInt64) + ((r >>> 8) % 64) * (if r % 4 == 0 then 8 else 1)).toNat
      let dir := (r >>> 20) % 3
      let v0 : Int := ((r >>> 32) % mod).toNat
      let mut j := 0
      while j < len && i < n do
        k := k.set! i (if dir == 0 then v0 + j else if dir == 1 then v0 + len - j else v0)
        j := j + 1
        i := i + 1
    | 4 =>
      k := k.set! i 0
      i := i + 1
    | 5 =>
      k := k.set! i (UInt64.ofNat i % mod).toNat
      i := i + 1
    | _ =>
      let r := h3 seed (UInt64.ofNat i) 6
      k := k.set! i (if r % 16 == 0 then ((r >>> 8) % UInt64.ofNat n).toNat else i)
      i := i + 1
  if neg > 0 then
    for j in [0:n] do
      if h3 seed (UInt64.ofNat j) 99 % neg == 0 then k := k.set! j (-1)
  return k

/-- FNV-1a hash of the keys (`TimSortTrace.keysHash`). -/
def keysHash (k : Array Int) : UInt64 := k.foldl (fun h x => fnv h (ofLong x)) fnvOffset

/-- FNV-1a hash of a permutation (`TimSortTrace.permHash`). -/
def permHash (p : Array Nat) : UInt64 := p.foldl (fun h x => fnv h (UInt64.ofNat x)) fnvOffset

/-- `TimSortTrace.ord3`. -/
def ord3 (r : UInt64) : Ordering :=
  match r % 3 with
  | 0 => .lt
  | 1 => .eq
  | _ => .gt

/-- `TimSortTrace.cmpRaw` without the throwing kinds (11/12 compare keys here; see `cmpM`):
0 key, 1 key then id, 2 reverse key, 3 constant 0, 4 random table, 5 symmetric random sign
(`a < b` and `b < a` both hold), 6 constant -1, 7 constant +1, 8 tournament (antisymmetric,
intransitive), 9 noisy key compare, 10 model order (0 when a key is undefined). -/
def cmpRaw (kind : Nat) (seed : UInt64) (keys : Array Int) (a b : Nat) : Ordering :=
  let ka := keys[a]!
  let kb := keys[b]!
  let a64 := UInt64.ofNat a
  let b64 := UInt64.ofNat b
  match kind with
  | 0 => compare ka kb
  | 1 => (compare ka kb).then (compare a b)
  | 2 => compare kb ka
  | 3 => .eq
  | 4 => ord3 (h3 seed a64 b64)
  | 5 => if a == b then .eq else if h3 seed (min a64 b64) (max a64 b64) % 2 == 0 then .lt else .gt
  | 6 => .lt
  | 7 => .gt
  | 8 =>
    if a == b then .eq
    else
      let o : Ordering := if h3 seed (min a64 b64) (max a64 b64) % 2 == 0 then .lt else .gt
      if a < b then o else o.swap
  | 9 =>
    let r := h3 seed a64 b64
    if r % 16 == 0 then ord3 (r >>> 8) else compare ka kb
  | 10 => if ka < 0 || kb < 0 then .eq else compare ka kb
  | _ => compare ka kb

/-- Comparator monad of the harness: the comparator's own exception over the call log
(calls, FNV-1a hash of `a, b, sign + 1`; `3` for a throwing call). -/
abbrev CmpM := ExceptT String (StateM (Nat × UInt64))

/-- Logging comparator; kind 11 throws at call `kth`, kind 12 on the first call touching an
undefined key (like `Port side is undefined` in node-size validation). -/
def cmpM (kind : Nat) (seed : UInt64) (kth : Nat) (keys : Array Int) (a b : Nat) : CmpM Ordering := do
  let (calls, h) ← get
  let calls := calls + 1
  let h := fnv (fnv h (UInt64.ofNat a)) (UInt64.ofNat b)
  let throws :=
    (kind == 11 && calls == kth) || (kind == 12 && (keys[a]! < 0 || keys[b]! < 0))
  if throws then
    set (calls, fnv h 3)
    throw "comparator exception"
  let r := cmpRaw kind seed keys a b
  set (calls, fnv h (match r with | .lt => 0 | .eq => 1 | .gt => 2))
  return r

private def natArr (v : Elk.Json.Value) : Array Nat :=
  (v.getArr?.getD #[]).map fun x => (x.getInt?.getD 0).toNat

private def getNat (c : Elk.Json.Value) (k : String) : Nat :=
  ((c.get? k).bind (·.getInt?)).getD 0 |>.toNat

private def getU64 (c : Elk.Json.Value) (k : String) : UInt64 :=
  UInt64.ofNat (((c.get? k).bind (·.getStr?)).getD "0").toNat!

/-- Result of one case: mismatch descriptions (empty = identical to Java) and the outcome. -/
def runCase (c : Elk.Json.Value) (checkPure : Bool) : Array String × String := Id.run do
  let n := getNat c "n"
  let keyKind := getNat c "keyKind"
  let kind := getNat c "cmp"
  let mod := UInt64.ofNat (getNat c "mod")
  let neg := UInt64.ofNat (getNat c "neg")
  let seed := getU64 c "seed"
  let kth := getNat c "k"
  let outcome := ((c.get? "outcome").bind (·.getStr?)).getD ""
  let keys := genKeys n keyKind mod neg seed
  let mut errs : Array String := #[]
  if keysHash keys != getU64 c "keysHash" then errs := errs.push "generated keys differ"
  let (res, (calls, hash)) :=
    ((javaSortByM (Array.range n) (cmpM kind seed kth keys)).run).run (0, fnvOffset)
  if calls != getNat c "calls" then errs := errs.push s!"calls {calls} vs Java {getNat c "calls"}"
  if hash != getU64 c "cmpHash" then errs := errs.push "comparison sequence differs"
  let got : String := match res with
    | .ok (.ok _) => "ok"
    | .ok (.error e) => if e == JavaSort.contractViolationMessage then "IAE" else s!"other:{e}"
    | .error _ => "throw"
  if got != outcome then errs := errs.push s!"outcome {got} vs Java {outcome}"
  if let .ok (.ok p) := res then
    if permHash p != getU64 c "permHash" then errs := errs.push "permutation differs"
    if let some pj := c.get? "perm" then
      if natArr pj != p then errs := errs.push "permutation list differs"
  if checkPure && kind < 11 then
    let pure := javaSortBy (Array.range n) (cmpRaw kind seed keys)
    let same := match pure, res with
      | .ok p, .ok (.ok q) => p == q
      | .error e, .ok (.error e') => e == e'
      | _, _ => false
    if !same then errs := errs.push "pure javaSortBy differs from javaSortByM"
  return (errs, got)

/-- Parses a JSON-lines file of `TimSortTrace` cases. -/
def readCases (path : String) : IO (Except String (Array Elk.Json.Value)) := do
  let text ← IO.FS.readFile path
  let mut out := #[]
  for line in text.splitOn "\n" do
    if line.isEmpty then continue
    match Elk.Json.parseString line with
    | .ok v => out := out.push v
    | .error e => return .error e
  return .ok out

/-- `core.util.JavaSort.fixtures`. -/
def fixtureTests : Suite := suite "core.util.JavaSort.fixtures" do
  match ← readCases "tests/fixtures/timsort/cases.jsonl" with
  | .error e => report "parse cases.jsonl" false e
  | .ok cases =>
    check "at least 600 cases" (cases.size ≥ 600)
    let mut iae := 0
    let mut throws := 0
    let mut idx := 0
    for c in cases do
      let (errs, got) := runCase c true
      if got == "IAE" then iae := iae + 1
      if got == "throw" then throws := throws + 1
      report s!"case {idx} (n {getNat c "n"}, keyKind {getNat c "keyKind"}, cmp {getNat c "cmp"})"
        errs.isEmpty (", ".intercalate errs.toList)
      idx := idx + 1
    check "fixtures contain contract violations" (iae ≥ 20)
    check "fixtures contain comparator exceptions" (throws ≥ 40)

/-- `core.util.JavaSort.full` (`ELK_TIMSORT_CASES`). -/
def fullTests : Suite := suite "core.util.JavaSort.full" do
  let some path ← IO.getEnv "ELK_TIMSORT_CASES"
    | IO.println "SKIP core.util.JavaSort.full: ELK_TIMSORT_CASES not set"
  match ← readCases path with
  | .error e => report "parse cases" false e
  | .ok cases =>
    let mut bad := 0
    let mut ok := 0
    let mut iae := 0
    let mut throws := 0
    let mut maxN := 0
    for c in cases do
      let (errs, got) := runCase c true
      if got == "ok" then ok := ok + 1
      if got == "IAE" then iae := iae + 1
      if got == "throw" then throws := throws + 1
      maxN := max maxN (getNat c "n")
      if !errs.isEmpty then
        bad := bad + 1
        if bad ≤ 20 then
          IO.println s!"MISMATCH n {getNat c "n"} keyKind {getNat c "keyKind"} mod {getNat c "mod"} neg {getNat c "neg"} cmp {getNat c "cmp"} seed {getU64 c "seed"} k {getNat c "k"}: {", ".intercalate errs.toList}"
    let summary := s!"sorted {ok}, IllegalArgumentException {iae}, comparator exception {throws}"
    IO.println s!"JavaSort full differential: {cases.size - bad}/{cases.size} identical (max n {maxN}; {summary})"
    report s!"{cases.size} cases identical to Java (sequence, outcome, permutation)" (bad == 0)
      s!"{bad} mismatches"

/-- Linear congruential generator for the property tests. -/
private def lcg (s : UInt64) : UInt64 := s * 6364136223846793005 + 1442695040888963407

/-- `core.util.JavaSort.basics`. -/
def basicTests : Suite := suite "core.util.JavaSort.basics" do
  -- consistent comparators: any stable sort gives the same result
  let mut s : UInt64 := 42
  let mut agree := true
  for n in [0, 1, 2, 5, 31, 32, 33, 64, 65, 100, 257, 513, 1000, 2000, 10000] do
    for modulus in [3, 50, 100000] do
      let mut a : Array (Nat × Nat) := #[]
      for i in [0:n] do
        s := lcg s
        a := a.push ((s >>> 33).toNat % modulus, i)
      let cmp := fun (x y : Nat × Nat) => compare x.1 y.1
      match javaSortBy a cmp with
      | .ok r => if r != stableSort a cmp then agree := false
      | .error _ => agree := false
  check "consistent comparators agree with stableSort" agree
  match javaSortByKey #[(3, "c"), (1, "a"), (2, "b"), (1, "a2")] (·.1) with
  | .ok r => checkEq "javaSortByKey" (r.map (·.2)) #["a", "a2", "b", "c"]
  | .error e => report "javaSortByKey" false e
  -- `List.sort` of fewer than two elements calls no comparator
  let counted (xs : Array Nat) : Nat :=
    ((javaSortByM xs (fun a b => do modify (· + 1); return compare a b : Nat → Nat → StateM Nat Ordering)).run 0).2
  checkEq "size 0: no comparator call" (counted #[]) 0
  checkEq "size 1: no comparator call" (counted #[7]) 0
  checkEq "size 2: one comparator call" (counted #[2, 1]) 1
  -- strictly descending input: reversed after n - 1 comparisons (run detection)
  checkEq "descending input: n - 1 comparisons" (counted (Array.range 1000).reverse) 999
  match javaSortBy (Array.range 1000).reverse compare with
  | .ok r => checkEq "descending input sorted" r (Array.range 1000)
  | .error e => report "descending input sorted" false e
  -- non-strictly descending runs are not reversed: equal elements keep their order
  match javaSortBy #[(2, 0), (1, 1), (1, 2), (0, 3)] (fun x y => compare x.1 y.1) with
  | .ok r => checkEq "stable on descending runs with ties" (r.map (·.2)) #[3, 1, 2, 0]
  | .error e => report "stable on descending runs with ties" false e
  -- `minRunLength`
  checkEq "minRunLength" ([0, 31, 32, 33, 63, 64, 65, 100, 1024, 1025, 5000].map JavaSort.minRunLength)
    [0, 31, 16, 17, 32, 16, 17, 25, 16, 17, 20]
  -- a constant "less" comparator gives one strictly descending run: reversed, no merge, no exception
  checkEq "constant -1 comparator: reversed without exception"
    (javaSortBy (Array.range 100) (fun _ _ => .lt)).toOption (some (Array.range 100).reverse)
  -- the contract violation as a Java exception (Java: IllegalArgumentException after 212 calls)
  let keys := genKeys 65 6 3 0 8310734273246065464
  let r ← (javaSortByIO (Array.range 65)
    (fun a b => (pure (cmpRaw 4 8310734273246065464 keys a b) : IO Ordering))).toBaseIO
  match r with
  | .ok _ => report "javaSortByIO throws IllegalArgumentException" false "no exception"
  | .error e => checkEq "javaSortByIO throws IllegalArgumentException" (toString e) JavaSort.contractViolationError

/-- `core.util.JavaSort.bench` (`ELK_TIMSORT_BENCH=1`): `javaSortBy` vs `stableSort` on Float keys. -/
def benchTests : Suite := suite "core.util.JavaSort.bench" do
  if (← IO.getEnv "ELK_TIMSORT_BENCH").isNone then
    IO.println "SKIP core.util.JavaSort.bench: ELK_TIMSORT_BENCH not set"
    return
  for (n, reps) in [(1000, 2000), (100000, 20)] do
    let mut s : UInt64 := 7
    let mut a : Array Float := #[]
    for _ in [0:n] do
      s := lcg s
      a := a.push ((s >>> 11).toFloat / 9007199254740992.0)
    let cmp := fun (x y : Float) => if x < y then Ordering.lt else if x > y then .gt else .eq
    let t0 ← IO.monoNanosNow
    let mut chk := 0.0
    for i in [0:reps] do
      let r := stableSort (a.set! 0 (Float.ofNat i)) cmp
      chk := chk + r[n / 2]!
    let t1 ← IO.monoNanosNow
    for i in [0:reps] do
      match javaSortBy (a.set! 0 (Float.ofNat i)) cmp with
      | .ok r => chk := chk + r[n / 2]!
      | .error _ => pure ()
    let t2 ← IO.monoNanosNow
    let us (t : Nat) : Float := t.toFloat / reps.toFloat / 1000.0
    IO.println s!"bench n={n}: stableSort {us (t1 - t0)} us, javaSortBy {us (t2 - t1)} us per sort ({chk})"
  check "bench ran" true

/-- All `JavaSort` suites. -/
def suites : Array Suite := #[fixtureTests, fullTests, basicTests, benchTests]

end Tests.Core.JavaSort
