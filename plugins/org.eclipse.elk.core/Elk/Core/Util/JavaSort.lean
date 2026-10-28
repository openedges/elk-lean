/-!
# Java `java.util.TimSort`, exact port

ELK Java sorts with `Collections.sort(list, c)`, `List.sort(c)`, `Arrays.sort(T[], c)` and stream
`sorted(c)`; in OpenJDK 21 every one of them ends in `java.util.TimSort.sort` (unless the
`java.util.Arrays.useLegacyMergeSort` system property is set, which ELK never does):

* `Collections.sort(list, c)` → `list.sort(c)`;
* `ArrayList.sort(c)` → `Arrays.sort(elementData, 0, size, c)` (in place), `List.sort(c)` (default
  method, e.g. `LinkedList`, `Arrays.asList`) → `toArray()`, `Arrays.sort(a, c)`, write back;
* `Arrays.sort(a, c)` / `Arrays.sort(a, from, to, c)` → `TimSort.sort(a, lo, hi, c, null, 0, 0)`;
  with `c == null` → `Arrays.sort(a)` → `ComparableTimSort.sort`, which is the same algorithm with
  `((Comparable) x).compareTo(y)` in place of `c.compare(x, y)` (same argument order, same call
  points; verified against the JDK 21 source), so `javaSortBy as compare` covers it too;
* stream `sorted(c)` → `Arrays.sort(array, 0, n, c)` or `list.sort(c)`.

For a consistent comparator (a total preorder) every stable sort yields the same permutation as
`stableSort`. For inconsistent comparators (model-order comparators answering 0 when an order is
missing, layer-sweep comparators, NaN-tolerant float comparators) and for comparators that throw or
read changing state, the result depends on the exact comparison sequence, so this module ports
`java.util.TimSort` of OpenJDK 21 (`TimSort.java`, Temurin 21.0.13) statement by statement:
`sort` (binary insertion sort below `MIN_MERGE = 32`), `binarySort`, `countRunAndMakeAscending`
(only *strictly* descending runs, `compare < 0`, are reversed), `reverseRange`, `minRunLength`,
`pushRun`, `mergeCollapse` (the corrected JDK 8u60+ invariant with the `runLen[n-2]` check),
`mergeForceCollapse`, `mergeAt`, `gallopLeft`, `gallopRight` (including the `int` overflow guard),
`mergeLo`, `mergeHi` (`MIN_GALLOP = 7`, the adaptive `minGallop` carried across merges of one sort)
and the two points where Java throws
`IllegalArgumentException("Comparison method violates its general contract!")`.

The comparator is called with exactly the arguments and in exactly the order Java calls
`c.compare`; only the sign of the result matters (`< 0`, `>= 0`, `> 0`, `<= 0` tests), so the
comparator returns `Ordering`. Lists and arrays of size < 2 are returned without any comparator call.
The temporary array (`tmp`, `ensureCapacity`) is reproduced as a scratch array of length `n / 2`
(its length never influences a comparison). The fixed-size run stack (`runBase`/`runLen` of length
5/10/24/49) cannot overflow with the corrected `mergeCollapse` (run lengths do not depend on the
comparator), so it is a growable array here.

Differences from Java that are not observable in a returned result: when the comparator throws or
the contract violation is detected, Java leaves the (in-place) array partially merged; this port
returns only the error. Differential test: `scripts/run_timsort_diff.sh`
(`scripts/java/TimSortTrace.java` against a real JDK 21), fixtures in `tests/fixtures/timsort/`.
-/
namespace Elk.Core.Util

namespace JavaSort

/-- Message of the `IllegalArgumentException` thrown by `TimSort.mergeLo`/`mergeHi`. -/
def contractViolationMessage : String := "Comparison method violates its general contract!"

/-- The Java exception text in the project's `IO.userError` convention. -/
def contractViolationError : String :=
  "java.lang.IllegalArgumentException: " ++ contractViolationMessage

/-- `TimSort.MIN_MERGE`. -/
def minMerge : Nat := 32

/-- `TimSort.MIN_GALLOP`. -/
def minGallopInit : Nat := 7

/-- Sorting monad: the comparator's monad plus the contract-violation exit. -/
abbrev SortM (m : Type → Type) := ExceptT String m

/-- `TimSort.minRunLength`. -/
def minRunLength (n : Nat) : Nat := Id.run do
  let mut n := n
  let mut r := 0
  while n ≥ minMerge do
    r := r ||| (n &&& 1)
    n := n >>> 1
  return n + r

/-- `ofs = (ofs << 1) + 1; if (ofs <= 0) ofs = maxOfs;` on Java `int`. -/
@[inline] def nextOfs (ofs maxOfs : Nat) : Nat :=
  let o := 2 * ofs + 1
  if o ≥ 2147483648 then maxOfs else o

variable {α : Type} [Inhabited α]

/-- `System.arraycopy(a, src, a, dst, len)` within one array (overlap-safe). -/
@[inline] def copyWithin (a : Array α) (src dst len : Nat) : Array α := Id.run do
  let mut a := a
  if dst ≤ src then
    for i in [0:len] do
      a := a.set! (dst + i) a[src + i]!
  else
    for k in [0:len] do
      let i := len - 1 - k
      a := a.set! (dst + i) a[src + i]!
  return a

/-- `System.arraycopy(src, sp, dst, dp, len)` between two arrays. -/
@[inline] def copyInto (src : Array α) (sp : Nat) (dst : Array α) (dp len : Nat) : Array α := Id.run do
  let mut dst := dst
  for i in [0:len] do
    dst := dst.set! (dp + i) src[sp + i]!
  return dst

/-- `TimSort.reverseRange`: reverses `a[lo..hi)`. -/
def reverseRange (a : Array α) (lo hi : Nat) : Array α := Id.run do
  let mut a := a
  let mut i := lo
  let mut j := hi
  while i + 1 < j do
    j := j - 1
    let t := a[i]!
    a := a.set! i a[j]!
    a := a.set! j t
    i := i + 1
  return a

variable {m : Type → Type} [Monad m]

/-- `TimSort.binarySort`: sorts `a[lo..hi)` assuming `a[lo..start)` is sorted. -/
@[specialize] def binarySort (cmp : α → α → SortM m Ordering) (a : Array α) (lo hi start : Nat) :
    SortM m (Array α) := do
  let mut a := a
  let start := if start == lo then start + 1 else start
  for s in [start:hi] do
    let pivot := a[s]!
    let mut left := lo
    let mut right := s
    while left < right do
      let mid := (left + right) / 2
      if (← cmp pivot a[mid]!) == .lt then
        right := mid
      else
        left := mid + 1
    a := copyWithin a left (left + 1) (s - left)
    a := a.set! left pivot
  return a

/-- `TimSort.countRunAndMakeAscending`: length of the run starting at `lo` (`lo < hi`); a strictly
descending run is reversed in place. -/
@[specialize] def countRunAndMakeAscending (cmp : α → α → SortM m Ordering) (a : Array α) (lo hi : Nat) :
    SortM m (Array α × Nat) := do
  let mut runHi := lo + 1
  if runHi == hi then return (a, 1)
  let first ← cmp a[runHi]! a[lo]!
  runHi := runHi + 1
  if first == .lt then
    let mut go := true
    while go && runHi < hi do
      if (← cmp a[runHi]! a[runHi - 1]!) == .lt then runHi := runHi + 1 else go := false
    return (reverseRange a lo runHi, runHi - lo)
  else
    let mut go := true
    while go && runHi < hi do
      if (← cmp a[runHi]! a[runHi - 1]!) != .lt then runHi := runHi + 1 else go := false
    return (a, runHi - lo)

/-- `TimSort.gallopLeft`: leftmost insertion point of `key` in the sorted range `arr[base..base+len)`
(`len > 0`, `hint < len`). -/
@[specialize] def gallopLeft (cmp : α → α → SortM m Ordering) (key : α) (arr : Array α) (base len hint : Nat) :
    SortM m Nat := do
  let mut lastOfs := 0
  let mut ofs := 1
  -- `lo = lastOfs + 1`, `hi = ofs` of the final binary search
  let mut lo := 0
  let mut hi := 0
  if (← cmp key arr[base + hint]!) == .gt then
    let maxOfs := len - hint
    let mut go := true
    while go && ofs < maxOfs do
      if (← cmp key arr[base + hint + ofs]!) == .gt then
        lastOfs := ofs
        ofs := nextOfs ofs maxOfs
      else go := false
    if ofs > maxOfs then ofs := maxOfs
    lo := lastOfs + hint + 1
    hi := ofs + hint
  else
    let maxOfs := hint + 1
    let mut go := true
    while go && ofs < maxOfs do
      if (← cmp key arr[base + hint - ofs]!) != .gt then
        lastOfs := ofs
        ofs := nextOfs ofs maxOfs
      else go := false
    if ofs > maxOfs then ofs := maxOfs
    lo := hint + 1 - ofs
    hi := hint - lastOfs
  while lo < hi do
    let mid := lo + (hi - lo) / 2
    if (← cmp key arr[base + mid]!) == .gt then lo := mid + 1 else hi := mid
  return hi

/-- `TimSort.gallopRight`: rightmost insertion point of `key` in the sorted range
`arr[base..base+len)` (`len > 0`, `hint < len`). -/
@[specialize] def gallopRight (cmp : α → α → SortM m Ordering) (key : α) (arr : Array α) (base len hint : Nat) :
    SortM m Nat := do
  let mut lastOfs := 0
  let mut ofs := 1
  let mut lo := 0
  let mut hi := 0
  if (← cmp key arr[base + hint]!) == .lt then
    let maxOfs := hint + 1
    let mut go := true
    while go && ofs < maxOfs do
      if (← cmp key arr[base + hint - ofs]!) == .lt then
        lastOfs := ofs
        ofs := nextOfs ofs maxOfs
      else go := false
    if ofs > maxOfs then ofs := maxOfs
    lo := hint + 1 - ofs
    hi := hint - lastOfs
  else
    let maxOfs := len - hint
    let mut go := true
    while go && ofs < maxOfs do
      if (← cmp key arr[base + hint + ofs]!) != .lt then
        lastOfs := ofs
        ofs := nextOfs ofs maxOfs
      else go := false
    if ofs > maxOfs then ofs := maxOfs
    lo := lastOfs + hint + 1
    hi := ofs + hint
  while lo < hi do
    let mid := lo + (hi - lo) / 2
    if (← cmp key arr[base + mid]!) == .lt then hi := mid else lo := mid + 1
  return hi

/-- `TimSort.mergeLo`: merges `a[base1..base1+len1)` and `a[base2..base2+len2)` (`len1 ≤ len2`,
first element of run 2 < first of run 1, last of run 1 > all of run 2) left to right, with run 1 in
`tmp`. Returns the arrays and the written-back `minGallop`. -/
@[specialize] def mergeLo (cmp : α → α → SortM m Ordering) (a tmp : Array α) (minGallop0 : Nat)
    (base1 len1 base2 len2 : Nat) : SortM m (Array α × Array α × Nat) := do
  let mut tmp := copyInto a base1 tmp 0 len1
  let mut a := a
  let mut len1 := len1
  let mut len2 := len2
  let mut cursor1 := 0
  let mut cursor2 := base2
  let mut dest := base1
  a := a.set! dest a[cursor2]!
  dest := dest + 1
  cursor2 := cursor2 + 1
  len2 := len2 - 1
  if len2 == 0 then
    return (copyInto tmp cursor1 a dest len1, tmp, minGallop0)
  if len1 == 1 then
    a := copyWithin a cursor2 dest len2
    return (a.set! (dest + len2) tmp[cursor1]!, tmp, minGallop0)
  let mut minGallop : Int := minGallop0
  let mut done := false
  while !done do
    let mut count1 := 0
    let mut count2 := 0
    -- straight merge until one run starts winning consistently
    let mut straight := true
    while straight do
      if (← cmp a[cursor2]! tmp[cursor1]!) == .lt then
        a := a.set! dest a[cursor2]!
        dest := dest + 1
        cursor2 := cursor2 + 1
        count2 := count2 + 1
        count1 := 0
        len2 := len2 - 1
        if len2 == 0 then
          done := true
          straight := false
      else
        a := a.set! dest tmp[cursor1]!
        dest := dest + 1
        cursor1 := cursor1 + 1
        count1 := count1 + 1
        count2 := 0
        len1 := len1 - 1
        if len1 == 1 then
          done := true
          straight := false
      if straight && !(Int.ofNat (count1 ||| count2) < minGallop) then straight := false
    if !done then
      -- galloping
      let mut gallop := true
      while gallop do
        count1 ← gallopRight cmp a[cursor2]! tmp cursor1 len1 0
        if count1 != 0 then
          a := copyInto tmp cursor1 a dest count1
          dest := dest + count1
          cursor1 := cursor1 + count1
          len1 := len1 - count1
          if len1 ≤ 1 then
            done := true
            gallop := false
        if gallop then
          a := a.set! dest a[cursor2]!
          dest := dest + 1
          cursor2 := cursor2 + 1
          len2 := len2 - 1
          if len2 == 0 then
            done := true
            gallop := false
        if gallop then
          count2 ← gallopLeft cmp tmp[cursor1]! a cursor2 len2 0
          if count2 != 0 then
            a := copyWithin a cursor2 dest count2
            dest := dest + count2
            cursor2 := cursor2 + count2
            len2 := len2 - count2
            if len2 == 0 then
              done := true
              gallop := false
        if gallop then
          a := a.set! dest tmp[cursor1]!
          dest := dest + 1
          cursor1 := cursor1 + 1
          len1 := len1 - 1
          if len1 == 1 then
            done := true
            gallop := false
        if gallop then
          minGallop := minGallop - 1
          if !(count1 ≥ minGallopInit || count2 ≥ minGallopInit) then gallop := false
      if !done then
        if minGallop < 0 then minGallop := 0
        minGallop := minGallop + 2
  let mg := if minGallop < 1 then 1 else minGallop.toNat
  if len1 == 1 then
    a := copyWithin a cursor2 dest len2
    return (a.set! (dest + len2) tmp[cursor1]!, tmp, mg)
  else if len1 == 0 then
    throw contractViolationMessage
  else
    return (copyInto tmp cursor1 a dest len1, tmp, mg)

/-- `TimSort.mergeHi`: like `mergeLo` but right to left with run 2 in `tmp` (`len1 ≥ len2`).
Cursors are kept as `index + 1` (`c1`, `c2`, `d`), since Java's reach `-1`. -/
@[specialize] def mergeHi (cmp : α → α → SortM m Ordering) (a tmp : Array α) (minGallop0 : Nat)
    (base1 len1 base2 len2 : Nat) : SortM m (Array α × Array α × Nat) := do
  let mut tmp := copyInto a base2 tmp 0 len2
  let mut a := a
  let mut len1 := len1
  let mut len2 := len2
  let mut c1 := base1 + len1   -- cursor1 + 1
  let mut c2 := len2           -- cursor2 + 1
  let mut d := base2 + len2    -- dest + 1
  a := a.set! (d - 1) a[c1 - 1]!
  d := d - 1
  c1 := c1 - 1
  len1 := len1 - 1
  if len1 == 0 then
    return (copyInto tmp 0 a (d - len2) len2, tmp, minGallop0)
  if len2 == 1 then
    d := d - len1
    c1 := c1 - len1
    a := copyWithin a c1 d len1
    return (a.set! (d - 1) tmp[c2 - 1]!, tmp, minGallop0)
  let mut minGallop : Int := minGallop0
  let mut done := false
  while !done do
    let mut count1 := 0
    let mut count2 := 0
    let mut straight := true
    while straight do
      if (← cmp tmp[c2 - 1]! a[c1 - 1]!) == .lt then
        a := a.set! (d - 1) a[c1 - 1]!
        d := d - 1
        c1 := c1 - 1
        count1 := count1 + 1
        count2 := 0
        len1 := len1 - 1
        if len1 == 0 then
          done := true
          straight := false
      else
        a := a.set! (d - 1) tmp[c2 - 1]!
        d := d - 1
        c2 := c2 - 1
        count2 := count2 + 1
        count1 := 0
        len2 := len2 - 1
        if len2 == 1 then
          done := true
          straight := false
      if straight && !(Int.ofNat (count1 ||| count2) < minGallop) then straight := false
    if !done then
      let mut gallop := true
      while gallop do
        let r1 ← gallopRight cmp tmp[c2 - 1]! a base1 len1 (len1 - 1)
        count1 := len1 - r1
        if count1 != 0 then
          d := d - count1
          c1 := c1 - count1
          len1 := len1 - count1
          a := copyWithin a c1 d count1
          if len1 == 0 then
            done := true
            gallop := false
        if gallop then
          a := a.set! (d - 1) tmp[c2 - 1]!
          d := d - 1
          c2 := c2 - 1
          len2 := len2 - 1
          if len2 == 1 then
            done := true
            gallop := false
        if gallop then
          let r2 ← gallopLeft cmp a[c1 - 1]! tmp 0 len2 (len2 - 1)
          count2 := len2 - r2
          if count2 != 0 then
            d := d - count2
            c2 := c2 - count2
            len2 := len2 - count2
            a := copyInto tmp c2 a d count2
            if len2 ≤ 1 then
              done := true
              gallop := false
        if gallop then
          a := a.set! (d - 1) a[c1 - 1]!
          d := d - 1
          c1 := c1 - 1
          len1 := len1 - 1
          if len1 == 0 then
            done := true
            gallop := false
        if gallop then
          minGallop := minGallop - 1
          if !(count1 ≥ minGallopInit || count2 ≥ minGallopInit) then gallop := false
      if !done then
        if minGallop < 0 then minGallop := 0
        minGallop := minGallop + 2
  let mg := if minGallop < 1 then 1 else minGallop.toNat
  if len2 == 1 then
    d := d - len1
    c1 := c1 - len1
    a := copyWithin a c1 d len1
    return (a.set! (d - 1) tmp[c2 - 1]!, tmp, mg)
  else if len2 == 0 then
    throw contractViolationMessage
  else
    return (copyInto tmp 0 a (d - len2) len2, tmp, mg)

/-- Run stack and merge state of one `TimSort` instance (`a`, `tmp`, `minGallop`, `runBase`,
`runLen`). -/
abbrev MergeState (α : Type) := Array α × Array α × Nat × Array Nat × Array Nat

/-- `TimSort.mergeAt`: merges the runs `i` and `i + 1` of the stack (`i = size - 2` or `size - 3`). -/
@[specialize] def mergeAt (cmp : α → α → SortM m Ordering) (st : MergeState α) (i : Nat) :
    SortM m (MergeState α) := do
  let (a, tmp, mg, runBase, runLen) := st
  let base1 := runBase[i]!
  let len1 := runLen[i]!
  let base2 := runBase[i + 1]!
  let len2 := runLen[i + 1]!
  let size := runLen.size
  let mut runBase := runBase
  let mut runLen := runLen.set! i (len1 + len2)
  if i + 3 == size then
    runBase := runBase.set! (i + 1) runBase[i + 2]!
    runLen := runLen.set! (i + 1) runLen[i + 2]!
  runBase := runBase.pop
  runLen := runLen.pop
  let k ← gallopRight cmp a[base2]! a base1 len1 0
  let base1 := base1 + k
  let len1 := len1 - k
  if len1 == 0 then return (a, tmp, mg, runBase, runLen)
  let len2 ← gallopLeft cmp a[base1 + len1 - 1]! a base2 len2 (len2 - 1)
  if len2 == 0 then return (a, tmp, mg, runBase, runLen)
  let (a, tmp, mg) ←
    if len1 ≤ len2 then mergeLo cmp a tmp mg base1 len1 base2 len2
    else mergeHi cmp a tmp mg base1 len1 base2 len2
  return (a, tmp, mg, runBase, runLen)

/-- `TimSort.mergeCollapse` (JDK 8u60+ version, checking the last four runs). -/
@[specialize] def mergeCollapse (cmp : α → α → SortM m Ordering) (st : MergeState α) :
    SortM m (MergeState α) := do
  let mut st := st
  let mut go := true
  while go && st.2.2.2.2.size > 1 do
    let runLen := st.2.2.2.2
    let mut n := runLen.size - 2
    if (n > 0 && runLen[n - 1]! ≤ runLen[n]! + runLen[n + 1]!) ||
        (n > 1 && runLen[n - 2]! ≤ runLen[n]! + runLen[n - 1]!) then
      if runLen[n - 1]! < runLen[n + 1]! then n := n - 1
      st ← mergeAt cmp st n
    else if runLen[n]! > runLen[n + 1]! then
      go := false
    else
      st ← mergeAt cmp st n
  return st

/-- `TimSort.mergeForceCollapse`. -/
@[specialize] def mergeForceCollapse (cmp : α → α → SortM m Ordering) (st : MergeState α) :
    SortM m (MergeState α) := do
  let mut st := st
  while st.2.2.2.2.size > 1 do
    let runLen := st.2.2.2.2
    let mut n := runLen.size - 2
    if n > 0 && runLen[n - 1]! < runLen[n + 1]! then n := n - 1
    st ← mergeAt cmp st n
  return st

/-- `TimSort.sort(a, lo, hi, c, null, 0, 0)`: sorts `a[lo..hi)`. -/
@[specialize] def sortRange (cmp : α → α → SortM m Ordering) (a : Array α) (lo hi : Nat) :
    SortM m (Array α) := do
  let nRemaining := hi - lo
  if nRemaining < 2 then return a
  if nRemaining < minMerge then
    let (a, initRunLen) ← countRunAndMakeAscending cmp a lo hi
    return ← binarySort cmp a lo hi (lo + initRunLen)
  let tmp := Array.replicate (nRemaining / 2) (default : α)
  let minRun := minRunLength nRemaining
  let mut st : MergeState α := (a, tmp, minGallopInit, #[], #[])
  let mut lo := lo
  let mut nRemaining := nRemaining
  while nRemaining != 0 do
    let (a, tmp, mg, runBase, runLen) := st
    let (a, rl) ← countRunAndMakeAscending cmp a lo hi
    let mut a := a
    let mut rl := rl
    if rl < minRun then
      let force := if nRemaining ≤ minRun then nRemaining else minRun
      a ← binarySort cmp a lo (lo + force) (lo + rl)
      rl := force
    st ← mergeCollapse cmp (a, tmp, mg, runBase.push lo, runLen.push rl)
    lo := lo + rl
    nRemaining := nRemaining - rl
  st ← mergeForceCollapse cmp st
  return st.1

end JavaSort

open JavaSort in
/-- Java `List.sort(c)` / `Collections.sort(list, c)` / `Arrays.sort(a, c)` (OpenJDK 21
`java.util.TimSort`) with a monadic comparator: the comparator is called with exactly the argument
sequence Java uses, so stateful or throwing comparators (exceptions of `m` propagate unchanged)
observe the same history. Returns `.error JavaSort.contractViolationMessage` where Java throws
`IllegalArgumentException("Comparison method violates its general contract!")`. -/
@[specialize] def javaSortByM {m : Type → Type} {α : Type} [Monad m] [Inhabited α] (as : Array α)
    (cmp : α → α → m Ordering) : m (Except String (Array α)) :=
  ExceptT.run (sortRange (fun a b => (ExceptT.lift (cmp a b) : SortM m Ordering)) as 0 as.size)

/-- `javaSortByM` with a pure comparator. -/
@[specialize] def javaSortBy {α : Type} [Inhabited α] (as : Array α) (cmp : α → α → Ordering) :
    Except String (Array α) :=
  Id.run (javaSortByM as (fun a b => pure (cmp a b)))

/-- `javaSortBy` with `Comparator.comparing(key)` (`compare (key a) (key b)`). -/
@[specialize] def javaSortByKey {α κ : Type} [Inhabited α] [Ord κ] (as : Array α) (key : α → κ) :
    Except String (Array α) :=
  javaSortBy as (fun a b => compare (key a) (key b))

/-- `javaSortByM` in a monad with `IO.Error` exceptions: the contract violation is thrown as
`IO.userError "java.lang.IllegalArgumentException: Comparison method violates its general contract!"`
(the exception Java propagates out of the sort). -/
@[specialize] def javaSortByIO {m : Type → Type} {α : Type} [Monad m] [MonadExceptOf IO.Error m]
    [Inhabited α] (as : Array α) (cmp : α → α → m Ordering) : m (Array α) := do
  match ← javaSortByM as cmp with
  | .ok r => return r
  | .error _ => throw (IO.userError JavaSort.contractViolationError)

end Elk.Core.Util
