import Elk.Core.Util.FastFloat
/-!
# Stable sorting

Java's `Collections.sort`/`List.sort` (TimSort) and Rust's `slice::sort_by`
are stable. Lean's `Array.qsort` is not, so all ports use `stableSort` with a
Java-style comparator returning `Ordering`.
-/
namespace Elk.Core.Util

/-- Stable merge sort (insertion sort on runs of 16, then bottom-up merges).
Elements comparing equal keep their input order. -/
@[specialize] def stableSort {α : Type} [Inhabited α] (as : Array α) (cmp : α → α → Ordering) : Array α := Id.run do
  let n := as.size
  if n < 2 then return as
  let run := 16
  let mut a := as
  -- insertion sort each run
  let mut start := 0
  while start < n do
    let stop := min (start + run) n
    let mut i := start + 1
    while i < stop do
      let x := a[i]!
      let mut j := i
      while j > start && cmp a[j - 1]! x == .gt do
        a := a.set! j a[j - 1]!
        j := j - 1
      a := a.set! j x
      i := i + 1
    start := stop
  -- bottom-up merges
  let mut width := run
  let mut src := a
  let mut dst := a
  while width < n do
    let mut lo := 0
    while lo < n do
      let mid := min (lo + width) n
      let hi := min (lo + 2 * width) n
      let mut i := lo
      let mut j := mid
      let mut k := lo
      while i < mid && j < hi do
        if cmp src[i]! src[j]! == .gt then
          dst := dst.set! k src[j]!
          j := j + 1
        else
          dst := dst.set! k src[i]!
          i := i + 1
        k := k + 1
      while i < mid do
        dst := dst.set! k src[i]!
        i := i + 1
        k := k + 1
      while j < hi do
        dst := dst.set! k src[j]!
        j := j + 1
        k := k + 1
      lo := hi
    let tmp := src
    src := dst
    dst := tmp
    width := width * 2
  return src

namespace StableSortTR

/-- Insertion of `x` (taken from index `j`) into the sorted prefix `a[start, j)`: shifts the
elements comparing `.gt` to `x` one to the right (`while j > start && cmp a[j - 1] x == .gt`). -/
@[specialize] partial def shift {α : Type} [Inhabited α] (cmp : α → α → Ordering) (a : Array α)
    (start j : Nat) (x : α) : Array α :=
  if j > start then
    let y := a[j - 1]!
    if cmp y x == .gt then shift cmp (a.set! j y) start (j - 1) x else a.set! j x
  else a.set! j x

/-- Insertion sort of the run `a[start, stop)` from index `i` on. -/
@[specialize] partial def insertRun {α : Type} [Inhabited α] (cmp : α → α → Ordering) (a : Array α)
    (start stop i : Nat) : Array α :=
  if i < stop then
    let x := a[i]!
    insertRun cmp (shift cmp a start i x) start stop (i + 1)
  else a

/-- Insertion sort of every run of 16 from `start` on. -/
@[specialize] partial def insertRuns {α : Type} [Inhabited α] (cmp : α → α → Ordering) (a : Array α)
    (n start : Nat) : Array α :=
  if start < n then
    let stop := min (start + 16) n
    insertRuns cmp (insertRun cmp a start stop (start + 1)) n stop
  else a

/-- Copies `src[i, stop)` to `dst[k, ..)`. -/
@[specialize] partial def copyTail {α : Type} [Inhabited α] (src dst : Array α) (i stop k : Nat) : Array α :=
  if i < stop then copyTail src (dst.set! k src[i]!) (i + 1) stop (k + 1) else dst

/-- Merges `src[i, mid)` and `src[j, hi)` into `dst[k, ..)` (the right element is taken when the
left one compares `.gt` to it). -/
@[specialize] partial def merge {α : Type} [Inhabited α] (cmp : α → α → Ordering) (src dst : Array α)
    (i mid j hi k : Nat) : Array α :=
  if i < mid && j < hi then
    let x := src[i]!
    let y := src[j]!
    if cmp x y == .gt then merge cmp src (dst.set! k y) i mid (j + 1) hi (k + 1)
    else merge cmp src (dst.set! k x) (i + 1) mid j hi (k + 1)
  else
    copyTail src (copyTail src dst i mid k) j hi (k + (mid - i))

/-- One merge pass of width `width` from `lo` on. -/
@[specialize] partial def mergePass {α : Type} [Inhabited α] (cmp : α → α → Ordering) (src dst : Array α)
    (n width lo : Nat) : Array α :=
  if lo < n then
    let mid := min (lo + width) n
    let hi := min (lo + 2 * width) n
    mergePass cmp src (merge cmp src dst lo mid mid hi lo) n width hi
  else dst

/-- The merge passes for `width, 2 * width, …` while `width < n`. -/
@[specialize] partial def mergeAll {α : Type} [Inhabited α] (cmp : α → α → Ordering) (src dst : Array α)
    (n width : Nat) : Array α :=
  if width < n then
    let dst := mergePass cmp src dst n width 0
    mergeAll cmp dst src n (width * 2)
  else src

end StableSortTR

/-- `stableSort` written with tail-recursive loops (no loop state tuples): the same algorithm
(insertion sort on runs of 16, then bottom-up merges), so the comparator is called on the same
pairs in the same order and the result is the same as `stableSort` for every comparator,
including inconsistent ones (differential test `core.util.sort.stableSortTR`). -/
@[specialize] def stableSortTR {α : Type} [Inhabited α] (as : Array α) (cmp : α → α → Ordering) : Array α :=
  let n := as.size
  if n < 2 then as
  else
    let a := StableSortTR.insertRuns cmp as n 0
    StableSortTR.mergeAll cmp a a n 16

/-- Stable sort by a key with a `compare` function on keys. -/
@[inline] def stableSortByKey {α κ : Type} [Inhabited α] [Ord κ] (as : Array α) (key : α → κ) : Array α :=
  stableSort as (fun a b => compare (key a) (key b))

/-- Stable sort by a `Float` key (NaN compares equal, like Rust `partial_cmp().unwrap_or(Equal)`). -/
@[inline] def stableSortByFloat {α : Type} [Inhabited α] (as : Array α) (key : α → Float) : Array α :=
  stableSort as (fun a b =>
    let x := key a
    let y := key b
    if x < y then .lt else if x > y then .gt else .eq)

/-- Java `Comparator.compare` style helper: `Integer.compare`. -/
@[inline] def compareInt (a b : Int) : Ordering := compare a b

/-- `Double.compare`-like partial ordering helper for comparator chains. -/
@[inline] def compareFloat (a b : Float) : Ordering :=
  if a < b then .lt else if a > b then .gt else .eq

/-- Chain two comparisons (`thenComparing`). -/
@[inline] def Ordering.thenCmp (o : Ordering) (next : Unit → Ordering) : Ordering :=
  match o with
  | .eq => next ()
  | o => o

/-- Java `Integer.compare` / `Long.compare` returning the sign as an `Int` (`-1`, `0`, `1`). -/
@[inline] def Ordering.toInt : Ordering → Int
  | .lt => -1
  | .eq => 0
  | .gt => 1

/-- Comparator from a Java-style `int`-returning compare function. -/
@[inline] def ofIntCmp (f : Int) : Ordering := if f < 0 then .lt else if f > 0 then .gt else .eq

/-- Java `Collections.reverse` / Rust `reverse` are in `Array.reverse`; this reverses a comparator. -/
@[inline] def reverseCmp {α : Type} (cmp : α → α → Ordering) : α → α → Ordering :=
  fun a b => cmp b a

end Elk.Core.Util
