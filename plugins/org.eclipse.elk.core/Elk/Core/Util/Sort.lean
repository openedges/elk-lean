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
