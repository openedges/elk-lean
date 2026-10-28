import Elk.Alg.Layered.Graph
import Elk.Core.Util.Sort
/-!
# `org.eclipse.elk.alg.layered.p3order.counting.CrossMinUtil`

elk-rs `cross_min_util.rs`, plus allocation-free helpers of the crossing minimisation hot loops
(no Java/Rust counterpart): a branch-free `PortSide` comparison (the derived `BEq` is an
out-of-line call) and `getPortSideView(side)` as an index range of the port list instead of a copy.
-/
namespace Elk.Alg.Layered.P3Order.Counting

open Elk.Core.Options Elk.Alg.Layered.Graph

/-- `0.0` as a global: a `Float` literal inside a loop is converted (`Float.ofScientific`) on
every evaluation, a global constant is a plain load. -/
def floatZero : Float := 0.0

/-- `1.0` as a global (see `floatZero`). -/
def floatOne : Float := 1.0

/-- `2.0` as a global (see `floatZero`). -/
def floatTwo : Float := 2.0

/-- `-1.0` as a global (see `floatZero`). -/
def floatMinusOne : Float := -1.0

/-- Rust `f64::min` with inline NaN tests (`x != x`; `Float.isNaN` is an out-of-line call). -/
@[inline] def fminInline (a b : Float) : Float :=
  if a != a then b else if b != b then a else if a < b then a else b

/-- Rust `f64::max` with inline NaN tests. -/
@[inline] def fmaxInline (a b : Float) : Float :=
  if a != a then b else if b != b then a else if a > b then a else b

/-- The inner loop of `insertionSortFrom`: shifts `x` down from position `j` (`> lo`) while the
element before it compares greater. -/
@[specialize] partial def insertDown {α : Type} [Inhabited α] (cmp : α → α → Ordering) (lo : Nat) (x : α) (j : Nat)
    (a : Array α) : Array α :=
  if j > lo then
    let y := a[j - 1]!
    if cmp y x == .gt then insertDown cmp lo x (j - 1) (a.setIfInBounds j y)
    else a.setIfInBounds j x
  else a.setIfInBounds j x

/-- Insertion sort of `a[lo:hi]` from position `i` on (positions `[lo, i)` are sorted). -/
@[specialize] partial def insertionSortFrom {α : Type} [Inhabited α] (cmp : α → α → Ordering) (lo hi i : Nat)
    (a : Array α) : Array α :=
  if i < hi then
    let x := a[i]!
    insertionSortFrom cmp lo hi (i + 1) (insertDown cmp lo x i a)
  else a

/-- `Elk.Core.Util.stableSort` for arrays of at most 16 elements (one insertion-sort run, the same
comparisons and moves, as tail-recursive loops without boxed loop state); longer arrays are
handed to `stableSort`. -/
@[inline] def stableSortSmall {α : Type} [Inhabited α] (as : Array α) (cmp : α → α → Ordering) : Array α :=
  if as.size < 2 then as
  else if as.size <= 16 then insertionSortFrom cmp 0 as.size 1 as
  else Elk.Core.Util.stableSort as cmp

/-! ### Keyed stable sort

`Elk.Core.Util.stableSort` (insertion sort of runs of 16, then bottom-up merges that take the right
element only when the left one compares greater) on the permutation `[0, n)` of key positions,
with `cmp i j == .gt` given as `gt i j` (specialised at each call site, so the keys are read
from unboxed arrays without a closure call). It performs the same comparisons and moves as
`stableSort` with the corresponding comparator and therefore returns the same permutation for
every comparator, also one that is not a total preorder (NaN keys). -/

/-- The inner insertion loop: moves `x` down from position `j` (not below `start`). -/
@[specialize] partial def keyedInsertDown (gt : Nat → Nat → Bool) (start x j : Nat) (a : Array Nat) : Array Nat :=
  if j > start then
    let y := a[j - 1]!
    if gt y x then keyedInsertDown gt start x (j - 1) (a.set! j y) else a.set! j x
  else a.set! j x

/-- Insertion sort of the run `a[start:stop]` from position `i`. -/
@[specialize] partial def keyedInsertRun (gt : Nat → Nat → Bool) (start stop i : Nat) (a : Array Nat) : Array Nat :=
  if i < stop then keyedInsertRun gt start stop (i + 1) (keyedInsertDown gt start a[i]! i a) else a

/-- Insertion sort of all runs of 16 from `start`. -/
@[specialize] partial def keyedInsertRuns (gt : Nat → Nat → Bool) (n start : Nat) (a : Array Nat) : Array Nat :=
  if start < n then
    let stop := min (start + 16) n
    keyedInsertRuns gt n stop (keyedInsertRun gt start stop (start + 1) a)
  else a

/-- Merges `src[i:mid]` and `src[j:hi]` into `dst[k:]`. -/
@[specialize] partial def keyedMerge (gt : Nat → Nat → Bool) (src : Array Nat) (mid hi i j k : Nat) (dst : Array Nat) :
    Array Nat :=
  if i < mid && j < hi then
    if gt src[i]! src[j]! then keyedMerge gt src mid hi i (j + 1) (k + 1) (dst.set! k src[j]!)
    else keyedMerge gt src mid hi (i + 1) j (k + 1) (dst.set! k src[i]!)
  else if i < mid then keyedMerge gt src mid hi (i + 1) j (k + 1) (dst.set! k src[i]!)
  else if j < hi then keyedMerge gt src mid hi i (j + 1) (k + 1) (dst.set! k src[j]!)
  else dst

/-- One bottom-up merge pass of width `width` from `lo`. -/
@[specialize] partial def keyedMergePass (gt : Nat → Nat → Bool) (n width lo : Nat) (src dst : Array Nat) : Array Nat :=
  if lo < n then
    let mid := min (lo + width) n
    let hi := min (lo + 2 * width) n
    keyedMergePass gt n width hi src (keyedMerge gt src mid hi lo mid lo dst)
  else dst

/-- The merge passes (`src`/`dst` swapped after each pass). -/
@[specialize] partial def keyedMergeAll (gt : Nat → Nat → Bool) (n width : Nat) (src dst : Array Nat) : Array Nat :=
  if width < n then
    let merged := keyedMergePass gt n width 0 src dst
    keyedMergeAll gt n (width * 2) merged src
  else src

/-- The stably sorted permutation of `[0, n)` (see "Keyed stable sort"). -/
@[inline] def keyedStableSort (n : Nat) (gt : Nat → Nat → Bool) : Array Nat :=
  let a := Array.range n
  if n < 2 then a
  else
    let runs := keyedInsertRuns gt n 0 a
    keyedMergeAll gt n 16 runs runs

/-- The constructor index of a `PortSide` (`ElkEnum.ordinal` as `UInt8`). -/
@[inline] def sideCode : PortSide → UInt8
  | .undefined => 0
  | .north => 1
  | .east => 2
  | .south => 3
  | .west => 4

/-- `a == b` on `PortSide`s without the out-of-line derived `BEq`. -/
@[inline] def sideIs (a b : PortSide) : Bool := sideCode a == sideCode b

/-- `getPortSideView(side)` of a node as the range `ports[lo:hi]` of its port list (see
`LGraphArena.nodePortSideView`). -/
structure SideView where
  lo : Nat
  hi : Nat

/-- The `SideView` of `getPortSideView(side)` of `nd` (exactly `LGraphArena.nodePortSideView`: the cached
or freshly found `[first, last)` range, clamped like `Array.extract`, not re-validated). -/
@[inline] def sideView (a : LGraphArena) (n : LNodeId) (nd : LNode) (side : PortSide) : SideView :=
  let indices := if nd.portSidesCached then
      match nd.portSideIndices with
      | some idx => idx
      | none => a.findPortIndices n
    else a.findPortIndices n
  match indices[ElkEnum.ordinal side]? with
  | some (some (first, last)) =>
    let hi := Nat.min last nd.ports.size
    if first >= hi then ⟨0, 0⟩ else ⟨first, hi⟩
  | _ => ⟨0, 0⟩

/-- Pushes `ports[i:hi]` (ascending) onto `out`. -/
partial def pushRange (ports : Array LPortId) (i hi : Nat) (out : Array LPortId) : Array LPortId :=
  if h : i < hi ∧ i < ports.size then pushRange ports (i + 1) hi (out.push ports[i]) else out

/-- Pushes `ports[lo:i]` (descending from `i - 1`) onto `out`. -/
partial def pushRangeRev (ports : Array LPortId) (lo i : Nat) (out : Array LPortId) : Array LPortId :=
  if lo < i then
    match ports[i - 1]? with
    | some p => pushRangeRev ports lo (i - 1) (out.push p)
    | none => pushRangeRev ports lo (i - 1) out
  else out

/-- Appends `getPortSideView(side)` of `node` (reversed with `rev`) to `out` without copying the view. -/
def appendSideView (a : LGraphArena) (node : LNodeId) (side : PortSide) (rev : Bool) (out : Array LPortId) :
    Array LPortId :=
  let nd := a.node node
  let v := sideView a node nd side
  if rev then pushRangeRev nd.ports v.lo v.hi out else pushRange nd.ports v.lo v.hi out

namespace CrossMinUtil

/-- `inNorthSouthEastWestOrder(node, side)`: the node's ports on `side` (`getPortSideView`)
ordered north→south on the east/west sides and west→east on the north/south sides, i.e.
`EAST`/`NORTH` as stored, `SOUTH`/`WEST` reversed; `UNDEFINED` yields no ports. -/
def inNorthSouthEastWestOrder (a : LGraphArena) (node : LNodeId) (side : PortSide) : Array LPortId :=
  match side with
  | .east | .north => a.nodePortSideView node side
  | .south | .west => (a.nodePortSideView node side).reverse
  | .undefined => #[]

end CrossMinUtil

end Elk.Alg.Layered.P3Order.Counting
