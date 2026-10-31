import Elk.Core.Util.Java
/-!
# `org.eclipse.elk.alg.layered.p3order.counting.BinaryIndexedTree`

Fenwick tree over `[0, maxNum)` counting how many entries were added per index (elk-rs
`binary_indexed_tree.rs`). Pure value; the counters keep it behind an `IO.Ref`.

Rust semantics kept: `add` beyond `maxNum` still increments `size` (but no bucket), `rank`
clamps the index to the tree size, `removeAll` ignores out-of-range indices. Both set `outOfRange`
(Java's `numsPerIndex[index]` would throw `ArrayIndexOutOfBoundsException`; a `rank` beyond the tree is
always followed by an `add` of the same index, so the flag also covers it) — the counters that can see
such indices turn it into Java's exception.
-/
namespace Elk.Alg.Layered.P3Order.Counting

/-- `BinaryIndexedTree` (`binarySums` has `maxNum + 1` entries, slot 0 unused). -/
structure BinaryIndexedTree where
  binarySums : Array Int := #[0]
  numsPerIndex : Array Int := #[]
  size : Int := 0
  maxNum : Nat := 0
  /-- An `add`/`removeAll` index was outside `[0, maxNum)` since the tree was created or cleared. -/
  outOfRange : Bool := false
  deriving Inhabited, Repr

namespace BinaryIndexedTree

/-- Lowest set bit of `i` (`i & i.wrapping_neg()`), `i > 0`. -/
@[inline] private def lowbit (i : Nat) : Nat := i - (i &&& (i - 1))

/-- `new BinaryIndexedTree(maxNum)`. -/
def new (maxNum : Nat) : BinaryIndexedTree :=
  { binarySums := Array.replicate (maxNum + 1) 0, numsPerIndex := Array.replicate maxNum 0, size := 0, maxNum }

/-- The update loop of `add`/`removeAll`: `sums[i] += delta` along the parents of `i`
(tail recursive, so the loop state is not boxed). -/
private partial def updateLoop (sums : Array Int) (i : Nat) (delta : Int) : Array Int :=
  if h : i < sums.size then updateLoop (sums.set i (sums[i] + delta)) (i + lowbit i) delta
  else sums

/-- The prefix sum loop of `rank`. -/
private partial def rankLoop (sums : Array Int) (i : Nat) (acc : Int) : Int :=
  if i > 0 then rankLoop sums (i - lowbit i) (acc + sums[i]!) else acc

/-- `add(index)`: one more entry at `index`. -/
def add (t : BinaryIndexedTree) (index : Nat) : BinaryIndexedTree :=
  if index >= t.numsPerIndex.size then { t with size := t.size + 1, outOfRange := true }
  else
    -- take the arrays out first so that they are updated in place
    let nums := t.numsPerIndex
    let sums := t.binarySums
    let t := { t with numsPerIndex := #[], binarySums := #[] }
    let nums := nums.modify index (· + 1)
    { t with numsPerIndex := nums, binarySums := updateLoop sums (index + 1) 1, size := t.size + 1 }

/-- `rank(index)`: number of entries at indices `< index`. -/
def rank (t : BinaryIndexedTree) (index : Nat) : Int :=
  rankLoop t.binarySums (Nat.min index (t.binarySums.size - 1)) 0

/-- `removeAll(index)`: drops all entries at `index`. -/
def removeAll (t : BinaryIndexedTree) (index : Nat) : BinaryIndexedTree :=
  if h : index < t.numsPerIndex.size then
    let numEntries := t.numsPerIndex[index]
    if numEntries == 0 then t
    else
      let nums := t.numsPerIndex
      let sums := t.binarySums
      let t := { t with numsPerIndex := #[], binarySums := #[] }
      let nums := nums.set! index 0
      { t with numsPerIndex := nums, binarySums := updateLoop sums (index + 1) (-numEntries), size := t.size - numEntries }
  else { t with outOfRange := true }

/-- `a` with every entry `0`, in place when unshared. -/
private partial def zeroFrom (a : Array Int) (i : Nat) : Array Int :=
  if h : i < a.size then zeroFrom (a.set i 0) (i + 1) else a

/-- `new maxNum` reusing the arrays of `t` when they have the sizes of a tree of `maxNum` buckets
(zeroed in place; Lean only): the same value as `new maxNum`, without allocating. -/
def renew (t : BinaryIndexedTree) (maxNum : Nat) : BinaryIndexedTree :=
  match t with
  | ⟨sums, nums, _, _, _⟩ =>
    if sums.size == maxNum + 1 && nums.size == maxNum then ⟨zeroFrom sums 0, zeroFrom nums 0, 0, maxNum, false⟩
    else new maxNum

/-- elk-rs `reset(maxNum)`: a fresh tree of the new size (Java creates a new tree). -/
def reset (_t : BinaryIndexedTree) (maxNum : Nat) : BinaryIndexedTree := new maxNum

/-- `clear()`: removes all entries, keeps the size. -/
def clear (t : BinaryIndexedTree) : BinaryIndexedTree :=
  { t with binarySums := Array.replicate t.binarySums.size 0, numsPerIndex := Array.replicate t.numsPerIndex.size 0, size := 0,
           outOfRange := false }

/-- `isEmpty()`. -/
def isEmpty (t : BinaryIndexedTree) : Bool := t.size == 0

end BinaryIndexedTree

/-! ## Packed tree loops

The between-layer crossing count (`CrossingsCounter.countCrossingsBetweenLayers` with a snapshot)
keeps a fresh tree of `n` buckets in one array `t` of `2 n + 1` `Nat`s: `t[1..n]` are `binarySums`
(slot `0` unused) and `t[n + 1 + x]` is `numsPerIndex[x]`. Counts never become negative; `size`
is not needed there. Tree indices are `USize`s (`i - lowbit i` is `i &&& (i - 1)`, `lowbit i` is
`i &&& (0 - i)`). -/

namespace BinaryIndexedTree

/-- `t[i] += 1` along the parents of `i` below `bound` (`n + 1`; `add`'s update loop). -/
partial def incLoopPacked (t : Array Nat) (bound i : USize) : Array Nat :=
  if i < bound then
    if h : i.toNat < t.size then incLoopPacked (t.uset i (t.uget i h + 1) h) bound (i + (i &&& (0 - i)))
    else t
  else t

/-- `t[i] -= delta` along the parents of `i` below `bound` (`removeAll`'s update loop). -/
partial def decLoopPacked (t : Array Nat) (bound i : USize) (delta : Nat) : Array Nat :=
  if i < bound then
    if h : i.toNat < t.size then decLoopPacked (t.uset i (t.uget i h - delta) h) bound (i + (i &&& (0 - i))) delta
    else t
  else t

/-- The prefix sum loop of `rank` on the packed sums. -/
partial def rankLoopPacked (t : Array Nat) (i : USize) (acc : Nat) : Nat :=
  if i == 0 then acc
  else if h : i.toNat < t.size then rankLoopPacked t (i &&& (i - 1)) (acc + t.uget i h)
  else acc

/-- `rank(index)` of a packed tree of `n` buckets. -/
@[inline] def rankPacked (t : Array Nat) (n index : Nat) : Nat :=
  rankLoopPacked t (Nat.min index n).toUSize 0

end BinaryIndexedTree

/-- Rust `x as usize` for an `i32` position/id: negative values wrap to huge indices (which
every consumer treats as out of range). -/
@[inline] def asUsize (v : Int) : Nat :=
  match v with
  | .ofNat n => n
  -- `-(m + 1) + 2^64`, `0` below `-2^64` (no `Int` comparison or big literal on the fast path)
  | .negSucc m => if (m + 1) >>> 64 != 0 then 0 else ((0 : UInt64) - (m + 1).toUInt64).toNat

end Elk.Alg.Layered.P3Order.Counting
