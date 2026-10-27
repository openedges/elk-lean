import Elk.Core.Util.Java
/-!
# `org.eclipse.elk.alg.layered.p3order.counting.BinaryIndexedTree`

Fenwick tree over `[0, maxNum)` counting how many entries were added per index (elk-rs
`binary_indexed_tree.rs`). Pure value; the counters keep it behind an `IO.Ref`.

Rust semantics kept: `add` beyond `maxNum` still increments `size` (but no bucket), `rank`
clamps the index to the tree size, `removeAll` ignores out-of-range indices.
-/
namespace Elk.Alg.Layered.P3Order.Counting

/-- `BinaryIndexedTree` (`binarySums` has `maxNum + 1` entries, slot 0 unused). -/
structure BinaryIndexedTree where
  binarySums : Array Int := #[0]
  numsPerIndex : Array Int := #[]
  size : Int := 0
  maxNum : Nat := 0
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
  if index >= t.numsPerIndex.size then { t with size := t.size + 1 }
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
  else t

/-- elk-rs `reset(maxNum)`: a fresh tree of the new size (Java creates a new tree). -/
def reset (_t : BinaryIndexedTree) (maxNum : Nat) : BinaryIndexedTree := new maxNum

/-- `clear()`: removes all entries, keeps the size. -/
def clear (t : BinaryIndexedTree) : BinaryIndexedTree :=
  { t with binarySums := Array.replicate t.binarySums.size 0, numsPerIndex := Array.replicate t.numsPerIndex.size 0, size := 0 }

/-- `isEmpty()`. -/
def isEmpty (t : BinaryIndexedTree) : Bool := t.size == 0

end BinaryIndexedTree

/-- Rust `x as usize` for an `i32` position/id: negative values wrap to huge indices (which
every consumer treats as out of range). -/
@[inline] def asUsize (v : Int) : Nat :=
  if v < 0 then (v + 18446744073709551616).toNat else v.toNat

end Elk.Alg.Layered.P3Order.Counting
