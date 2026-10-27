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

/-- `add(index)`: one more entry at `index`. -/
def add (t : BinaryIndexedTree) (index : Nat) : BinaryIndexedTree := Id.run do
  let t := { t with size := t.size + 1 }
  if index >= t.numsPerIndex.size then return t
  let mut nums := t.numsPerIndex
  nums := nums.modify index (· + 1)
  let mut sums := t.binarySums
  let mut i := index + 1
  while i < sums.size do
    sums := sums.modify i (· + 1)
    i := i + lowbit i
  return { t with numsPerIndex := nums, binarySums := sums }

/-- `rank(index)`: number of entries at indices `< index`. -/
def rank (t : BinaryIndexedTree) (index : Nat) : Int := Id.run do
  let mut i := Nat.min index (t.binarySums.size - 1)
  let mut sum : Int := 0
  while i > 0 do
    sum := sum + t.binarySums[i]!
    i := i - lowbit i
  return sum

/-- `removeAll(index)`: drops all entries at `index`. -/
def removeAll (t : BinaryIndexedTree) (index : Nat) : BinaryIndexedTree := Id.run do
  if index >= t.numsPerIndex.size then return t
  let numEntries := t.numsPerIndex[index]!
  if numEntries == 0 then return t
  let nums := t.numsPerIndex.set! index 0
  let mut sums := t.binarySums
  let mut i := index + 1
  while i < sums.size do
    sums := sums.modify i (· - numEntries)
    i := i + lowbit i
  return { t with numsPerIndex := nums, binarySums := sums, size := t.size - numEntries }

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
