import Elk.Core.Util.FastFloat
/-!
# Rust `slice::sort_by` (driftsort), exact port

elk-rs sorts with `slice::sort_by` / `slice::sort_by_key`. For a consistent
comparator any stable sort gives the same result as `stableSort`, but several
elk-rs comparators are not total orders (model-order comparators that answer
"equal" when an order is missing, NaN-tolerant float comparators). For those
the result depends on the exact comparison sequence and element moves of
Rust's implementation, so this module ports the Rust 1.97.1 standard library
stable sort itself:

* `alloc/src/slice.rs`: `sort_by` (`is_less = compare(a, b) == Less`),
  `sort_by_key` (`f(a).lt(&f(b))`), `stable_sort`, `Vec` as `BufGuard`
  (heap scratch of exactly the requested capacity);
* `core/src/slice/sort/stable/mod.rs`: `sort` (insertion sort up to 20
  elements), `driftsort_main` (scratch length policy, 4 KiB stack scratch,
  `eager_sort`);
* `core/src/slice/sort/stable/drift.rs`: `sort`, `create_run`,
  `logical_merge`, `stable_quicksort`, `merge_tree_depth`, `sqrt_approx`;
* `core/src/slice/sort/stable/quicksort.rs`: `quicksort`,
  `stable_partition`;
* `core/src/slice/sort/stable/merge.rs`: `merge` (`MergeState::merge_up`,
  `merge_down`, `Drop`);
* `core/src/slice/sort/shared/mod.rs`: `find_existing_run`;
* `core/src/slice/sort/shared/pivot.rs`: `choose_pivot`, `median3_rec`,
  `median3`;
* `core/src/slice/sort/shared/smallsort.rs`: the `T: Freeze` specialisation
  of `StableSmallSortTypeImpl` (`SMALL_SORT_GENERAL_THRESHOLD = 32`,
  `small_sort_general_with_scratch`, `sort8_stable` for
  `size_of::<T>() <= 16`, `sort4_stable`, `insert_tail`,
  `insertion_sort_shift_left`, `bidirectional_merge`,
  `panic_on_ord_violation`).

Specialisation: every type elk-rs sorts (`Arc<..>`/`Rc<..>` handles,
references, `usize`/integer ids, `f64` tuples) is `Freeze` (no direct
`UnsafeCell`), so the `Freeze` path is the only one ported: small-sort
threshold 32 and pivot copies passed as left-ancestor pivots. The 16-bit /
`optimize_for_size` configurations (`tiny.rs`) are not used on 64-bit targets.

The element size (`size_of::<T>()` in bytes) changes the scratch length and
the small-sort primitive, so it is an explicit parameter `elemSize`:
`Arc<T>`/`Rc<T>`/`&T`/`usize`/`u64`/`f64` = 8 (default), `u32`/`i32`/`f32` = 4,
`(f64, usize)`/`(usize, usize)`/fat pointers (`&[T]`, `&str`, `Box<dyn ..>`) = 16,
`(f64, f64, usize)` = 24. `elemSize = 0` (zero-sized types) returns the input.

Inconsistent comparators: Rust 1.81+ panics with "user-provided comparison
function does not correctly implement a total order" when
`bidirectional_merge` detects an inconsistency. This port reports that as
`Except.error rustSortOrdViolation` (callers that mirror the panic may turn it
into `throw (IO.userError ..)`); every other inconsistent comparison sequence
completes exactly like Rust.
-/
namespace Elk.Core.Util

namespace RustSort

/-- Message of `smallsort.rs::panic_on_ord_violation`. -/
def ordViolationMessage : String :=
  "user-provided comparison function does not correctly implement a total order"

/-- Sorting monad: the comparator's monad plus the `panic_on_ord_violation` exit. -/
abbrev SortM (m : Type → Type) := ExceptT String m

/-- `smallsort.rs::SMALL_SORT_GENERAL_THRESHOLD` (`T: Freeze` small-sort threshold). -/
def smallSortThreshold : Nat := 32

/-- `smallsort.rs::SMALL_SORT_GENERAL_SCRATCH_LEN`. -/
def smallSortGeneralScratchLen : Nat := smallSortThreshold + 16

/-- `stable/mod.rs::sort` `MAX_LEN_ALWAYS_INSERTION_SORT`. -/
def maxLenAlwaysInsertionSort : Nat := 20

variable {m : Type → Type} [Monad m] {α : Type} [Inhabited α]

/-- `smallsort.rs::insert_tail`: sorts `buf[begin..=tail]` assuming
`buf[begin..tail]` is sorted. -/
@[specialize] def insertTail (lt : α → α → SortM m Bool) (buf : Array α) (begin tail : Nat) :
    SortM m (Array α) := do
  let tmp := buf[tail]!
  if !(← lt tmp buf[tail - 1]!) then return buf
  let mut buf := buf
  let mut gap := tail
  let mut sift := tail - 1
  for _ in [0:tail - begin] do
    buf := buf.set! gap buf[sift]!
    gap := sift
    if sift == begin then break
    sift := sift - 1
    if !(← lt tmp buf[sift]!) then break
  return buf.set! gap tmp

/-- `smallsort.rs::insertion_sort_shift_left`: sorts `v[lo..lo+len]` assuming
`v[lo..lo+offset]` is sorted (`1 ≤ offset ≤ len`). -/
@[specialize] def insertionSortShiftLeft (lt : α → α → SortM m Bool) (v : Array α) (lo len offset : Nat) :
    SortM m (Array α) := do
  let mut v := v
  for i in [offset:len] do
    v ← insertTail lt v lo (lo + i)
  return v

/-- `smallsort.rs::sort4_stable`: stably sorts `src[sb..sb+4]` into `dst[db..db+4]`. -/
@[specialize] def sort4Stable (lt : α → α → SortM m Bool) (src : Array α) (sb : Nat) (dst : Array α) (db : Nat) :
    SortM m (Array α) := do
  let c1 ← lt src[sb + 1]! src[sb]!
  let c2 ← lt src[sb + 3]! src[sb + 2]!
  let a := sb + (if c1 then 1 else 0)
  let b := sb + (if c1 then 0 else 1)
  let c := sb + 2 + (if c2 then 1 else 0)
  let d := sb + 2 + (if c2 then 0 else 1)
  let c3 ← lt src[c]! src[a]!
  let c4 ← lt src[d]! src[b]!
  let mn := if c3 then c else a
  let mx := if c4 then b else d
  let ul := if c3 then a else if c4 then c else b
  let ur := if c4 then d else if c3 then b else c
  let c5 ← lt src[ur]! src[ul]!
  let l := if c5 then ur else ul
  let h := if c5 then ul else ur
  return dst |>.set! db src[mn]! |>.set! (db + 1) src[l]! |>.set! (db + 2) src[h]! |>.set! (db + 3) src[mx]!

/-- `smallsort.rs::bidirectional_merge` (with `merge_up`/`merge_down`): merges
`src[sb..sb+len/2]` and `src[sb+len/2..sb+len]` into `dst[db..db+len]`
(`len ≥ 2`), failing with `panic_on_ord_violation` when the comparator is
detected to be inconsistent. -/
@[specialize] def bidirectionalMerge (lt : α → α → SortM m Bool) (src : Array α) (sb len : Nat)
    (dst : Array α) (db : Nat) : SortM m (Array α) := do
  let h := len / 2
  let mut dst := dst
  let mut left := sb
  let mut right := sb + h
  let mut out := db
  -- `left_rev + 1`, `right_rev + 1`, `dst_rev + 1` (kept as `Nat`)
  let mut leftRev1 := sb + h
  let mut rightRev1 := sb + len
  let mut outRev1 := db + len
  for _ in [0:h] do
    -- merge_up
    let r := src[right]!
    let l := src[left]!
    let isL := !(← lt r l)
    dst := dst.set! out (if isL then l else r)
    if isL then left := left + 1 else right := right + 1
    out := out + 1
    -- merge_down
    let r' := src[rightRev1 - 1]!
    let l' := src[leftRev1 - 1]!
    let isL' := !(← lt r' l')
    dst := dst.set! (outRev1 - 1) (if isL' then r' else l')
    if isL' then rightRev1 := rightRev1 - 1 else leftRev1 := leftRev1 - 1
    outRev1 := outRev1 - 1
  if len % 2 == 1 then
    let leftNonempty := left < leftRev1
    dst := dst.set! out (if leftNonempty then src[left]! else src[right]!)
    if leftNonempty then left := left + 1 else right := right + 1
  if left != leftRev1 || right != rightRev1 then
    throw ordViolationMessage
  return dst

/-- `smallsort.rs::sort8_stable`: stably sorts `v[vb..vb+8]` into
`dst[db..db+8]` (the 8-element temporary is a fresh array instead of the tail
of the scratch buffer; it is never read afterwards). -/
@[specialize] def sort8Stable (lt : α → α → SortM m Bool) (v : Array α) (vb : Nat) (dst : Array α) (db : Nat) :
    SortM m (Array α) := do
  let tmp := Array.replicate 8 (default : α)
  let tmp ← sort4Stable lt v vb tmp 0
  let tmp ← sort4Stable lt v (vb + 4) tmp 4
  bidirectionalMerge lt tmp 0 8 dst db

/-- `smallsort.rs::small_sort_general_with_scratch` (the `T: Freeze`
`StableSmallSortTypeImpl::small_sort`): sorts `v[lo..lo+len]`, `len ≤ 32`. -/
@[specialize] def smallSortGeneralWithScratch (lt : α → α → SortM m Bool) (elemSize : Nat) (v : Array α)
    (lo len : Nat) (s : Array α) : SortM m (Array α × Array α) := do
  if len < 2 then return (v, s)
  let h := len / 2
  let mut s := s
  let mut presorted := 1
  if elemSize ≤ 16 && len ≥ 16 then
    s ← sort8Stable lt v lo s 0
    s ← sort8Stable lt v (lo + h) s h
    presorted := 8
  else if len ≥ 8 then
    s ← sort4Stable lt v lo s 0
    s ← sort4Stable lt v (lo + h) s h
    presorted := 4
  else
    s := s.set! 0 v[lo]! |>.set! h v[lo + h]!
  for offset in [0, h] do
    let desired := if offset == 0 then h else len - h
    for i in [presorted:desired] do
      s := s.set! (offset + i) v[lo + offset + i]!
      s ← insertTail lt s offset (offset + i)
  let v ← bidirectionalMerge lt s 0 len v lo
  return (v, s)

/-- `shared/mod.rs::find_existing_run`: length of the sorted prefix of
`v[lo..lo+len]` and whether it is strictly descending. -/
@[specialize] def findExistingRun (lt : α → α → SortM m Bool) (v : Array α) (lo len : Nat) :
    SortM m (Nat × Bool) := do
  if len < 2 then return (len, false)
  let desc ← lt v[lo + 1]! v[lo]!
  let mut runLen := 2
  for _ in [2:len] do
    let isLt ← lt v[lo + runLen]! v[lo + runLen - 1]!
    if isLt != desc then break
    runLen := runLen + 1
  return (runLen, desc)

/-- `pivot.rs::median3`: median of `v[a]`, `v[b]`, `v[c]` (absolute indices). -/
@[specialize] def median3 (lt : α → α → SortM m Bool) (v : Array α) (a b c : Nat) : SortM m Nat := do
  let x ← lt v[a]! v[b]!
  let y ← lt v[a]! v[c]!
  if x == y then
    let z ← lt v[b]! v[c]!
    return if z != x then c else b
  else
    return a

/-- `pivot.rs::median3_rec`: recursive pseudo-median of three regions of `n`
elements starting at `a`, `b`, `c`. -/
def median3Rec (lt : α → α → SortM m Bool) (v : Array α) (a b c n : Nat) : SortM m Nat := do
  if hn : n * 8 ≥ 64 then
    let n8 := n / 8
    let a' ← median3Rec lt v a (a + n8 * 4) (a + n8 * 7) n8
    let b' ← median3Rec lt v b (b + n8 * 4) (b + n8 * 7) n8
    let c' ← median3Rec lt v c (c + n8 * 4) (c + n8 * 7) n8
    median3 lt v a' b' c'
  else
    median3 lt v a b c
termination_by n
decreasing_by all_goals omega

/-- `pivot.rs::choose_pivot`: pivot position (relative to `lo`) in
`v[lo..lo+len]`, `len ≥ 8`. -/
@[specialize] def choosePivot (lt : α → α → SortM m Bool) (v : Array α) (lo len : Nat) : SortM m Nat := do
  let l8 := len / 8
  let a := lo
  let b := lo + l8 * 4
  let c := lo + l8 * 7
  let idx ← if len < 64 then median3 lt v a b c else median3Rec lt v a b c l8
  return idx - lo

/-- `quicksort.rs::stable_partition`: stably partitions `v[lo..lo+len]` around
the pivot `v[lo+pivotPos]` (elements with `lt x pivot` first; the pivot itself
goes left iff `pivotGoesLeft`, without being compared) and returns the left
size. -/
@[specialize] def stablePartition (lt : α → α → SortM m Bool) (v : Array α) (lo len : Nat) (s : Array α)
    (pivotPos : Nat) (pivotGoesLeft : Bool) : SortM m (Array α × Array α × Nat) := do
  let pivot := v[lo + pivotPos]!
  let mut s := s
  let mut numLeft := 0
  for i in [0:len] do
    let x := v[lo + i]!
    let towardsLeft ← if i == pivotPos then pure pivotGoesLeft else lt x pivot
    -- `PartitionState::partition_one`: left side grows up, right side down
    let dst := if towardsLeft then numLeft else len - (i + 1) + numLeft
    s := s.set! dst x
    if towardsLeft then numLeft := numLeft + 1
  let mut v := v
  for i in [0:numLeft] do
    v := v.set! (lo + i) s[i]!
  for i in [0:len - numLeft] do
    v := v.set! (lo + numLeft + i) s[len - 1 - i]!
  return (v, s, numLeft)

/-- `merge.rs::merge`: merges the sorted runs `v[lo..lo+mid]` and
`v[lo+mid..lo+len]` using the scratch buffer for the shorter one. -/
@[specialize] def merge (lt : α → α → SortM m Bool) (v : Array α) (lo len mid : Nat) (s : Array α) :
    SortM m (Array α × Array α) := do
  if mid == 0 || mid ≥ len || s.size < min mid (len - mid) then return (v, s)
  let leftLen := mid
  let rightLen := len - mid
  let mut v := v
  let mut s := s
  if leftLen ≤ rightLen then
    for i in [0:leftLen] do
      s := s.set! i v[lo + i]!
    -- MergeState::merge_up: start = left (in s), end = leftLen, dst = out (in v)
    let mut left := 0
    let mut right := lo + mid
    let mut out := lo
    for _ in [0:len] do
      if left == leftLen || right == lo + len then break
      let r := v[right]!
      let l := s[left]!
      let consumeLeft := !(← lt r l)
      v := v.set! out (if consumeLeft then l else r)
      if consumeLeft then left := left + 1 else right := right + 1
      out := out + 1
    -- MergeState::drop
    for i in [0:leftLen - left] do
      v := v.set! (out + i) s[left + i]!
  else
    for i in [0:rightLen] do
      s := s.set! i v[lo + mid + i]!
    -- MergeState::merge_down: start = 0, end (in s), dst (in v)
    let mut dst := lo + mid
    let mut fin := rightLen
    let mut out := lo + len
    for _ in [0:len] do
      let left := dst - 1
      let right := fin - 1
      out := out - 1
      let l := v[left]!
      let r := s[right]!
      let consumeLeft ← lt r l
      v := v.set! out (if consumeLeft then l else r)
      dst := if consumeLeft then left else left + 1
      fin := if consumeLeft then right + 1 else right
      if dst == lo || fin == 0 then break
    -- MergeState::drop
    for i in [0:fin] do
      v := v.set! (dst + i) s[i]!
  return (v, s)

/-- `drift.rs::merge_tree_scale_factor`: `ceil(2^62 / n)`. -/
def mergeTreeScaleFactor (n : Nat) : UInt64 :=
  -- in `u64` like Rust (`n >= 1`, no overflow below `2^64`); a `Nat` `2^62` would be parsed from a
  -- string with GMP on every call
  let n := n.toUInt64
  (((1 : UInt64) <<< 62) + n - 1) / n

/-- `u64::leading_zeros`. -/
def leadingZeros64 (x : UInt64) : Nat :=
  if x == 0 then 64 else 63 - x.toNat.log2

/-- `drift.rs::merge_tree_depth` (wrapping `u64` products). -/
def mergeTreeDepth (left mid right : Nat) (scale : UInt64) : Nat :=
  let x := UInt64.ofNat (left + mid)
  let y := UInt64.ofNat (mid + right)
  leadingZeros64 ((scale * x) ^^^ (scale * y))

/-- `drift.rs::sqrt_approx`. -/
def sqrtApprox (n : Nat) : Nat :=
  let ilog := (n ||| 1).log2
  let shift := (ilog + 1) / 2
  ((1 <<< shift) + (n >>> shift)) / 2

/-- `[T]::reverse` on `v[lo..lo+len]`. -/
def reverseRange (v : Array α) (lo len : Nat) : Array α := Id.run do
  let mut v := v
  for i in [0:len / 2] do
    let a := v[lo + i]!
    let b := v[lo + len - 1 - i]!
    v := v.set! (lo + i) b |>.set! (lo + len - 1 - i) a
  return v

/-- `drift.rs::DriftsortRun` as `(length, sorted)`. -/
abbrev DriftsortRun := Nat × Bool

mutual

/-- `quicksort.rs::quicksort`: sorts `v[lo..lo+len]`; `limit` bounds the
number of imbalanced partitions, `ancestor` is the left-ancestor pivot copy
(`T: Freeze`). The `loop` over the left side is the tail call. -/
@[specialize] partial def quicksort (lt : α → α → SortM m Bool) (elemSize : Nat) (v : Array α) (lo len : Nat)
    (s : Array α) (limit : Nat) (ancestor : Option α) : SortM m (Array α × Array α) := do
  if len ≤ smallSortThreshold then
    return ← smallSortGeneralWithScratch lt elemSize v lo len s
  if limit == 0 then
    return ← driftSort lt elemSize v lo len s true
  let limit := limit - 1
  let pivotPos ← choosePivot lt v lo len
  let pivotCopy := v[lo + pivotPos]!
  let mut performEqual := false
  if let some la := ancestor then
    performEqual := !(← lt la v[lo + pivotPos]!)
  let mut v := v
  let mut s := s
  let mut leftLen := 0
  if !performEqual then
    let (v', s', n) ← stablePartition lt v lo len s pivotPos false
    v := v'
    s := s'
    leftLen := n
    performEqual := n == 0
  if performEqual then
    let (v', s', midEq) ← stablePartition (fun a b => do return !(← lt b a)) v lo len s pivotPos true
    quicksort lt elemSize v' (lo + midEq) (len - midEq) s' limit none
  else
    let (v', s') ← quicksort lt elemSize v (lo + leftLen) (len - leftLen) s limit (some pivotCopy)
    quicksort lt elemSize v' lo leftLen s' limit ancestor

/-- `drift.rs::stable_quicksort`: quicksort with `limit = 2 * floor(log2(len))`. -/
@[specialize] partial def stableQuicksort (lt : α → α → SortM m Bool) (elemSize : Nat) (v : Array α) (lo len : Nat)
    (s : Array α) : SortM m (Array α × Array α) :=
  quicksort lt elemSize v lo len s (2 * (len ||| 1).log2) none

/-- `drift.rs::create_run`: the next logical run starting at `v[lo]`. -/
@[specialize] partial def createRun (lt : α → α → SortM m Bool) (elemSize : Nat) (v : Array α) (lo len : Nat)
    (s : Array α) (minGoodRunLen : Nat) (eager : Bool) : SortM m (Array α × Array α × DriftsortRun) := do
  if len ≥ minGoodRunLen then
    let (runLen, wasReversed) ← findExistingRun lt v lo len
    if runLen ≥ minGoodRunLen then
      let v := if wasReversed then reverseRange v lo runLen else v
      return (v, s, (runLen, true))
  if eager then
    let eagerLen := min smallSortThreshold len
    let (v, s) ← quicksort lt elemSize v lo eagerLen s 0 none
    return (v, s, (eagerLen, true))
  else
    return (v, s, (min minGoodRunLen len, false))

/-- `drift.rs::logical_merge`: merges the adjacent runs `left`, `right`
covering `v[lo..lo+len]`, physically when one is sorted or they no longer fit
in the scratch buffer. -/
@[specialize] partial def logicalMerge (lt : α → α → SortM m Bool) (elemSize : Nat) (v : Array α) (lo len : Nat)
    (s : Array α) (left right : DriftsortRun) : SortM m (Array α × Array α × DriftsortRun) := do
  let canFitInScratch := len ≤ s.size
  if !canFitInScratch || left.2 || right.2 then
    let mut v := v
    let mut s := s
    if !left.2 then
      (v, s) ← stableQuicksort lt elemSize v lo left.1 s
    if !right.2 then
      (v, s) ← stableQuicksort lt elemSize v (lo + left.1) (len - left.1) s
    (v, s) ← merge lt v lo len left.1 s
    return (v, s, (len, true))
  else
    return (v, s, (len, false))

/-- `drift.rs::sort`: driftsort main loop (powersort merge policy over lazy
logical runs) on `v[lo..lo+len]`. -/
@[specialize] partial def driftSort (lt : α → α → SortM m Bool) (elemSize : Nat) (v : Array α) (lo len : Nat)
    (s : Array α) (eager : Bool) : SortM m (Array α × Array α) := do
  if len < 2 then return (v, s)
  let scale := mergeTreeScaleFactor len
  let minGoodRunLen := if len ≤ 64 * 64 then min (len - len / 2) 64 else sqrtApprox len
  let mut v := v
  let mut s := s
  let mut runs : Array DriftsortRun := #[]
  let mut depths : Array Nat := #[]
  let mut scan := 0
  let mut prev : DriftsortRun := (0, true)
  for _ in [0:len + 1] do
    let mut next : DriftsortRun := (0, true)
    let mut depth := 0
    if scan < len then
      let (v', s', r) ← createRun lt elemSize v (lo + scan) (len - scan) s minGoodRunLen eager
      v := v'
      s := s'
      next := r
      depth := mergeTreeDepth (scan - prev.1) scan (scan + r.1) scale
    while runs.size > 1 && depths[depths.size - 1]! ≥ depth do
      let left := runs[runs.size - 1]!
      let mergedLen := left.1 + prev.1
      let (v', s', r) ← logicalMerge lt elemSize v (lo + scan - mergedLen) mergedLen s left prev
      v := v'
      s := s'
      prev := r
      runs := runs.pop
      depths := depths.pop
    runs := runs.push prev
    depths := depths.push depth
    if scan ≥ len then break
    scan := scan + next.1
    prev := next
  if !prev.2 then
    stableQuicksort lt elemSize v lo len s
  else
    return (v, s)

end

/-- `stable/mod.rs::sort` + `driftsort_main` on the whole array with
`is_less = lt`. -/
@[specialize] def sortCore (lt : α → α → SortM m Bool) (elemSize : Nat) (as : Array α) : SortM m (Array α) := do
  if elemSize == 0 then return as
  let len := as.size
  if len < 2 then return as
  if len ≤ maxLenAlwaysInsertionSort then
    return ← insertionSortShiftLeft lt as 0 len 1
  -- driftsort_main: max(max(len - len / 2, min(len, 8MB / size)), 48)
  let maxFullAlloc := 8000000 / elemSize
  let allocLen := max (max (len - len / 2) (min len maxFullAlloc)) smallSortGeneralScratchLen
  -- AlignedStorage::<T, 4096>, else Vec::with_capacity(alloc_len)
  let stackLen := 4096 / elemSize
  let scratchLen := if stackLen ≥ allocLen then stackLen else allocLen
  let s := Array.replicate scratchLen (default : α)
  let eager := len ≤ smallSortThreshold * 2
  let (v, _) ← driftSort lt elemSize as 0 len s eager
  return v

end RustSort

open RustSort in
/-- Rust `slice::sort_by` (`alloc/src/slice.rs`, driftsort of Rust 1.97.1)
with a monadic comparator: the comparator is called with exactly the same
argument sequence as Rust calls `compare`, so stateful comparators observe the
same history. `elemSize` is `size_of::<T>()` of the Rust element type (see the
module docs). Returns `.error RustSort.ordViolationMessage` where Rust panics
in `panic_on_ord_violation`. -/
@[specialize] def rustSortByM {m : Type → Type} {α : Type} [Monad m] [Inhabited α] (as : Array α)
    (cmp : α → α → m Ordering) (elemSize : Nat := 8) : m (Except String (Array α)) :=
  ExceptT.run (sortCore (fun a b => do return (← (cmp a b : m Ordering)) == .lt) elemSize as)

/-- Rust `slice::sort_by` (`alloc/src/slice.rs`, driftsort of Rust 1.97.1)
with a pure comparator; see `rustSortByM`. -/
@[specialize] def rustSortBy {α : Type} [Inhabited α] (as : Array α) (cmp : α → α → Ordering)
    (elemSize : Nat := 8) : Except String (Array α) :=
  Id.run (rustSortByM as (fun a b => pure (cmp a b)) elemSize)

/-- Rust `slice::sort_by_key` (`is_less = f(a).lt(&f(b))`); see `rustSortByM`. -/
@[specialize] def rustSortByKey {α κ : Type} [Inhabited α] [Ord κ] (as : Array α) (key : α → κ)
    (elemSize : Nat := 8) : Except String (Array α) :=
  rustSortBy as (fun a b => compare (key a) (key b)) elemSize

end Elk.Core.Util
