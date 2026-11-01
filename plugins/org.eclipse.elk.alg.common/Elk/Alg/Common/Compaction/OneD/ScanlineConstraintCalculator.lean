import Elk.Alg.Common.Compaction.Scanline
import Elk.Alg.Common.Compaction.OneD.IConstraintCalculationAlgorithm
import Elk.Alg.Common.Compaction.OneD.CompareFuzzy
import Elk.Core.Exceptions
import Elk.Core.Util.FloatConst
open Elk.Core.Util.FloatConst
/-!
# `org.eclipse.elk.alg.common.compaction.oned.ScanlineConstraintCalculator`

Scanline constraint calculation (elk-rs `scanline_constraint_calculator.rs`): a sweep over
the low/high y coordinates of the hitboxes keeps the active intervals ordered by their x
center; when an interval ends, constraints to its left/right neighbours are added if the
neighbour was its candidate.

Kept elk-rs specifics:
* the timestamp comparator of elk-rs (ending positive intervals first, zero-height intervals
  inserted and removed together, ordered by node id) — this differs from Java;
* `insertionPos` is the first position whose x center is not smaller (linear scan);
* the trailing `floor`/`overlap` check of `delete` has no effect in Rust and is not executed.

## Fast path (`sweep`)
The handler only adds constraints; the hitboxes and groups it reads do not change during a sweep.
`sweep` therefore precomputes the sort keys (y of every event, its zero-height/low/high rank) and
the x centres and groups of the nodes once, sorts the event codes with the same `stableSort` and a
comparator that yields the same result for every pair as `timestampCmp` (hence the same
permutation), runs the handler as the pure kernel `Kernel.run` on position-indexed arrays and then
appends the recorded constraints to the nodes in the order the handler adds them. The original
monadic handler is kept as `sweepReference` (differential test `alg.common.compaction.scanlineFast`).
`EdgeAwareScanlineConstraintCalculation` (layered) uses the same kernel with its own comparator.
-/

namespace Elk.Alg.Common.Compaction.OneD

open Elk.Core Elk.Core.Util CompactM

namespace ScanlineConstraintCalculator

/-- `Timestamp`: the low (`low = true`) or high end of a node's hitbox. -/
structure Timestamp where
  node : CNodeId
  low : Bool
  deriving Inhabited, BEq, Repr

/-- `timestamp_cmp(p1, p2)` evaluated on the graph `g` (uses `CNode.id` for zero-height ties). -/
def timestampCmp (g : CGraph) (p1 p2 : Timestamp) : Ordering :=
  let n1 := g.cNode p1.node
  let n2 := g.cNode p2.node
  let y1 := if p1.low then n1.hitbox.y else n1.hitbox.y + n1.hitbox.height
  let y2 := if p2.low then n2.hitbox.y else n2.hitbox.y + n2.hitbox.height
  let cmp := Float.comparePartial y1 y2
  if cmp == .eq then
    -- End positive intervals first. A zero-height interval must be inserted and removed
    -- together, before positive intervals starting here.
    let rank (n : CNode) (low : Bool) : Nat :=
      if n.hitbox.height == fl0p0 then 1 else if low then 2 else 0
    let first := rank n1 p1.low
    let order := compare first (rank n2 p2.low)
    if order != .eq then order
    else if first == 1 then
      (compare n1.id n2.id).then (compare p2.low p1.low)
    else cmp
  else cmp

/-- `ConstraintsScanlineHandler`: active intervals (ordered by x center) and the candidate of
each node (indexed by `CNode.id`). -/
structure Handler where
  intervals : Array CNodeId := #[]
  cand : Array (Option CNodeId) := #[]

private abbrev HandlerM := StateT Handler CompactM

private def centerX (n : CNodeId) : CompactM Float := do
  let c ← getCNode n
  return c.hitbox.x + c.hitbox.width / 2.0

private def indexOf (h : Handler) (n : CNodeId) : Option Nat := h.intervals.findIdx? (· == n)

private def lower (h : Handler) (n : CNodeId) : Option CNodeId := do
  let idx ← indexOf h n
  if idx > 0 then h.intervals[idx - 1]? else none

private def higher (h : Handler) (n : CNodeId) : Option CNodeId := do
  let idx ← indexOf h n
  h.intervals[idx + 1]?

private def differentGroup (a b : CNodeId) : CompactM Bool := do
  match (← getCNode a).cGroup, (← getCNode b).cGroup with
  | some ga, some gb => return ga != gb
  | _, _ => return true

private def nodeIdx (n : CNodeId) : CompactM Nat := return (← getCNode n).id.toNat

private def insertionPos (n : CNodeId) : HandlerM Nat := do
  let nodeCenter ← centerX n
  let intervals := (← get).intervals
  let mut pos := 0
  while pos < intervals.size do
    if (← centerX intervals[pos]!) < nodeCenter then pos := pos + 1 else break
  return pos

private def insert (n : CNodeId) : HandlerM Unit := do
  let pos ← insertionPos n
  if (← get).intervals[pos]? == some n then
    throwIllegalState "Invalid hitboxes for scanline constraint calculation"
  modify fun h => { h with intervals := h.intervals.insertIdxIfInBounds pos n }
  let nodeId ← nodeIdx n
  let low := lower (← get) n
  modify fun h => { h with cand := h.cand.setIfInBounds nodeId low }
  if let some right := higher (← get) n then
    let rightId ← nodeIdx right
    modify fun h => { h with cand := h.cand.setIfInBounds rightId (some n) }

private def delete (n : CNodeId) : HandlerM Unit := do
  let h ← get
  let left := lower h n
  let right := higher h n
  let nodeId ← nodeIdx n
  if let some left := left then
    if (h.cand[nodeId]?).join == some left then
      if ← differentGroup left n then
        modifyCNode left fun c => { c with constraints := c.constraints.push n }
  if let some right := right then
    let rightId ← nodeIdx right
    if (h.cand[rightId]?).join == some n then
      if ← differentGroup right n then
        modifyCNode n fun c => { c with constraints := c.constraints.push right }
  modify fun h => { h with intervals := h.intervals.filter (· != n) }
  -- Rust: `if let Some(floor) = self.floor(node) { if overlap(node, &floor) { let _ = compactor; } }`
  -- has no effect and is omitted.

private def handle (t : Timestamp) : HandlerM Unit :=
  if t.low then insert t.node else delete t.node

/-- The original monadic `ScanlineConstraintCalculator::sweep(compactor, nodes)` (reference of the
fast path `sweep`): assigns `CNode.id := index` and runs the scanline over the low/high timestamps
of `nodes`. -/
def sweepReference (nodes : Array CNodeId) : CompactM Unit := do
  let mut points : Array Timestamp := Array.mkEmpty (nodes.size * 2)
  for n in nodes do
    points := points.push ⟨n, true⟩
    points := points.push ⟨n, false⟩
  for i in [0:nodes.size] do
    modifyCNode nodes[i]! fun c => { c with id := i }
  let g := (← get).cGraph
  let cmp := timestampCmp g
  let handler : Handler := { cand := Array.replicate nodes.size none }
  let _ ← (Scanline.execute points cmp ⟨handle⟩ : HandlerM Unit).run handler

/-! ### Pure kernel of the constraint scanline handler

Positions `i` index the swept node list (`CNode.id = i` during the sweep); an event code is
`2 * i + 1` for the low end and `2 * i` for the high end. Candidates are stored as `position + 1`
(`0` = none), groups as `group index + 1` (`0` = no group). -/
namespace Kernel

/-- Rust `insertion_pos`: first position whose x centre is not smaller than `c` (linear scan). -/
partial def insertionPos (intervals : Array Nat) (center : FloatArray) (c : Float) (pos : Nat) : Nat :=
  if h : pos < intervals.size then
    if center.get! intervals[pos] < c then insertionPos intervals center c (pos + 1) else pos
  else pos

/-- First index of `n` in `intervals`, `intervals.size` if absent (`findIdx?`). -/
partial def indexOf (intervals : Array Nat) (n : Nat) (i : Nat) : Nat :=
  if h : i < intervals.size then
    if intervals[i] == n then i else indexOf intervals n (i + 1)
  else i

/-- Rust `in_different_groups` / `different_group` on encoded groups. -/
@[inline] def differentGroup (group : Array Nat) (a b : Nat) : Bool :=
  let ga := group[a]!
  let gb := group[b]!
  ga == 0 || gb == 0 || ga != gb

/-- Result of `run`: the constraints in the order the handler adds them (`pushFrom[k]` gets the
constraint to `pushTo[k]`) and whether `insert` met an invalid hitbox. -/
structure Result where
  pushFrom : Array Nat
  pushTo : Array Nat
  invalid : Bool
  deriving Inhabited

/-- The handler (`insert` on low ends, `delete` on high ends) over the sorted event codes, from
event `k` on. `checkInvalid` enables the "Invalid hitboxes" check of `insert` (the
edge-aware handler has none). Stops at an invalid insertion with the constraints added so far. -/
partial def run (events : Array Nat) (center : FloatArray) (group : Array Nat) (checkInvalid : Bool)
    (k : Nat) (intervals cand pushFrom pushTo : Array Nat) : Result :=
  if h : k < events.size then
    let e := events[k]
    let n := e / 2
    if e % 2 == 1 then
      let pos := insertionPos intervals center (center.get! n) 0
      if checkInvalid && intervals[pos]? == some n then
        { pushFrom, pushTo, invalid := true }
      else
        let intervals := intervals.insertIdxIfInBounds pos n
        let idx := indexOf intervals n 0
        let low := if idx < intervals.size && idx > 0 then intervals[idx - 1]! + 1 else 0
        let cand := cand.setIfInBounds n low
        let cand := if idx + 1 < intervals.size then cand.setIfInBounds intervals[idx + 1]! (n + 1) else cand
        run events center group checkInvalid (k + 1) intervals cand pushFrom pushTo
    else
      let idx := indexOf intervals n 0
      let present := idx < intervals.size
      let left := if present && idx > 0 then intervals[idx - 1]! + 1 else 0
      let right := if present && idx + 1 < intervals.size then intervals[idx + 1]! + 1 else 0
      let addLeft := left != 0 && cand[n]?.getD 0 == left && differentGroup group (left - 1) n
      let pushFrom := if addLeft then pushFrom.push (left - 1) else pushFrom
      let pushTo := if addLeft then pushTo.push n else pushTo
      let addRight := right != 0 && cand[right - 1]?.getD 0 == n + 1 && differentGroup group (right - 1) n
      let pushFrom := if addRight then pushFrom.push n else pushFrom
      let pushTo := if addRight then pushTo.push (right - 1) else pushTo
      let intervals := intervals.filter (· != n)
      run events center group checkInvalid (k + 1) intervals cand pushFrom pushTo
  else { pushFrom, pushTo, invalid := false }

/-- The x centres (`x + width / 2`) and encoded groups of `nodes` in `g`. -/
def nodeData (g : CGraph) (nodes : Array CNodeId) : FloatArray × Array Nat :=
  nodes.foldl (init := (FloatArray.emptyWithCapacity nodes.size, Array.mkEmpty nodes.size))
    fun (center, group) n =>
      let c := g.cNode n
      (center.push (c.hitbox.x + c.hitbox.width / 2.0),
        group.push (match c.cGroup with | some gr => gr.idx + 1 | none => 0))

/-- Appends the recorded constraints to the nodes (positions mapped through `nodes`). -/
def applyPushes (g : CGraph) (nodes : Array CNodeId) (r : Result) : CGraph := Id.run do
  let mut g := g
  for h : k in [0:r.pushFrom.size] do
    let a := nodes[r.pushFrom[k]]!
    let b := nodes[r.pushTo[k]!]!
    g := g.modifyCNode a fun c => { c with constraints := c.constraints.push b }
  return g

end Kernel

/-- `timestampCmp` on precomputed keys: `ys[e]` is the y of event `e`, `ranks[e]` its tie rank
(`1` zero-height, `2` low end, `0` high end of a positive interval). -/
@[inline] def keyCmp (ys : FloatArray) (ranks : ByteArray) (a b : Nat) : Ordering :=
  let cmp := Float.comparePartial (ys.get! a) (ys.get! b)
  if cmp == .eq then
    let ra := ranks.get! a
    let rb := ranks.get! b
    if ra < rb then .lt
    else if ra > rb then .gt
    else if ra == 1 then
      -- `(compare n1.id n2.id).then (compare p2.low p1.low)` with `id = position`
      let ia := a / 2
      let ib := b / 2
      if ia < ib then .lt else if ia > ib then .gt
      else compare (b % 2 == 1) (a % 2 == 1)
    else cmp
  else cmp

/-- Sort keys of the events of `nodes` in `g`, indexed by event code: the y of the event and its
tie rank (as `timestampCmp`). -/
def eventKeys (g : CGraph) (nodes : Array CNodeId) : FloatArray × ByteArray :=
  nodes.foldl (init := (FloatArray.emptyWithCapacity (nodes.size * 2), ByteArray.emptyWithCapacity (nodes.size * 2)))
    fun (ys, ranks) n =>
      let c := g.cNode n
      let zero := c.hitbox.height == fl0p0
      ((ys.push (c.hitbox.y + c.hitbox.height)).push c.hitbox.y,
        (ranks.push (if zero then 1 else 0)).push (if zero then 1 else 2))

/-- The event codes in the order of the Rust `points` (low, then high end of every node). -/
def eventCodes (count : Nat) : Array Nat :=
  (Array.range count).foldl (init := Array.mkEmpty (count * 2)) fun acc i => (acc.push (2 * i + 1)).push (2 * i)

/-- Runs the kernel on the current graph and appends the constraints; throws like `insert` on an
invalid hitbox (after the constraints added before it, as the monadic handler does). -/
def runKernel (nodes : Array CNodeId) (events : Array Nat) (checkInvalid : Bool) : CompactM Unit := do
  let r := (fun (g : CGraph) =>
      let (center, group) := Kernel.nodeData g nodes
      Kernel.run events center group checkInvalid 0 #[] (Array.replicate nodes.size 0) #[] #[]) (← get).cGraph
  if !r.pushFrom.isEmpty then
    modify fun s => { s with cGraph := Kernel.applyPushes s.cGraph nodes r }
  if r.invalid then
    throwIllegalState "Invalid hitboxes for scanline constraint calculation"

/-- `ScanlineConstraintCalculator::sweep(compactor, nodes)` (fast path of `sweepReference`, see
the module doc): assigns `CNode.id := index` and adds the constraints the scanline over the
low/high timestamps of `nodes` finds. -/
def sweep (nodes : Array CNodeId) : CompactM Unit := do
  for i in [0:nodes.size] do
    modifyCNode nodes[i]! fun c => { c with id := i }
  let (ys, ranks) := eventKeys (← get).cGraph nodes
  let events := stableSort (eventCodes nodes.size) (keyCmp ys ranks)
  runKernel nodes events true

/-- `ScanlineConstraintCalculator.calculateConstraints(compactor)`: sweeps over all nodes. -/
def calculateConstraints : CompactM Unit := do
  sweep (← cNodeIds)

end ScanlineConstraintCalculator

/-- `new ScanlineConstraintCalculator()`. -/
def ScanlineConstraintCalculator : ConstraintCalculationAlgorithm :=
  ⟨ScanlineConstraintCalculator.calculateConstraints⟩

end Elk.Alg.Common.Compaction.OneD
