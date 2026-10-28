import Elk.Alg.Common.Compaction.Scanline
import Elk.Alg.Common.Compaction.OneD.IConstraintCalculationAlgorithm
import Elk.Alg.Common.Compaction.OneD.CompareFuzzy
import Elk.Core.Exceptions
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
-/
/-! Float literals as global constants (FL): inside branches, loops and specialised code the compiler
shares a literal's `Nat`/`Bool` arguments with unrelated variables (CSE) and then parses it on every
evaluation (`FastFloat.ofScientificImpl`); a top-level constant is a load (PLAN §7.1 items 17, 22). -/
private def fl0p0 : Float := 0.0

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

/-- `ScanlineConstraintCalculator::sweep(compactor, nodes)`: assigns `CNode.id := index` and runs
the scanline over the low/high timestamps of `nodes`. -/
def sweep (nodes : Array CNodeId) : CompactM Unit := do
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

/-- `ScanlineConstraintCalculator.calculateConstraints(compactor)`: sweeps over all nodes. -/
def calculateConstraints : CompactM Unit := do
  sweep (← cNodeIds)

end ScanlineConstraintCalculator

/-- `new ScanlineConstraintCalculator()`. -/
def ScanlineConstraintCalculator : ConstraintCalculationAlgorithm :=
  ⟨ScanlineConstraintCalculator.calculateConstraints⟩

end Elk.Alg.Common.Compaction.OneD
