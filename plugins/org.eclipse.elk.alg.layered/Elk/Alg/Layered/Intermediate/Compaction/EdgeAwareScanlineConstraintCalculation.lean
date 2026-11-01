import Elk.Alg.Common.Compaction.Scanline
import Elk.Alg.Common.Compaction.OneD.IConstraintCalculationAlgorithm
import Elk.Alg.Common.Compaction.OneD.ScanlineConstraintCalculator
import Elk.Alg.Layered.Intermediate.Compaction.CompactionMetadata
import Elk.Core.Util.FloatConst
open Elk.Core.Util.FloatConst
/-!
# `org.eclipse.elk.alg.layered.intermediate.compaction.EdgeAwareScanlineConstraintCalculation`

An extended scanline procedure that is able to properly handle different spacing values between
nodes and edges (elk-rs `EdgeAwareScanlineConstraintCalculation` of
`intermediate/horizontal_graph_compactor.rs`). The hitboxes are temporarily enlarged by half the
spacing (minus `EPSILON`) and swept in several rounds (segments only, nodes only, everything),
each round adding the constraints found by the scanline.

Ported from Rust, which differs from the Java subclass of `ScanlineConstraintCalculator`:
* own timestamp comparator `edge_aware_timestamp_cmp` (on equal y, high ends before low ends;
  no node id tie-break) and own handler (`EdgeAwareScanlineHandler`, no "invalid hitboxes"
  check on insertion);
* `sweep` assigns `CNode.id := index` to all nodes, but only the filtered ones take part;
* the node spacing of the "nodes" round falls back to `SPACING_EDGE_EDGE` of the graph when a node
  has no individual value (`unwrap_or(vertical_edge_edge_spacing)`), the minimum spacing falls
  back to `0` when no node contributes;
* the enlargement and its undo are not exact inverses (the `SMALL_EPSILON` is subtracted from
  `y` in both directions); this is kept, as in Java and Rust.

`sweep` is the fast path of the original monadic `sweepReference`: the sort keys are precomputed
and the handler runs as the pure kernel `ScanlineConstraintCalculator.Kernel.run` (without the
invalid hitbox check), as described in `ScanlineConstraintCalculator`; differential test
`layered.intermediate.compaction.edgeAwareSweepFast`.

The scheduled undo operations (Java `Runnable`s) are replayed in the same order. Unknown routing
styles do nothing (Rust `_ => {}`; Java throws `UnsupportedConfigurationException`).
-/

namespace Elk.Alg.Layered.Intermediate.Compaction

open Elk.Core Elk.Core.Util Elk.Core.Options Elk.Alg.Common.Compaction Elk.Alg.Common.Compaction.OneD
open CompactM

/-- Rust `EdgeAwareScanlineConstraintCalculation`. -/
structure EdgeAwareScanlineConstraintCalculation where
  /-- `edgeRouting` of the graph. -/
  edgeRouting : EdgeRouting
  /-- `verticalEdgeEdgeSpacing` (graph `SPACING_EDGE_EDGE`). -/
  verticalEdgeEdgeSpacing : Float
  /-- The CNode origins (Rust `metadata`). -/
  metadata : CompactionMetadata

namespace EdgeAwareScanlineConstraintCalculation

/-- `EPSILON` (Rust `EDGE_AWARE_EPSILON`). -/
def EPSILON : Float := 0.5

/-- `SMALL_EPSILON` (Rust `EDGE_AWARE_SMALL_EPSILON`). -/
def SMALL_EPSILON : Float := 0.01

/-- Rust `EdgeAwareTimestamp`: the low (`low = true`) or high end of a node's hitbox. -/
structure Timestamp where
  node : CNodeId
  low : Bool
  deriving Inhabited, BEq, Repr

/-- Rust `edge_aware_timestamp_cmp(left, right)` on the hitboxes of `g`. -/
def timestampCmp (g : CGraph) (left right : Timestamp) : Ordering :=
  let ln := g.cNode left.node
  let rn := g.cNode right.node
  let leftY := if left.low then ln.hitbox.y else ln.hitbox.y + ln.hitbox.height
  let rightY := if right.low then rn.hitbox.y else rn.hitbox.y + rn.hitbox.height
  let cmp := Float.comparePartial leftY rightY
  if cmp == .eq then
    if !left.low && right.low then .lt
    else if !right.low && left.low then .gt
    else cmp
  else cmp

/-- Rust `EdgeAwareScanlineHandler`: active intervals ordered by x center and the candidate of
each node (indexed by `CNode.id`). -/
structure Handler where
  intervals : Array CNodeId := #[]
  cand : Array (Option CNodeId) := #[]

private abbrev HandlerM := StateT Handler CompactM

/-- Rust `cnode_center_x(node)`. -/
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

/-- Rust `in_different_groups(left, right)` (`true` unless both have the same group). -/
private def inDifferentGroups (a b : CNodeId) : CompactM Bool := do
  match (← getCNode a).cGroup, (← getCNode b).cGroup with
  | some ga, some gb => return ga != gb
  | _, _ => return true

private def nodeIdx (n : CNodeId) : CompactM Nat := return (← getCNode n).id.toNat

/-- Rust `insertion_pos`: first position whose x center is not smaller than the node's. -/
private def insertionPos (n : CNodeId) : HandlerM Nat := do
  let center ← centerX n
  let intervals := (← get).intervals
  let mut pos := 0
  while pos < intervals.size do
    if (← centerX intervals[pos]!) < center then pos := pos + 1 else break
  return pos

/-- Rust `EdgeAwareScanlineHandler::insert`. -/
private def insert (n : CNodeId) : HandlerM Unit := do
  let pos ← insertionPos n
  modify fun h => { h with intervals := h.intervals.insertIdxIfInBounds pos n }
  let nodeId ← nodeIdx n
  let low := lower (← get) n
  modify fun h => { h with cand := h.cand.setIfInBounds nodeId low }
  if let some right := higher (← get) n then
    let rightId ← nodeIdx right
    modify fun h => { h with cand := h.cand.setIfInBounds rightId (some n) }

/-- Rust `EdgeAwareScanlineHandler::delete`: adds the constraints to the neighbours whose
candidate the node is (or which are its candidate), then removes the node. -/
private def delete (n : CNodeId) : HandlerM Unit := do
  let h ← get
  let left := lower h n
  let right := higher h n
  if let some left := left then
    let nodeId ← nodeIdx n
    if (h.cand[nodeId]?).join == some left then
      if ← inDifferentGroups left n then
        modifyCNode left fun c => { c with constraints := c.constraints.push n }
  if let some right := right then
    let rightId ← nodeIdx right
    if (h.cand[rightId]?).join == some n then
      if ← inDifferentGroups right n then
        modifyCNode n fun c => { c with constraints := c.constraints.push right }
  modify fun h => { h with intervals := h.intervals.filter (· != n) }

private def handle (t : Timestamp) : HandlerM Unit :=
  if t.low then insert t.node else delete t.node

/-- The original monadic Rust `sweep(compactor, filter)` (reference of the fast path `sweep`):
assigns `CNode.id := index` to all nodes and runs the scanline over the low/high timestamps of
the nodes accepted by `filter`. -/
def sweepReference (filter : CNodeId → Bool) : CompactM Unit := do
  let allNodes ← cNodeIds
  for h : i in [0:allNodes.size] do
    modifyCNode allNodes[i] fun c => { c with id := i }
  let mut points : Array Timestamp := #[]
  for n in allNodes do
    if filter n then
      points := points.push ⟨n, true⟩
      points := points.push ⟨n, false⟩
  if points.isEmpty then return
  let g := (← get).cGraph
  let handler : Handler := { cand := Array.replicate allNodes.size none }
  let _ ← (Scanline.execute points (timestampCmp g) ⟨handle⟩ : HandlerM Unit).run handler

/-- `timestampCmp` on precomputed keys (`ys[e]`: y of event code `e`, odd codes are low ends). -/
@[inline] def keyCmp (ys : FloatArray) (a b : Nat) : Ordering :=
  let cmp := Float.comparePartial (ys.get! a) (ys.get! b)
  if cmp == .eq then
    let aLow := a % 2 == 1
    let bLow := b % 2 == 1
    if !aLow && bLow then .lt
    else if !bLow && aLow then .gt
    else cmp
  else cmp

/-- Rust `sweep(compactor, filter)` (fast path of `sweepReference`, see the module doc): assigns
`CNode.id := index` to all nodes and adds the constraints of the scanline over the low/high
timestamps of the nodes accepted by `filter`. -/
def sweep (filter : CNodeId → Bool) : CompactM Unit := do
  let allNodes ← cNodeIds
  for h : i in [0:allNodes.size] do
    modifyCNode allNodes[i] fun c => { c with id := i }
  let mut points : Array Nat := #[]
  for h : i in [0:allNodes.size] do
    if filter allNodes[i] then
      points := (points.push (2 * i + 1)).push (2 * i)
  if points.isEmpty then return
  let (ys, _) := ScanlineConstraintCalculator.eventKeys (← get).cGraph allNodes
  let events := stableSort points (keyCmp ys)
  ScanlineConstraintCalculator.runKernel allNodes events false

/-- Rust `alter_hitbox(node, spacing, fac)` (Java `alterHitbox`): segments are enlarged upwards
unless `ignoreSpacingUp` (else downwards unless `ignoreSpacingDown`), nodes in both directions. -/
def alterHitbox (md : CompactionMetadata) (node : CNodeId) (spacing fac : Float) : CompactM Unit := do
  let delta := spacing * fac
  match md.segmentInfo node with
  | some segment =>
    if !segment.ignoreSpacingUp then
      modifyCNode node fun c =>
        { c with hitbox := { c.hitbox with
            y := c.hitbox.y - (delta + SMALL_EPSILON)
            height := c.hitbox.height + (delta + SMALL_EPSILON) } }
    else if !segment.ignoreSpacingDown then
      modifyCNode node fun c =>
        { c with hitbox := { c.hitbox with height := c.hitbox.height + (delta + SMALL_EPSILON) } }
  | none =>
    if (md.nodeOrigin node).isSome then
      modifyCNode node fun c =>
        { c with hitbox := { c.hitbox with y := c.hitbox.y - delta, height := c.hitbox.height + fl2p0 * delta } }

/-- Rust `alter_grouped_hitbox_orthogonal(group, spacing, fac)` (Java
`alterGroupedHitboxOrthogonal`): alters the group's master (or first node) like `alterHitbox`
and shrinks the group's segments on their ignored side. -/
def alterGroupedHitboxOrthogonal (md : CompactionMetadata) (group : CGroupId) (spacing fac : Float) :
    CompactM Unit := do
  let grp ← getCGroup group
  let master := match grp.master with
    | some m => some m
    | none => grp.cNodes[0]?
  let some master := master | return
  alterHitbox md master spacing fac
  let groupNodes := (← getCGroup group).cNodes
  if groupNodes.size <= 1 then return
  let delta := spacing * fac
  for node in groupNodes do
    if node == master then continue
    let some segment := md.segmentInfo node | continue
    if segment.ignoreSpacingUp then
      modifyCNode node fun c =>
        { c with hitbox := { c.hitbox with
            y := c.hitbox.y + (delta + SMALL_EPSILON)
            height := c.hitbox.height - (delta + SMALL_EPSILON) } }
    else if segment.ignoreSpacingDown then
      modifyCNode node fun c =>
        { c with hitbox := { c.hitbox with height := c.hitbox.height - (delta + SMALL_EPSILON) } }

/-- Rust `segment_spacing()`: `max(0, verticalEdgeEdgeSpacing / 2 - EPSILON)`. -/
def segmentSpacing (self : EdgeAwareScanlineConstraintCalculation) : Float :=
  fmax (self.verticalEdgeEdgeSpacing / 2.0 - EPSILON) 0.0

/-- Rust `minimum_spacing(compactor)`: the smallest half spacing over all segments and nodes
(external port dummies excluded); `0` if there is none. -/
def minimumSpacing (self : EdgeAwareScanlineConstraintCalculation) : CompactM Float := do
  let md := self.metadata
  let mut minSpacing := Float.posInf
  for node in (← cNodeIds) do
    if md.isExternalPortNode node then continue
    if md.isSegment node then
      minSpacing := fmin minSpacing self.segmentSpacing
      continue
    if let some spacing := md.nodeNodeSpacing node then
      minSpacing := fmin minSpacing (fmax (spacing / fl2p0 - EPSILON) fl0p0)
  return if minSpacing.isFinite then minSpacing else fl0p0

/-- Rust `calculate_for_spline(compactor)` (Java `calculateForSpline`). -/
def calculateForSpline (self : EdgeAwareScanlineConstraintCalculation) : CompactM Unit := do
  let md := self.metadata
  sweep md.isSegment
  let minSpacing ← self.minimumSpacing
  let nodes ← cNodeIds
  for node in nodes do
    if (md.nodeOrigin node).isSome then
      alterHitbox md node minSpacing fl1p0
  sweep fun _ => true
  for node in nodes do
    if (md.nodeOrigin node).isSome then
      alterHitbox md node minSpacing (-fl1p0)

/-- The "nodes" round of `calculate_for_orthogonal`: nodes are enlarged by half their
edge-edge spacing (minus `EPSILON`) and swept among themselves. -/
private def orthogonalNodeRound (self : EdgeAwareScanlineConstraintCalculation) (nodes : Array CNodeId) :
    CompactM Unit := do
  let md := self.metadata
  let mut schedule : Array (CNodeId × Float) := #[]
  for node in nodes do
    if (md.nodeOrigin node).isSome then
      let spacing := (md.nodeEdgeSpacing node).getD self.verticalEdgeEdgeSpacing
      let adjusted := fmax (spacing / fl2p0 - EPSILON) fl0p0
      alterHitbox md node adjusted fl1p0
      schedule := schedule.push (node, adjusted)
  sweep fun n => (md.nodeOrigin n).isSome
  for (node, spacing) in schedule do
    alterHitbox md node spacing (-fl1p0)

/-- Rust `calculate_for_orthogonal(compactor)` (Java `calculateForOrthogonal`): segments, nodes,
then everything with the grouped hitboxes enlarged by the minimum spacing. -/
def calculateForOrthogonal (self : EdgeAwareScanlineConstraintCalculation) : CompactM Unit := do
  let md := self.metadata
  let segmentSpacing := self.segmentSpacing
  let nodes ← cNodeIds
  let mut segmentNodes : Array CNodeId := #[]
  for node in nodes do
    if md.isSegment node then
      alterHitbox md node segmentSpacing fl1p0
      segmentNodes := segmentNodes.push node
  sweep md.isSegment
  for node in segmentNodes do
    alterHitbox md node segmentSpacing (-fl1p0)
  self.orthogonalNodeRound nodes
  let minSpacing ← self.minimumSpacing
  let groups ← cGroupIds
  for group in groups do
    alterGroupedHitboxOrthogonal md group minSpacing fl1p0
  sweep fun _ => true
  for group in groups do
    alterGroupedHitboxOrthogonal md group minSpacing (-fl1p0)

/-- `calculateConstraints(compactor)`: dispatches on the edge routing. -/
def calculateConstraints (self : EdgeAwareScanlineConstraintCalculation) : CompactM Unit :=
  match self.edgeRouting with
  | .orthogonal => self.calculateForOrthogonal
  | .splines => self.calculateForSpline
  | _ => pure ()

/-- The strategy as an alg.common `ConstraintCalculationAlgorithm`. -/
def toAlgorithm (self : EdgeAwareScanlineConstraintCalculation) : ConstraintCalculationAlgorithm :=
  ⟨self.calculateConstraints⟩

end EdgeAwareScanlineConstraintCalculation

end Elk.Alg.Layered.Intermediate.Compaction
