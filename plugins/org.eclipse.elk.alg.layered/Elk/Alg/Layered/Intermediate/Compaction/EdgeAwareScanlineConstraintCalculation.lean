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

The sweep is Java's (`ScanlineConstraintCalculator.sweep` with its `ConstraintsScanlineHandler`,
agent EXT; elk-rs has its own handler without the check and with an identity-ordered interval
list): events sorted by `Double.compare` of the y coordinate, high ends before low ends on equal y
(a zero-height hitbox is deleted before it is inserted and then stays active); the active intervals
form a `TreeSet` keyed by the x centre, so an interval whose centre equals an active one's is
rejected with `IllegalStateException("Invalid hitboxes for scanline constraint calculation.")`,
and `lower`/`higher`/`remove` work by key; a constraint needs the neighbour to have a group that
differs from the node's.

Ported from Rust, which differs from the Java subclass of `ScanlineConstraintCalculator`:
* `sweep` assigns `CNode.id := index` to all nodes, but only the filtered ones take part;
* the node spacing of the "nodes" round falls back to `SPACING_EDGE_EDGE` of the graph when a node
  has no individual value (`unwrap_or(vertical_edge_edge_spacing)`), the minimum spacing falls
  back to `0` when no node contributes;
* the enlargement and its undo are not exact inverses (the `SMALL_EPSILON` is subtracted from
  `y` in both directions); this is kept, as in Java and Rust.

`sweep` is the fast path of the original monadic `sweepReference`: the sort keys are precomputed
and the handler runs as the pure kernel `JavaKernel.run`; differential test
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

/-- Java `constraintsScanlineComparator` on the hitboxes of `g`: `Double.compare` of the y
coordinates, on equal y high ends before low ends (so a zero-height hitbox is deleted before it is
inserted, and stays in the interval set for the rest of the sweep, as in Java). -/
def timestampCmp (g : CGraph) (left right : Timestamp) : Ordering :=
  let ln := g.cNode left.node
  let rn := g.cNode right.node
  let leftY := if left.low then ln.hitbox.y else ln.hitbox.y + ln.hitbox.height
  let rightY := if right.low then rn.hitbox.y else rn.hitbox.y + rn.hitbox.height
  let cmp := Float.compareJava leftY rightY
  if cmp == .eq then
    if !left.low && right.low then .lt
    else if !right.low && left.low then .gt
    else cmp
  else cmp

/-- Java `ConstraintsScanlineHandler`: the `TreeSet` of active intervals keyed by the x centre
(`Double.compare`, so two intervals with the same centre cannot both be in it) and the candidate of
each node (indexed by `CNode.id`). `intervals` is kept sorted by centre. -/
structure Handler where
  intervals : Array CNodeId := #[]
  cand : Array (Option CNodeId) := #[]

private abbrev HandlerM := StateT Handler CompactM

/-- `cNode.hitbox.x + cNode.hitbox.width / 2` (the `TreeSet` key). -/
private def centerX (n : CNodeId) : CompactM Float := do
  let c ← getCNode n
  return c.hitbox.x + c.hitbox.width / 2.0

/-- `TreeSet.lower(n)`: the active interval with the greatest centre below `n`'s (by key, also for a
node that is not in the set). -/
private def lower (n : CNodeId) : HandlerM (Option CNodeId) := do
  let c ← centerX n
  let mut best : Option CNodeId := none
  for e in (← get).intervals do
    if Float.compareJava (← centerX e) c == .lt then best := some e else break
  return best

/-- `TreeSet.higher(n)`: the active interval with the least centre above `n`'s. -/
private def higher (n : CNodeId) : HandlerM (Option CNodeId) := do
  let c ← centerX n
  for e in (← get).intervals do
    if Float.compareJava (← centerX e) c == .gt then return some e
  return none

/-- Java's group test of `delete`: `neighbour.cGroup != null && neighbour.cGroup != node.cGroup`. -/
private def otherGroup (neighbour n : CNodeId) : CompactM Bool := do
  match (← getCNode neighbour).cGroup with
  | some g => return (← getCNode n).cGroup != some g
  | none => return false

private def nodeIdx (n : CNodeId) : CompactM Nat := return (← getCNode n).id.toNat

/-- The text of Java's `IllegalStateException` when `TreeSet.add` rejects an interval. -/
def invalidHitboxesMessage : String := "Invalid hitboxes for scanline constraint calculation."

/-- Java `ConstraintsScanlineHandler.insert`: `TreeSet.add` (an interval with the same centre is
already active: `IllegalStateException`), the node's candidate is its lower neighbour, and it
becomes the candidate of its higher neighbour. -/
private def insert (n : CNodeId) : HandlerM Unit := do
  let c ← centerX n
  let intervals := (← get).intervals
  let mut pos := intervals.size
  for h : i in [0:intervals.size] do
    match Float.compareJava (← centerX intervals[i]) c with
    | .eq => throwIllegalState invalidHitboxesMessage
    | .gt => pos := i; break
    | .lt => pure ()
  modify fun h => { h with intervals := h.intervals.insertIdxIfInBounds pos n }
  let nodeId ← nodeIdx n
  let low ← lower n
  modify fun h => { h with cand := h.cand.setIfInBounds nodeId low }
  if let some right ← higher n then
    let rightId ← nodeIdx right
    modify fun h => { h with cand := h.cand.setIfInBounds rightId (some n) }

/-- Java `ConstraintsScanlineHandler.delete`: adds the constraints to the neighbours (by key) whose
candidate the node is (or which are its candidate) in another group, then `TreeSet.remove` (the
interval with the same centre, if any). -/
private def delete (n : CNodeId) : HandlerM Unit := do
  let h ← get
  let left ← lower n
  let right ← higher n
  if let some left := left then
    let nodeId ← nodeIdx n
    if (h.cand[nodeId]?).join == some left then
      if ← otherGroup left n then
        modifyCNode left fun c => { c with constraints := c.constraints.push n }
  if let some right := right then
    let rightId ← nodeIdx right
    if (h.cand[rightId]?).join == some n then
      if ← otherGroup right n then
        modifyCNode n fun c => { c with constraints := c.constraints.push right }
  let c ← centerX n
  let mut kept : Array CNodeId := #[]
  for e in (← get).intervals do
    if Float.compareJava (← centerX e) c != .eq then kept := kept.push e
  modify fun h => { h with intervals := kept }

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
  let cmp := Float.compareJava (ys.get! a) (ys.get! b)
  if cmp == .eq then
    let aLow := a % 2 == 1
    let bLow := b % 2 == 1
    if !aLow && bLow then .lt
    else if !bLow && aLow then .gt
    else cmp
  else cmp

/-! The pure kernel of the Java handler (`insert`/`delete` above) on positions: `center[i]` is the
`TreeSet` key of node `i`, `group[i]` its group (`+1`, `0` = none), `intervals` the active
positions sorted by key; candidates are `position + 1` (`0` = none). -/
namespace JavaKernel

/-- `TreeSet.lower`: last active position with a smaller key. -/
partial def lowerOf (intervals : Array Nat) (center : FloatArray) (c : Float) (i : Nat) (best : Nat) : Nat :=
  if h : i < intervals.size then
    if Float.compareJava (center.get! intervals[i]) c == .lt then lowerOf intervals center c (i + 1) (intervals[i] + 1)
    else best
  else best

/-- `TreeSet.higher`: first active position with a greater key. -/
partial def higherOf (intervals : Array Nat) (center : FloatArray) (c : Float) (i : Nat) : Nat :=
  if h : i < intervals.size then
    if Float.compareJava (center.get! intervals[i]) c == .gt then intervals[i] + 1
    else higherOf intervals center c (i + 1)
  else 0

/-- Insertion position of key `c`, or `none` when an active interval has the same key. -/
partial def insertPos (intervals : Array Nat) (center : FloatArray) (c : Float) (i : Nat) : Option Nat :=
  if h : i < intervals.size then
    match Float.compareJava (center.get! intervals[i]) c with
    | .lt => insertPos intervals center c (i + 1)
    | .eq => none
    | .gt => some i
  else some i

/-- Java's group test (`neighbour.cGroup != null && neighbour.cGroup != node.cGroup`). -/
@[inline] def otherGroup (group : Array Nat) (neighbour n : Nat) : Bool :=
  let gn := group[neighbour]!
  gn != 0 && gn != group[n]!

/-- The handler over the sorted event codes from event `k` on; stops at a rejected insertion. -/
partial def run (events : Array Nat) (center : FloatArray) (group : Array Nat) (k : Nat)
    (intervals cand pushFrom pushTo : Array Nat) : ScanlineConstraintCalculator.Kernel.Result :=
  if h : k < events.size then
    let e := events[k]
    let n := e / 2
    let c := center.get! n
    if e % 2 == 1 then
      match insertPos intervals center c 0 with
      | none => { pushFrom, pushTo, invalid := true }
      | some pos =>
        let intervals := intervals.insertIdxIfInBounds pos n
        let cand := cand.setIfInBounds n (lowerOf intervals center c 0 0)
        let right := higherOf intervals center c 0
        let cand := if right != 0 then cand.setIfInBounds (right - 1) (n + 1) else cand
        run events center group (k + 1) intervals cand pushFrom pushTo
    else
      let left := lowerOf intervals center c 0 0
      let right := higherOf intervals center c 0
      let addLeft := left != 0 && cand[n]?.getD 0 == left && otherGroup group (left - 1) n
      let pushFrom := if addLeft then pushFrom.push (left - 1) else pushFrom
      let pushTo := if addLeft then pushTo.push n else pushTo
      let addRight := right != 0 && cand[right - 1]?.getD 0 == n + 1 && otherGroup group (right - 1) n
      let pushFrom := if addRight then pushFrom.push n else pushFrom
      let pushTo := if addRight then pushTo.push (right - 1) else pushTo
      let intervals := intervals.filter fun i => Float.compareJava (center.get! i) c != .eq
      run events center group (k + 1) intervals cand pushFrom pushTo
  else { pushFrom, pushTo, invalid := false }

end JavaKernel

/-- Java `sweep(filter)` (fast path of `sweepReference`, see the module doc): assigns
`CNode.id := index` to all nodes and adds the constraints of the scanline over the low/high
timestamps of the nodes accepted by `filter`; a rejected insertion throws Java's
`IllegalStateException` (after the constraints added before it). -/
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
  let r := (fun (g : CGraph) =>
      let (center, group) := ScanlineConstraintCalculator.Kernel.nodeData g allNodes
      JavaKernel.run events center group 0 #[] (Array.replicate allNodes.size 0) #[] #[]) (← get).cGraph
  if !r.pushFrom.isEmpty then
    modify fun st => { st with cGraph := ScanlineConstraintCalculator.Kernel.applyPushes st.cGraph allNodes r }
  if r.invalid then
    throwIllegalState invalidHitboxesMessage

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
