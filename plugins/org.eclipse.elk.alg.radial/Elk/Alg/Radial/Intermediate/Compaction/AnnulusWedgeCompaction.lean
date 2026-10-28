import Std.Data.HashMap
import Elk.Graph
import Elk.Core.Options
import Elk.Alg.Radial.InternalProperties
import Elk.Alg.Radial.RadialUtil
import Elk.Alg.Radial.Options.RadialOptions
import Elk.Alg.Radial.Options.SortingStrategy
import Elk.Alg.Radial.Sorting.IRadialSorter
import Elk.Alg.Radial.Sorting.PolarCoordinateSorter
import Elk.Alg.Radial.Intermediate.Compaction.AbstractRadiusExtensionCompaction
import Elk.Alg.Radial.Intermediate.Compaction.IRadialCompactor
/-!
# `org.eclipse.elk.alg.radial.intermediate.compaction.AnnulusWedgeCompaction`

Port of `annulus_wedge_compaction.rs` (elk-rs): contracts every first-level subtree (wedge)
towards the root until it would touch the contour of the neighbouring wedges, its own layer
neighbours, or the previous layers; two passes over all wedges.

The Rust struct fields `left_contour` / `right_contour` (`HashMap` from wedge parent to the
outermost node of every level) are `IO.Ref` tables in the `Context`; `sorter` is shared by all
sorting calls like the Rust `Option<Box<dyn IRadialSorter>>`.
-/
/-! Float literals as global constants (FL): inside branches, loops and specialised code the compiler
shares a literal's `Nat`/`Bool` arguments with unrelated variables (CSE) and then parses it on every
evaluation (`FastFloat.ofScientificImpl`); a top-level constant is a load (PLAN §7.1 items 17, 22). -/
private def fl0p0 : Float := 0.0

namespace Elk.Alg.Radial.Intermediate.Compaction

open Elk.Graph Elk.Core.Options Elk.Alg.Radial.Options Elk.Alg.Radial.Sorting

namespace AnnulusWedgeCompaction

/-- State of an `AnnulusWedgeCompaction` object. -/
structure Context where
  /-- `base`. -/
  base : AbstractRadiusExtensionCompaction
  /-- `sorter`. -/
  sorter : Option IRadialSorter
  /-- `left_contour`: wedge parent to the leftmost node of every level. -/
  leftContour : IO.Ref (Std.HashMap NodeId (Array NodeId))
  /-- `right_contour`: wedge parent to the rightmost node of every level. -/
  rightContour : IO.Ref (Std.HashMap NodeId (Array NodeId))

/-- Sorts with the sorter, if there is one (`if let Some(sorter) = self.sorter.as_mut()`). -/
def sortWith (ctx : Context) (nodes : Array NodeId) : RadialM (Array NodeId) :=
  match ctx.sorter with
  | some sorter => sorter.sort nodes
  | none => pure nodes

/-- `contour_overlap(neighbour_wedge_parent, node, left)`. -/
def contourOverlap (ctx : Context) (neighbourWedgeParent node : NodeId) (left : Bool) : ElkM Bool := do
  let contours ← if left then ctx.leftContour.get else ctx.rightContour.get
  if let some contour := contours.get? neighbourWedgeParent then
    for contourNode in contour do
      if ← ctx.base.overlap node contourNode then return true
  return false

/-- `overlapping(predecessors, left_parent, right_parent, layer_nodes)`. -/
def overlapping (ctx : Context) (predecessors : Array NodeId) (leftParent rightParent : NodeId)
    (layerNodes : Array NodeId) : RadialM Bool := do
  let layerNodes ← sortWith ctx layerNodes
  let some firstNode := layerNodes[0]? | return false
  if ← contourOverlap ctx leftParent firstNode false then return true
  let some lastNode := layerNodes.back? | return false
  if ← contourOverlap ctx rightParent lastNode true then return true
  if ← ctx.base.overlapLayer layerNodes then return true
  for node in layerNodes do
    for predecessor in predecessors do
      if ← ctx.base.overlap node predecessor then return true
  return false

/-- `contract_wedge(root, predecessors, radial_predecessor, radial_successor, current_radius_nodes)`. -/
partial def contractWedge (ctx : Context) (root : NodeId) (predecessors : Array NodeId)
    (radialPredecessor radialSuccessor : NodeId) (currentRadiusNodes : Array NodeId) : RadialM Unit := do
  let mut isOverlapping ← overlapping ctx predecessors radialPredecessor radialSuccessor currentRadiusNodes
  let mut wasContracted := false
  while !isOverlapping do
    ctx.base.contractLayer root currentRadiusNodes true
    wasContracted := true
    isOverlapping ← overlapping ctx predecessors radialPredecessor radialSuccessor currentRadiusNodes
  if wasContracted then ctx.base.contractLayer root currentRadiusNodes false
  let mut nextLevelNodes ← RadialUtil.getNextLevelNodes currentRadiusNodes
  if !nextLevelNodes.isEmpty then
    nextLevelNodes ← sortWith ctx nextLevelNodes
    contractWedge ctx root currentRadiusNodes radialPredecessor radialSuccessor nextLevelNodes

/-- Appends a node to a contour of the wedge parent `key`. -/
def pushContour (ref : IO.Ref (Std.HashMap NodeId (Array NodeId))) (key node : NodeId) : IO Unit :=
  ref.modify fun m => m.insert key ((m.getD key #[]).push node)

/-- `construct_contour(nodes)`. -/
def constructContour (ctx : Context) (nodes : Array NodeId) : RadialM Unit := do
  for node in nodes do
    pushContour ctx.leftContour node node
    pushContour ctx.rightContour node node
    let mut successors ← RadialUtil.getSuccessors node
    if !successors.isEmpty then
      successors ← sortWith ctx successors
      pushContour ctx.leftContour node successors[0]!
      pushContour ctx.rightContour node successors.back!
      while !(← RadialUtil.getNextLevelNodes successors).isEmpty do
        successors ← RadialUtil.getNextLevelNodes successors
        successors ← sortWith ctx successors
        pushContour ctx.leftContour node successors[0]!
        pushContour ctx.rightContour node successors.back!

/-- `compact(graph)`. -/
def compact (graph : NodeId) : RadialM Unit := do
  let some root ← RadialUtil.rootFromGraph graph | return
  let props := (← ElkM.getNode graph).props
  let sorter ← (props.getD RadialOptions.SORTER SortingStrategy.none).create
  let mut base : AbstractRadiusExtensionCompaction := {}
  if let some stepSize := props.get RadialOptions.COMPACTION_STEP_SIZE then
    base := { base with compactionStep := stepSize }
  base := { base with spacing := (props.get CoreOptions.SPACING_NODE_NODE).getD fl0p0 }
  let ctx : Context :=
    { base, sorter, leftContour := ← IO.mkRef {}, rightContour := ← IO.mkRef {} }
  let mut successors ← RadialUtil.getNextLevelNodes #[root]
  successors ← sortWith ctx successors
  constructContour ctx successors
  let rootList := #[root]
  for _ in [0:2] do
    for i in [0:successors.size] do
      let wedgeParent := successors[i]!
      let rightParent := if i < successors.size - 1 then successors[i + 1]! else successors[0]!
      let leftParent := if i == 0 then successors.back! else successors[i - 1]!
      contractWedge ctx root rootList leftParent rightParent #[wedgeParent]

/-- The `IRadialCompactor` of this class. -/
def compactor : IRadialCompactor := { compact := compact }

end AnnulusWedgeCompaction

end Elk.Alg.Radial.Intermediate.Compaction
