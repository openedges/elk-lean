import Std.Data.HashSet
import Elk.Core.Alg.LayoutProcessor
import Elk.Alg.Layered.Graph.LGraphUtil
import Elk.Alg.Layered.Compound.CrossHierarchyEdgeComparator
/-!
# `org.eclipse.elk.alg.layered.compound.CompoundGraphPostprocessor`

Port of `CompoundGraphPostprocessor` of `compound/mod.rs` (elk-rs) and
`CompoundGraphPostprocessor.java`: restores the original cross-hierarchy edges recorded in
`LGraphInternals.crossHierarchyMap` of the top-level graph. For every original edge the
segments are sorted from start to end, their bend points (and junction points) are transformed
into the coordinate system of the reference graph and concatenated, the labels are moved back,
the edge is reconnected to the actual source and target ports and the dummy segments are
disconnected (each once, in first-use order).

`OrthogonalRoutingGenerator.TOLERANCE` (p5edges, `1e-3`) is the only p5 dependency of the Rust
code; it is defined locally as `TOLERANCE`. The `ElkTrace` debug prints (`[compound-post]`) are
not ported.
-/
namespace Elk.Alg.Layered.Compound

open Elk.Graph Elk.Core Elk.Core.Alg Elk.Core.Math Elk.Core.Options Elk.Core.Util
open Elk.Alg.Layered.Graph Elk.Alg.Layered.Options LayeredM

namespace CompoundGraphPostprocessor

/-- `OrthogonalRoutingGenerator.TOLERANCE` (elk-rs `orthogonal_routing_generator.rs`): the
tolerance below which two coordinates count as equal when deciding about a bend point. -/
def TOLERANCE : Float := 1e-3

/-- Rust `copy_junction_points(source_edge, target, offset)`: appends the segment's junction
points (moved by `offset`) to the collected chain, if junction points are collected. -/
def copyJunctionPoints (sourceEdge : LEdgeId) (target : Option KVectorChain) (offset : KVector) :
    LayeredM (Option KVectorChain) := do
  let some chain := target | return none
  match (← getEdge sourceEdge).props.get LayeredOptions.JUNCTION_POINTS with
  | some jps => return some (chain ++ jps.offsetValues offset.x offset.y)
  | none => return some chain

/-- Rust `copy_labels_back(hierarchy_segment, orig_edge, reference_graph)`: moves the labels of
the segment that belong to the original edge back to it, converting their positions from the
segment's source graph to the reference graph. -/
def copyLabelsBack (hierarchySegment origEdge : LEdgeId) (referenceGraph : LGraphId) : LayeredM Unit := do
  let some source := (← getEdge hierarchySegment).source | return
  let some sourceNode := (← getPort source).owner | return
  let some segmentSourceGraph ← nodeGraph sourceNode | return
  let mut labelsToMove : Array LLabelId := #[]
  let mut remaining : Array LLabelId := #[]
  for label in (← getEdge hierarchySegment).labels do
    if (← getLabel label).internal.originalLabelEdge == some origEdge then
      labelsToMove := labelsToMove.push label
    else
      remaining := remaining.push label
  let kept := remaining
  modifyEdge hierarchySegment fun e => { e with labels := kept }
  for label in labelsToMove do
    let position ← LGraphUtil.changeCoordSystem (← getLabel label).position segmentSourceGraph referenceGraph
    modifyLabel label fun lb => { lb with position := position }
    modifyEdge origEdge fun e => { e with labels := e.labels.push label }

/-- Restores one original edge from its sorted segments (body of the Rust loop over the map
keys). Returns the dummy edges seen, extended by the segments of this edge. -/
private def restoreEdge (origEdge : LEdgeId) (crossEdges : Array CrossHierarchyEdge)
    (addUnnecessaryBendpoints : Bool) (dummyEdges : Array LEdgeId) (seen : Std.HashSet LEdgeId) :
    LayeredM (Array LEdgeId × Std.HashSet LEdgeId) := do
  let some firstEdge := crossEdges[0]? | return (dummyEdges, seen)
  let some lastEdge := crossEdges.back? | return (dummyEdges, seen)
  let some sourcePort ← firstEdge.actualSource | return (dummyEdges, seen)
  let some targetPort ← lastEdge.actualTarget | return (dummyEdges, seen)
  let some referenceNode := (← getPort sourcePort).owner
    | throw (IO.userError "java.lang.IllegalStateException: source port missing node")
  let some targetNode := (← getPort targetPort).owner
    | throw (IO.userError "java.lang.IllegalStateException: target port missing node")
  let referenceGraph ← if ← LGraphUtil.isDescendant targetNode referenceNode then
      pure (← getNode referenceNode).nestedGraph
    else nodeGraph referenceNode
  let some referenceGraph := referenceGraph | return (dummyEdges, seen)
  let mut hasJunctionPoints := false
  for crossEdge in crossEdges do
    if ← crossEdge.hasJunctionPoints then hasJunctionPoints := true
  let mut junctionPoints : Option KVectorChain := if hasJunctionPoints then some #[] else none
  modifyEdge origEdge fun e =>
    let props := if hasJunctionPoints then e.props.set LayeredOptions.JUNCTION_POINTS #[]
      else e.props.remove LayeredOptions.JUNCTION_POINTS
    { e with props := props, bendPoints := #[] }
  let mut lastPoint : Option KVector := none
  let mut dummyEdges := dummyEdges
  let mut seen := seen
  for crossEdge in crossEdges do
    let offset ← LGraphUtil.changeCoordSystem ⟨0.0, 0.0⟩ crossEdge.graph referenceGraph
    let ledge := crossEdge.edge
    let ed ← getEdge ledge
    let bendPoints := ed.bendPoints.offsetValues offset.x offset.y
    let sourcePoint ← match ed.source with
      | some p => pure ((← withArena (·.portAbsoluteAnchor p)).getD ⟨0.0, 0.0⟩)
      | none => pure ⟨0.0, 0.0⟩
    let targetPoint ← match ed.target with
      | some p => pure ((← withArena (·.portAbsoluteAnchor p)).getD ⟨0.0, 0.0⟩)
      | none => pure ⟨0.0, 0.0⟩
    let sourcePoint := sourcePoint + offset
    let targetPoint := targetPoint + offset
    match lastPoint with
    | some lp =>
      let nextPoint := if bendPoints.isEmpty then targetPoint else bendPoints[0]!
      let xDiffEnough := Float.abs (lp.x - nextPoint.x) > TOLERANCE
      let yDiffEnough := Float.abs (lp.y - nextPoint.y) > TOLERANCE
      let shouldAdd := if addUnnecessaryBendpoints then xDiffEnough || yDiffEnough
        else xDiffEnough && yDiffEnough
      modifyEdge origEdge fun e =>
        let bps := if shouldAdd then e.bendPoints.push sourcePoint else e.bendPoints
        { e with bendPoints := bps ++ bendPoints }
    | none =>
      modifyEdge origEdge fun e => { e with bendPoints := e.bendPoints ++ bendPoints }
    lastPoint := some (if bendPoints.isEmpty then sourcePoint else bendPoints.back!)
    junctionPoints ← copyJunctionPoints ledge junctionPoints offset
    if (← crossEdge.actualTarget) == some targetPort then
      let targetGraph ← nodeGraph targetNode
      let mut targetOffset := offset
      if let some tg := targetGraph then
        if tg != crossEdge.graph then
          targetOffset ← LGraphUtil.changeCoordSystem ⟨0.0, 0.0⟩ tg referenceGraph
      let finalOffset := targetOffset
      modifyEdge origEdge fun e => { e with internal := { e.internal with targetOffset := some finalOffset } }
    copyLabelsBack ledge origEdge referenceGraph
    if !seen.contains ledge then
      seen := seen.insert ledge
      dummyEdges := dummyEdges.push ledge
  setEdgeSource origEdge (some sourcePort)
  setEdgeTarget origEdge (some targetPort)
  if let some jps := junctionPoints then
    setEdgeProp origEdge LayeredOptions.JUNCTION_POINTS jps
  return (dummyEdges, seen)

/-- `process(graph, progressMonitor)` (Rust `process_with_ref`). -/
def process (graph : LGraphId) (monitor : ProgressMonitor) : LayeredM Unit := do
  discard <| monitor.begin "Compound graph postprocessor" 1.0
  let gr ← getGraph graph
  let addUnnecessaryBendpoints := gr.props.getD LayeredOptions.UNNECESSARY_BENDPOINTS false
  let crossHierarchyMap := gr.internal.crossHierarchyMap
  let mut dummyEdges : Array LEdgeId := #[]
  let mut seen : Std.HashSet LEdgeId := {}
  for origEdge in CrossHierarchyMap.keys crossHierarchyMap do
    let crossEdges := CrossHierarchyMap.get crossHierarchyMap origEdge
    if crossEdges.isEmpty then continue
    let crossEdges ← CrossHierarchyEdgeComparator.sortCrossHierarchyEdges crossEdges graph
    let (d, s) ← restoreEdge origEdge crossEdges addUnnecessaryBendpoints dummyEdges seen
    dummyEdges := d
    seen := s
  for dummyEdge in dummyEdges do
    setEdgeSource dummyEdge none
    setEdgeTarget dummyEdge none
  monitor.done

end CompoundGraphPostprocessor

/-- `new CompoundGraphPostprocessor()` as a layout processor. -/
def CompoundGraphPostprocessor.processor : LayoutProcessor LayeredM LGraphId where
  name := "CompoundGraphPostprocessor"
  process := CompoundGraphPostprocessor.process

end Elk.Alg.Layered.Compound
