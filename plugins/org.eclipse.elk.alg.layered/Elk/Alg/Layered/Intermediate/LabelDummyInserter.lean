import Elk.Alg.Layered.LayeredPhases
import Elk.Alg.Layered.Graph.LGraphUtil
import Elk.Core.Util.Java
/-!
# `org.eclipse.elk.alg.layered.intermediate.LabelDummyInserter`

Port of elk-rs `intermediate/label_dummy_inserter.rs` (Java `LabelDummyInserter`): "Processor that
inserts dummy nodes into edges that have center labels to reserve space for them. At most one dummy
node is created for each edge."

Slot: before phase 2. Precondition: an unlayered acyclic graph. Postcondition: dummy nodes of type
`LABEL` represent the center labels; the center labels are removed from their edges and attached to
the dummies (`REPRESENTED_LABELS`).

Iteration order (Rust): the layerless nodes as they were at the start (the new dummies are appended
to `layerlessNodes` at the end), per node `LNode::outgoing_edges()` (ports in order, outgoing edges in
order). Nodes without a graph are skipped (Rust `node.graph()` is `None`), and each dummy is created
in its source node's graph (`LNode::new(&graph)`).

The dummy size starts at `(0, thickness)` (`LongEdgeSplitter.splitEdge` sets the height to the
thickness, Rust uses a fresh vector with the same value) and grows per center label: horizontally
`x = max(x, label.x)`, `y += label.y + labelLabelSpacing`; vertically `x += label.x + labelLabelSpacing`,
`y = max(y, label.y)` (`f64::max`). Finally `y += edgeLabelSpacing - labelLabelSpacing + thickness`
(horizontal) or `x -= labelLabelSpacing; y += edgeLabelSpacing + thickness` (vertical).

`splitEdge` is a private copy of elk-rs `LongEdgeSplitter::split_edge` (`set_dummy_node_properties`,
`move_head_labels`); it is to be replaced by `LongEdgeSplitter.splitEdge` once that processor is in
the tree.
-/
namespace Elk.Alg.Layered.Intermediate

open Elk.Graph Elk.Core Elk.Core.Alg Elk.Core.Math Elk.Core.Options Elk.Core.Util Elk.Alg.Layered
  Elk.Alg.Layered.Graph Elk.Alg.Layered.Options LayeredM

namespace LabelDummyInserter

/-- `EDGE_LABELS_PLACEMENT` of a label, `CENTER` when unset (Rust `unwrap_or(Center)`). -/
private def labelPlacement (l : LLabelId) : LayeredM EdgeLabelPlacement := do
  return (← getLabel l).props.getD LayeredOptions.EDGE_LABELS_PLACEMENT EdgeLabelPlacement.center

/-- Rust `label_is_center` (Java `CENTER_LABEL` predicate). -/
def labelIsCenter (l : LLabelId) : LayeredM Bool := do
  return (← labelPlacement l) == .center

/-- Rust `edge_needs_processing` (Java `edgeNeedsToBeProcessed`): not a self loop and at least one
center label. -/
def edgeNeedsProcessing (edge : LEdgeId) : LayeredM Bool := do
  if (← withArena (·.edgeIsSelfLoop edge)) then return false
  for l in (← getEdge edge).labels do
    if ← labelIsCenter l then return true
  return false

/-- `EDGE_THICKNESS` if the edge stores it, else `1.0`; negative values are clamped to `0` and written
back (Rust `retrieve_thickness`, the same logic is part of `split_edge`). -/
def retrieveThickness (edge : LEdgeId) : LayeredM Float := do
  let ed ← getEdge edge
  let thickness := (if ed.props.has CoreOptions.EDGE_THICKNESS then
    ed.props.get CoreOptions.EDGE_THICKNESS else none).getD 1.0
  if thickness < 0.0 then
    setEdgeProp edge CoreOptions.EDGE_THICKNESS 0.0
    return 0.0
  return thickness

/-- Copy of elk-rs `long_edge_splitter::move_head_labels(old_edge, new_edge)`: moves the `HEAD`
labels (only labels that store the placement) to the new edge and records the old edge as their
`END_LABEL_EDGE` unless set. -/
private def moveHeadLabels (oldEdge newEdge : LEdgeId) : LayeredM Unit := do
  for label in (← getEdge oldEdge).labels do
    let lb ← getLabel label
    let placement := (if lb.props.has LayeredOptions.EDGE_LABELS_PLACEMENT then
      lb.props.get LayeredOptions.EDGE_LABELS_PLACEMENT else none).getD EdgeLabelPlacement.center
    if placement != .head then continue
    modifyEdge oldEdge fun e => { e with labels := e.labels.filter (· != label) }
    modifyEdge newEdge fun e => { e with labels := e.labels.push label }
    modifyLabel label fun l =>
      if l.internal.endLabelEdge.isSome then l
      else { l with internal := { l.internal with endLabelEdge := some oldEdge } }

/-- Copy of elk-rs `long_edge_splitter::set_dummy_node_properties(dummy, in_edge, out_edge)`. -/
private def setDummyNodeProperties (dummyNode : LNodeId) (inEdge outEdge : LEdgeId) : LayeredM Unit := do
  let inEdgeSource := (← getEdge inEdge).source
  let outEdgeTarget := (← getEdge outEdge).target
  let inEdgeSourceNode ← match inEdgeSource with
    | some p => pure (← getPort p).owner
    | none => pure none
  let outEdgeTargetNode ← match outEdgeTarget with
    | some p => pure (← getPort p).owner
    | none => pure none
  let inSourceType ← match inEdgeSourceNode with
    | some n => pure (some (← getNode n).type)
    | none => pure none
  let outTargetType ← match outEdgeTargetNode with
    | some n => pure (some (← getNode n).type)
    | none => pure none
  if inSourceType == some NodeType.longEdge then
    if let some source := inEdgeSourceNode then
      let src := (← getNode source).internal
      modifyNode dummyNode fun d => { d with internal := { d.internal with
        longEdgeSource := src.longEdgeSource, longEdgeTarget := src.longEdgeTarget,
        longEdgeHasLabelDummies := src.longEdgeHasLabelDummies } }
  else if inSourceType == some NodeType.label then
    if let some source := inEdgeSourceNode then
      let src := (← getNode source).internal
      modifyNode dummyNode fun d => { d with internal := { d.internal with
        longEdgeSource := src.longEdgeSource, longEdgeTarget := src.longEdgeTarget,
        longEdgeHasLabelDummies := true } }
  else if outTargetType == some NodeType.label then
    if let some target := outEdgeTargetNode then
      let tgt := (← getNode target).internal
      modifyNode dummyNode fun d => { d with internal := { d.internal with
        longEdgeSource := tgt.longEdgeSource, longEdgeTarget := tgt.longEdgeTarget,
        longEdgeHasLabelDummies := true } }
  else
    modifyNode dummyNode fun d => { d with internal := { d.internal with
      longEdgeSource := inEdgeSource, longEdgeTarget := outEdgeTarget } }

/-- Copy of elk-rs `LongEdgeSplitter::split_edge(edge, dummy_node)`: the dummy gets the height
`thickness`, a `WEST` input and an `EAST` output port at `floor(thickness / 2)`; `edge` now ends at the
input port and a new edge (all properties of `edge` except `JUNCTION_POINTS`, Rust `copy_properties`
into an empty map = the public map and the typed internals) leads from the output port to the old
target. Returns the new edge. -/
private def splitEdge (edge : LEdgeId) (dummyNode : LNodeId) : LayeredM LEdgeId := do
  let oldEdgeTarget := (← getEdge edge).target
  let thickness ← retrieveThickness edge
  modifyNode dummyNode fun n => { n with size := { n.size with y := thickness } }
  let portPos := Float.floor (thickness / 2.0)
  let dummyInput ← createPort
  modifyPort dummyInput fun p =>
    let p := p.setSide .west
    { p with position := { p.position with y := portPos } }
  setPortNode dummyInput (some dummyNode)
  let dummyOutput ← createPort
  modifyPort dummyOutput fun p =>
    let p := p.setSide .east
    { p with position := { p.position with y := portPos } }
  setPortNode dummyOutput (some dummyNode)
  setEdgeTarget edge (some dummyInput)
  let old ← getEdge edge
  let dummyEdge ← createEdge { props := old.props.remove LayeredOptions.JUNCTION_POINTS, internal := old.internal }
  setEdgeSource dummyEdge (some dummyOutput)
  setEdgeTarget dummyEdge oldEdgeTarget
  setDummyNodeProperties dummyNode edge dummyEdge
  moveHeadLabels edge dummyEdge
  return dummyEdge

/-- Rust `create_label_dummy(graph, edge, thickness)` (Java `createLabelDummy`): a `LABEL` node with
`ORIGIN = edge`, `PORT_CONSTRAINTS = FIXED_POS` and the edge's end ports as long edge source/target,
then the edge is split at it and its ports are placed at `floor(thickness / 2)`. -/
def createLabelDummy (graph : LGraphId) (edge : LEdgeId) (thickness : Float) : LayeredM LNodeId := do
  let ed ← getEdge edge
  let dummy ← createNode graph { type := .label }
  modifyNode dummy fun n =>
    { n with
      props := n.props.set LayeredOptions.PORT_CONSTRAINTS PortConstraints.fixedPos
      internal := { n.internal with
        origin := some (.lEdge edge)
        longEdgeSource := ed.source
        longEdgeTarget := ed.target } }
  let _ ← splitEdge edge dummy
  let portPos := Float.floor (thickness / 2.0)
  for port in (← getNode dummy).ports do
    modifyPort port fun p => { p with position := { p.position with y := portPos } }
  return dummy

/-- Rust `collect_center_labels_and_size(edge, direction, thickness, edgeLabelSpacing,
labelLabelSpacing)`: moves the center labels of `edge` into the returned list (the other labels stay
on the edge, in order) and computes the dummy size. -/
def collectCenterLabelsAndSize (edge : LEdgeId) (layoutDirection : Direction) (thickness edgeLabelSpacing
    labelLabelSpacing : Float) : LayeredM (Array LLabelId × KVector) := do
  let labels := (← getEdge edge).labels
  let mut represented : Array LLabelId := #[]
  let mut remaining : Array LLabelId := #[]
  let mut dummySize : KVector := ⟨0.0, thickness⟩
  for label in labels do
    let lb ← getLabel label
    let placement := lb.props.getD LayeredOptions.EDGE_LABELS_PLACEMENT EdgeLabelPlacement.center
    if placement == .center then
      if layoutDirection.isVertical then
        dummySize := ⟨dummySize.x + (lb.size.x + labelLabelSpacing), fmax dummySize.y lb.size.y⟩
      else
        dummySize := ⟨fmax dummySize.x lb.size.x, dummySize.y + (lb.size.y + labelLabelSpacing)⟩
      represented := represented.push label
    else
      remaining := remaining.push label
  if !represented.isEmpty then
    if layoutDirection.isVertical then
      dummySize := ⟨dummySize.x - labelLabelSpacing, dummySize.y + (edgeLabelSpacing + thickness)⟩
    else
      dummySize := { dummySize with y := dummySize.y + (edgeLabelSpacing - labelLabelSpacing + thickness) }
  let rest := remaining
  modifyEdge edge fun e => { e with labels := rest }
  return (represented, dummySize)

/-- `process(layeredGraph, monitor)`. -/
def process (layeredGraph : LGraphId) (monitor : ProgressMonitor) : LayeredM Unit := do
  let _ ← monitor.begin "Label dummy insertions" 1.0
  let gr ← getGraph layeredGraph
  let edgeLabelSpacing := gr.props.getD LayeredOptions.SPACING_EDGE_LABEL 2.0
  let labelLabelSpacing := gr.props.getD LayeredOptions.SPACING_LABEL_LABEL 1.0
  let layoutDirection := gr.props.getD LayeredOptions.DIRECTION Direction.right
  let nodes := gr.layerlessNodes
  let mut newDummyNodes : Array LNodeId := #[]
  for node in nodes do
    let some graph ← nodeGraph node | continue
    let outgoingEdges ← withArena (·.nodeOutgoingEdges node)
    for edge in outgoingEdges do
      if !(← edgeNeedsProcessing edge) then continue
      let thickness ← retrieveThickness edge
      let dummyNode ← createLabelDummy graph edge thickness
      newDummyNodes := newDummyNodes.push dummyNode
      let (representedLabels, dummySize) ←
        collectCenterLabelsAndSize edge layoutDirection thickness edgeLabelSpacing labelLabelSpacing
      modifyNode dummyNode fun n =>
        { n with size := dummySize, internal := { n.internal with representedLabels := representedLabels } }
  let added := newDummyNodes
  modifyGraph layeredGraph fun g => { g with layerlessNodes := g.layerlessNodes ++ added }
  monitor.done

/-- The `LabelDummyInserter` processor. -/
def processor : LayeredProcessor := { name := "LabelDummyInserter", process := process }

end LabelDummyInserter

builtin_initialize registerLabelDummyInserter : Unit ←
  IntermediateProcessorStrategy.register .labelDummyInserter LabelDummyInserter.processor

end Elk.Alg.Layered.Intermediate
