import Elk.Alg.Layered.LayeredPhases
import Elk.Core.Util.Java
import Elk.Alg.Layered.Intermediate.EndLabelPreprocessor
/-!
# `org.eclipse.elk.alg.layered.intermediate.LabelSideSelector`

Port of elk-rs `intermediate/label_side_selector.rs` (Java `LabelSideSelector`): "Decides for each
edge label whether to place it above or below its respective edge. How the decision is made depends
on the active edge label side selection strategy."

Slot: before phase 4 (same-slot dependencies `InLayerConstraintProcessor`,
`LabelManagementProcessor`, `LabelDummySwitcher`). Postcondition: every label has its `LABEL_SIDE`;
label dummies have it too and their ports are moved so that the label extends above or below the
edge.

Strategies (`EDGE_LABELS_SIDE_SELECTION`, default `SMART_DOWN`): `ALWAYS_UP`/`ALWAYS_DOWN` (same side
for everything), `DIRECTION_UP`/`DIRECTION_DOWN` (by whether the edge points right, i.e. is not
`REVERSED`) and `SMART_UP`/`SMART_DOWN` (patterns of consecutive dummy runs and end labels per port
side, falling back to the default side).

Rust deviations from Java (followed here): `apply_label_side_to_dummy` also writes the side to the
dummy's represented labels; the edge thickness used to move the ports is the `EDGE_THICKNESS` of the
dummy's first incoming (else first outgoing) edge (Java: of the `ORIGIN` edge); the edge label
spacing is read once from the graph (`2.0` when not stored).

The Rust `VecDeque`s are arrays (`push_back` = `push`, `front`/`back` = first/last element).
The end labels of a port are gathered with `EndLabelPreprocessor.gatherLabels` (elk-rs
`end_label_preprocessor::gather_labels`, with its side effects: `END_LABEL_EDGE` of the gathered
labels and `MAX_EDGE_THICKNESS` of the port).
-/
/-! Float literals as global constants (FL): inside branches, loops and specialised code the compiler
shares a literal's `Nat`/`Bool` arguments with unrelated variables (CSE) and then parses it on every
evaluation (`FastFloat.ofScientificImpl`); a top-level constant is a load (PLAN §7.1 items 17, 22). -/
private def fl0p0 : Float := 0.0
private def fl1p0 : Float := 1.0
private def fl2p0 : Float := 2.0

namespace Elk.Alg.Layered.Intermediate

open Elk.Graph Elk.Core Elk.Core.Alg Elk.Core.Math Elk.Core.Options Elk.Core.Util Elk.Alg.Layered
  Elk.Alg.Layered.Graph Elk.Alg.Layered.Options LayeredM

namespace LabelSideSelector

/-- Rust `get_origin_edge_thickness(label_dummy)`: `EDGE_THICKNESS` of the first incoming edge, else
of the first outgoing edge, else `0`. -/
def originEdgeThickness (labelDummy : LNodeId) : LayeredM Float := do
  let incoming ← withArena (·.nodeIncomingEdges labelDummy)
  if let some edge := incoming[0]? then
    return (← getEdge edge).props.getD CoreOptions.EDGE_THICKNESS 0.0
  let outgoing ← withArena (·.nodeOutgoingEdges labelDummy)
  if let some edge := outgoing[0]? then
    return (← getEdge edge).props.getD CoreOptions.EDGE_THICKNESS 0.0
  return 0.0

/-- Rust `apply_label_side_to_dummy(node, side, edge_label_spacing)`: only for `LABEL` nodes. The side
(`INLINE` for inline edge label dummies) is set on the dummy and its represented labels; unless the
labels go `BELOW` the edge, the ports move to `height - ceil(thickness / 2)` (`ABOVE`) or to
`ceil(height - spacing - thickness) / 2` with the dummy shrunk by `spacing + thickness` (`INLINE`). -/
def applyLabelSideToDummy (node : LNodeId) (side : LabelSide) (edgeLabelSpacing : Float) : LayeredM Unit := do
  if (← getNode node).type != .label then return
  let effectiveSide := if ← withArena (·.nodeIsInlineEdgeLabel node) then LabelSide.inline else side
  modifyNode node fun n => { n with internal := { n.internal with labelSide := effectiveSide } }
  for label in (← getNode node).internal.representedLabels do
    modifyLabel label fun l => { l with internal := { l.internal with labelSide := effectiveSide } }
  if effectiveSide != .below then
    let thickness ← originEdgeThickness node
    let mut portPos : Float := fl0p0
    if effectiveSide == .above then
      let nodeHeight := (← getNode node).size.y
      portPos := nodeHeight - Float.ceil (thickness / fl2p0)
    else if effectiveSide == .inline then
      let nodeHeight := (← getNode node).size.y
      portPos := Float.ceil (nodeHeight - edgeLabelSpacing - thickness) / fl2p0
      modifyNode node fun n => { n with size := { n.size with y := n.size.y - edgeLabelSpacing - thickness } }
    let pos := portPos
    for port in (← getNode node).ports do
      modifyPort port fun p => { p with position := { p.position with y := pos } }

/-- Rust `apply_label_side_to_edge(edge, side)`: the side of every label of the edge. -/
def applyLabelSideToEdge (edge : LEdgeId) (side : LabelSide) : LayeredM Unit := do
  for label in (← getEdge edge).labels do
    modifyLabel label fun l => { l with internal := { l.internal with labelSide := side } }

/-- Rust `apply_label_side_to_labels(labels, side)`. -/
def applyLabelSideToLabels (labels : Array LLabelId) (side : LabelSide) : LayeredM Unit := do
  for label in labels do
    modifyLabel label fun l => { l with internal := { l.internal with labelSide := side } }

/-- Rust `does_edge_point_right_edge(edge)`: not `REVERSED`. -/
def doesEdgePointRightEdge (edge : LEdgeId) : LayeredM Bool := do
  return !(← getEdge edge).internal.reversed

/-- Rust `does_edge_point_right_node(label_dummy)`: the first incoming or the first outgoing edge
points right. -/
def doesEdgePointRightNode (labelDummy : LNodeId) : LayeredM Bool := do
  let incoming ← withArena (·.nodeIncomingEdges labelDummy)
  let outgoing ← withArena (·.nodeOutgoingEdges labelDummy)
  let incomingRight ← match incoming[0]? with
    | some e => doesEdgePointRightEdge e
    | none => pure false
  let outgoingRight ← match outgoing[0]? with
    | some e => doesEdgePointRightEdge e
    | none => pure false
  return incomingRight || outgoingRight

/-- Rust `same_side(graph, label_side, spacing)`: every label dummy and every outgoing edge's labels. -/
def sameSide (graph : LGraphId) (labelSide : LabelSide) (edgeLabelSpacing : Float) : LayeredM Unit := do
  let layers := (← getGraph graph).layers
  for layer in layers do
    let nodes := (← getLayer layer).nodes
    for node in nodes do
      applyLabelSideToDummy node labelSide edgeLabelSpacing
      for edge in (← withArena (·.nodeOutgoingEdges node)) do
        applyLabelSideToEdge edge labelSide

/-- Rust `based_on_direction(graph, side_for_rightward_edges, spacing)`. -/
def basedOnDirection (graph : LGraphId) (sideForRightwardEdges : LabelSide) (edgeLabelSpacing : Float) : LayeredM Unit := do
  let layers := (← getGraph graph).layers
  for layer in layers do
    let nodes := (← getLayer layer).nodes
    for node in nodes do
      if (← getNode node).type == .label then
        let side := if ← doesEdgePointRightNode node then sideForRightwardEdges else sideForRightwardEdges.opposite
        applyLabelSideToDummy node side edgeLabelSpacing
      for edge in (← withArena (·.nodeOutgoingEdges node)) do
        let side := if ← doesEdgePointRightEdge edge then sideForRightwardEdges else sideForRightwardEdges.opposite
        applyLabelSideToEdge edge side

/-- Rust `get_long_edge_end_node(dummy, source)`: owner of `LONG_EDGE_SOURCE`/`LONG_EDGE_TARGET`. -/
def longEdgeEndNode (dummy : LNodeId) (source : Bool) : LayeredM (Option LNodeId) := do
  let nd ← getNode dummy
  let port := if source then nd.internal.longEdgeSource else nd.internal.longEdgeTarget
  match port with
  | some p => return (← getPort p).owner
  | none => return none

/-- Rust `apply_label_sides_to_label_dummy_run(run, default_side, spacing)`: a run of exactly two
dummies gets `ABOVE`/`BELOW`, otherwise every dummy the default side. Returns the emptied run. -/
def applyLabelSidesToLabelDummyRun (labelDummyRun : Array LNodeId) (defaultSide : LabelSide)
    (edgeLabelSpacing : Float) : LayeredM (Array LNodeId) := do
  if labelDummyRun.isEmpty then return labelDummyRun
  if labelDummyRun.size == 2 then
    applyLabelSideToDummy labelDummyRun[0]! .above edgeLabelSpacing
    applyLabelSideToDummy labelDummyRun[1]! .below edgeLabelSpacing
  else
    for dummyNode in labelDummyRun do
      applyLabelSideToDummy dummyNode defaultSide edgeLabelSpacing
  return #[]

/-- Rust `apply_for_dummy_node_run_with_simple_loops(dummies, count, default_side, spacing)`: splits
the run into sub-runs of dummies with the same long edge source and target nodes (`none == none`
counts as equal) and applies `applyLabelSidesToLabelDummyRun` to each. -/
def applyForDummyNodeRunWithSimpleLoops (dummyNodes : Array LNodeId) (defaultSide : LabelSide)
    (edgeLabelSpacing : Float) : LayeredM Unit := do
  let mut labelDummyRun : Array LNodeId := Array.mkEmpty dummyNodes.size
  let mut prevLongEdgeSource : Option LNodeId := none
  let mut prevLongEdgeTarget : Option LNodeId := none
  for currentDummy in dummyNodes do
    let currLongEdgeSource ← longEdgeEndNode currentDummy true
    let currLongEdgeTarget ← longEdgeEndNode currentDummy false
    if prevLongEdgeSource != currLongEdgeSource || prevLongEdgeTarget != currLongEdgeTarget then
      labelDummyRun ← applyLabelSidesToLabelDummyRun labelDummyRun defaultSide edgeLabelSpacing
      prevLongEdgeSource := currLongEdgeSource
      prevLongEdgeTarget := currLongEdgeTarget
    labelDummyRun := labelDummyRun.push currentDummy
  let _ ← applyLabelSidesToLabelDummyRun labelDummyRun defaultSide edgeLabelSpacing

/-- Rust `smart_for_consecutive_dummy_node_run(dummies, label_count, top, bottom, default, spacing)`:
a single label dummy at the top (bottom) of the layer goes `ABOVE` (`BELOW`), a run of two dummies
gets `ABOVE`/`BELOW`, everything else is handled by the simple loop detection. The caller clears the
queue afterwards. -/
def smartForConsecutiveDummyNodeRun (dummyNodes : Array LNodeId) (labelDummyCount : Nat) (topGroup bottomGroup : Bool)
    (defaultSide : LabelSide) (edgeLabelSpacing : Float) : LayeredM Unit := do
  let firstIsLabel ← match dummyNodes[0]? with
    | some n => pure ((← getNode n).type == .label)
    | none => pure false
  let lastIsLabel ← match dummyNodes.back? with
    | some n => pure ((← getNode n).type == .label)
    | none => pure false
  if topGroup && (!bottomGroup || dummyNodes.size > 1) && labelDummyCount == 1 && firstIsLabel then
    if let some front := dummyNodes[0]? then
      applyLabelSideToDummy front .above edgeLabelSpacing
  else if bottomGroup && (!topGroup || dummyNodes.size > 1) && labelDummyCount == 1 && lastIsLabel then
    if let some back := dummyNodes.back? then
      applyLabelSideToDummy back .below edgeLabelSpacing
  else if dummyNodes.size == 2 then
    applyLabelSideToDummy dummyNodes[0]! .above edgeLabelSpacing
    applyLabelSideToDummy dummyNodes[1]! .below edgeLabelSpacing
  else
    applyForDummyNodeRunWithSimpleLoops dummyNodes defaultSide edgeLabelSpacing

/-- Rust `smart_for_regular_node_port_end_labels(queue, port_side, default_side)`: two ports with end
labels on one side get opposite sides (`ABOVE` first on `NORTH`/`EAST`, `BELOW` first otherwise);
otherwise every list gets the default side. -/
def smartForRegularNodePortEndLabels (endLabelQueue : Array (Array LLabelId)) (portSide : PortSide)
    (defaultSide : LabelSide) : LayeredM Unit := do
  if endLabelQueue.size == 2 then
    if portSide == .north || portSide == .east then
      applyLabelSideToLabels endLabelQueue[0]! .above
      applyLabelSideToLabels endLabelQueue[1]! .below
    else
      applyLabelSideToLabels endLabelQueue[0]! .below
      applyLabelSideToLabels endLabelQueue[1]! .above
  else
    for labelList in endLabelQueue do
      applyLabelSideToLabels labelList defaultSide

/-- Rust `smart_for_regular_node(node, default_side)`: groups the end label lists of consecutive ports
with the same side. -/
def smartForRegularNode (node : LNodeId) (defaultSide : LabelSide) : LayeredM Unit := do
  let ports := (← getNode node).ports
  let mut endLabelQueue : Array (Array LLabelId) := Array.mkEmpty ports.size
  let mut currentPortSide : Option PortSide := none
  for port in ports do
    let portSide := (← getPort port).side
    if some portSide != currentPortSide then
      if !endLabelQueue.isEmpty then
        if let some cps := currentPortSide then
          smartForRegularNodePortEndLabels endLabelQueue cps defaultSide
      endLabelQueue := #[]
      currentPortSide := some portSide
    if let some portEndLabels ← EndLabelPreprocessor.gatherLabels port then
      endLabelQueue := endLabelQueue.push portEndLabels
  if !endLabelQueue.isEmpty then
    if let some cps := currentPortSide then
      smartForRegularNodePortEndLabels endLabelQueue cps defaultSide

/-- Rust `smart(graph, default_side, spacing)`: per layer, runs of consecutive `LABEL`/`LONG_EDGE`
dummies are collected; any other node ends the run (`NORMAL` nodes first get their end label sides);
the first run of a layer is the top group, the remaining queue at the end is the bottom group. -/
def smart (graph : LGraphId) (defaultSide : LabelSide) (edgeLabelSpacing : Float) : LayeredM Unit := do
  let mut dummyNodeQueue : Array LNodeId := #[]
  let layers := (← getGraph graph).layers
  for layer in layers do
    let mut topGroup := true
    let mut labelDummiesInQueue : Nat := 0
    let nodes := (← getLayer layer).nodes
    for node in nodes do
      let nodeType := (← getNode node).type
      match nodeType with
      | .label =>
        labelDummiesInQueue := labelDummiesInQueue + 1
        dummyNodeQueue := dummyNodeQueue.push node
      | .longEdge =>
        dummyNodeQueue := dummyNodeQueue.push node
      | _ =>
        if nodeType == .normal then
          smartForRegularNode node defaultSide
        if !dummyNodeQueue.isEmpty then
          smartForConsecutiveDummyNodeRun dummyNodeQueue labelDummiesInQueue topGroup false defaultSide edgeLabelSpacing
          dummyNodeQueue := #[]
        topGroup := false
        labelDummiesInQueue := 0
    if !dummyNodeQueue.isEmpty then
      smartForConsecutiveDummyNodeRun dummyNodeQueue labelDummiesInQueue topGroup true defaultSide edgeLabelSpacing
      dummyNodeQueue := #[]

/-- `process(layeredGraph, monitor)`. -/
def process (graph : LGraphId) (monitor : ProgressMonitor) : LayeredM Unit := do
  let gr ← getGraph graph
  let mode := gr.props.getD LayeredOptions.EDGE_LABELS_SIDE_SELECTION EdgeLabelSideSelection.smartDown
  let edgeLabelSpacing := if gr.props.has LayeredOptions.SPACING_EDGE_LABEL then
    gr.props.getD LayeredOptions.SPACING_EDGE_LABEL fl2p0 else fl2p0
  let _ ← monitor.begin "Label side selection" fl1p0
  match mode with
  | .alwaysUp => sameSide graph .above edgeLabelSpacing
  | .alwaysDown => sameSide graph .below edgeLabelSpacing
  | .directionUp => basedOnDirection graph .above edgeLabelSpacing
  | .directionDown => basedOnDirection graph .below edgeLabelSpacing
  | .smartUp => smart graph .above edgeLabelSpacing
  | .smartDown => smart graph .below edgeLabelSpacing
  monitor.done

/-- The `LabelSideSelector` processor. -/
def processor : LayeredProcessor := { name := "LabelSideSelector", process := process }

end LabelSideSelector

builtin_initialize registerLabelSideSelector : Unit ←
  IntermediateProcessorStrategy.register .labelSideSelector LabelSideSelector.processor

end Elk.Alg.Layered.Intermediate
