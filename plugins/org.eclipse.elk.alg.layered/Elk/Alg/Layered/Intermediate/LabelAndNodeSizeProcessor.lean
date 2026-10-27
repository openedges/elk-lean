import Std.Data.HashSet
import Elk.Core.Util.ElkTrace
import Elk.Alg.Layered.LayeredPhases
import Elk.Alg.Layered.Graph.Transform.LGraphAdapters
import Elk.Alg.Common.NodeSpacing.NodeDimensionCalculation
import Elk.Alg.Layered.Intermediate.LabelAndNodeSize.PortPlacement
import Elk.Alg.Layered.Intermediate.LabelAndNodeSize.PortDrivenSizing
import Elk.Alg.Layered.Intermediate.LabelAndNodeSize.ExternalPortDummyLabels
/-!
# `org.eclipse.elk.alg.layered.intermediate.LabelAndNodeSizeProcessor`

Port of elk-rs `intermediate/label_and_node_size_processor.rs` (Java `LabelAndNodeSizeProcessor`):
"Calculates node sizes, places ports, and places node and port labels."

Slot: before phase 4. Precondition: the port lists are sorted (`PortListSorter`).

`process` (Rust order):
1. `NodeDimensionCalculation.calculateLabelAndNodeSizes` on
   `LGraphAdapters.adapt(graph, true, true, NORMAL)` (Java: the whole processor).
2. Only when `ENABLE_PHASE1_PORT_PLACEMENT` (environment, see `LabelAndNodeSizeFlags`): the elk-rs
   phase-2 workaround (no Java counterpart). Every pass visits the layerless nodes and then the
   layer nodes, each node once (Rust `seen` set):
   * step 2: `placePortsOnNode` for nodes without `INSIDE_SELF_LOOPS_ACTIVATE`
     (`shouldApplyPhase1PortPlacement`), counting resized nodes;
   * phase 2a: when nodes were resized and some port has labels, the label and node size
     calculation runs again (same adapter);
   * phase 2b: again when some node has INSIDE port labels with `PORT_LABELS` size constraints;
   * phase 2c: `placePortsOnNode` again for self-loop holders with `PORTS` constraints, nodes whose
     ports overflow their side and nodes with inside NORTH/SOUTH port labels; phase 2d: the
     calculation again when 2c touched a node; phase 2e: 2c once more (final stabilisation);
   * phase 2f: in graphs with a non-zero `PORT_BORDER_OFFSET`, nodes without fixed port positions
     or ratios get their ports re-placed against the final size (`repositionPortsOnlyOnNode`,
     including the clockwise port reordering unless `ELK_DISABLE_CLOCKWISE_SIDE_ORDER`).
3. With `EXTERNAL_PORTS`, the labels of the external port dummies of every layer are placed
   (`placeExternalPortDummyLabels`).

The `ElkTrace.global.nodeSize` (`ELK_TRACE_NODE_SIZE`) diagnostics are printed to stderr like
elk-rs; the Rust `{:?}` renderings of size constraints, port constraints and port label placements
are printed with the Lean `toString` (Java names).

Deviation: the Rust `LazyLock` switches are read once at startup into
`LabelAndNodeSizeFlags.global` (like `NodeDimensionFlags.global`); `processWith` takes them
explicitly (tests).
-/
namespace Elk.Alg.Layered.Intermediate

open Elk.Graph Elk.Core Elk.Core.Alg Elk.Core.Math Elk.Core.Options Elk.Core.Util Elk.Alg.Layered
  Elk.Alg.Layered.Graph Elk.Alg.Layered.Options LayeredM
open Elk.Alg.Layered.Graph.Transform Elk.Alg.Common.NodeSpacing Elk.Alg.Layered.Intermediate.LabelAndNodeSize

/-- The elk-rs environment switches of `label_and_node_size_processor.rs` (`LazyLock` statics). -/
structure LabelAndNodeSizeFlags where
  /-- `NODE_DIM_USE_FULL_PROCESS` of `node_dimension_calculation.rs` (`ELK_NODE_DIM_SKIP_FULL_PROCESS`
  unset), the mode of `calculateLabelAndNodeSizes`. -/
  useFullProcess : Bool := true
  /-- `ENABLE_PHASE1_PORT_PLACEMENT`: `ELK_NODE_DIM_SKIP_FULL_PROCESS` set and
  `ELK_LAYERED_ENABLE_LABEL_NODE_PHASE1` neither `0` nor `false` (ASCII case-insensitive; unset =
  enabled). -/
  enablePhase1PortPlacement : Bool := false
  /-- `DISABLE_CLOCKWISE_SIDE_ORDER`: `ELK_DISABLE_CLOCKWISE_SIDE_ORDER` set. -/
  disableClockwiseSideOrder : Bool := false
  deriving Inhabited, Repr

namespace LabelAndNodeSizeFlags

/-- Reads the switches from the environment. -/
def fromEnv : IO LabelAndNodeSizeFlags := do
  let skipFullProcess := (← IO.getEnv "ELK_NODE_DIM_SKIP_FULL_PROCESS").isSome
  let enable ← if !skipFullProcess then pure false else do
    match ← IO.getEnv "ELK_LAYERED_ENABLE_LABEL_NODE_PHASE1" with
    | some value => pure !(value == "0" || value.toLower == "false")
    | none => pure true
  return {
    useFullProcess := !skipFullProcess
    enablePhase1PortPlacement := enable
    disableClockwiseSideOrder := (← IO.getEnv "ELK_DISABLE_CLOCKWISE_SIDE_ORDER").isSome }

end LabelAndNodeSizeFlags

/-- The process-wide switches, computed once at startup (elk-rs `LazyLock`). -/
builtin_initialize LabelAndNodeSizeFlags.global : LabelAndNodeSizeFlags ← LabelAndNodeSizeFlags.fromEnv

namespace LabelAndNodeSizeProcessor

/-- `eprintln!` under `ElkTrace::global().node_size`. -/
def traceNodeSize (msg : String) : LayeredM Unit := do
  if ElkTrace.global.nodeSize then IO.eprintln msg

/-! ## Phase 2 predicates -/

/-- Rust `should_apply_phase1_port_placement(node)`: nodes with `INSIDE_SELF_LOOPS_ACTIVATE` are
skipped by every phase-2 port placement pass. -/
def shouldApplyPhase1PortPlacement (nd : LNode) : Bool :=
  !nd.props.getD CoreOptions.INSIDE_SELF_LOOPS_ACTIVATE false

/-- Rust `should_reposition_ports_after_phase2(node, graphs_with_non_zero_border_offset)`: phase-1
nodes of a graph with a non-zero port border offset whose port positions and ratios are not
fixed. -/
def shouldRepositionPortsAfterPhase2 (node : LNodeId) (graphsWithNonZeroBorderOffset : Std.HashSet LGraphId) :
    LayeredM Bool := do
  let nd ← getNode node
  if !shouldApplyPhase1PortPlacement nd then return false
  let some graph ← nodeGraph node | return false
  if !graphsWithNonZeroBorderOffset.contains graph then return false
  let constraints := nd.props.getD LayeredOptions.PORT_CONSTRAINTS PortConstraints.undefined
  return !constraints.isPosFixed && !constraints.isRatioFixed

/-- Rust `should_reapply_phase2_self_loop_port_sizing(node)`: self-loop holders with `PORTS` size
constraints. -/
def shouldReapplyPhase2SelfLoopPortSizing (nd : LNode) : Bool :=
  shouldApplyPhase1PortPlacement nd && nd.internal.selfLoopHolder.isSome &&
    (nd.props.getD LayeredOptions.NODE_SIZE_CONSTRAINTS EnumSet.empty).contains .ports

/-- Rust `should_reapply_phase2_port_axis_overflow_sizing(node)`: nodes with `PORTS` or
`PORT_LABELS` size constraints and free port positions with a port that leaves its side's range
(by more than `1e-6`). -/
def shouldReapplyPhase2PortAxisOverflowSizing (node : LNodeId) : LayeredM Bool := do
  let nd ← getNode node
  if !shouldApplyPhase1PortPlacement nd then return false
  let nodeSize := nd.size
  let sizeConstraints := nd.props.getD LayeredOptions.NODE_SIZE_CONSTRAINTS EnumSet.empty
  let portConstraints := nd.props.getD LayeredOptions.PORT_CONSTRAINTS PortConstraints.undefined
  if !sizeConstraints.contains .ports && !sizeConstraints.contains .portLabels then return false
  if portConstraints.isPosFixed || portConstraints.isRatioFixed then return false
  let eps : Float := 1e-6
  for port in nd.ports do
    let pt ← getPort port
    let pos := pt.position
    let size := pt.size
    let overflows := match pt.side with
      | .north | .south => pos.x < -eps || pos.x + size.x > nodeSize.x + eps
      | .east | .west => pos.y < -eps || pos.y + size.y > nodeSize.y + eps
      | .undefined => false
    if overflows then return true
  return false

/-- Whether the node has a NORTH or SOUTH port with labels. -/
def hasNorthSouthPortLabels (node : LNodeId) : LayeredM Bool := do
  for port in (← getNode node).ports do
    let pt ← getPort port
    if (pt.side == .north || pt.side == .south) && !pt.labels.isEmpty then return true
  return false

/-- Rust `should_reapply_phase2_inside_north_south_label_sizing(node)`: `PORT_LABELS` size
constraints, INSIDE port labels and a labelled NORTH/SOUTH port. -/
def shouldReapplyPhase2InsideNorthSouthLabelSizing (node : LNodeId) : LayeredM Bool := do
  let nd ← getNode node
  if !shouldApplyPhase1PortPlacement nd then return false
  let sizeConstraints := nd.props.getD LayeredOptions.NODE_SIZE_CONSTRAINTS EnumSet.empty
  let placement := nd.props.getD CoreOptions.PORT_LABELS_PLACEMENT EnumSet.empty
  if !sizeConstraints.contains .portLabels || !placement.contains .inside then return false
  hasNorthSouthPortLabels node

/-- The disjunction of the phase 2c/2e predicates (Rust `||` order). -/
def shouldReapplyPhase2Sizing (node : LNodeId) : LayeredM Bool := do
  if shouldReapplyPhase2SelfLoopPortSizing (← getNode node) then return true
  if ← shouldReapplyPhase2PortAxisOverflowSizing node then return true
  shouldReapplyPhase2InsideNorthSouthLabelSizing node

/-- Rust `node_has_inside_port_label_constraints(node)`: INSIDE port labels with `PORT_LABELS` size
constraints. -/
def nodeHasInsidePortLabelConstraints (nd : LNode) : Bool :=
  (nd.props.getD CoreOptions.PORT_LABELS_PLACEMENT EnumSet.empty).contains .inside &&
    (nd.props.getD CoreOptions.NODE_SIZE_CONSTRAINTS EnumSet.empty).contains .portLabels

/-- The nodes visited by every phase-2 pass: the layerless nodes, then the nodes of the layers,
each node once (Rust `seen` set; the predicates only read the node itself, so collecting the list
first is equivalent). -/
def phase2Nodes (graph : LGraphId) : LayeredM (Array LNodeId) := do
  let gr ← getGraph graph
  let mut seen : Std.HashSet LNodeId := {}
  let mut nodes : Array LNodeId := #[]
  for node in gr.layerlessNodes do
    if !seen.contains node then
      seen := seen.insert node
      nodes := nodes.push node
  for layer in gr.layers do
    for node in (← getLayer layer).nodes do
      if !seen.contains node then
        seen := seen.insert node
        nodes := nodes.push node
  return nodes

/-- Rust `graph_needs_phase2b_inside_port_label_restack(graph)`. -/
def graphNeedsPhase2bInsidePortLabelRestack (graph : LGraphId) : LayeredM Bool := do
  for node in ← phase2Nodes graph do
    if nodeHasInsidePortLabelConstraints (← getNode node) then return true
  return false

/-- Rust `graph_has_any_port_labels(graph)`. -/
def graphHasAnyPortLabels (graph : LGraphId) : LayeredM Bool := do
  for node in ← phase2Nodes graph do
    for port in (← getNode node).ports do
      if !(← getPort port).labels.isEmpty then return true
  return false

/-! ## Port placement on one node -/

/-- Whether two sizes differ by more than `EPSILON` in either coordinate. -/
@[inline] def sizeChanged (a b : KVector) : Bool :=
  (a.x - b.x).abs > Float.epsilon || (a.y - b.y).abs > Float.epsilon

/-- The four sides in the Rust placement order. -/
def placementSides : Array PortSide := #[.north, .south, .east, .west]

/-- The `ELK_TRACE_NODE_SIZE` node line of `place_ports_on_node`. -/
private def traceNodeLine (node : LNodeId) (nodeSize : KVector) (sizeConstraints : EnumSet SizeConstraint)
    (portConstraints : PortConstraints) : LayeredM Unit := do
  if !ElkTrace.global.nodeSize then return
  let a ← get
  let nd := a.node node
  let placement := nd.props.getD CoreOptions.PORT_LABELS_PLACEMENT EnumSet.empty
  let count := fun side => (a.nodePortSideView node side).size
  IO.eprintln s!"label-node-size: node id={nd.id} ident={a.nodeDesignation node} size=({Float.toRustDisplay nodeSize.x}, {Float.toRustDisplay nodeSize.y}) constraints={sizeConstraints} port_constraints={portConstraints} placement={placement} sides(N/E/S/W/U)=({count .north}/{count .east}/{count .south}/{count .west}/{count .undefined})"

/-- Places the ports of all four sides for the node's port constraints (shared tail of
`place_ports_on_node` and `reposition_ports_only_on_node`): inside self loops, FIXED_POS border
snapping, FIXED_RATIO, or `placePortsOnSide`; then `updateNodeMargin`. -/
def placePortsForConstraints (node : LNodeId) (nodeSize : KVector) (portConstraints : PortConstraints)
    (insideSelfLoopsActive : Bool) (graphPortSpacing : Float) (graphPortsSurrounding : ElkMargin) : LayeredM Unit := do
  if insideSelfLoopsActive then
    placeInsideSelfLoopPorts node nodeSize.x nodeSize.y
  else if portConstraints.isPosFixed then
    -- Java's FIXED_POS path keeps the axis-aligned coordinate and snaps only the border coordinate
    for side in placementSides do adjustPortsOnSide node side nodeSize.x nodeSize.y
  else if portConstraints.isRatioFixed then
    for side in placementSides do placePortsFixedRatioOnSide node side nodeSize.x nodeSize.y
  else
    for side in placementSides do
      placePortsOnSide node side nodeSize.x nodeSize.y graphPortSpacing graphPortsSurrounding
  updateNodeMargin node

/-- Rust `place_ports_on_node(node, graph_port_spacing, graph_ports_surrounding,
graph_topdown_layout, graph_node_size_fixed_graph_size)`: for `NORMAL` nodes, enforces the
port-driven (`PORTS`) and inside port label (`PORT_LABELS`) minimum sizes (shrinking allowed
unless top-down layout, a fixed graph size or inside NORTH/SOUTH port labels), shifts the labels
after a resize, places the ports for the port constraints and recomputes the margin. Returns
whether the node size changed. -/
def placePortsOnNode (node : LNodeId) (graphPortSpacing : Float) (graphPortsSurrounding : ElkMargin)
    (graphTopdownLayout graphNodeSizeFixedGraphSize : Bool) : LayeredM Bool := do
  let nd ← getNode node
  let portLabelsPlacement := nd.props.getD CoreOptions.PORT_LABELS_PLACEMENT EnumSet.empty
  let hasInsideNorthSouthPortLabels := portLabelsPlacement.contains .inside && (← hasNorthSouthPortLabels node)
  let topdownLayout := nodePropertyOrGraphDefault nd CoreOptions.TOPDOWN_LAYOUT graphTopdownLayout
  let nodeSizeFixedGraphSize := nodePropertyOrGraphDefault nd CoreOptions.NODE_SIZE_FIXED_GRAPH_SIZE
    graphNodeSizeFixedGraphSize
  let nodeType := nd.type
  let mut nodeSize := nd.size
  let portConstraints := nd.props.getD LayeredOptions.PORT_CONSTRAINTS PortConstraints.undefined
  let insideSelfLoopsActive := nd.props.getD CoreOptions.INSIDE_SELF_LOOPS_ACTIVATE false
  let sizeConstraints := nd.props.getD LayeredOptions.NODE_SIZE_CONSTRAINTS EnumSet.empty
  let initialSize := nodeSize
  traceNodeLine node nodeSize sizeConstraints portConstraints
  if nodeType != .normal then return false
  -- Java's NodeDimensionCalculation places side-sorted PortContexts but keeps the node's port list
  -- order; the side-specific placement order is applied by `placePortsOnSide`.
  let allowShrink := !(topdownLayout || nodeSizeFixedGraphSize || hasInsideNorthSouthPortLabels)
  if sizeConstraints.contains .ports then
    nodeSize ← enforcePortDrivenMinimumSize node nodeSize graphPortSpacing graphPortsSurrounding
      (sizeConstraints.contains .portLabels) allowShrink
  if sizeConstraints.contains .portLabels then
    nodeSize ← enforceInsidePortLabelMinimumSize node nodeSize graphPortSpacing graphPortsSurrounding allowShrink
  applyInsideNorthSouthLabelPostResizeAdjustments node initialSize nodeSize hasInsideNorthSouthPortLabels
  placePortsForConstraints node nodeSize portConstraints insideSelfLoopsActive graphPortSpacing graphPortsSurrounding
  let changed := sizeChanged nodeSize initialSize
  if changed && (insideSelfLoopsActive || !(portConstraints.isPosFixed || portConstraints.isRatioFixed)) then
    let suffix := if insideSelfLoopsActive then " [inside-self-loop path]" else ""
    traceNodeSize s!"label-node-size: node id={nd.id} resized by phase1 from ({Float.toRustDisplay initialSize.x}, {Float.toRustDisplay initialSize.y}) -> ({Float.toRustDisplay nodeSize.x}, {Float.toRustDisplay nodeSize.y}){suffix}"
  return changed

/-- Rust `reposition_ports_only_on_node(node, graph_port_spacing, graph_ports_surrounding)`: for
`NORMAL` nodes, the clockwise port reordering (unless disabled or skipped for border offset nodes
with SOUTH and WEST ports), then the port placement for the port constraints against the current
size (no resizing) and the margin. -/
def repositionPortsOnlyOnNode (flags : LabelAndNodeSizeFlags) (node : LNodeId) (graphPortSpacing : Float)
    (graphPortsSurrounding : ElkMargin) : LayeredM Unit := do
  let nd ← getNode node
  let nodeSize := nd.size
  let portConstraints := nd.props.getD LayeredOptions.PORT_CONSTRAINTS PortConstraints.undefined
  let insideSelfLoopsActive := nd.props.getD CoreOptions.INSIDE_SELF_LOOPS_ACTIVATE false
  if nd.type != .normal then return
  if !flags.disableClockwiseSideOrder && !(← shouldSkipClockwiseReorderForPhase2f node) then
    ensureClockwisePortOrder node portConstraints
  placePortsForConstraints node nodeSize portConstraints insideSelfLoopsActive graphPortSpacing graphPortsSurrounding

/-! ## Process -/

/-- The graph values read once by `process`. -/
structure GraphSettings where
  portSpacing : Float
  portsSurrounding : ElkMargin
  topdownLayout : Bool
  nodeSizeFixedGraphSize : Bool

/-- `place_ports_on_node` with the graph settings. -/
@[inline] def placePorts (s : GraphSettings) (node : LNodeId) : LayeredM Bool :=
  placePortsOnNode node s.portSpacing s.portsSurrounding s.topdownLayout s.nodeSizeFixedGraphSize

/-- Phase 2c/2e: `placePortsOnNode` for the nodes that need it again; returns the count. -/
def reapplyPortSizing (graph : LGraphId) (s : GraphSettings) : LayeredM Nat := do
  let mut count : Nat := 0
  for node in ← phase2Nodes graph do
    if ← shouldReapplyPhase2Sizing node then
      let _ ← placePorts s node
      count := count + 1
  return count

/-- The phase-2 workaround of Rust `process` (steps 2, 2a–2f; see the module doc). -/
def phase2 (flags : LabelAndNodeSizeFlags) (graph : LGraphId) (adapter : LAdapters) (s : GraphSettings) :
    LayeredM Unit := do
  traceNodeSize "label-node-size: step2 (port placement) begin"
  let mut phase2ResizedNodes : Nat := 0
  for node in ← phase2Nodes graph do
    if shouldApplyPhase1PortPlacement (← getNode node) then
      if ← placePorts s node then
        phase2ResizedNodes := phase2ResizedNodes + 1
  traceNodeSize s!"label-node-size: step2 (port placement) done, resized_nodes={phase2ResizedNodes}"
  let shouldRunPhase2a := phase2ResizedNodes > 0 && (← graphHasAnyPortLabels graph)
  if shouldRunPhase2a then
    traceNodeSize "label-node-size: phase2a (reflow labels after phase1 node resize) begin"
    NodeDimensionCalculation.calculateLabelAndNodeSizesWith adapter graph flags.useFullProcess
    traceNodeSize "label-node-size: phase2a (reflow labels after phase1 node resize) done"
  else if phase2ResizedNodes > 0 then
    traceNodeSize "label-node-size: phase2a skipped (no port labels)"
  if ← graphNeedsPhase2bInsidePortLabelRestack graph then
    traceNodeSize "label-node-size: phase2b (inside port label restack) begin"
    NodeDimensionCalculation.calculateLabelAndNodeSizesWith adapter graph flags.useFullProcess
    traceNodeSize "label-node-size: phase2b (inside port label restack) done"
  else
    traceNodeSize "label-node-size: phase2b skipped (no inside port labels)"
  -- Java parity guard: phase2b can shrink nodes again after port placement
  let phase2cReappliedNodes ← reapplyPortSizing graph s
  traceNodeSize s!"label-node-size: phase2c (self-loop port sizing reapply) nodes={phase2cReappliedNodes}"
  if phase2cReappliedNodes > 0 then
    traceNodeSize "label-node-size: phase2d (reflow labels after phase2c node resize) begin"
    NodeDimensionCalculation.calculateLabelAndNodeSizesWith adapter graph flags.useFullProcess
    traceNodeSize "label-node-size: phase2d (reflow labels after phase2c node resize) done"
  -- Final stabilisation pass: phase2d can re-shrink some port-driven sizes
  let phase2eReappliedNodes ← reapplyPortSizing graph s
  traceNodeSize s!"label-node-size: phase2e (final port sizing stabilization) nodes={phase2eReappliedNodes}"
  -- Final port reposition pass against the final node sizes, without further resizing
  let mut graphsWithNonZeroBorderOffset : Std.HashSet LGraphId := {}
  for node in ← phase2Nodes graph do
    if ← nodeHasNonZeroBorderOffset node then
      if let some g ← nodeGraph node then
        graphsWithNonZeroBorderOffset := graphsWithNonZeroBorderOffset.insert g
  let mut phase2fRepositionedNodes : Nat := 0
  for node in ← phase2Nodes graph do
    if ← shouldRepositionPortsAfterPhase2 node graphsWithNonZeroBorderOffset then
      repositionPortsOnlyOnNode flags node s.portSpacing s.portsSurrounding
      phase2fRepositionedNodes := phase2fRepositionedNodes + 1
  traceNodeSize s!"label-node-size: phase2f (final port reposition) nodes={phase2fRepositionedNodes}"

/-- Phase 3: with `EXTERNAL_PORTS`, the labels of the `EXTERNAL_PORT` dummies of every layer
(graph `PORT_LABELS_PLACEMENT`, `NEXT_TO_PORT_IF_POSSIBLE`, `PORT_LABELS_TREAT_AS_GROUP`). -/
def phase3 (graph : LGraphId) : LayeredM Unit := do
  let gr ← getGraph graph
  if !gr.internal.graphProperties.contains .externalPorts then return
  let portLabelPlacement := gr.props.getD CoreOptions.PORT_LABELS_PLACEMENT EnumSet.empty
  let placeNextToPort := portLabelPlacement.contains .nextToPortIfPossible
  let treatAsGroup := gr.props.getD CoreOptions.PORT_LABELS_TREAT_AS_GROUP true
  for layer in gr.layers do
    for dummy in (← getLayer layer).nodes do
      if (← getNode dummy).type == .externalPort then
        placeExternalPortDummyLabels dummy portLabelPlacement placeNextToPort treatAsGroup

/-- Rust `process(graph, monitor)` with explicit switches (see the module doc). -/
def processWith (flags : LabelAndNodeSizeFlags) (graph : LGraphId) (monitor : ProgressMonitor) : LayeredM Unit := do
  let _ ← monitor.begin "Node and Port Label Placement and Node Sizing" 1.0
  let gr ← getGraph graph
  let s : GraphSettings :=
    { portSpacing := gr.props.getD LayeredOptions.SPACING_PORT_PORT 10.0
      portsSurrounding := gr.props.getD LayeredOptions.SPACING_PORTS_SURROUNDING {}
      topdownLayout := gr.props.getD CoreOptions.TOPDOWN_LAYOUT false
      nodeSizeFixedGraphSize := gr.props.getD CoreOptions.NODE_SIZE_FIXED_GRAPH_SIZE false }
  -- Step 1: node sizes and labels via NodeDimensionCalculation (Java: the whole processor)
  traceNodeSize "label-node-size: step1 (node sizing) begin"
  let adapter ← LGraphAdapters.adapt graph true true fun n => n.type == .normal
  NodeDimensionCalculation.calculateLabelAndNodeSizesWith adapter graph flags.useFullProcess
  traceNodeSize "label-node-size: step1 (node sizing) done"
  -- Step 2: port placement workaround (not present in Java)
  if flags.enablePhase1PortPlacement then
    phase2 flags graph adapter s
  else
    traceNodeSize "label-node-size: step2 skipped (experiment)"
  -- Phase 3: labels of external port dummies
  traceNodeSize "label-node-size: phase3 begin"
  phase3 graph
  traceNodeSize "label-node-size: phase3 done"
  monitor.done

/-- `process(graph, monitor)` with the process-wide switches (`LabelAndNodeSizeFlags.global`). -/
def process (graph : LGraphId) (monitor : ProgressMonitor) : LayeredM Unit :=
  processWith LabelAndNodeSizeFlags.global graph monitor

/-- The `LabelAndNodeSizeProcessor` processor. -/
def processor : LayeredProcessor := { name := "LabelAndNodeSizeProcessor", process := process }

end LabelAndNodeSizeProcessor

builtin_initialize registerLabelAndNodeSizeProcessor : Unit ←
  IntermediateProcessorStrategy.register .labelAndNodeSizeProcessor LabelAndNodeSizeProcessor.processor

end Elk.Alg.Layered.Intermediate
