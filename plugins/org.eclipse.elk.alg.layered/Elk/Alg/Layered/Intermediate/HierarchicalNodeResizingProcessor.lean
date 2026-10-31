import Elk.Alg.Layered.LayeredPhases
import Elk.Alg.Layered.Graph.LGraphUtil
import Elk.Core.Util.ElkUtil
/-!
# `org.eclipse.elk.alg.layered.intermediate.HierarchicalNodeResizingProcessor`

Port of elk-rs `intermediate/hierarchical_node_resizing_processor.rs`. Run as the last
non-hierarchical processor of a (nested) graph: moves all nodes back to `layerlessNodes`, removes
the layers, resizes the graph (minimum size, `CONTENT_ALIGNMENT`, eastern/southern external port
dummies moved with the growth) and, for a nested graph, transfers the layout to the parent node:
every external port dummy whose `ORIGIN` is an `LPort` of the parent node gets the port's position
on the parent border and its side, and the parent node is resized to the graph's actual size. Like
Java, the position is used as computed: elk-rs subtracted the dummy's y coordinate for eastern "pure
self loop" dummies (only self loops or, as the only eastern dummy without edges, none), which moved
e.g. the outside port of a compound node next to a hierarchical one (removed by GS).

The `ORIGIN` read here is an `LPort` of the parent graph (same arena), so no `ElkGraph` access is
needed.

Differences to Java (Rust is followed):
* the external port position is computed by a local copy of `getExternalPortPosition` (Rust
  `get_external_port_position_for_graph`) that groups the additions as `x += (a + b - c)` and has no
  connected-components compaction quirk (unlike `LGraphUtil.getExternalPortPosition`);
* the elk-rs `ELK_TRACE*` diagnostics written to stderr (`[hierarchical-resize]`, `[ext-port]`,
  `[hnr]`, `TRACE resize_graph`) are not ported.

Slot: after phase 5.
-/
/-! Float literals as global constants (FL): inside branches, loops and specialised code the compiler
shares a literal's `Nat`/`Bool` arguments with unrelated variables (CSE) and then parses it on every
evaluation (`FastFloat.ofScientificImpl`); a top-level constant is a load (PLAN §7.1 items 17, 22). -/
private def fl0p0 : Float := 0.0
private def fl2p0 : Float := 2.0

namespace Elk.Alg.Layered.Intermediate

open Elk.Graph Elk.Core Elk.Core.Alg Elk.Core.Math Elk.Core.Options Elk.Core.Util Elk.Alg.Layered
  Elk.Alg.Layered.Graph Elk.Alg.Layered.Options LayeredM

namespace HierarchicalNodeResizingProcessor

/-- Rust `get_external_port_position_for_graph` (`LGraphUtil.getExternalPortPosition`): the external
port's position in the parent's coordinates; also moves the dummy onto the graph border. -/
def getExternalPortPositionForGraph (graph : LGraphId) (portDummy : LNodeId) (portWidth portHeight : Float) :
    LayeredM KVector := do
  let nd ← getNode portDummy
  let pos := nd.position
  let size := nd.size
  let mut portPos : KVector := ⟨pos.x + size.x / 2.0, pos.y + size.y / 2.0⟩
  let portOffset := (nd.props.get CoreOptions.PORT_BORDER_OFFSET).getD 0.0
  let extSide := nd.internal.extPortSide
  let gr ← getGraph graph
  let graphSize := gr.size
  let padding := gr.padding
  let graphOffset := gr.offset
  match extSide with
  | .north =>
    portPos := { portPos with x := portPos.x + (padding.left + graphOffset.x - portWidth / 2.0) }
    portPos := { portPos with y := -portHeight - portOffset }
    let y := -(padding.top + portOffset + graphOffset.y)
    modifyNode portDummy fun x => { x with position := { x.position with y := y } }
  | .east =>
    portPos := { portPos with x := graphSize.x + padding.left + padding.right + portOffset }
    portPos := { portPos with y := portPos.y + (padding.top + graphOffset.y - portHeight / 2.0) }
    let x := graphSize.x + padding.right + portOffset - graphOffset.x
    modifyNode portDummy fun n => { n with position := { n.position with x := x } }
  | .south =>
    portPos := { portPos with x := portPos.x + (padding.left + graphOffset.x - portWidth / 2.0) }
    portPos := { portPos with y := graphSize.y + padding.top + padding.bottom + portOffset }
    let y := graphSize.y + padding.bottom + portOffset - graphOffset.y
    modifyNode portDummy fun x => { x with position := { x.position with y := y } }
  | .west =>
    portPos := { portPos with x := -portWidth - portOffset }
    portPos := { portPos with y := portPos.y + (padding.top + graphOffset.y - portHeight / 2.0) }
    let x := -(padding.left + portOffset + graphOffset.x)
    modifyNode portDummy fun n => { n with position := { n.position with x := x } }
  | .undefined => pure ()
  return portPos

/-- `graphLayoutToNode(node, lgraph)` (Rust `graph_layout_to_node`): transfers the external port
positions to the parent node's ports and resizes the parent node. -/
def graphLayoutToNode (node : LNodeId) (lgraph : LGraphId) : LayeredM Unit := do
  for child in (← getGraph lgraph).layerlessNodes do
    let childNode ← getNode child
    let some (.lPort portRef) := childNode.internal.origin | continue
    let portSize := (← getPort portRef).size
    let portPosition ← getExternalPortPositionForGraph lgraph child portSize.x portSize.y
    modifyPort portRef fun p => LPort.setSide { p with position := portPosition } childNode.internal.extPortSide
  let actualGraphSize := (← getGraph lgraph).actualSize
  let hasExternalPorts := (← getGraph lgraph).internal.graphProperties.contains .externalPorts
  if hasExternalPorts then
    setNodeProp node CoreOptions.PORT_CONSTRAINTS PortConstraints.fixedPos
    if let some parentGraph ← nodeGraph node then
      modifyGraph parentGraph fun g => { g with internal := { g.internal with
        graphProperties := g.internal.graphProperties.insert .nonFreePorts } }
    LGraphUtil.resizeNode node actualGraphSize false true
  else
    LGraphUtil.resizeNode node actualGraphSize true true

/-- `resizeGraphNoReallyIMeanIt(lgraph, oldSize, newSize)` (Rust
`resize_graph_no_really_i_mean_it`): content alignment offsets, eastern/southern external port
dummies moved by the growth, then the new size minus padding. -/
def resizeGraphNoReallyIMeanIt (lgraph : LGraphId) (oldSize newSize : KVector) : LayeredM Unit := do
  let gr ← getGraph lgraph
  let contentAlignment := (gr.props.get CoreOptions.CONTENT_ALIGNMENT).getD EnumSet.noneOf
  let hasExternalPorts := gr.internal.graphProperties.contains .externalPorts
  if newSize.x > oldSize.x then
    if contentAlignment.contains .hCenter then
      modifyGraph lgraph fun g => { g with offset := { g.offset with x := g.offset.x + (newSize.x - oldSize.x) / fl2p0 } }
    else if contentAlignment.contains .hRight then
      modifyGraph lgraph fun g => { g with offset := { g.offset with x := g.offset.x + (newSize.x - oldSize.x) } }
  if newSize.y > oldSize.y then
    if contentAlignment.contains .vCenter then
      modifyGraph lgraph fun g => { g with offset := { g.offset with y := g.offset.y + (newSize.y - oldSize.y) / fl2p0 } }
    else if contentAlignment.contains .vBottom then
      modifyGraph lgraph fun g => { g with offset := { g.offset with y := g.offset.y + (newSize.y - oldSize.y) } }
  if hasExternalPorts && (newSize.x > oldSize.x || newSize.y > oldSize.y) then
    for node in (← getGraph lgraph).layerlessNodes do
      modifyNode node fun nd =>
        if nd.type == .externalPort then
          match nd.internal.extPortSide with
          | .east => { nd with position := { nd.position with x := nd.position.x + (newSize.x - oldSize.x) } }
          | .south => { nd with position := { nd.position with y := nd.position.y + (newSize.y - oldSize.y) } }
          | _ => nd
        else nd
  modifyGraph lgraph fun g => { g with size := ⟨newSize.x - g.padding.left - g.padding.right,
    newSize.y - g.padding.top - g.padding.bottom⟩ }

/-- `resizeGraph(lgraph)` (Rust `resize_graph`): applies the minimum size (with the default minimum
size option) to the graph's actual size. -/
def resizeGraph (lgraph : LGraphId) : LayeredM Unit := do
  let gr ← getGraph lgraph
  let sizeConstraint := (gr.props.get CoreOptions.NODE_SIZE_CONSTRAINTS).getD EnumSet.noneOf
  let sizeOptions := (gr.props.get CoreOptions.NODE_SIZE_OPTIONS).getD EnumSet.noneOf
  let calculatedSize := gr.actualSize
  let mut adjustedSize := calculatedSize
  if sizeConstraint.contains .minimumSize then
    let mut minSize := (gr.props.get CoreOptions.NODE_SIZE_MINIMUM).getD {}
    if sizeOptions.contains .defaultMinimumSize then
      if minSize.x <= fl0p0 then minSize := { minSize with x := ElkUtil.DEFAULT_MIN_WIDTH }
      if minSize.y <= fl0p0 then minSize := { minSize with y := ElkUtil.DEFAULT_MIN_HEIGHT }
    adjustedSize := ⟨fmax adjustedSize.x minSize.x, fmax adjustedSize.y minSize.y⟩
  resizeGraphNoReallyIMeanIt lgraph calculatedSize adjustedSize

/-- `process(graph, monitor)` body. -/
def run (graph : LGraphId) : LayeredM Unit := do
  -- move all nodes from all layers to the layerless nodes (layer by layer, in layer order)
  for layer in (← getGraph graph).layers do
    let layerNodes := (← getLayer layer).nodes
    modifyGraph graph fun g => { g with layerlessNodes := g.layerlessNodes ++ layerNodes }
    modifyLayer layer fun l => { l with nodes := #[] }
  for node in (← getGraph graph).layerlessNodes do
    setNodeLayer node none
  modifyGraph graph fun g => { g with layers := #[] }
  resizeGraph graph
  if let some parentNode := (← getGraph graph).parentNode then
    graphLayoutToNode parentNode graph

/-- The `HierarchicalNodeResizingProcessor`. -/
def processor : LayeredProcessor :=
  { name := "HierarchicalNodeResizingProcessor"
    process := fun graph monitor => do
      let _ ← monitor.begin "Resize child graph to fit parent." 1.0
      run graph
      monitor.done }

end HierarchicalNodeResizingProcessor

builtin_initialize registerHierarchicalNodeResizingProcessor : Unit ←
  IntermediateProcessorStrategy.register .hierarchicalNodeResizer HierarchicalNodeResizingProcessor.processor

end Elk.Alg.Layered.Intermediate
