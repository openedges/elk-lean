import Elk.Alg.Layered.LayeredPhases
import Elk.Core.Util.Java
import Elk.Alg.Common.NodeSpacing.CellSystem.LabelCell
import Elk.Alg.Common.Overlaps.RectangleStripOverlapRemover
import Elk.Core.Util.FloatConst
open Elk.Core.Util.FloatConst
/-!
# `org.eclipse.elk.alg.layered.intermediate.EndLabelPreprocessor`

Port of elk-rs `intermediate/end_label_preprocessor.rs` (Java `EndLabelPreprocessor`): "Places
head and tail labels of edges and calculates node margins accordingly. The labels are placed
assuming the edges will be routed orthogonally. The label positions computed here are relative to
the node; the `EndLabelPostprocessor` offsets them once the node positions are known."

Slot: before phase 4 (requested by the orthogonal and polyline edge routers). Postcondition: every
node with end labels has `END_LABELS` (per port the label cell holding its end labels) and margins
that include the label cells.

Per node, the end labels of each port (`gatherLabels`: tail labels of outgoing and head labels of
incoming edges, also those of the port's north/south `PORT_DUMMY` ports created for it) are
collected in a label cell sized to its minimum size, placed next to the port depending on the port
side and the first label's `LABEL_SIDE`, and the cells of the "problematic" sides (NORTH/SOUTH for
horizontal layouts, EAST/WEST for vertical ones) are freed of overlaps with a
`RectangleStripOverlapRemover`. The node margin is grown to contain all cells.

Representation: an end label cell is a standalone `CellSystem.Cell LLabelId` whose `kind` is
`.label` (the type of `LNodeInternals.endLabels`, consumed by `EndLabelPostprocessor`). The Rust
`EndLabelMap` is a `HashMap`; the Lean map keeps the port order (the postprocessor's result does not
depend on the order). `LabelCell::add_label(LGraphAdapters::adapt_label(label))` reads the label
size through the adapter; the port reads `LLabel.size` directly (the same value).
The overlap remover works on copies of the cell rectangles (Rust: raw pointers into the cells); the
updated rectangles are written back into the cells in insertion order.

Follows Java (agent COV): the port index is written into `port.id` like Java (elk-rs did not; no
later processor reads a port id without assigning it first, so the value was never observable).
`gatherLabels`/`gatherLabelsFromPort` are public (Rust `pub(crate)`): `LabelSideSelector` uses them.
-/

namespace Elk.Alg.Layered.Intermediate

open Elk.Graph Elk.Core Elk.Core.Alg Elk.Core.Math Elk.Core.Options Elk.Core.Util Elk.Alg.Layered
  Elk.Alg.Layered.Graph Elk.Alg.Layered.Options LayeredM
open Elk.Alg.Common.NodeSpacing Elk.Alg.Common.Overlaps

namespace EndLabelPreprocessor

/-- Rust `EndLabelCell` (`Arc<Mutex<LabelCell<LLabelAdapter, LLabelRef>>>`): a label cell. -/
abbrev EndLabelCell := CellSystem.Cell LLabelId

/-! ## Label gathering -/

/-- Rust `NO_INCIDENT_EDGE_THICKNESS`. -/
def NO_INCIDENT_EDGE_THICKNESS : Float := -1.0

/-- Rust `gather_labels_from_port(port, target_list)`: appends the end labels of the port's
connected edges (incoming then outgoing; tail labels of outgoing, head labels of incoming edges,
placement default `CENTER`) to `targetList` and returns the maximum incident edge thickness
(`NO_INCIDENT_EDGE_THICKNESS` without edges). `END_LABEL_EDGE` is set on gathered labels that have
none yet. -/
def gatherLabelsFromPort (port : LPortId) (targetList : Array LLabelId) : LayeredM (Float × Array LLabelId) := do
  let mut maxEdgeThickness := NO_INCIDENT_EDGE_THICKNESS
  let mut target := targetList
  let edges := (← getPort port).connectedEdges
  for edge in edges do
    let ed ← getEdge edge
    let edgeThickness := ed.props.getD CoreOptions.EDGE_THICKNESS fl0p0
    let isSource := ed.source == some port
    maxEdgeThickness := fmax maxEdgeThickness edgeThickness
    for label in ed.labels do
      let placement := (← getLabel label).props.getD LayeredOptions.EDGE_LABELS_PLACEMENT EdgeLabelPlacement.center
      let isEndLabel := if isSource then placement == .tail else placement == .head
      if isEndLabel then
        modifyLabel label fun l =>
          if l.internal.endLabelEdge.isNone then { l with internal := { l.internal with endLabelEdge := some edge } }
          else l
        target := target.push label
  return (maxEdgeThickness, target)

/-- Rust `gather_labels(port)` (Java `gatherLabels(LPort)`): the end labels of the port and of the
ports of its `PORT_DUMMY` whose `ORIGIN` is the port; `none` if no edge is incident (the port then
contributes nothing), otherwise the (possibly empty) list. Sets `MAX_EDGE_THICKNESS` when labels
were found. -/
def gatherLabels (port : LPortId) : LayeredM (Option (Array LLabelId)) := do
  let (thickness0, labels0) ← gatherLabelsFromPort port #[]
  let mut maxEdgeThickness := thickness0
  let mut labels := labels0
  if let some dummyNode := (← getPort port).internal.portDummy then
    let dummyPorts := (← getNode dummyNode).ports
    for dummyPort in dummyPorts do
      if (← getPort dummyPort).internal.origin == some (.lPort port) then
        let (t, ls) ← gatherLabelsFromPort dummyPort labels
        labels := ls
        maxEdgeThickness := fmax maxEdgeThickness t
  if !labels.isEmpty then
    let m := maxEdgeThickness
    modifyPort port fun p => { p with internal := { p.internal with maxEdgeThickness := m } }
  if maxEdgeThickness != NO_INCIDENT_EDGE_THICKNESS then return some labels
  return none

/-! ## Label cells -/

/-- Rust `create_configured_label_cell(labels, label_label_spacing, vertical_layout)`: `none` for no
or an empty label list; otherwise a label cell (`new_with_layout_mode(spacing, !vertical)`) with the
labels, its rectangle sized to the cell's minimum width and height. -/
def createConfiguredLabelCell (labels : Option (Array LLabelId)) (labelLabelSpacing : Float)
    (verticalLayout : Bool) : LayeredM (Option EndLabelCell) := do
  let some labels := labels | return none
  if labels.isEmpty then return none
  let mut d : CellSystem.LabelCellData LLabelId :=
    { gap := labelLabelSpacing, horizontalLayoutMode := !verticalLayout }
  for label in labels do
    d := CellSystem.LabelCell.addLabel d label (← getLabel label).size
  let padding : ElkPadding := {}
  let minHeight := CellSystem.LabelCell.minimumHeight d padding
  let minWidth := CellSystem.LabelCell.minimumWidth d padding
  return some { padding := padding, cellRectangle := { height := minHeight, width := minWidth }, kind := .label d }

/-- Rust `get_label_side(label_cell)`: the internal `LABEL_SIDE` of the cell's first label
(`UNKNOWN` without labels). -/
def getLabelSide (cell : EndLabelCell) : LayeredM LabelSide := do
  match cell.kind with
  | .label d =>
    match d.labels[0]? with
    | some (l, _) => return (← getLabel l).internal.labelSide
    | none => return .unknown
  | _ => return .unknown

/-- `labelCell.setHorizontalAlignment(h)` + `setVerticalAlignment(v)` on a standalone label cell. -/
def withAlignments (cell : EndLabelCell) (h : CellSystem.HorizontalLabelAlignment)
    (v : CellSystem.VerticalLabelAlignment) : EndLabelCell :=
  match cell.kind with
  | .label d => { cell with kind := .label { d with horizontalAlignment := h, verticalAlignment := v } }
  | _ => cell

/-! ## Label placement -/

/-- Rust `place_labels_for_port(port, label_cell, edge_label_spacing)`: positions the cell next to
the port (relative to the node) by port side and the first label's side, and sets the cell's
alignments. Ports without node keep the cell unchanged. -/
def placeLabelsForPort (port : LPortId) (cell : EndLabelCell) (edgeLabelSpacing : Float) :
    LayeredM EndLabelCell := do
  let pt ← getPort port
  let some owner := pt.owner | return cell
  let nd ← getNode owner
  let nodeSize := nd.size
  let nodeMargin := nd.margin
  let portPos := pt.position
  let maxEdgeThickness := pt.internal.maxEdgeThickness
  let portAnchor : KVector := ⟨portPos.x + pt.anchor.x, portPos.y + pt.anchor.y⟩
  let labelSide ← getLabelSide cell
  let rect := cell.cellRectangle
  let rectWidth := rect.width
  let rectHeight := rect.height
  match pt.side with
  | .north =>
    if labelSide == .above then
      return { withAlignments cell .right .bottom with cellRectangle := { rect with
        y := -nodeMargin.top - edgeLabelSpacing - rectHeight
        x := portAnchor.x - maxEdgeThickness - edgeLabelSpacing - rectWidth } }
    else
      return { withAlignments cell .left .bottom with cellRectangle := { rect with
        y := -nodeMargin.top - edgeLabelSpacing - rectHeight
        x := portAnchor.x + maxEdgeThickness + edgeLabelSpacing } }
  | .east =>
    if labelSide == .above then
      return { withAlignments cell .left .bottom with cellRectangle := { rect with
        x := nodeSize.x + nodeMargin.right + edgeLabelSpacing
        y := portAnchor.y - maxEdgeThickness - edgeLabelSpacing - rectHeight } }
    else
      return { withAlignments cell .left .top with cellRectangle := { rect with
        x := nodeSize.x + nodeMargin.right + edgeLabelSpacing
        y := portAnchor.y + maxEdgeThickness + edgeLabelSpacing } }
  | .south =>
    if labelSide == .above then
      return { withAlignments cell .right .top with cellRectangle := { rect with
        y := nodeSize.y + nodeMargin.bottom + edgeLabelSpacing
        x := portAnchor.x - maxEdgeThickness - edgeLabelSpacing - rectWidth } }
    else
      return { withAlignments cell .left .top with cellRectangle := { rect with
        y := nodeSize.y + nodeMargin.bottom + edgeLabelSpacing
        x := portAnchor.x + maxEdgeThickness + edgeLabelSpacing } }
  | .west =>
    if labelSide == .above then
      return { withAlignments cell .right .bottom with cellRectangle := { rect with
        x := -nodeMargin.left - edgeLabelSpacing - rectWidth
        y := portAnchor.y - maxEdgeThickness - edgeLabelSpacing - rectHeight } }
    else
      return { withAlignments cell .right .top with cellRectangle := { rect with
        x := -nodeMargin.left - edgeLabelSpacing - rectWidth
        y := portAnchor.y + maxEdgeThickness + edgeLabelSpacing } }
  | .undefined => return cell

/-- Rust `port_side_to_overlap_removal_direction(port_side)` (`DOWN` for UNDEFINED). -/
def portSideToOverlapRemovalDirection : PortSide → OverlapRemovalDirection
  | .north => .up
  | .south => .down
  | .east => .right
  | .west => .left
  | .undefined => .down

/-- Rust `calculate_overlap_start_coordinate(node, port_side, edge_label_spacing)`: the node border
(including its margin) plus the edge label spacing on the given side (`0` for UNDEFINED). -/
def calculateOverlapStartCoordinate (node : LNodeId) (portSide : PortSide) (edgeLabelSpacing : Float) :
    LayeredM Float := do
  let nd ← getNode node
  let nodeSize := nd.size
  let nodeMargin := nd.margin
  return match portSide with
    | .north => -nodeMargin.top - edgeLabelSpacing
    | .south => nodeSize.y + nodeMargin.bottom + edgeLabelSpacing
    | .east => nodeSize.x + nodeMargin.right + edgeLabelSpacing
    | .west => -nodeMargin.left - edgeLabelSpacing
    | .undefined => 0.0

/-- Rust `remove_label_overlaps(node, ports, port_label_cells, port_side, spacing, edge_spacing)`:
the cells of the ports on `portSide` (port order) go through a `RectangleStripOverlapRemover`
(direction by side, gap `labelLabelSpacing` both ways, start coordinate at the node border); the
moved rectangles are written back into the cells. -/
def removeLabelOverlaps (node : LNodeId) (ports : Array LPortId) (cells : Array (Option EndLabelCell))
    (portSide : PortSide) (labelLabelSpacing edgeLabelSpacing : Float) : LayeredM (Array (Option EndLabelCell)) := do
  let mut overlapRemover := RectangleStripOverlapRemover.createForDirection (portSideToOverlapRemovalDirection portSide)
    |>.withGap labelLabelSpacing labelLabelSpacing
    |>.withStartCoordinate (← calculateOverlapStartCoordinate node portSide edgeLabelSpacing)
  let mut indices : Array Nat := #[]
  for i in [0:ports.size] do
    let some port := ports[i]? | continue
    if (← getPort port).side != portSide then continue
    let some cell := (cells[i]?).bind id | continue
    overlapRemover := overlapRemover.addRectangle cell.cellRectangle
    indices := indices.push i
  let (rects, _) := overlapRemover.removeOverlaps
  let mut cells := cells
  for (i, r) in indices.zip rects do
    cells := cells.modify i fun c => c.map fun c => { c with cellRectangle := r }
  return cells

/-- Rust `place_labels(node, ports, port_label_cells, label_label_spacing, edge_label_spacing,
vertical_layout)`: places every cell next to its port, then removes overlaps on EAST and WEST
(vertical layouts) or NORTH and SOUTH (horizontal layouts) with twice the label-label spacing. -/
def placeLabels (node : LNodeId) (ports : Array LPortId) (cells : Array (Option EndLabelCell))
    (labelLabelSpacing edgeLabelSpacing : Float) (verticalLayout : Bool) : LayeredM (Array (Option EndLabelCell)) := do
  let mut cells := cells
  for i in [0:ports.size] do
    let some port := ports[i]? | continue
    if let some cell := (cells[i]?).bind id then
      let placed ← placeLabelsForPort port cell edgeLabelSpacing
      cells := cells.set! i (some placed)
  let overlapSpacing := 2.0 * labelLabelSpacing
  if verticalLayout then
    cells ← removeLabelOverlaps node ports cells .east overlapSpacing edgeLabelSpacing
    cells ← removeLabelOverlaps node ports cells .west overlapSpacing edgeLabelSpacing
  else
    cells ← removeLabelOverlaps node ports cells .north overlapSpacing edgeLabelSpacing
    cells ← removeLabelOverlaps node ports cells .south overlapSpacing edgeLabelSpacing
  return cells

/-! ## Node margins -/

/-- Rust `update_node_margins(node, label_cells)`: the union of the node's current margin rectangle
(relative to the node) with every cell rectangle becomes the new margin. -/
def updateNodeMargins (node : LNodeId) (cells : Array (Option EndLabelCell)) : LayeredM Unit := do
  let nd ← getNode node
  let nodeSize := nd.size
  let nodeMargin := nd.margin
  let mut rect := ElkRectangle.ofValues (-nodeMargin.left) (-nodeMargin.top)
    (nodeMargin.left + nodeSize.x + nodeMargin.right) (nodeMargin.top + nodeSize.y + nodeMargin.bottom)
  for c in cells do
    if let some cell := c then
      rect := rect.union cell.cellRectangle
  let left := -rect.x
  let top := -rect.y
  let right := rect.width - left - nodeSize.x
  let bottom := rect.height - top - nodeSize.y
  modifyNode node fun x => { x with margin := { x.margin with left := left, top := top, right := right, bottom := bottom } }

/-! ## Processor -/

/-- Rust `process_node(node, edge_label_spacing, label_label_spacing, vertical_layout)`: one label
cell per port with end labels, placed and freed of overlaps; if any, `END_LABELS` is set (port
order) and the node margins are updated. -/
def processNode (node : LNodeId) (edgeLabelSpacing labelLabelSpacing : Float) (verticalLayout : Bool) :
    LayeredM Unit := do
  let ports := (← getNode node).ports
  if ports.isEmpty then return
  let mut cells : Array (Option EndLabelCell) := Array.mkEmpty ports.size
  for h : portIndex in [0:ports.size] do
    let port := ports[portIndex]
    -- Java `port.id = portIndex`
    modifyPort port fun p => { p with id := (portIndex : Int) }
    let labels ← gatherLabels port
    cells := cells.push (← createConfiguredLabelCell labels labelLabelSpacing verticalLayout)
  cells ← placeLabels node ports cells labelLabelSpacing edgeLabelSpacing verticalLayout
  let mut portToLabelCell : Array (LPortId × EndLabelCell) := #[]
  for (port, c) in ports.zip cells do
    if let some cell := c then
      portToLabelCell := portToLabelCell.push (port, cell)
  if !portToLabelCell.isEmpty then
    let m := portToLabelCell
    modifyNode node fun x => { x with internal := { x.internal with endLabels := some m } }
    updateNodeMargins node cells

/-- `process(layeredGraph, monitor)`: every node of every layer (no type filter). Spacings and
direction are read once from the graph (`SPACING_EDGE_LABEL`, `SPACING_LABEL_LABEL`, `DIRECTION`). -/
def process (graph : LGraphId) (monitor : ProgressMonitor) : LayeredM Unit := do
  let _ ← monitor.begin "End label pre-processing" 1.0
  let gr ← getGraph graph
  let edgeLabelSpacing := gr.props.getD LayeredOptions.SPACING_EDGE_LABEL 2.0
  let labelLabelSpacing := gr.props.getD LayeredOptions.SPACING_LABEL_LABEL 1.0
  let layoutDirection := gr.props.getD LayeredOptions.DIRECTION Direction.right
  let verticalLayout := layoutDirection.isVertical
  for layer in gr.layers do
    let nodes := (← getLayer layer).nodes
    for node in nodes do
      processNode node edgeLabelSpacing labelLabelSpacing verticalLayout
  monitor.done

/-- The `EndLabelPreprocessor` processor. -/
def processor : LayeredProcessor := { name := "EndLabelPreprocessor", process := process }

end EndLabelPreprocessor

builtin_initialize registerEndLabelPreprocessor : Unit ←
  IntermediateProcessorStrategy.register .endLabelPreprocessor EndLabelPreprocessor.processor

end Elk.Alg.Layered.Intermediate
