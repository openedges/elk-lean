import Std.Data.HashSet
import Elk.Alg.Layered.LayeredPhases
import Elk.Alg.Layered.Options.LayeredOptions
/-!
# `org.eclipse.elk.alg.layered.intermediate.GraphTransformer`

Port of elk-rs `intermediate/graph_transformer.rs` (Java `GraphTransformer.java`). Transforms the
coordinates of a layered graph between the input layout direction and the internally used
left-to-right direction by mirroring (`mirrorAllX`/`mirrorAllY`) and transposing (`transposeAll`)
graph offset/size/padding, nodes (position, size, padding, `POSITION`, `ALIGNMENT`,
`NODE_SIZE_MINIMUM`, `NODE_LABELS_PLACEMENT`), ports (position, size, anchor, side,
`PORT_INDEX`), the outgoing edges of each port (bend points, `JUNCTION_POINTS`, labels), node and
port labels, and external port dummies (`EXT_PORT_SIDE`, layer constraints).

The processor is registered twice, with the elk-rs mode assignment (swapped relative to Java):
`DIRECTION_PREPROCESSOR` uses `Mode.toInputDirection` and `DIRECTION_POSTPROCESSOR`
`Mode.toInternalLtr`. Its trace name is the Rust `type_name` `GraphTransformer` for both.

Like Rust (and Java) only the nodes of the processed graph are transformed: nested graphs are
processed by their own layered run, so `LNode.nestedGraph` is not followed here.

Differences to Java, following Rust:
* the node list (layerless nodes, then the nodes of each layer) is de-duplicated, keeping the
  first occurrence (Rust `process`, `HashSet` of node pointers);
* junction points are only mirrored/transposed when the edge *stores* `JUNCTION_POINTS`
  (Rust `has_property` check; Java's `getProperty` would materialise the empty default);
* the progress monitor task name uses the Rust `Debug` form of the mode
  (`Graph transformation (ToInternalLtr)`), Java prints `TO_INTERNAL_LTR`.
-/
namespace Elk.Alg.Layered.Intermediate

open Elk.Graph Elk.Core Elk.Core.Alg Elk.Core.Math Elk.Core.Options Elk.Core.Util Elk.Alg.Layered
  Elk.Alg.Layered.Graph Elk.Alg.Layered.Options LayeredM

namespace GraphTransformer

/-- `GraphTransformer.Mode`. -/
inductive Mode where
  /-- `TO_INTERNAL_LTR`: the input graph's direction to the internal direction (left-to-right). -/
  | toInternalLtr
  /-- `TO_INPUT_DIRECTION`: the internal direction back to the input graph's direction. -/
  | toInputDirection
  deriving BEq, Repr, Inhabited, DecidableEq

/-- Rust `format!("{:?}", mode)` (`ToInternalLtr` / `ToInputDirection`). -/
def Mode.debugName : Mode → String
  | .toInternalLtr => "ToInternalLtr"
  | .toInputDirection => "ToInputDirection"

/-! ## Pure helpers (Rust free functions) -/

/-- `mirror_vector_x`: `x := offset - x`. -/
@[inline] def mirrorVectorX (v : KVector) (offset : Float) : KVector := { v with x := offset - v.x }

/-- `mirror_vector_y`: `y := offset - y`. -/
@[inline] def mirrorVectorY (v : KVector) (offset : Float) : KVector := { v with y := offset - v.y }

/-- `transpose_vector`: swaps `x` and `y`. -/
@[inline] def transposeVector (v : KVector) : KVector := ⟨v.y, v.x⟩

/-- `mirror_padding_x` / `mirror_elk_padding_x`: swaps left and right. -/
@[inline] def mirrorPaddingX (p : ElkPadding) : ElkPadding := { p with left := p.right, right := p.left }

/-- `mirror_padding_y` / `mirror_elk_padding_y`: swaps top and bottom. -/
@[inline] def mirrorPaddingY (p : ElkPadding) : ElkPadding := { p with top := p.bottom, bottom := p.top }

/-- `transpose_padding` / `transpose_elk_padding`: top ↔ left, bottom ↔ right. -/
@[inline] def transposePadding (p : ElkPadding) : ElkPadding :=
  { top := p.left, bottom := p.right, left := p.top, right := p.bottom }

/-- `get_mirrored_port_side_x`: east ↔ west. -/
def mirroredPortSideX : PortSide → PortSide
  | .east => .west
  | .west => .east
  | s => s

/-- `get_mirrored_port_side_y`: north ↔ south. -/
def mirroredPortSideY : PortSide → PortSide
  | .north => .south
  | .south => .north
  | s => s

/-- `transpose_port_side`: north ↔ west, south ↔ east, `UNDEFINED` otherwise. -/
def transposePortSide : PortSide → PortSide
  | .north => .west
  | .west => .north
  | .south => .east
  | .east => .south
  | .undefined => .undefined

/-- `reverse_index`: negates a stored `PORT_INDEX`. -/
def reverseIndex (props : PropertyMap) : PropertyMap :=
  match props.get LayeredOptions.PORT_INDEX with
  | some index => props.set LayeredOptions.PORT_INDEX (-index)
  | none => props

/-- `mirror_node_label_placement_x`: swaps `H_LEFT`/`H_RIGHT` of a stored `NODE_LABELS_PLACEMENT`
(re-stores the set even when unchanged, like Rust). -/
def mirrorNodeLabelPlacementX (props : PropertyMap) : PropertyMap :=
  if !props.has LayeredOptions.NODE_LABELS_PLACEMENT then props
  else
    let placement := props.getD LayeredOptions.NODE_LABELS_PLACEMENT EnumSet.empty
    let placement :=
      if placement.contains .hLeft then (placement.erase .hLeft).insert .hRight
      else if placement.contains .hRight then (placement.erase .hRight).insert .hLeft
      else placement
    props.set LayeredOptions.NODE_LABELS_PLACEMENT placement

/-- `mirror_node_label_placement_y`: swaps `V_TOP`/`V_BOTTOM` of a stored `NODE_LABELS_PLACEMENT`. -/
def mirrorNodeLabelPlacementY (props : PropertyMap) : PropertyMap :=
  if !props.has LayeredOptions.NODE_LABELS_PLACEMENT then props
  else
    let placement := props.getD LayeredOptions.NODE_LABELS_PLACEMENT EnumSet.empty
    let placement :=
      if placement.contains .vTop then (placement.erase .vTop).insert .vBottom
      else if placement.contains .vBottom then (placement.erase .vBottom).insert .vTop
      else placement
    props.set LayeredOptions.NODE_LABELS_PLACEMENT placement

/-- `transpose_node_label_placement`: rebuilds a stored, non-empty `NODE_LABELS_PLACEMENT` with
horizontal and vertical alignments swapped (`INSIDE`/`OUTSIDE` kept, `H_PRIORITY` toggled). -/
def transposeNodeLabelPlacement (props : PropertyMap) : PropertyMap := Id.run do
  if !props.has LayeredOptions.NODE_LABELS_PLACEMENT then return props
  let placement := props.getD LayeredOptions.NODE_LABELS_PLACEMENT EnumSet.empty
  if placement.isEmpty then return props
  let mut np : EnumSet NodeLabelPlacement := EnumSet.noneOf
  if placement.contains .inside then np := np.insert .inside
  else np := np.insert .outside
  if !placement.contains .hPriority then np := np.insert .hPriority
  if placement.contains .hLeft then np := np.insert .vTop
  else if placement.contains .hCenter then np := np.insert .vCenter
  else if placement.contains .hRight then np := np.insert .vBottom
  if placement.contains .vTop then np := np.insert .hLeft
  else if placement.contains .vCenter then np := np.insert .hCenter
  else if placement.contains .vBottom then np := np.insert .hRight
  return props.set LayeredOptions.NODE_LABELS_PLACEMENT np

/-- The `ALIGNMENT` of a node (Rust `get_property(ALIGNMENT).unwrap_or(Center)`). -/
@[inline] private def alignmentOf (props : PropertyMap) : Alignment :=
  props.getD LayeredOptions.ALIGNMENT .center

/-- Stores `newAlignment` only when it differs from `old` (Rust `if new_alignment != alignment`). -/
@[inline] private def setAlignmentIfChanged (props : PropertyMap) (old newAlignment : Alignment) : PropertyMap :=
  if newAlignment != old then props.set LayeredOptions.ALIGNMENT newAlignment else props

/-- `transpose_properties`: `NODE_SIZE_MINIMUM` (always stored, transposed), `ALIGNMENT`
(left ↔ top, right ↔ bottom) and a stored `POSITION`. -/
def transposeProperties (props : PropertyMap) : PropertyMap := Id.run do
  let minSize := props.getD LayeredOptions.NODE_SIZE_MINIMUM {}
  let mut props := props.set LayeredOptions.NODE_SIZE_MINIMUM ⟨minSize.y, minSize.x⟩
  let alignment := alignmentOf props
  let newAlignment : Alignment := match alignment with
    | .left => .top
    | .right => .bottom
    | .top => .left
    | .bottom => .right
    | a => a
  props := setAlignmentIfChanged props alignment newAlignment
  if props.has LayeredOptions.POSITION then
    if let some pos := props.get LayeredOptions.POSITION then
      props := props.set LayeredOptions.POSITION (transposeVector pos)
  return props

/-- The x part of `mirror_node_x` applied to the node itself (position, label placement, padding,
`POSITION`, `ALIGNMENT` left ↔ right). -/
def mirrorNodeShapeX (offset : Float) (nd : LNode) : LNode := Id.run do
  let size := nd.size
  let mut props := mirrorNodeLabelPlacementX nd.props
  if props.has LayeredOptions.POSITION then
    if let some pos := props.get LayeredOptions.POSITION then
      props := props.set LayeredOptions.POSITION (mirrorVectorX pos (offset - size.x))
  let alignment := alignmentOf props
  let newAlignment : Alignment := match alignment with
    | .left => .right
    | .right => .left
    | a => a
  props := setAlignmentIfChanged props alignment newAlignment
  return { nd with position := mirrorVectorX nd.position (offset - size.x),
                   padding := mirrorPaddingX nd.padding, props := props }

/-- The y part of `mirror_node_y` applied to the node itself (`ALIGNMENT` top ↔ bottom). -/
def mirrorNodeShapeY (offset : Float) (nd : LNode) : LNode := Id.run do
  let size := nd.size
  let mut props := mirrorNodeLabelPlacementY nd.props
  if props.has LayeredOptions.POSITION then
    if let some pos := props.get LayeredOptions.POSITION then
      props := props.set LayeredOptions.POSITION (mirrorVectorY pos (offset - size.y))
  let alignment := alignmentOf props
  let newAlignment : Alignment := match alignment with
    | .top => .bottom
    | .bottom => .top
    | a => a
  props := setAlignmentIfChanged props alignment newAlignment
  return { nd with position := mirrorVectorY nd.position (offset - size.y),
                   padding := mirrorPaddingY nd.padding, props := props }

/-- The node part of `transpose_node` (position, size, label placement, padding, properties). -/
def transposeNodeShape (nd : LNode) : LNode :=
  { nd with position := transposeVector nd.position, size := transposeVector nd.size,
            props := transposeProperties (transposeNodeLabelPlacement nd.props),
            padding := transposePadding nd.padding }

/-- The port part of `mirror_port_x`: position (against the node width), anchor (against the port
width), mirrored side via `LPort.setSide` (which resets a non-explicit anchor), `PORT_INDEX`. -/
def mirrorPortShapeX (nodeSizeX : Float) (p : LPort) : LPort :=
  let size := p.size
  let p := { p with position := mirrorVectorX p.position (nodeSizeX - size.x),
                    anchor := mirrorVectorX p.anchor size.x }
  let p := p.setSide (mirroredPortSideX p.side)
  { p with props := reverseIndex p.props }

/-- The port part of `mirror_port_y`. -/
def mirrorPortShapeY (nodeSizeY : Float) (p : LPort) : LPort :=
  let size := p.size
  let p := { p with position := mirrorVectorY p.position (nodeSizeY - size.y),
                    anchor := mirrorVectorY p.anchor size.y }
  let p := p.setSide (mirroredPortSideY p.side)
  { p with props := reverseIndex p.props }

/-- The port part of `transpose_port`: position, size and anchor transposed, then the transposed
side via `LPort.setSide` (computed from the transposed size), `PORT_INDEX`. -/
def transposePortShape (p : LPort) : LPort :=
  let p := { p with position := transposeVector p.position, size := transposeVector p.size,
                    anchor := transposeVector p.anchor }
  let p := p.setSide (transposePortSide p.side)
  { p with props := reverseIndex p.props }

/-- `mirror_label_x(label, base_offset)`: `x := baseOffset - width - x`. -/
@[inline] def mirrorLabelShapeX (baseOffset : Float) (l : LLabel) : LLabel :=
  { l with position := mirrorVectorX l.position (baseOffset - l.size.x) }

/-- `mirror_label_y(label, base_offset)`. -/
@[inline] def mirrorLabelShapeY (baseOffset : Float) (l : LLabel) : LLabel :=
  { l with position := mirrorVectorY l.position (baseOffset - l.size.y) }

/-- `transpose_label`: position and size transposed. -/
@[inline] def transposeLabelShape (l : LLabel) : LLabel :=
  { l with position := transposeVector l.position, size := transposeVector l.size }

/-- Applies `f` to every point of a *stored* `JUNCTION_POINTS` chain (Rust `has_property` check). -/
def mapJunctionPoints (props : PropertyMap) (f : KVector → KVector) : PropertyMap :=
  if props.has LayeredOptions.JUNCTION_POINTS then
    match props.get LayeredOptions.JUNCTION_POINTS with
    | some jps => props.set LayeredOptions.JUNCTION_POINTS (jps.map f)
    | none => props
  else props

/-- Bend points and junction points of an edge mapped with `f`. -/
def mapEdgePoints (f : KVector → KVector) (e : LEdge) : LEdge :=
  { e with bendPoints := e.bendPoints.map f, props := mapJunctionPoints e.props f }

/-- `mirror_layer_constraint_x`: `FIRST` ↔ `LAST`, `FIRST_SEPARATE` ↔ `LAST_SEPARATE`. -/
def mirrorLayerConstraintX (props : PropertyMap) : PropertyMap :=
  let constraint := props.getD LayeredOptions.LAYERING_LAYER_CONSTRAINT .none
  let newConstraint : LayerConstraint := match constraint with
    | .first => .last
    | .firstSeparate => .lastSeparate
    | .last => .first
    | .lastSeparate => .firstSeparate
    | c => c
  if newConstraint != constraint then props.set LayeredOptions.LAYERING_LAYER_CONSTRAINT newConstraint else props

/-- `mirror_in_layer_constraint_y`: `IN_LAYER_CONSTRAINT` top ↔ bottom. -/
def mirrorInLayerConstraintY (nd : LNode) : LNode :=
  let newConstraint : InLayerConstraint := match nd.internal.inLayerConstraint with
    | .top => .bottom
    | .bottom => .top
    | c => c
  { nd with internal := { nd.internal with inLayerConstraint := newConstraint } }

/-- `transpose_layer_constraint`: `FIRST_SEPARATE`/`LAST_SEPARATE` layer constraints become
`TOP`/`BOTTOM` in-layer constraints and vice versa. -/
def transposeLayerConstraint (nd : LNode) : LNode :=
  let layerConstraint := nd.props.getD LayeredOptions.LAYERING_LAYER_CONSTRAINT .none
  let setBoth (lc : LayerConstraint) (ilc : InLayerConstraint) : LNode :=
    { nd with props := nd.props.set LayeredOptions.LAYERING_LAYER_CONSTRAINT lc,
              internal := { nd.internal with inLayerConstraint := ilc } }
  if layerConstraint == .firstSeparate then setBoth .none .top
  else if layerConstraint == .lastSeparate then setBoth .none .bottom
  else if nd.internal.inLayerConstraint == .top then setBoth .firstSeparate .none
  else if nd.internal.inLayerConstraint == .bottom then setBoth .lastSeparate .none
  else nd

/-- Maps the `EXT_PORT_SIDE` of a node (`transpose_external_port_side`,
`mirror_external_port_side_x/y`; the property has a default, so it is always rewritten). -/
@[inline] def mapExtPortSide (f : PortSide → PortSide) (nd : LNode) : LNode :=
  { nd with internal := { nd.internal with extPortSide := f nd.internal.extPortSide } }

/-! ## Mirroring and transposing elements (`LayeredM`) -/

/-- `mirror_edge_x(edge, offset)`: bend points, stored junction points, labels. -/
def mirrorEdgeX (e : LEdgeId) (offset : Float) : LayeredM Unit := do
  modifyEdge e (mapEdgePoints fun v => mirrorVectorX v offset)
  for l in (← getEdge e).labels do
    modifyLabel l (mirrorLabelShapeX offset)

/-- `mirror_edge_y(edge, offset)`. -/
def mirrorEdgeY (e : LEdgeId) (offset : Float) : LayeredM Unit := do
  modifyEdge e (mapEdgePoints fun v => mirrorVectorY v offset)
  for l in (← getEdge e).labels do
    modifyLabel l (mirrorLabelShapeY offset)

/-- `mirror_port_x(port, offset, node_size_x)`: the port, its outgoing edges, its labels. -/
def mirrorPortX (p : LPortId) (offset nodeSizeX : Float) : LayeredM Unit := do
  modifyPort p (mirrorPortShapeX nodeSizeX)
  let pt ← getPort p
  for e in pt.outgoingEdges do
    mirrorEdgeX e offset
  for l in pt.labels do
    modifyLabel l (mirrorLabelShapeX pt.size.x)

/-- `mirror_port_y(port, offset, node_size_y)`. -/
def mirrorPortY (p : LPortId) (offset nodeSizeY : Float) : LayeredM Unit := do
  modifyPort p (mirrorPortShapeY nodeSizeY)
  let pt ← getPort p
  for e in pt.outgoingEdges do
    mirrorEdgeY e offset
  for l in pt.labels do
    modifyLabel l (mirrorLabelShapeY pt.size.y)

/-- `mirror_node_x(node, offset)`: node, ports, external port dummy data, node labels
(`mirror_node_label_x`: label placement, then position against the node width). -/
def mirrorNodeX (n : LNodeId) (offset : Float) : LayeredM Unit := do
  modifyNode n (mirrorNodeShapeX offset)
  let nd ← getNode n
  for p in nd.ports do
    mirrorPortX p offset nd.size.x
  if nd.type == .externalPort then
    modifyNode n (mapExtPortSide mirroredPortSideX)
    modifyNode n fun x => { x with props := mirrorLayerConstraintX x.props }
  for l in nd.labels do
    modifyLabel l fun lb =>
      mirrorLabelShapeX nd.size.x { lb with props := mirrorNodeLabelPlacementX lb.props }

/-- `mirror_node_y(node, offset)`. -/
def mirrorNodeY (n : LNodeId) (offset : Float) : LayeredM Unit := do
  modifyNode n (mirrorNodeShapeY offset)
  let nd ← getNode n
  for p in nd.ports do
    mirrorPortY p offset nd.size.y
  if nd.type == .externalPort then
    modifyNode n (mapExtPortSide mirroredPortSideY)
    modifyNode n mirrorInLayerConstraintY
  for l in nd.labels do
    modifyLabel l fun lb =>
      mirrorLabelShapeY nd.size.y { lb with props := mirrorNodeLabelPlacementY lb.props }

/-- `mirror_x(nodes, graph)`: the mirror offset is the graph width (or, when the width is still
`0`, the maximum of `x + width + margin.right` over the nodes) minus twice the graph offset. -/
def mirrorX (nodes : Array LNodeId) (graph : LGraphId) : LayeredM Unit := do
  let gr ← getGraph graph
  let mut offset : Float := 0.0
  if gr.size.x == 0.0 then
    for n in nodes do
      let nd ← getNode n
      offset := fmax offset (nd.position.x + nd.size.x + nd.margin.right)
  else
    offset := gr.size.x - gr.offset.x
  offset := offset - gr.offset.x
  for n in nodes do
    mirrorNodeX n offset

/-- `mirror_y(nodes, graph)`. -/
def mirrorY (nodes : Array LNodeId) (graph : LGraphId) : LayeredM Unit := do
  let gr ← getGraph graph
  let mut offset : Float := 0.0
  if gr.size.y == 0.0 then
    for n in nodes do
      let nd ← getNode n
      offset := fmax offset (nd.position.y + nd.size.y + nd.margin.bottom)
  else
    offset := gr.size.y - gr.offset.y
  offset := offset - gr.offset.y
  for n in nodes do
    mirrorNodeY n offset

/-- `transpose_edge(edge)`: bend points, stored junction points, labels. -/
def transposeEdge (e : LEdgeId) : LayeredM Unit := do
  modifyEdge e (mapEdgePoints transposeVector)
  for l in (← getEdge e).labels do
    modifyLabel l transposeLabelShape

/-- `transpose_port(port)`: the port, its outgoing edges, its labels. -/
def transposePort (p : LPortId) : LayeredM Unit := do
  modifyPort p transposePortShape
  let pt ← getPort p
  for e in pt.outgoingEdges do
    transposeEdge e
  for l in pt.labels do
    modifyLabel l transposeLabelShape

/-- `transpose_node(node)`: node, ports, external port dummy data, node labels (placement, size,
position). -/
def transposeNode (n : LNodeId) : LayeredM Unit := do
  modifyNode n transposeNodeShape
  let nd ← getNode n
  for p in nd.ports do
    transposePort p
  if nd.type == .externalPort then
    modifyNode n (mapExtPortSide transposePortSide)
    modifyNode n transposeLayerConstraint
  for l in nd.labels do
    modifyLabel l fun lb =>
      transposeLabelShape { lb with props := transposeNodeLabelPlacement lb.props }

/-- `transpose(nodes)`. -/
def transpose (nodes : Array LNodeId) : LayeredM Unit := do
  for n in nodes do
    transposeNode n

/-- Maps the graph's `NODE_LABELS_PADDING` (Rust `if let Some(padding)`; the option has a default,
so the mapped padding is always stored). -/
def mapGraphNodeLabelsPadding (f : ElkPadding → ElkPadding) (gr : LGraph) : LGraph :=
  match gr.props.get LayeredOptions.NODE_LABELS_PADDING with
  | some p => { gr with props := gr.props.set LayeredOptions.NODE_LABELS_PADDING (f p) }
  | none => gr

/-- `transpose_edge_label_placement(graph)`: `EDGE_LABELS_SIDE_SELECTION` up ↔ down. -/
def transposeEdgeLabelPlacement (gr : LGraph) : LGraph :=
  match gr.props.get LayeredOptions.EDGE_LABELS_SIDE_SELECTION with
  | some old => { gr with props := gr.props.set LayeredOptions.EDGE_LABELS_SIDE_SELECTION old.transpose }
  | none => gr

/-- `mirror_all_x(graph, nodes)`: nodes, graph padding, `NODE_LABELS_PADDING`. -/
def mirrorAllX (graph : LGraphId) (nodes : Array LNodeId) : LayeredM Unit := do
  mirrorX nodes graph
  modifyGraph graph fun g => { g with padding := mirrorPaddingX g.padding }
  modifyGraph graph (mapGraphNodeLabelsPadding mirrorPaddingX)

/-- `mirror_all_y(graph, nodes)`. -/
def mirrorAllY (graph : LGraphId) (nodes : Array LNodeId) : LayeredM Unit := do
  mirrorY nodes graph
  modifyGraph graph fun g => { g with padding := mirrorPaddingY g.padding }
  modifyGraph graph (mapGraphNodeLabelsPadding mirrorPaddingY)

/-- `transpose_all(graph, nodes)`: nodes, edge label side selection, graph offset, size, padding,
`NODE_LABELS_PADDING`. -/
def transposeAll (graph : LGraphId) (nodes : Array LNodeId) : LayeredM Unit := do
  transpose nodes
  modifyGraph graph transposeEdgeLabelPlacement
  modifyGraph graph fun g => { g with offset := transposeVector g.offset, size := transposeVector g.size,
                                      padding := transposePadding g.padding }
  modifyGraph graph (mapGraphNodeLabelsPadding transposePadding)

/-- `rotate90_clockwise`: transpose, then mirror x. -/
def rotate90Clockwise (graph : LGraphId) (nodes : Array LNodeId) : LayeredM Unit := do
  transposeAll graph nodes
  mirrorAllX graph nodes

/-- `rotate90_counter_clockwise`: mirror x, then transpose. -/
def rotate90CounterClockwise (graph : LGraphId) (nodes : Array LNodeId) : LayeredM Unit := do
  mirrorAllX graph nodes
  transposeAll graph nodes

/-- The nodes to transform: layerless nodes, then the nodes of each layer, first occurrence only
(Rust `process`, de-duplicated with a pointer `HashSet`). -/
def collectNodes (graph : LGraphId) : LayeredM (Array LNodeId) := do
  let gr ← getGraph graph
  let mut seen : Std.HashSet LNodeId := {}
  let mut nodes : Array LNodeId := #[]
  for n in gr.layerlessNodes do
    if !seen.contains n then
      seen := seen.insert n
      nodes := nodes.push n
  for l in gr.layers do
    for n in (← getLayer l).nodes do
      if !seen.contains n then
        seen := seen.insert n
        nodes := nodes.push n
  return nodes

/-- `GraphTransformer.process(graph, monitor)`. `DIRECTION_CONGRUENCY` falls back to
`READING_DIRECTION` and `DIRECTION` to `RIGHT` (Rust `unwrap_or`; both options have defaults). -/
def process (mode : Mode) (graph : LGraphId) (monitor : ProgressMonitor) : LayeredM Unit := do
  let _ ← monitor.begin s!"Graph transformation ({mode.debugName})" 1.0
  let nodes ← collectNodes graph
  let gr ← getGraph graph
  let congruency := gr.props.getD LayeredOptions.DIRECTION_CONGRUENCY .readingDirection
  let direction := gr.props.getD LayeredOptions.DIRECTION .right
  if congruency == .readingDirection then
    match direction with
    | .left => mirrorAllX graph nodes
    | .down => transposeAll graph nodes
    | .up =>
      match mode with
      | .toInternalLtr =>
        transposeAll graph nodes
        mirrorAllY graph nodes
      | .toInputDirection =>
        mirrorAllY graph nodes
        transposeAll graph nodes
    | _ => pure ()
  else
    match mode with
    | .toInternalLtr =>
      match direction with
      | .left =>
        mirrorAllX graph nodes
        mirrorAllY graph nodes
      | .down => rotate90Clockwise graph nodes
      | .up => rotate90CounterClockwise graph nodes
      | _ => pure ()
    | .toInputDirection =>
      match direction with
      | .left =>
        mirrorAllX graph nodes
        mirrorAllY graph nodes
      | .down => rotate90CounterClockwise graph nodes
      | .up => rotate90Clockwise graph nodes
      | _ => pure ()
  monitor.done

/-- `new GraphTransformer(mode)` as a layered processor (trace name `GraphTransformer`). -/
def processor (mode : Mode) : LayeredProcessor :=
  { name := "GraphTransformer", process := process mode }

end GraphTransformer

-- elk-rs (the oracle) swaps the modes relative to Java: `DirectionPreprocessor` creates
-- `GraphTransformer::new(ToInputDirection)` and `DirectionPostprocessor` `ToInternalLtr`
-- (`intermediate_processor_strategy.rs`); only `UP` (reading direction) and the rotation variants
-- are affected. Verified against the oracle trace (a north output port of a 100×20 node ends as an
-- east port at (20, 0) for `UP`).
builtin_initialize registerGraphTransformerDirectionPreprocessor : Unit ←
  IntermediateProcessorStrategy.register .directionPreprocessor (GraphTransformer.processor .toInputDirection)

builtin_initialize registerGraphTransformerDirectionPostprocessor : Unit ←
  IntermediateProcessorStrategy.register .directionPostprocessor (GraphTransformer.processor .toInternalLtr)

end Elk.Alg.Layered.Intermediate
