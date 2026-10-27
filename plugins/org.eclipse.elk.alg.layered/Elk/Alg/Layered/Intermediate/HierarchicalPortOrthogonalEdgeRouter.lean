import Std.Data.HashSet
import Elk.Alg.Layered.LayeredPhases
import Elk.Alg.Layered.Graph.Transform.LGraphAdapters
import Elk.Alg.Layered.Options.LayeredOptions
import Elk.Alg.Layered.P5Edges.Orthogonal.OrthogonalRoutingGenerator
import Elk.Alg.Common.NodeSpacing.NodeDimensionCalculation
import Elk.Core.Util.ElkTrace
import Elk.Core.Util.Sort
import Elk.Core.Util.Java
/-!
# `org.eclipse.elk.alg.layered.intermediate.HierarchicalPortOrthogonalEdgeRouter`

Port of elk-rs `intermediate/hierarchical_port_orthogonal_edge_router.rs` (Java
`HierarchicalPortOrthogonalEdgeRouter`). Routes the edges of northern and southern external port
dummies orthogonally after phase 5 and fixes the coordinates of all external port dummies:

1. `restoreNorthSouthDummies`: the original north/south dummies removed by
   `HierarchicalPortConstraintProcessor` (`EXT_PORT_REPLACED_DUMMIES`) are restored (port side
   flipped, port labels placed) and every replacement dummy gets a new port on its external port side
   connected to its original; the originals are appended to the last layer.
2. `setNorthSouthDummyCoordinates`: `x` from the connected ports (`FREE`/`FIXED_SIDE`/`FIXED_ORDER`),
   the ratio or the position (`FIXED_RATIO`/`FIXED_POS`, converted from border to content area
   coordinates), `y` on the top/bottom border; overlapping (or, for `FIXED_ORDER`, misordered)
   dummies are moved right.
3. `routeEdges`: south-to-north routing between the replacement dummies and the northern originals
   starting `SPACING_NODE_NODE` above the content area, north-to-south routing for the southern ones;
   the graph offset/height grow by the space the routing slots need.
4. `removeTemporaryNorthSouthDummies`: the edges of the replacement dummies are reconnected to the
   originals, with the routed bend points of the dummy → original edge appended (incoming edges) or
   prepended in reverse (outgoing edges); the replacement dummies are removed.
5. `fixCoordinates`: `x` of east/west dummies on the borders, `y` for `FIXED_RATIO`/`FIXED_POS`
   (growing the graph if needed), `y` of north/south dummies on the (new) borders.
6. `correctSlantedEdgeSegments`: the first/last bend point of edges at east/west dummies is aligned
   with the port anchor.

Rust's `northern_ext_port_edge_routing_height` field is only written (reset by every `process`); it
is the return value of `routeEdges` here.

Differences from Java reproduced from elk-rs:
* `restoreDummy`: Rust adapts the graph (`LGraphAdapters::adapt(graph, false, false, all)`) and runs
  the margin calculator only on the adapter node that is the dummy. The adapter snapshots the layer
  nodes and the restored dummy is not in a layer yet, so no margins are computed (Java adapts the
  dummy directly and computes them). Reproduced by the same search.
* `fixCoordinates` / `correctSlantedEdgeSegments` process the last layer only when it differs from
  the first one (Java processes a single layer twice); `fixCoordinates` returns for a graph without
  layers (Java throws).
* Missing properties fall back to defaults (`PORT_ANCHOR` → `(0, 0)`, unset spacings → `0`) and
  missing ports/edges skip the element (Java throws `NullPointerException`).
* `Math.max` → Rust `f64::max` (`fmax`); sorts use the stable Rust `sort_by` with `partial_cmp`
  (`Float.comparePartial`), Java `Arrays.sort` with `Double.compare`.

Trace output (`ELK_TRACE_HIER_PORT_ORTHO`) prints the Rust `{:.1}` values with
`Float.toRustDisplay` (approximation; stderr only). Like Rust, the `route_edges prep` line is printed
before the layers are collected and thus always shows `0` sizes.

Precondition: a layered graph after phase 5 (orthogonal routing). Slot: after phase 5.
-/
namespace Elk.Alg.Layered.Intermediate

open Elk.Graph Elk.Core Elk.Core.Alg Elk.Core.Math Elk.Core.Options Elk.Core.Util Elk.Alg.Layered
  Elk.Alg.Layered.Graph Elk.Alg.Layered.Graph.Transform Elk.Alg.Layered.Options
  Elk.Alg.Layered.P5Edges.Orthogonal LayeredM

namespace HierarchicalPortOrthogonalEdgeRouter

/-- Rust `trace_step(message)` (`ELK_TRACE_HIER_PORT_ORTHO`). -/
def traceStep (message : String) : IO Unit := do
  if ElkTrace.global.hierPortOrtho then IO.eprintln s!"[hier-port-ortho] {message}"

/-! ## Step 1: restore north / south dummies -/

/-- The label placement of `restoreDummy` for `INSIDE` port labels: stacked below the port top-down
starting at `SPACING_LABEL_PORT_VERTICAL`, centred on the dummy. -/
private def placeInsideLabels (labels : Array LLabelId) (dummyWidth portPosX spacingVertical labelLabelSpacing : Float) :
    LayeredM Unit := do
  let mut currentY := spacingVertical
  let xCenterRelative := dummyWidth / 2.0 - portPosX
  for label in labels do
    let y := currentY
    modifyLabel label fun l => { l with position := ⟨xCenterRelative - l.size.x / 2.0, y⟩ }
    currentY := currentY + ((← getLabel label).size.y + labelLabelSpacing)

/-- `restoreDummy(dummy, graph)` (Rust `restore_dummy`): flips the side of the dummy's port
(northern dummies get a southern port and vice versa) and, if port labels are part of the graph's
size constraints, places the port labels (`INSIDE`: stacked and centred, `OUTSIDE`: `x` right of
the dummy) and runs the margin calculator on the dummy's adapter (never found, see module doc). -/
def restoreDummy (dummy : LNodeId) (graph : LGraphId) : LayeredM Unit := do
  let nd ← getNode dummy
  let portSide := nd.internal.extPortSide
  let some dummyPort := nd.ports[0]? | return
  match portSide with
  | .north => modifyPort dummyPort (·.setSide .south)
  | .south => modifyPort dummyPort (·.setSide .north)
  | _ => pure ()
  let gr ← getGraph graph
  let sizeConstraints := (gr.props.get LayeredOptions.NODE_SIZE_CONSTRAINTS).getD EnumSet.noneOf
  if !sizeConstraints.contains .portLabels then return
  let portLabelSpacingHorizontal := (nd.props.get LayeredOptions.SPACING_LABEL_PORT_HORIZONTAL).getD 0.0
  let portLabelSpacingVertical := (nd.props.get LayeredOptions.SPACING_LABEL_PORT_VERTICAL).getD 0.0
  let labelLabelSpacing := (nd.props.get LayeredOptions.SPACING_LABEL_LABEL).getD 0.0
  let portLabelPlacement := (gr.props.get CoreOptions.PORT_LABELS_PLACEMENT).getD PortLabelPlacement.outsideSet
  let pt ← getPort dummyPort
  if portLabelPlacement.contains .inside then
    placeInsideLabels pt.labels nd.size.x pt.position.x portLabelSpacingVertical labelLabelSpacing
  else if portLabelPlacement.contains .outside then
    let x := portLabelSpacingHorizontal + nd.size.x - pt.position.x
    for label in pt.labels do
      modifyLabel label fun l => { l with position := { l.position with x := x } }
  -- Rust: search the adapter's (layer) nodes for the dummy, which is not in a layer yet
  let adapter ← LGraphAdapters.adapt graph false false fun _ => true
  let calculator := Elk.Alg.Common.NodeSpacing.NodeDimensionCalculation.getNodeMarginCalculator adapter
  for n in ← adapter.getNodes graph do
    if n == dummy then
      calculator.processNode adapter graph n
      break

/-- `connectNodeToDummy(layeredGraph, node, dummy)` (Rust `connect_node_to_dummy`): a new port of
`node` on its `EXT_PORT_SIDE`, connected by a new edge to the first port of `dummy` (no edge when
the dummy has no port; the port is created anyway, like Rust). -/
def connectNodeToDummy (node dummy : LNodeId) : LayeredM Unit := do
  let outPort ← LayeredM.createPort
  setPortNode outPort (some node)
  let extPortSide := (← getNode node).internal.extPortSide
  modifyPort outPort (·.setSide extPortSide)
  let some inPort := (← getNode dummy).ports[0]? | return
  let edge ← LayeredM.createEdge
  setEdgeSource edge (some outPort)
  setEdgeTarget edge (some inPort)

/-- `restoreNorthSouthDummies(layeredGraph)` (Rust `restore_north_south_dummies`): restores the
dummies of `EXT_PORT_REPLACED_DUMMIES` (in list order), connects every external port dummy with an
`EXT_PORT_REPLACED_DUMMY` (layer order, node order) to its original and appends the originals to the
last layer. Rust returns early when the property is unset (Lean: empty list). -/
def restoreNorthSouthDummies (graph : LGraphId) : LayeredM (Array LNodeId) := do
  let dummies := (← getGraph graph).internal.extPortReplacedDummies
  if dummies.isEmpty then return #[]
  let mut restored : Array LNodeId := #[]
  for dummy in dummies do
    restoreDummy dummy graph
    restored := restored.push dummy
  for layer in (← getGraph graph).layers do
    for node in (← getLayer layer).nodes do
      let nd ← getNode node
      if nd.type != .externalPort then continue
      if let some replacedDummy := nd.internal.extPortReplacedDummy then
        connectNodeToDummy node replacedDummy
  if let some lastLayer := (← getGraph graph).layers.back? then
    for dummy in restored do
      setNodeLayer dummy (some lastLayer)
  return restored

/-! ## Step 2: north / south dummy coordinates -/

/-- `x` of the dummy's `PORT_ANCHOR` (`(0, 0)` when unset, Rust `unwrap_or_default`). -/
private def portAnchorOf (nd : LNode) : KVector := (nd.props.get LayeredOptions.PORT_ANCHOR).getD {}

/-- `calculateNorthSouthDummyPositions(dummy)` (Rust `calculate_north_south_dummy_positions`): the
mean absolute anchor `x` of the ports connected to the dummy's port (`0` without any) minus the
dummy's `PORT_ANCHOR.x`. -/
def calculateNorthSouthDummyPositions (dummy : LNodeId) : LayeredM Unit := do
  let some dummyPort := (← getNode dummy).ports[0]? | return
  let connectedPorts ← withArena (·.portConnectedPorts dummyPort)
  if connectedPorts.isEmpty then
    modifyNode dummy fun x => { x with position := { x.position with x := 0.0 } }
    return
  let mut posSum := 0.0
  for port in connectedPorts do
    let pt ← getPort port
    if let some owner := pt.owner then
      let node ← getNode owner
      posSum := posSum + (node.position.x + pt.position.x + pt.anchor.x)
  let offset := (portAnchorOf (← getNode dummy)).x
  let x := posSum / connectedPorts.size.toFloat - offset
  modifyNode dummy fun nd => { nd with position := { nd.position with x := x } }

/-- `applyNorthSouthDummyRatio(dummy, width)` (Rust `apply_north_south_dummy_ratio`). -/
def applyNorthSouthDummyRatio (dummy : LNodeId) (width : Float) : LayeredM Unit := do
  let nd ← getNode dummy
  let x := width * nd.internal.portRatioOrPosition - (portAnchorOf nd).x
  modifyNode dummy fun n => { n with position := { n.position with x := x } }

/-- `applyNorthSouthDummyPosition(dummy)` (Rust `apply_north_south_dummy_position`). -/
def applyNorthSouthDummyPosition (dummy : LNodeId) : LayeredM Unit := do
  let nd ← getNode dummy
  let x := nd.internal.portRatioOrPosition - (portAnchorOf nd).x
  modifyNode dummy fun n => { n with position := { n.position with x := x } }

/-- `dummy.borderToContentAreaCoordinates(true, false)` as inlined by Rust: `x -= padding.left +
offset.x` of the layered graph. -/
private def borderToContentAreaX (graph : LGraphId) (dummy : LNodeId) : LayeredM Unit := do
  let gr ← getGraph graph
  let d := gr.padding.left + gr.offset.x
  modifyNode dummy fun n => { n with position := { n.position with x := n.position.x - d } }

/-- `assignAscendingCoordinates(dummies, graph)` (Rust `assign_ascending_coordinates`): moves dummies
right so that consecutive dummies keep `SPACING_PORT_PORT` between their margins, widening the graph
to contain them. -/
def assignAscendingCoordinates (dummies : Array LNodeId) (graph : LGraphId) : LayeredM Unit := do
  let some first := dummies[0]? | return
  let spacing := ((← getGraph graph).props.get LayeredOptions.SPACING_PORT_PORT).getD 0.0
  let f ← getNode first
  let mut nextValid := f.position.x + f.size.x + f.margin.right + spacing
  for i in [1:dummies.size] do
    let dummy := dummies[i]!
    let nd ← getNode dummy
    let delta := nd.position.x - nd.margin.left - nextValid
    if delta < 0.0 then
      modifyNode dummy fun n => { n with position := { n.position with x := n.position.x - delta } }
    let currentPos := (← getNode dummy).position.x
    let sizeX := nd.size.x
    modifyGraph graph fun g => { g with size := { g.size with x := fmax g.size.x (currentPos + sizeX) } }
    nextValid := currentPos + sizeX + nd.margin.right + spacing

/-- `ensureUniquePositions(dummies, graph)` (Rust `ensure_unique_positions`): sorted by `x`
(stable, `partial_cmp`), then `assignAscendingCoordinates`. -/
def ensureUniquePositions (dummies : Array LNodeId) (graph : LGraphId) : LayeredM Unit := do
  if dummies.isEmpty then return
  let keyed ← dummies.mapM fun d => do return (d, (← getNode d).position.x)
  let sorted := (stableSort keyed fun p q => Float.comparePartial p.2 q.2).map (·.1)
  assignAscendingCoordinates sorted graph

/-- `restoreProperOrder(dummies, graph)` (Rust `restore_proper_order`): sorted by
`PORT_RATIO_OR_POSITION` (stable, `partial_cmp`), then `assignAscendingCoordinates`. -/
def restoreProperOrder (dummies : Array LNodeId) (graph : LGraphId) : LayeredM Unit := do
  if dummies.isEmpty then return
  let keyed ← dummies.mapM fun d => do return (d, (← getNode d).internal.portRatioOrPosition)
  let sorted := (stableSort keyed fun p q => Float.comparePartial p.2 q.2).map (·.1)
  assignAscendingCoordinates sorted graph

/-- The `x` coordinate step of `setNorthSouthDummyCoordinates` for one dummy. -/
private def setDummyX (graph : LGraphId) (constraints : PortConstraints) (graphWidth : Float) (dummy : LNodeId) :
    LayeredM Unit := do
  match constraints with
  | .free | .fixedSide | .fixedOrder => calculateNorthSouthDummyPositions dummy
  | .fixedRatio =>
    applyNorthSouthDummyRatio dummy graphWidth
    borderToContentAreaX graph dummy
  | .fixedPos =>
    applyNorthSouthDummyPosition dummy
    borderToContentAreaX graph dummy
    let nd ← getNode dummy
    let requiredX := nd.position.x + nd.size.x / 2.0
    modifyGraph graph fun g => { g with size := { g.size with x := fmax g.size.x requiredX } }
  | .undefined => pure ()

/-- `setNorthSouthDummyCoordinates(layeredGraph, northSouthDummies)` (Rust
`set_north_south_dummy_coordinates`): `x` per port constraints, `y` on the top (`-padding.top -
offset.y`) or bottom (`size.y + padding.top + padding.bottom - offset.y`) border, then
`ensureUniquePositions` (`FREE`, `FIXED_SIDE`) or `restoreProperOrder` (`FIXED_ORDER`) per side. -/
def setNorthSouthDummyCoordinates (graph : LGraphId) (northSouthDummies : Array LNodeId) : LayeredM Unit := do
  let gr ← getGraph graph
  let constraints := (gr.props.get LayeredOptions.PORT_CONSTRAINTS).getD .undefined
  let graphSize := gr.size
  let graphPadding := gr.padding
  let graphWidth := graphSize.x + graphPadding.left + graphPadding.right
  let northY := 0.0 - graphPadding.top - gr.offset.y
  let southY := graphSize.y + graphPadding.top + graphPadding.bottom - gr.offset.y
  let mut northernDummies : Array LNodeId := #[]
  let mut southernDummies : Array LNodeId := #[]
  for dummy in northSouthDummies do
    setDummyX graph constraints graphWidth dummy
    match (← getNode dummy).internal.extPortSide with
    | .north =>
      modifyNode dummy fun n => { n with position := { n.position with y := northY } }
      northernDummies := northernDummies.push dummy
    | .south =>
      modifyNode dummy fun n => { n with position := { n.position with y := southY } }
      southernDummies := southernDummies.push dummy
    | _ => pure ()
  match constraints with
  | .free | .fixedSide =>
    ensureUniquePositions northernDummies graph
    ensureUniquePositions southernDummies graph
  | .fixedOrder =>
    restoreProperOrder northernDummies graph
    restoreProperOrder southernDummies graph
  | _ => pure ()

/-! ## Step 3: edge routing -/

/-- The target and source "layers" of `routeEdges` for one side (Rust `LinkedHashSet` replacement:
insertion order, first occurrence): the dummies of that side and the source nodes of their incoming
edges. Rust fills the northern and southern sets in one loop; the sets are independent, so collecting
them per side gives the same orders. -/
def collectRoutingLayers (northSouthDummies : Array LNodeId) (side : PortSide) :
    LayeredM (Array LNodeId × Array LNodeId) := do
  let mut sourceLayer : Array LNodeId := #[]
  let mut targetLayer : Array LNodeId := #[]
  let mut sourceSeen : Std.HashSet LNodeId := {}
  let mut targetSeen : Std.HashSet LNodeId := {}
  for dummy in northSouthDummies do
    if (← getNode dummy).internal.extPortSide != side then continue
    if !targetSeen.contains dummy then
      targetSeen := targetSeen.insert dummy
      targetLayer := targetLayer.push dummy
    for edge in ← withArena (·.nodeIncomingEdges dummy) do
      let some sourcePort := (← getEdge edge).source | continue
      let some sourceNode := (← getPort sourcePort).owner | continue
      if !sourceSeen.contains sourceNode then
        sourceSeen := sourceSeen.insert sourceNode
        sourceLayer := sourceLayer.push sourceNode
  return (sourceLayer, targetLayer)

/-- `ELK_TRACE_HIER_PORT_ORTHO` graph geometry suffix. -/
private def traceGeometry (graph : LGraphId) : LayeredM String := do
  let gr ← getGraph graph
  return s!"graph(size=({Float.toRustDisplay gr.size.x},{Float.toRustDisplay gr.size.y}) " ++
    s!"offset=({Float.toRustDisplay gr.offset.x},{Float.toRustDisplay gr.offset.y}))"

/-- `routeEdges(monitor, layeredGraph, northSouthDummies)` (Rust `route_edges`): south-to-north
routing ("extnorth") from the sources of the northern dummies' edges starting at
`-SPACING_NODE_NODE - offset.y`; with `slots > 0` the offset and height grow by
`nodeSpacing + (slots - 1) · edgeSpacing`. Then north-to-south routing ("extsouth") starting at
`size.y + nodeSpacing - offset.y`, growing the height the same way. Each generator call takes the
`ArenaSync` snapshot of the graph at that moment (`scope := none`). Returns Rust's
`northern_ext_port_edge_routing_height`. -/
def routeEdges (graph : LGraphId) (northSouthDummies : Array LNodeId) : LayeredM Float := do
  let gr ← getGraph graph
  let nodeSpacing := (gr.props.get LayeredOptions.SPACING_NODE_NODE).getD 0.0
  let edgeSpacing := (gr.props.get LayeredOptions.SPACING_EDGE_EDGE).getD 0.0
  if ElkTrace.global.hierPortOrtho then
    -- Rust prints the (still empty) set sizes
    IO.eprintln (s!"[hier-port-ortho] route_edges prep north(src=0,tgt=0) south(src=0,tgt=0) " ++
      s!"spacing(node={Float.toRustDisplay nodeSpacing},edge={Float.toRustDisplay edgeSpacing}) " ++
      (← traceGeometry graph))
  let (northernSourceLayer, northernTargetLayer) ← collectRoutingLayers northSouthDummies .north
  let (southernSourceLayer, southernTargetLayer) ← collectRoutingLayers northSouthDummies .south
  let mut northernHeight := 0.0
  if !northernSourceLayer.isEmpty then
    let routingGenerator := OrthogonalRoutingGenerator.new .southToNorth edgeSpacing (some "extnorth")
    let startPos := -nodeSpacing - (← getGraph graph).offset.y
    let slots ← routingGenerator.routeEdges graph northernSourceLayer 0 northernTargetLayer startPos
    if slots > 0 then
      let h := nodeSpacing + (slots.toFloat - 1.0) * edgeSpacing
      northernHeight := h
      modifyGraph graph fun g => { g with
        offset := { g.offset with y := g.offset.y + h }
        size := { g.size with y := g.size.y + h } }
    if ElkTrace.global.hierPortOrtho then
      IO.eprintln (s!"[hier-port-ortho] north slots={slots} added_height={Float.toRustDisplay northernHeight} " ++
        (← traceGeometry graph))
  if !southernSourceLayer.isEmpty then
    let routingGenerator := OrthogonalRoutingGenerator.new .northToSouth edgeSpacing (some "extsouth")
    let g ← getGraph graph
    let startPos := g.size.y + nodeSpacing - g.offset.y
    let slots ← routingGenerator.routeEdges graph southernSourceLayer 0 southernTargetLayer startPos
    if slots > 0 then
      let h := nodeSpacing + (slots.toFloat - 1.0) * edgeSpacing
      modifyGraph graph fun g => { g with size := { g.size with y := g.size.y + h } }
    if ElkTrace.global.hierPortOrtho then
      IO.eprintln s!"[hier-port-ortho] south slots={slots} {← traceGeometry graph}"
  return northernHeight

/-! ## Step 4: remove the temporary dummies -/

/-- The input (`WEST`), output (`EAST`) and origin (any other side) ports of a replacement dummy
(the last port of each kind, like the Rust/Java loop). -/
private def classifyPorts (ports : Array LPortId) : LayeredM (Option LPortId × Option LPortId × Option LPortId) := do
  let mut inPort : Option LPortId := none
  let mut outPort : Option LPortId := none
  let mut originPort : Option LPortId := none
  for port in ports do
    match (← getPort port).side with
    | .west => inPort := some port
    | .east => outPort := some port
    | _ => originPort := some port
  return (inPort, outPort, originPort)

/-- Reconnects the edges of one replacement dummy to its original (Rust loop body of
`remove_temporary_north_south_dummies`); `false` when the dummy is skipped. -/
private def reconnectTemporaryDummy (node replacedDummy : LNodeId) : LayeredM Bool := do
  let nd ← getNode node
  let (some nodeInPort, some nodeOutPort, some nodeOriginPort) ← classifyPorts nd.ports | return false
  let some nodeToOriginEdge := (← getPort nodeOriginPort).outgoingEdges[0]? | return false
  let originBends := (← getEdge nodeToOriginEdge).bendPoints
  let originPortPos := (← getPort nodeOriginPort).position
  let firstBend := originPortPos + nd.position
  let incomingBends := #[firstBend] ++ originBends
  let outgoingBends := originBends.reverse.push firstBend
  let some replacedDummyPort := (← getNode replacedDummy).ports[0]? | return false
  for edge in (← getPort nodeInPort).incomingEdges do
    setEdgeTarget edge (some replacedDummyPort)
    modifyEdge edge fun e => { e with bendPoints := e.bendPoints ++ incomingBends }
  for edge in (← getPort nodeOutPort).outgoingEdges do
    setEdgeSource edge (some replacedDummyPort)
    modifyEdge edge fun e => { e with bendPoints := outgoingBends ++ e.bendPoints }
  setEdgeSource nodeToOriginEdge none
  setEdgeTarget nodeToOriginEdge none
  return true

/-- `removeTemporaryNorthSouthDummies(layeredGraph)` (Rust `remove_temporary_north_south_dummies`):
for every external port dummy with an `EXT_PORT_REPLACED_DUMMY` (layer order, node order), the
incoming edges of its `WEST` port are retargeted to the original's port with
`[origin port + dummy position] ++ routed bends` appended, the outgoing edges of its `EAST` port get
the original's port as source with `reverse(routed bends) ++ [origin port + dummy position]`
prepended; the dummy → original edge is disconnected and the dummy removed from its layer. -/
def removeTemporaryNorthSouthDummies (graph : LGraphId) : LayeredM Unit := do
  let mut nodesToRemove : Array LNodeId := #[]
  for layer in (← getGraph graph).layers do
    for node in (← getLayer layer).nodes do
      let nd ← getNode node
      if nd.type != .externalPort then continue
      let some replacedDummy := nd.internal.extPortReplacedDummy | continue
      if ← reconnectTemporaryDummy node replacedDummy then
        nodesToRemove := nodesToRemove.push node
  for node in nodesToRemove do
    setNodeLayer node none

/-! ## Step 5: fix the dummy coordinates -/

/-- `fixCoordinates(layer, constraints, graph)` (Rust `fix_coordinates_for_layer`): east/west dummies
get their `x` on the border and, for `FIXED_RATIO`/`FIXED_POS`, their `y` (the graph grows to the
largest required height); then north/south dummies get their `y` on the (new) border. Padding,
offset and the actual size are read once at the start (Rust). -/
def fixCoordinatesForLayer (layer : LayerId) (constraints : PortConstraints) (graph : LGraphId) : LayeredM Unit := do
  let gr ← getGraph graph
  let padding := gr.padding
  let offset := gr.offset
  let graphActualSize := gr.actualSize
  let mut newActualHeight := graphActualSize.y
  let nodes := (← getLayer layer).nodes
  for node in nodes do
    let nd ← getNode node
    if nd.type != .externalPort then continue
    let extSide := nd.internal.extPortSide
    let extSize := nd.internal.extPortSize
    let portAnchor := portAnchorOf nd
    match extSide with
    | .east =>
      let x := (← getGraph graph).size.x + padding.right - offset.x
      modifyNode node fun n => { n with position := { n.position with x := x } }
    | .west =>
      let x := -offset.x - padding.left
      modifyNode node fun n => { n with position := { n.position with x := x } }
    | _ => pure ()
    let mut requiredHeight := 0.0
    if extSide == .east || extSide == .west then
      let y? : Option Float :=
        if constraints == .fixedRatio then some (graphActualSize.y * nd.internal.portRatioOrPosition - portAnchor.y)
        else if constraints == .fixedPos then some (nd.internal.portRatioOrPosition - portAnchor.y)
        else none
      if let some y := y? then
        requiredHeight := y + extSize.y
        let y := y - (padding.top + offset.y)
        modifyNode node fun n => { n with position := { n.position with y := y } }
    newActualHeight := fmax newActualHeight requiredHeight
  let dy := newActualHeight - graphActualSize.y
  modifyGraph graph fun g => { g with size := { g.size with y := g.size.y + dy } }
  for node in nodes do
    let nd ← getNode node
    if nd.type != .externalPort then continue
    match nd.internal.extPortSide with
    | .north =>
      let y := -offset.y - padding.top
      modifyNode node fun n => { n with position := { n.position with y := y } }
    | .south =>
      let y := (← getGraph graph).size.y + padding.bottom - offset.y
      modifyNode node fun n => { n with position := { n.position with y := y } }
    | _ => pure ()

/-- `fixCoordinates(layeredGraph)` (Rust `fix_coordinates`): the first layer, then the last one if
different (see module doc). -/
def fixCoordinates (graph : LGraphId) : LayeredM Unit := do
  let gr ← getGraph graph
  let constraints := (gr.props.get LayeredOptions.PORT_CONSTRAINTS).getD .undefined
  let layers := gr.layers
  let some first := layers[0]? | return
  fixCoordinatesForLayer first constraints graph
  if layers.size > 1 then
    fixCoordinatesForLayer layers[layers.size - 1]! constraints graph

/-! ## Step 6: slanted edge segments -/

/-- `correctSlantedEdgeSegments(layer)` (Rust `correct_slanted_edge_segments_layer`): for the edges
of east/west dummies (`getConnectedEdges` order) with bend points, the first bend point gets the `y`
of the source anchor when the source port belongs to the dummy, the last one the `y` of the target
anchor when the target port does. -/
def correctSlantedEdgeSegmentsLayer (layer : LayerId) : LayeredM Unit := do
  for node in (← getLayer layer).nodes do
    let nd ← getNode node
    if nd.type != .externalPort then continue
    let extSide := nd.internal.extPortSide
    if extSide != .east && extSide != .west then continue
    for edge in ← withArena (·.nodeConnectedEdges node) do
      let ed ← getEdge edge
      if ed.bendPoints.isEmpty then continue
      if let some sourcePort := ed.source then
        if (← getPort sourcePort).owner == some node then
          if let some anchor := (← withArena (·.portAbsoluteAnchor sourcePort)) then
            modifyEdge edge fun e => { e with bendPoints := e.bendPoints.modify 0 fun p => { p with y := anchor.y } }
      if let some targetPort := ed.target then
        if (← getPort targetPort).owner == some node then
          if let some anchor := (← withArena (·.portAbsoluteAnchor targetPort)) then
            modifyEdge edge fun e =>
              { e with bendPoints := e.bendPoints.modify (e.bendPoints.size - 1) fun p => { p with y := anchor.y } }

/-- `correctSlantedEdgeSegments(layeredGraph)` (Rust `correct_slanted_edge_segments`): the first
layer, then the last one if different. -/
def correctSlantedEdgeSegments (graph : LGraphId) : LayeredM Unit := do
  let layers := (← getGraph graph).layers
  let some first := layers[0]? | return
  correctSlantedEdgeSegmentsLayer first
  if layers.size > 1 then
    correctSlantedEdgeSegmentsLayer layers[layers.size - 1]!

/-! ## Processor -/

/-- `process(layeredGraph, monitor)` body (steps 1 to 6). -/
def run (graph : LGraphId) : LayeredM Unit := do
  traceStep "restore_north_south_dummies"
  let northSouthDummies ← restoreNorthSouthDummies graph
  traceStep "set_north_south_dummy_coordinates"
  setNorthSouthDummyCoordinates graph northSouthDummies
  traceStep "route_edges"
  let _ ← routeEdges graph northSouthDummies
  traceStep "remove_temporary_north_south_dummies"
  removeTemporaryNorthSouthDummies graph
  traceStep "fix_coordinates"
  fixCoordinates graph
  traceStep "correct_slanted_edge_segments"
  correctSlantedEdgeSegments graph

/-- The `HierarchicalPortOrthogonalEdgeRouter`. -/
def processor : LayeredProcessor :=
  { name := "HierarchicalPortOrthogonalEdgeRouter"
    process := fun graph monitor => do
      let _ ← monitor.begin "Orthogonally routing hierarchical port edges" 1.0
      run graph
      monitor.done }

end HierarchicalPortOrthogonalEdgeRouter

builtin_initialize registerHierarchicalPortOrthogonalEdgeRouter : Unit ←
  IntermediateProcessorStrategy.register .hierarchicalPortOrthogonalEdgeRouter HierarchicalPortOrthogonalEdgeRouter.processor

end Elk.Alg.Layered.Intermediate
