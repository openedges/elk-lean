import Std.Data.HashMap
import Std.Data.HashSet
import Elk.Alg.Layered.LayeredPhases
import Elk.Alg.Layered.Graph.LGraphUtil
import Elk.Alg.Layered.Options.LayeredOptions
import Elk.Alg.Layered.P5Edges.Splines.SplineSegment
import Elk.Alg.Layered.P5Edges.Splines.SplinesMath
import Elk.Graph.ArrayModify
/-!
# `org.eclipse.elk.alg.layered.p5edges.splines.SplineEdgeRouter`

Port of elk-rs `p5edges/splines/spline_edge_router.rs` (plus the graph-reading constructors of
`spline_segment.rs`). Routes the edges with splines: for every pair of adjacent layers the edges
between them are grouped into `SplineSegment`s (1:n hyperedges first, then single edges), a
dependency graph between the segments is built (which segment must lie left of which to save
crossings), its cycles are broken (ties by the graph's `RANDOM`) and a topological numbering assigns
each segment its vertical slot (`rank`). The slots determine the gap between the layers, so the
router places the nodes horizontally (`LGraphUtil.placeNodesHorizontally`) and sets the graph width.
**No bend points** are computed: the segments of each spline route are remembered for the
`FinalSplineBendpointsCalculator` (`SPLINE_ROUTE_START`, `SPLINE_EDGE_CHAIN`).

## State and arena mapping
- The Rust struct fields are `SplineEdgeRouter.State`, threaded with `RouterM := StateT State LayeredM`.
- `SplineSegmentRef` → `SplineSegmentId` into `State.segments` (creation order = Rust
  `all_spline_segments` order); `DependencyRef` → `DependencyId`, numbered in creation order
  (`State.dependencyCount`). The dependencies of a layer gap only live while the gap is ranked: they
  are the arrays of `GapDeps` (see "Dependency graph, cycle breaking and ranking of one layer gap"),
  the segments keep their final `outgoing`/`incoming` id lists.
- `left/right_ports_layer` and `edges_remaining_layer` (`Vec` + linear `contains`/`remove`) keep the
  Rust order in arrays; a `Std.HashSet` answers the membership tests (an edge is pushed at most once
  per layer pair, so the set and the array stay in sync).
- `edge_to_segment_map`/`successing_edge` (`FxHashMap`, lookups only) → `Std.HashMap`.
- `RANDOM`: like Rust (`get_property(RANDOM).unwrap_or_else(|| Random::new(0))`, an `Arc`-shared
  generator) a graph generator is shared — every draw is written back — while a missing one is a
  local `Random(0)` that is not stored.
- Every graph read is on the live graph (Rust locks `LNodeRef`/`LPortRef`; no `ArenaSync`), so port
  edge lists are `LPort.incomingEdges`/`outgoingEdges` order and `node.incoming_edges()` is
  `LGraphArena.nodeIncomingEdges`.

## Persisting the routes (shared-module change pending)
Rust stores `SPLINE_ROUTE_START: Vec<SplineSegmentRef>` on each start edge; the segments must
outlive the phase. The Lean port appends the router's segment table to the graph
(`LGraphInternals.splineSegments`) and stores the ids on the edge
(`LEdgeInternals.splineRouteStart`); `route` starts its table at the graph's current table. The
later processors (`BreakingPointRemover`, `HorizontalGraphCompactor`,
`FinalSplineBendpointsCalculator`) access that table with `getSplineSegment`/`modifySplineSegment`.
`SPLINE_NS_PORT_Y_COORD` is a *port* property in Java/Rust (set by `NorthSouthPortPostprocessor`)
and is read through `splineNsPortYCoordOf`.

## Rust vs Java
Rust uses insertion-ordered `Vec`s where Java uses `HashSet`s (up/down hyperedge candidates,
segment ports and edges) and `getSplinePath` stops at the first edge without a segment (Java
throws a `NullPointerException`); the Rust behaviour is kept. The only Lean deviation: the
successor walks of `getEdgeChain`/`getSplinePath` stop at a repeated edge where Rust and Java
never terminate.
-/
namespace Elk.Alg.Layered.P5Edges.Splines

open Elk.Graph Elk.Core Elk.Core.Alg Elk.Core.Math Elk.Core.Options Elk.Core.Util Elk.Alg.Layered
  Elk.Alg.Layered.Graph Elk.Alg.Layered.Options Elk.Alg.Layered.Intermediate LayeredM

namespace SplineEdgeRouter

/-- `MAX_VERTICAL_DIFF_FOR_STRAIGHT` (`0.2`): an edge is straight if source and target differ less in y. -/
def MAX_VERTICAL_DIFF_FOR_STRAIGHT : Float := 0.2
/-- `SPLINE_DIMENSION` (`3`): default dimension of an edge spline. -/
def SPLINE_DIMENSION : Nat := 3

/-- `isStraight(firstY, secondY)`. -/
def isStraight (firstY secondY : Float) : Bool := (firstY - secondY).abs < MAX_VERTICAL_DIFF_FOR_STRAIGHT

/-- `isNormalNode(node)`: `NORMAL` and `BREAKING_POINT` nodes count as normal. -/
def isNormalNode (node : LNode) : Bool :=
  match node.type with
  | .normal | .breakingPoint => true
  | _ => false

/-- `isQualifiedAsStartingNode(node)`: nodes whose edges may start a spline chain (not long-edge or
label dummies). -/
def isQualifiedAsStartingNode (node : LNode) : Bool :=
  match node.type with
  | .normal | .northSouthPort | .externalPort | .breakingPoint => true
  | _ => false

/-- `PolylineEdgeRouter.PRED_EXTERNAL_WEST_OR_EAST_PORT` (Rust `is_external_west_or_east_port`).
TODO(dedupe-polyline): local copy until `PolylineEdgeRouter` is ported. -/
def isExternalWestOrEastPort (node : LNode) : Bool :=
  node.type == .externalPort && (node.internal.extPortSide == .west || node.internal.extPortSide == .east)

end SplineEdgeRouter

/-- `LPort.getAbsoluteAnchor().y`, `0.0` for an unowned port (Rust `.map(|a| a.y).unwrap_or(0.0)`):
the y sum of `LGraphArena.portAbsoluteAnchor` without building the vector. -/
def absoluteAnchorY (a : LGraphArena) (port : LPortId) : Float :=
  let pt := a.port port
  match pt.owner with
  | some owner => (a.node owner).position.y + pt.position.y + pt.anchor.y
  | none => 0.0

/-- `port.getProperty(InternalProperties.SPLINE_NS_PORT_Y_COORD)` (`LPortInternals.splineNsPortYCoord`). -/
def splineNsPortYCoordOf (p : LPort) : Option Float := p.internal.splineNsPortYCoord

/-- Reads the spline segment `id` of `graph`'s persisted segment table
(`LGraphInternals.splineSegments`, Rust `SplineSegmentRef::lock`). -/
def getSplineSegment (graph : LGraphId) (id : SplineSegmentId) : LayeredM SplineSegment := do
  return (← getGraph graph).internal.splineSegments[id.idx]!

/-- Updates the spline segment `id` of `graph`'s segment table in place (Rust: mutation through the
shared `SplineSegmentRef`); out-of-range ids are ignored. -/
def modifySplineSegment (graph : LGraphId) (id : SplineSegmentId) (f : SplineSegment → SplineSegment) :
    LayeredM Unit :=
  modifyGraph graph fun g =>
    { g with internal := { g.internal with splineSegments := g.internal.splineSegments.modifyIn id.idx f } }

namespace SplineSegment

/-- `anchorY(port)`: for northern/southern ports the y of the removed north/south dummy
(`SPLINE_NS_PORT_Y_COORD`, falling back to the absolute anchor like Rust), else the absolute anchor y. -/
def anchorY (a : LGraphArena) (port : LPortId) : Float :=
  let pt := a.port port
  let absY := absoluteAnchorY a port
  if pt.side == .north || pt.side == .south then (splineNsPortYCoordOf pt).getD absY else absY

/-- `addEdge(edge)`: adds the edge (once) and records its `EdgeInformation`. -/
def addEdge (a : LGraphArena) (s : SplineSegment) (edge : LEdgeId) : SplineSegment :=
  if s.edges.contains edge then s
  else
    let s := { s with edges := s.edges.push edge }
    let ed := a.edge edge
    let info : EdgeInformation := match ed.source, ed.target with
      | some sp, some tp =>
        let ownerNormal (p : LPortId) : Bool :=
          ((a.port p).owner.map fun n => SplineEdgeRouter.isNormalNode (a.node n)).getD false
        { startY := anchorY a sp, endY := anchorY a tp,
          normalSourceNode := ownerNormal sp, normalTargetNode := ownerNormal tp,
          invertedLeft := (a.port sp).side == .west, invertedRight := (a.port tp).side == .east }
      | _, _ => {}
    { s with edgeInformation := s.edgeInformation.push (edge, info) }

/-- Adds a port to the left or right port list. -/
private def insertPortOnSide (s : SplineSegment) (side : SideToProcess) (port : LPortId) : SplineSegment :=
  match side with
  | .left => { s with leftPorts := insertUniquePort s.leftPorts port }
  | .right => { s with rightPorts := insertUniquePort s.rightPorts port }

/-- `SplineSegment(singlePort, edges, sourceSide)` (Rust `new_hyper_edge`): a 1:n hyperedge from
`singlePort`; `edges` pairs each edge with the side of its other port. -/
def newHyperEdge (a : LGraphArena) (singlePort : LPortId) (edges : Array (SideToProcess × LEdgeId))
    (sourceSide : SideToProcess) : SplineSegment := Id.run do
  let mut s : SplineSegment := insertPortOnSide {} sourceSide singlePort
  let mut yMinTarget := Float.posInf
  let mut yMaxTarget := Float.negInf
  for (side, edge) in edges do
    let ed := a.edge edge
    let (some sourcePort, some targetPort) := (ed.source, ed.target) | continue
    let tgtPort := if sourcePort == singlePort then targetPort else sourcePort
    s := insertPortOnSide s side tgtPort
    let yPosTarget := anchorY a tgtPort
    yMinTarget := fmin yMinTarget yPosTarget
    yMaxTarget := fmax yMaxTarget yPosTarget
  let yPosSingle := anchorY a singlePort
  s := s.setRelevantPositions yPosSingle yMinTarget yMaxTarget
  for (_, edge) in edges do
    s := addEdge a s edge
  return { s with isStraight := false }

/-- `SplineSegment(edge, sourceSide, targetSide)` (Rust `new_single_edge`): a segment for one edge,
straight if both ends are (almost) at the same height. -/
def newSingleEdge (a : LGraphArena) (edge : LEdgeId) (sourceSide targetSide : SideToProcess) : SplineSegment :=
  let ed := a.edge edge
  match ed.source, ed.target with
  | some sourcePort, some targetPort =>
    let s := insertPortOnSide {} sourceSide sourcePort
    let s := insertPortOnSide s targetSide targetPort
    let s := addEdge a s edge
    let sourceY := anchorY a sourcePort
    let targetY := anchorY a targetPort
    let s := s.setRelevantPositions sourceY targetY targetY
    { s with isStraight := SplineEdgeRouter.isStraight sourceY targetY }
  | _, _ => {}

end SplineSegment

namespace SplineEdgeRouter

/-- `BASELINE_PROCESSING_ADDITIONS`: `FINAL_SPLINE_BENDPOINTS_CALCULATOR` after P5,
`INVERTED_PORT_PROCESSOR` before P3. -/
def BASELINE_PROCESSING_ADDITIONS : LayeredProcessorConfiguration :=
  ((LayoutProcessorConfiguration.create : LayeredProcessorConfiguration)
    |>.addAfter .p5EdgeRouting .finalSplineBendpointsCalculator)
    |>.addBefore .p3NodeOrdering .invertedPortProcessor

/-- `SELF_LOOP_PROCESSING_ADDITIONS`. -/
def SELF_LOOP_PROCESSING_ADDITIONS : LayeredProcessorConfiguration :=
  let c := ((LayoutProcessorConfiguration.create : LayeredProcessorConfiguration)
    |>.addBefore .p1CycleBreaking .selfLoopPreprocessor)
    |>.addAfter .p5EdgeRouting .selfLoopPostprocessor
  let c := c.before .p4NodePlacement
  -- `before` selected the slot, so `add` cannot fail
  match c.add .selfLoopPortRestorer >>= (·.add .selfLoopRouter) with
  | .ok c => c
  | .error _ => c

/-- `CENTER_EDGE_LABEL_PROCESSING_ADDITIONS`. -/
def CENTER_EDGE_LABEL_PROCESSING_ADDITIONS : LayeredProcessorConfiguration :=
  ((((LayoutProcessorConfiguration.create : LayeredProcessorConfiguration)
    |>.addBefore .p2Layering .labelDummyInserter)
    |>.addBefore .p4NodePlacement .labelDummySwitcher)
    |>.addBefore .p4NodePlacement .labelSideSelector)
    |>.addAfter .p5EdgeRouting .labelDummyRemover

/-- `NORTH_SOUTH_PORT_PROCESSING_ADDITIONS`. -/
def NORTH_SOUTH_PORT_PROCESSING_ADDITIONS : LayeredProcessorConfiguration :=
  ((LayoutProcessorConfiguration.create : LayeredProcessorConfiguration)
    |>.addBefore .p3NodeOrdering .northSouthPortPreprocessor)
    |>.addBefore .p5EdgeRouting .northSouthPortPostprocessor

/-- `END_EDGE_LABEL_PROCESSING_ADDITIONS`. -/
def END_EDGE_LABEL_PROCESSING_ADDITIONS : LayeredProcessorConfiguration :=
  (((LayoutProcessorConfiguration.create : LayeredProcessorConfiguration)
    |>.addBefore .p4NodePlacement .labelSideSelector)
    |>.addBefore .p4NodePlacement .endLabelPreprocessor)
    |>.addAfter .p5EdgeRouting .endLabelPostprocessor

/-- `getLayoutProcessorConfiguration(graph)`: the baseline plus the additions selected by the
graph's `GRAPH_PROPERTIES`. -/
def layoutProcessorConfiguration (graphProperties : EnumSet GraphProperties) : LayeredProcessorConfiguration := Id.run do
  let mut configuration := (LayoutProcessorConfiguration.create : LayeredProcessorConfiguration).addAll BASELINE_PROCESSING_ADDITIONS
  if graphProperties.contains .selfLoops then
    configuration := configuration.addAll SELF_LOOP_PROCESSING_ADDITIONS
  if graphProperties.contains .centerLabels then
    configuration := configuration.addAll CENTER_EDGE_LABEL_PROCESSING_ADDITIONS
  if graphProperties.contains .northSouthPorts then
    configuration := configuration.addAll NORTH_SOUTH_PORT_PROCESSING_ADDITIONS
  if graphProperties.contains .endLabels then
    configuration := configuration.addAll END_EDGE_LABEL_PROCESSING_ADDITIONS
  return configuration

/-- Rust `SplineEdgeRouter` fields plus the segment table and the dependency id counter. -/
structure State where
  /-- Segment table: `SplineSegmentId.idx` indexes it (creation order = `all_spline_segments`). -/
  segments : Array SplineSegment := #[]
  /-- Number of dependencies created so far (the next `DependencyId`). -/
  dependencyCount : Nat := 0
  /-- `edges_remaining_layer`. -/
  edgesRemainingLayer : Array LEdgeId := #[]
  /-- Membership of `edgesRemainingLayer`. -/
  edgesRemainingSet : Std.HashSet LEdgeId := {}
  /-- `spline_segments_layer`. -/
  splineSegmentsLayer : Array SplineSegmentId := #[]
  /-- `left_ports_layer`. -/
  leftPortsLayer : Array LPortId := #[]
  /-- Membership of `leftPortsLayer`. -/
  leftPortsSet : Std.HashSet LPortId := {}
  /-- `right_ports_layer`. -/
  rightPortsLayer : Array LPortId := #[]
  /-- Membership of `rightPortsLayer`. -/
  rightPortsSet : Std.HashSet LPortId := {}
  /-- `self_loops_layer` (collected, unused by the router like in Rust). -/
  selfLoopsLayer : Array LEdgeId := #[]
  /-- `start_edges`: edges whose source node may start a spline. -/
  startEdges : Array LEdgeId := #[]
  /-- `all_spline_segments`. -/
  allSplineSegments : Array SplineSegmentId := #[]
  /-- `edge_to_segment_map`. -/
  edgeToSegmentMap : Std.HashMap LEdgeId SplineSegmentId := {}
  /-- `successing_edge`: the next edge of a long edge. -/
  successingEdge : Std.HashMap LEdgeId LEdgeId := {}
  /-- The `random` of `process`. -/
  random : Random := Random.ofInt 0
  /-- Whether `random` is the graph's (shared) generator. -/
  sharedRandom : Bool := false
  /-- The routes stored as `SPLINE_ROUTE_START` (start edge → segment chain), in `startEdges` order. -/
  routeStarts : Array (LEdgeId × Array SplineSegmentId) := #[]
  deriving Inhabited

/-- Router monad. -/
abbrev RouterM := StateT State LayeredM

/-- The segment `id`. -/
@[inline] def getSegment (id : SplineSegmentId) : RouterM SplineSegment := do
  return (← get).segments[id.idx]!

/-- Updates the segment `id` in place. -/
@[inline] def modifySegment (id : SplineSegmentId) (f : SplineSegment → SplineSegment) : RouterM Unit :=
  modify fun s => { s with segments := s.segments.modifyIn id.idx f }

/-- Appends a segment to the table. -/
def addSegment (segment : SplineSegment) : RouterM SplineSegmentId :=
  modifyGet fun s => (⟨s.segments.size⟩, { s with segments := s.segments.push segment })

/-- `insert_unique_port(left_ports_layer, port)`. -/
def insertLeftPort (port : LPortId) : RouterM Unit := modify fun s =>
  if s.leftPortsSet.contains port then s
  else { s with leftPortsLayer := s.leftPortsLayer.push port, leftPortsSet := s.leftPortsSet.insert port }

/-- `insert_unique_port(right_ports_layer, port)`. -/
def insertRightPort (port : LPortId) : RouterM Unit := modify fun s =>
  if s.rightPortsSet.contains port then s
  else { s with rightPortsLayer := s.rightPortsLayer.push port, rightPortsSet := s.rightPortsSet.insert port }

/-- `edges_remaining_layer.push(edge)`. -/
def pushRemaining (edge : LEdgeId) : RouterM Unit := modify fun s =>
  { s with edgesRemainingLayer := s.edgesRemainingLayer.push edge, edgesRemainingSet := s.edgesRemainingSet.insert edge }

/-- `remove_arc(edges_remaining_layer, edge)`: removes the (single) occurrence. -/
def removeRemaining (edge : LEdgeId) : RouterM Unit := modify fun s =>
  if s.edgesRemainingSet.contains edge then
    { s with edgesRemainingLayer := s.edgesRemainingLayer.erase edge, edgesRemainingSet := s.edgesRemainingSet.erase edge }
  else s

/-- `findAndAddSuccessor(edge)`: for an edge into a dummy node, the first outgoing edge of that node
continues the long edge. -/
def findAndAddSuccessor (edge : LEdgeId) : RouterM Unit := do
  let next? ← withArena fun a =>
    match (a.edge edge).target.bind (fun p => (a.port p).owner) with
    | none => none
    | some targetNode =>
      if isNormalNode (a.node targetNode) then none else (a.nodeOutgoingEdges targetNode)[0]?
  if let some next := next? then
    modify fun s => { s with successingEdge := s.successingEdge.insert edge next }

/-- Registers one outgoing edge of a left-layer `EAST` port or a right-layer `WEST` port
(the shared loop body of Rust `clear_then_fill_mappings`). -/
def fillEdge (edge : LEdgeId) (leftLayer rightLayer : Option LayerId) : RouterM Unit := do
  if ← withArena (·.edgeIsSelfLoop edge) then return
  pushRemaining edge
  findAndAddSuccessor edge
  let ed ← getEdge edge
  let qualified ← withArena fun a =>
    ((ed.source.bind fun p => (a.port p).owner).map fun n => isQualifiedAsStartingNode (a.node n)).getD false
  if qualified then
    modify fun s => { s with startEdges := s.startEdges.push edge }
  let targetLayer ← withArena fun a =>
    (ed.target.bind fun p => (a.port p).owner).bind fun n => (a.node n).layer
  if let (some targetLayer, some targetPort) := (targetLayer, ed.target) then
    if rightLayer == some targetLayer then
      insertRightPort targetPort
      return
    if leftLayer == some targetLayer then
      insertLeftPort targetPort
      return
  -- unhandled situation (probably incoming and outgoing edges on the same port)
  removeRemaining edge

/-- `clearThenFillMappings(leftLayer, rightLayer)`: collects the ports, edges and self loops of a
pair of layers (left: `EAST` ports, right: `WEST` ports, in node and port order). -/
def clearThenFillMappings (leftLayer rightLayer : Option LayerId) : RouterM Unit := do
  modify fun s => { s with
    leftPortsLayer := #[], leftPortsSet := {}, rightPortsLayer := #[], rightPortsSet := {},
    edgesRemainingLayer := #[], edgesRemainingSet := {}, splineSegmentsLayer := #[], selfLoopsLayer := #[] }
  if let some left := leftLayer then
    for node in (← getLayer left).nodes do
      let ports ← withArena (·.nodePortsBySide node .east)
      for port in ports do
        insertLeftPort port
        for edge in (← getPort port).outgoingEdges do
          fillEdge edge leftLayer rightLayer
  if let some right := rightLayer then
    for node in (← getLayer right).nodes do
      let allPorts := (← getNode node).ports
      let westPorts ← withArena (·.nodePortsBySide node .west)
      for port in allPorts do
        for edge in (← getPort port).outgoingEdges do
          if ← withArena (·.edgeIsSelfLoop edge) then
            modify fun s => { s with selfLoopsLayer := s.selfLoopsLayer.push edge }
      for port in westPorts do
        insertRightPort port
        for edge in (← getPort port).outgoingEdges do
          fillEdge edge leftLayer rightLayer

/-- `computeSloppySpacing(rightLayer, edgeEdgeSpacing, nodeNodeSpacing, sloppyLayerSpacingFactor)`:
the layer gap that limits the slope of the edges into `rightLayer` (sloppy routing). -/
def computeSloppySpacing (rightLayer : LayerId) (edgeEdgeSpacing nodeNodeSpacing sloppyLayerSpacingFactor : Float) :
    LayeredM Float := do
  let mut maxVertDiff := 0.0
  for node in (← getLayer rightLayer).nodes do
    let incomingEdges ← withArena (·.nodeIncomingEdges node)
    let mut maxCurrInputYDiff := 0.0
    for incomingEdge in incomingEdges do
      let (sourcePos, targetPos) ← withArena fun a =>
        let ed := a.edge incomingEdge
        ((ed.source.map (absoluteAnchorY a ·)).getD 0.0, (ed.target.map (absoluteAnchorY a ·)).getD 0.0)
      maxCurrInputYDiff := fmax maxCurrInputYDiff (targetPos - sourcePos).abs
    maxVertDiff := fmax maxVertDiff maxCurrInputYDiff
  return sloppyLayerSpacingFactor * fmin (edgeEdgeSpacing / nodeNodeSpacing) 1.0 * maxVertDiff

/-- `createSplineSegments(edges, leftPorts, rightPorts, hyperEdges)`: a single-edge segment for every
remaining edge. -/
def createSplineSegments : RouterM Unit := do
  for edge in (← get).edgesRemainingLayer do
    let ed ← getEdge edge
    let (some sourcePort, some targetPort) := (ed.source, ed.target) | continue
    let st ← get
    let sourceSide ←
      if st.leftPortsSet.contains sourcePort then pure SideToProcess.left
      else if st.rightPortsSet.contains sourcePort then pure SideToProcess.right
      else throw (IO.userError "java.lang.IllegalArgumentException: Source port must be in one of the port sets.")
    let targetSide ←
      if st.leftPortsSet.contains targetPort then pure SideToProcess.left
      else if st.rightPortsSet.contains targetPort then pure SideToProcess.right
      else throw (IO.userError "java.lang.IllegalArgumentException: Target port must be in one of the port sets.")
    let segment ← withArena fun a => SplineSegment.newSingleEdge a edge sourceSide targetSide
    let id ← addSegment segment
    modify fun s => { s with edgeToSegmentMap := s.edgeToSegmentMap.insert edge id,
                             splineSegmentsLayer := s.splineSegmentsLayer.push id }

/-- Creates the hyperedge segment of `singlePort` for the collected edges (Rust inner block of
`create_spline_segments_for_hyper_edges`). -/
def createHyperEdgeSegment (singlePort : LPortId) (edges : Array (SideToProcess × LEdgeId))
    (sideToProcess : SideToProcess) : RouterM Unit := do
  let segment ← withArena fun a => SplineSegment.newHyperEdge a singlePort edges sideToProcess
  let id ← addSegment segment
  for (_, edge) in edges do
    modify fun s => { s with edgeToSegmentMap := s.edgeToSegmentMap.insert edge id }
    removeRemaining edge
  modify fun s => { s with splineSegmentsLayer := s.splineSegmentsLayer.push id }

/-- `createSplineSegmentsForHyperEdges(leftPorts, rightPorts, sideToProcess, reversed, …)`: for each
port of the processed side, the remaining (`REVERSED == reversed`), non-straight edges going up
resp. down form a hyperedge if there are at least two of them. -/
def createSplineSegmentsForHyperEdges (leftPorts rightPorts : Array LPortId) (leftSet : Std.HashSet LPortId)
    (sideToProcess : SideToProcess) (reversed : Bool) : RouterM Unit := do
  let portsToProcess := match sideToProcess with
    | .left => leftPorts
    | .right => rightPorts
  for singlePort in portsToProcess do
    let singlePortPosition ← withArena (absoluteAnchorY · singlePort)
    let connectedEdges := (← getPort singlePort).connectedEdges
    let mut upEdges : Array (SideToProcess × LEdgeId) := #[]
    let mut downEdges : Array (SideToProcess × LEdgeId) := #[]
    for edge in connectedEdges do
      let ed ← getEdge edge
      if ed.internal.reversed != reversed then continue
      if !(← get).edgesRemainingSet.contains edge then continue
      let (some sourcePort, some targetPort) := (ed.source, ed.target) | continue
      let otherPort := if targetPort == singlePort then sourcePort else targetPort
      let otherPortPosition ← withArena (absoluteAnchorY · otherPort)
      if isStraight otherPortPosition singlePortPosition then continue
      let side := if leftSet.contains otherPort then SideToProcess.left else SideToProcess.right
      if otherPortPosition < singlePortPosition then
        upEdges := upEdges.push (side, edge)
      else
        downEdges := downEdges.push (side, edge)
    if upEdges.size > 1 then
      createHyperEdgeSegment singlePort upEdges sideToProcess
    if downEdges.size > 1 then
      createHyperEdgeSegment singlePort downEdges sideToProcess

/-! ### Dependency graph, cycle breaking and ranking of one layer gap

`createDependency`, `breakCycles` and `topologicalNumbering` run on arrays indexed by the position
of a segment in `splineSegmentsLayer` (its *local index*) and by the position of a dependency in the
gap's creation order (Rust keeps marks, weights and ranks in the `SplineSegment`s and `Dependency`s).
The anchors and hyperedge ranges the dependencies need are read once per segment (`GapSegments`; the
arena does not change while a gap is ranked); the results are written back to the segments once per
gap (`writeGapRanking`). Every loop visits segments and dependencies in Rust's order (segment list
order, dependency list order). The queues are arrays with a head index (Rust `VecDeque`; a segment
may be queued more than once); Rust's order-preserving `unprocessed` list is a flag per segment plus
the list `order` of the segments not yet known to be removed (compacted when more than half of it is
stale), so the max-outflow scan visits the unprocessed segments in list order. -/

/-- The segment data of one layer gap read by `createDependency` and `topologicalNumbering`, per
local index `i`: the hyperedge y-range and the absolute anchor y values of the right ports
(`ys[starts[2i]:starts[2i+1]]`) and the left ports (`ys[starts[2i+1]:starts[2i+2]]`), list order. -/
structure GapSegments where
  /-- `hyperEdgeTopYPos`. -/
  tops : FloatArray
  /-- `hyperEdgeBottomYPos`. -/
  bottoms : FloatArray
  /-- Port anchor y values (see the structure doc). -/
  ys : FloatArray
  /-- Range boundaries into `ys` (`2 * n + 1` entries). -/
  starts : Array Nat
  /-- `leftPorts.isEmpty()`. -/
  leftEmpty : Array Bool

/-- Appends the absolute anchor y values of `ports` (list order) to `ys`. -/
def pushAnchorYs (a : LGraphArena) (ports : Array LPortId) (ys : FloatArray) : FloatArray :=
  ports.foldl (fun ys p => ys.push (absoluteAnchorY a p)) ys

/-- Reads the `GapSegments` of the segments `ids` (local index = position in `ids`). -/
def GapSegments.read (a : LGraphArena) (segments : Array SplineSegment) (ids : Array SplineSegmentId) :
    GapSegments :=
  let n := ids.size
  ids.foldl (init := ⟨FloatArray.emptyWithCapacity n, FloatArray.emptyWithCapacity n,
      FloatArray.emptyWithCapacity (2 * n), (Array.emptyWithCapacity (2 * n + 1)).push 0,
      Array.emptyWithCapacity n⟩) fun gs id =>
    let s := segments[id.idx]!
    match gs with
    | ⟨tops, bottoms, ys, starts, leftEmpty⟩ =>
      let ys := pushAnchorYs a s.rightPorts ys
      let starts := starts.push ys.size
      let ys := pushAnchorYs a s.leftPorts ys
      ⟨tops.push s.hyperEdgeTopYPos, bottoms.push s.hyperEdgeBottomYPos, ys, starts.push ys.size,
        leftEmpty.push s.leftPorts.isEmpty⟩

/-- `acc` plus the crossing counter contribution of the anchors `ys[k:stop]` (the right ports
`ys[k:mid]` count `+1`, the left ports `-1`) that lie between `top` and `bottom`
(`SplinesMath.isBetween`). -/
partial def crossingCounter (ys : FloatArray) (k mid stop : Nat) (top bottom : Float) (acc : Int) : Int :=
  if k < stop then
    if SplinesMath.isBetween ys[k]! top bottom then
      crossingCounter ys (k + 1) mid stop top bottom (if k < mid then acc + 1 else acc - 1)
    else crossingCounter ys (k + 1) mid stop top bottom acc
  else acc

/-- `Dependency.source`, `Dependency.target` and `Dependency.weight` of the dependencies of one gap, in
creation order (`source`/`target` are local segment indices). -/
structure GapDepTable where
  source : Array Nat
  target : Array Nat
  weight : Array Int

/-- `createDependency(edge0, edge1)` for the local segment `i` (`edge0`, hyperedge range `top0`–
`bottom0`, anchors `ys[r0:l0]`/`ys[l0:e0]`) and the segments `j, j + 1, …` (`edge1`): a weighted
dependency between two vertically overlapping segments (two zero-weight dependencies if the order
does not matter). The crossing counter of a segment is the number of its right ports minus the
number of its left ports whose anchor lies within the other segment's hyperedge y-range. -/
partial def dependencyRow (gs : GapSegments) (i : Nat) (top0 bottom0 : Float) (r0 l0 e0 j : Nat)
    (t : GapDepTable) : GapDepTable :=
  if j < gs.tops.size then
    let top1 := gs.tops[j]!
    let bottom1 := gs.bottoms[j]!
    if top0 > bottom1 || top1 > bottom0 then dependencyRow gs i top0 bottom0 r0 l0 e0 (j + 1) t
    else
      let edge0Counter := crossingCounter gs.ys r0 l0 e0 top1 bottom1 0
      let edge1Counter := crossingCounter gs.ys gs.starts[2 * j]! gs.starts[2 * j + 1]! gs.starts[2 * j + 2]!
        top0 bottom0 0
      match t with
      | ⟨src, tgt, wgt⟩ =>
        let t : GapDepTable :=
          if edge0Counter < edge1Counter then ⟨src.push i, tgt.push j, wgt.push (edge1Counter - edge0Counter)⟩
          else if edge1Counter < edge0Counter then ⟨src.push j, tgt.push i, wgt.push (edge0Counter - edge1Counter)⟩
          else ⟨(src.push j).push i, (tgt.push i).push j, (wgt.push 0).push 0⟩
        dependencyRow gs i top0 bottom0 r0 l0 e0 (j + 1) t
  else t

/-- `createDependency` for every pair `i < j` of the local segments from `i` on, pairs in list order. -/
partial def dependencyRows (gs : GapSegments) (i : Nat) (t : GapDepTable) : GapDepTable :=
  if i + 1 < gs.tops.size then
    let t := dependencyRow gs i gs.tops[i]! gs.bottoms[i]! gs.starts[2 * i]! gs.starts[2 * i + 1]!
      gs.starts[2 * i + 2]! (i + 1) t
    dependencyRows gs (i + 1) t
  else t

/-- The dependency lists of the segments `0 … n - 1`: the dependencies whose `owner` (source or target)
is the segment, in creation order, as ids `base + position` (Rust `new Dependency` appends to the
source's `outgoing` and the target's `incoming` list). -/
def dependencyLists (n base : Nat) (owner : Array Nat) : Array (Array DependencyId) :=
  let counts := owner.foldl (fun counts x => counts.modify x (· + 1)) (Array.replicate n 0)
  owner.size.fold (init := counts.map fun c => Array.emptyWithCapacity c) fun d h lists =>
    lists.modifyIn owner[d] (·.push ⟨base + d⟩)

/-- The dependencies of one layer gap: the table and the per-segment `outgoing`/`incoming` lists of
dependency ids (`id.idx - base` is the position in the table). -/
structure GapDeps where
  /-- The id of the first dependency of the gap. -/
  base : Nat
  /-- `Dependency.source` (local index) per position. -/
  source : Array Nat
  /-- `Dependency.target` (local index) per position. -/
  target : Array Nat
  /-- `Dependency.weight` per position. -/
  weight : Array Int
  /-- `SplineSegment.outgoing` per local segment. -/
  outgoing : Array (Array DependencyId)
  /-- `SplineSegment.incoming` per local segment. -/
  incoming : Array (Array DependencyId)

/-- The dependencies of the gap's segments (`GapSegments`), ids from `base`. -/
def createDependencies (gs : GapSegments) (base : Nat) : GapDeps :=
  let n := gs.tops.size
  match dependencyRows gs 0 ⟨#[], #[], #[]⟩ with
  | ⟨src, tgt, wgt⟩ =>
    let outgoing := dependencyLists n base src
    let incoming := dependencyLists n base tgt
    ⟨base, src, tgt, wgt, outgoing, incoming⟩

/-- Working state of `breakCycles` (per local segment). -/
structure CycleState where
  /-- `SplineSegment.mark`. -/
  mark : Array Int
  /-- `SplineSegment.inweight`. -/
  inweight : Array Int
  /-- `SplineSegment.outweight`. -/
  outweight : Array Int
  /-- `sources` queue (`sourcesHead` = front). -/
  sources : Array Nat
  sourcesHead : Nat
  /-- `sinks` queue (`sinksHead` = front). -/
  sinks : Array Nat
  sinksHead : Nat
  /-- Membership in Rust's `unprocessed` list. -/
  unprocessed : Array Bool
  /-- Number of segments in `unprocessed`. -/
  unprocessedCount : Nat
  /-- `unprocessed` in list order (may still hold removed segments). -/
  order : Array Nat
  /-- `next_left` (marks of sources and max-outflow segments, counting up). -/
  nextLeft : Int
  /-- `next_right` (marks of sinks, counting down). -/
  nextRight : Int

/-- `acc` plus the weights of the dependencies `deps[k:]`. -/
partial def sumWeights (g : GapDeps) (deps : Array DependencyId) (k : Nat) (acc : Int) : Int :=
  if h : k < deps.size then sumWeights g deps (k + 1) (acc + g.weight[deps[k].idx - g.base]!) else acc

/-- The initial state of `breakCycles`: marks `-1, -2, …`, the in/out weights and the initial sinks
(no outgoing weight) and sources (else no incoming weight), both in segment order. -/
def initCycleBreaking (g : GapDeps) : CycleState :=
  let n := g.outgoing.size
  let inweight := g.incoming.map fun deps => sumWeights g deps 0 0
  let outweight := g.outgoing.map fun deps => sumWeights g deps 0 0
  { mark := (Array.range n).map fun (i : Nat) => -1 - (i : Int), inweight, outweight
    sources := (Array.range n).filter fun i => outweight[i]! != 0 && inweight[i]! == 0, sourcesHead := 0
    sinks := (Array.range n).filter fun i => outweight[i]! == 0, sinksHead := 0
    unprocessed := Array.replicate n true, unprocessedCount := n, order := Array.range n
    nextLeft := (n : Int) + 1, nextRight := (n : Int) - 1 }

/-- Outgoing half of `updateNeighbors`: for the dependencies `deps[k:]` of the processed segment,
removes the weight from the unmarked targets (`inweight`) and queues those that became sources. -/
partial def updateTargets (g : GapDeps) (deps : Array DependencyId) (mark outweight : Array Int) (k : Nat)
    (inweight : Array Int) (sources : Array Nat) : Array Int × Array Nat :=
  if h : k < deps.size then
    let p := deps[k].idx - g.base
    let weight := g.weight[p]!
    let target := g.target[p]!
    if weight > 0 && mark[target]! < 0 then
      let w := inweight[target]! - weight
      let sources := if w <= 0 && outweight[target]! > 0 then sources.push target else sources
      updateTargets g deps mark outweight (k + 1) (inweight.set! target w) sources
    else updateTargets g deps mark outweight (k + 1) inweight sources
  else (inweight, sources)

/-- Incoming half of `updateNeighbors`: removes the weight from the unmarked sources of `deps[k:]`
(`outweight`) and queues those that became sinks. -/
partial def updateSources (g : GapDeps) (deps : Array DependencyId) (mark inweight : Array Int) (k : Nat)
    (outweight : Array Int) (sinks : Array Nat) : Array Int × Array Nat :=
  if h : k < deps.size then
    let p := deps[k].idx - g.base
    let weight := g.weight[p]!
    let source := g.source[p]!
    if weight > 0 && mark[source]! < 0 then
      let w := outweight[source]! - weight
      let sinks := if w <= 0 && inweight[source]! > 0 then sinks.push source else sinks
      updateSources g deps mark inweight (k + 1) (outweight.set! source w) sinks
    else updateSources g deps mark inweight (k + 1) outweight sinks
  else (outweight, sinks)

/-- Rust `remove_segment(unprocessed, edge)`, `edge.mark = m` and `updateNeighbors(edge, sources,
sinks)` (the targets' half first; the sources' half sees the updated in-weights). -/
def processSegment (g : GapDeps) (st : CycleState) (edge : Nat) (m : Int) : CycleState :=
  match st with
  | ⟨mark, inweight, outweight, sources, sourcesHead, sinks, sinksHead, unprocessed, unprocessedCount, order,
      nextLeft, nextRight⟩ =>
    let wasUnprocessed := unprocessed[edge]!
    let unprocessed := if wasUnprocessed then unprocessed.set! edge false else unprocessed
    let unprocessedCount := if wasUnprocessed then unprocessedCount - 1 else unprocessedCount
    let mark := mark.set! edge m
    let (inweight, sources) := updateTargets g g.outgoing[edge]! mark outweight 0 inweight sources
    let (outweight, sinks) := updateSources g g.incoming[edge]! mark inweight 0 outweight sinks
    ⟨mark, inweight, outweight, sources, sourcesHead, sinks, sinksHead, unprocessed, unprocessedCount, order,
      nextLeft, nextRight⟩

/-- `while let Some(sink) = sinks.pop_front()`: processes the queued sinks (marks counting down). -/
partial def drainSinks (g : GapDeps) (st : CycleState) : CycleState :=
  if h : st.sinksHead < st.sinks.size then
    let sink := st.sinks[st.sinksHead]
    let m := st.nextRight
    drainSinks g (processSegment g { st with sinksHead := st.sinksHead + 1, nextRight := m - 1 } sink m)
  else st

/-- `while let Some(source) = sources.pop_front()`: processes the queued sources (marks counting up). -/
partial def drainSources (g : GapDeps) (st : CycleState) : CycleState :=
  if h : st.sourcesHead < st.sources.size then
    let source := st.sources[st.sourcesHead]
    let m := st.nextLeft
    drainSources g (processSegment g { st with sourcesHead := st.sourcesHead + 1, nextLeft := m + 1 } source m)
  else st

/-- The unprocessed segments among `order[k:]` with the maximal `outweight - inweight` (list order). -/
partial def maxOutflowSegments (st : CycleState) (k : Nat) (maxOutflow : Int) (maxEdges : Array Nat) :
    Array Nat :=
  if h : k < st.order.size then
    let i := st.order[k]
    if st.unprocessed[i]! then
      let outflow := st.outweight[i]! - st.inweight[i]!
      if outflow > maxOutflow then maxOutflowSegments st (k + 1) outflow #[i]
      else if outflow == maxOutflow then maxOutflowSegments st (k + 1) maxOutflow (maxEdges.push i)
      else maxOutflowSegments st (k + 1) maxOutflow maxEdges
    else maxOutflowSegments st (k + 1) maxOutflow maxEdges
  else maxEdges

/-- Rust `i32::MIN`, the initial maximal outflow. -/
def I32_MIN : Int := -2147483648

/-- The main loop of `breakCycles` (`while !unprocessed.is_empty()`): sinks, then sources, then a
random segment of maximal outflow. Returns the state, the generator and whether it was drawn from. -/
partial def breakCyclesLoop (g : GapDeps) (st : CycleState) (random : Random) (drawn : Bool) :
    CycleState × Random × Bool :=
  if st.unprocessedCount == 0 then (st, random, drawn)
  else
    let st := drainSources g (drainSinks g st)
    -- drop the removed entries once they make up more than half of the scanned list
    let st := if st.order.size > 2 * st.unprocessedCount then
        { st with order := st.order.filter fun i => st.unprocessed[i]! }
      else st
    let maxEdges := maxOutflowSegments st 0 I32_MIN #[]
    if maxEdges.isEmpty then breakCyclesLoop g st random drawn
    else
      let (index, random) := random.nextInt (maxEdges.size : Int)
      let maxEdge := maxEdges[index.toNat]!
      let m := st.nextLeft
      breakCyclesLoop g (processSegment g { st with nextLeft := m + 1 } maxEdge m) random true

/-- `deps` without the entries `keep` rejects (list order). -/
@[inline] def keepDependencies (deps : Array DependencyId) (keep : DependencyId → Bool) : Array DependencyId :=
  deps.foldl (fun acc d => if keep d then acc.push d else acc) (Array.emptyWithCapacity deps.size)

/-- Reversal state of `breakCycles`' final step: the dependencies, which of them were removed with
weight 0, and which incoming lists hold removed entries. -/
structure ReversalState where
  deps : GapDeps
  dropped : Array Bool
  incomingStale : Array Bool

/-- The final step of `breakCycles` for the dependencies `deps[k:]` of one segment (its outgoing list
when its turn came): a dependency pointing from a higher to a lower mark is removed (weight 0,
`dropped`) or reversed (`source`/`target` swapped, appended to the new source's outgoing and the new
target's incoming list). `removed` tells whether an entry of the segment's list was removed.

Rust removes the dependency from its source's outgoing and its target's incoming list right away
(`retain`); here the lists keep the entry: the segment's outgoing list is compacted after its turn
(`reverseLeftwardDependencies`) and the incoming lists at the end, dropping the entries that were
removed with weight 0 or no longer start (end) at the list's segment. This is the same: entries leave
an outgoing list only during the turn of their source (which iterates a copy of the list), a reversed
dependency is never reversed again (its marks are increasing) and is appended to lists of other
segments only. -/
partial def reverseLeftward (mark : Array Int) (deps : Array DependencyId) (k : Nat) (st : ReversalState)
    (removed : Bool) : ReversalState × Bool :=
  if h : k < deps.size then
    let d := deps[k]
    match st with
    | ⟨⟨base, src, tgt, wgt, out, inc⟩, dropped, incomingStale⟩ =>
      let p := d.idx - base
      let s := src[p]!
      let t := tgt[p]!
      if mark[s]! > mark[t]! then
        let incomingStale := incomingStale.set! t true
        if wgt[p]! > 0 then
          reverseLeftward mark deps (k + 1)
            ⟨⟨base, src.set! p t, tgt.set! p s, wgt, out.modifyIn t (·.push d), inc.modifyIn s (·.push d)⟩,
              dropped, incomingStale⟩ true
        else
          reverseLeftward mark deps (k + 1)
            ⟨⟨base, src, tgt, wgt, out, inc⟩, dropped.set! p true, incomingStale⟩ true
      else reverseLeftward mark deps (k + 1) ⟨⟨base, src, tgt, wgt, out, inc⟩, dropped, incomingStale⟩ removed
  else (st, removed)

/-- `reverseLeftward` for the segments `i, i + 1, …` (list order); a segment's outgoing list drops
the removed entries right after its turn. -/
partial def reverseLeftwardDependencies (mark : Array Int) (i : Nat) (st : ReversalState) : ReversalState :=
  if h : i < st.deps.outgoing.size then
    let deps := st.deps.outgoing[i]
    match reverseLeftward mark deps 0 st false with
    | (st, false) => reverseLeftwardDependencies mark (i + 1) st
    | (⟨⟨base, src, tgt, wgt, out, inc⟩, dropped, incomingStale⟩, true) =>
      let out := out.modifyIn i fun list =>
        keepDependencies list fun d => src[d.idx - base]! == i && !dropped[d.idx - base]!
      reverseLeftwardDependencies mark (i + 1) ⟨⟨base, src, tgt, wgt, out, inc⟩, dropped, incomingStale⟩
  else st

/-- Drops the removed entries of the incoming lists marked `incomingStale` (see `reverseLeftward`). -/
def compactIncomingLists (st : ReversalState) : GapDeps :=
  match st with
  | ⟨⟨base, src, tgt, wgt, out, inc⟩, dropped, incomingStale⟩ =>
    let inc := inc.mapIdx fun x list =>
      if incomingStale[x]! then keepDependencies list fun d => tgt[d.idx - base]! == x && !dropped[d.idx - base]!
      else list
    ⟨base, src, tgt, wgt, out, inc⟩

/-- `breakCycles(edges, random)`: Eades–Lin–Smyth style marking (sinks get decreasing marks below
the segment count `n`, sources and the random max-outflow segments increasing marks above it; the
marks below `n` are then shifted by `n + 1`), then the leftward dependencies are removed or
reversed. Returns the dependencies, the cycle state, the generator and whether it was drawn from. -/
def breakCycles (g : GapDeps) (random : Random) : GapDeps × CycleState × Random × Bool :=
  let n := g.outgoing.size
  let (st, random, drawn) := breakCyclesLoop g (initCycleBreaking g) random false
  let markBase : Int := n
  let shiftBase : Int := (n : Int) + 1
  match st with
  | ⟨mark, inweight, outweight, sources, sourcesHead, sinks, sinksHead, unprocessed, unprocessedCount, order,
      nextLeft, nextRight⟩ =>
    let mark := mark.map fun m => if m < markBase then m + shiftBase else m
    let dependencyCount := g.source.size
    let g := compactIncomingLists
      (reverseLeftwardDependencies mark 0 ⟨g, Array.replicate dependencyCount false, Array.replicate n false⟩)
    (g, ⟨mark, inweight, outweight, sources, sourcesHead, sinks, sinksHead, unprocessed, unprocessedCount, order,
        nextLeft, nextRight⟩, random, drawn)

/-- Working state of `topologicalNumbering` (per local segment). -/
structure RankState where
  /-- `SplineSegment.rank`. -/
  rank : Array Int
  /-- `SplineSegment.inweight` (unprocessed incoming dependencies). -/
  inweight : Array Int
  /-- `SplineSegment.outweight` (unprocessed outgoing dependencies). -/
  outweight : Array Int
  /-- The queue (`sources`, later `rightward_targets`). -/
  queue : Array Nat
  /-- `max_rank`. -/
  maxRank : Int

/-- Longest-path step for the outgoing dependencies `deps[k:]` of a source of rank `edgeRank`. -/
partial def rankTargets (g : GapDeps) (deps : Array DependencyId) (edgeRank : Int) (k : Nat) (st : RankState) :
    RankState :=
  if h : k < deps.size then
    let target := g.target[deps[k].idx - g.base]!
    match st with
    | ⟨rank, inweight, outweight, queue, maxRank⟩ =>
      let r := max rank[target]! (edgeRank + 1)
      let w := inweight[target]! - 1
      rankTargets g deps edgeRank (k + 1)
        ⟨rank.set! target r, inweight.set! target w, outweight, if w == 0 then queue.push target else queue,
          max maxRank r⟩
  else st

/-- Processes the queued sources from `head` on (longest path from the sources). -/
partial def rankSources (g : GapDeps) (head : Nat) (st : RankState) : RankState :=
  if h : head < st.queue.size then
    let edge := st.queue[head]
    let edgeRank := st.rank[edge]!
    rankSources g (head + 1) (rankTargets g g.outgoing[edge]! edgeRank 0 st)
  else st

/-- Moves the sources without left ports of the incoming dependencies `deps[k:]` of a rightward
segment of rank `edgeRank` right (rank at most `edgeRank - 1`). -/
partial def rankRightwardSources (g : GapDeps) (leftEmpty : Array Bool) (deps : Array DependencyId)
    (edgeRank : Int) (k : Nat) (st : RankState) : RankState :=
  if h : k < deps.size then
    let source := g.source[deps[k].idx - g.base]!
    if !leftEmpty[source]! then rankRightwardSources g leftEmpty deps edgeRank (k + 1) st
    else
      match st with
      | ⟨rank, inweight, outweight, queue, maxRank⟩ =>
        let r := min rank[source]! (edgeRank - 1)
        let w := outweight[source]! - 1
        rankRightwardSources g leftEmpty deps edgeRank (k + 1)
          ⟨rank.set! source r, inweight, outweight.set! source w, if w == 0 then queue.push source else queue,
            maxRank⟩
  else st

/-- Processes the queued rightward targets from `head` on. -/
partial def rankRightward (g : GapDeps) (leftEmpty : Array Bool) (head : Nat) (st : RankState) : RankState :=
  if h : head < st.queue.size then
    let edge := st.queue[head]
    let edgeRank := st.rank[edge]!
    rankRightward g leftEmpty (head + 1) (rankRightwardSources g leftEmpty g.incoming[edge]! edgeRank 0 st)
  else st

/-- `topologicalNumbering(edges)`: longest-path ranks from the sources; afterwards segments whose
horizontal parts all point right (no left ports) are moved as far right as possible. -/
def topologicalNumbering (g : GapDeps) (leftEmpty : Array Bool) : RankState :=
  let n := g.outgoing.size
  let inweight : Array Int := g.incoming.map fun deps => (deps.size : Int)
  let outweight : Array Int := g.outgoing.map fun deps => (deps.size : Int)
  let sources := (Array.range n).filter fun i => g.incoming[i]!.isEmpty
  let rightwardTargets := (Array.range n).filter fun i => g.outgoing[i]!.isEmpty && leftEmpty[i]!
  match rankSources g 0 ⟨Array.replicate n 0, inweight, outweight, sources, -1⟩ with
  | ⟨rank, inweight, outweight, queue, maxRank⟩ =>
    if maxRank > -1 then
      let rank := rightwardTargets.foldl (fun rank edge => rank.set! edge maxRank) rank
      rankRightward g leftEmpty 0 ⟨rank, inweight, outweight, rightwardTargets, maxRank⟩
    else ⟨rank, inweight, outweight, queue, maxRank⟩

/-- Writes the ranking of the gap's segments `ids` back (dependency lists, mark, weights, rank) and
advances the dependency id counter. -/
def writeGapRanking (ids : Array SplineSegmentId) (g : GapDeps) (mark : Array Int) (rs : RankState) :
    RouterM Unit :=
  match g with
  | ⟨_, src, _, _, outgoing, incoming⟩ =>
    modify fun s =>
      let segments := ids.size.fold (init := s.segments) fun i h segments =>
        segments.modifyIn ids[i].idx fun x => { x with
          outgoing := outgoing[i]!, incoming := incoming[i]!, mark := mark[i]!, inweight := rs.inweight[i]!,
          outweight := rs.outweight[i]!, rank := rs.rank[i]! }
      { s with segments, dependencyCount := s.dependencyCount + src.size }

/-- `createSegmentsAndComputeRanking()`: hyperedge segments (left side reversed/non-reversed, then
right side), single-edge segments, dependencies between every pair (in list order), cycle breaking
and ranking. -/
def createSegmentsAndComputeRanking (graph : LGraphId) : RouterM Unit := do
  let leftPorts := (← get).leftPortsLayer
  let rightPorts := (← get).rightPortsLayer
  let leftSet := (← get).leftPortsSet
  createSplineSegmentsForHyperEdges leftPorts rightPorts leftSet .left true
  createSplineSegmentsForHyperEdges leftPorts rightPorts leftSet .left false
  createSplineSegmentsForHyperEdges leftPorts rightPorts leftSet .right true
  createSplineSegmentsForHyperEdges leftPorts rightPorts leftSet .right false
  createSplineSegments
  let layerSegments := (← get).splineSegmentsLayer
  let segments := (← get).segments
  let gs ← withArena fun a => GapSegments.read a segments layerSegments
  let (deps, cycles, random, drawn) := breakCycles (createDependencies gs (← get).dependencyCount) (← get).random
  if drawn then
    modify fun s => { s with random := random }
    if (← get).sharedRandom then
      LayeredM.setGraphRandom graph random
  writeGapRanking layerSegments deps cycles.mark (topologicalNumbering deps gs.leftEmpty)

/-- `getEdgeChain(start)`: the edge and its successors (long edge). Deviation: Rust/Java loop
forever on a successor cycle (only possible for malformed dummy wiring); the walk stops at the
first repeated edge instead. -/
def getEdgeChain (start : LEdgeId) : RouterM (Array LEdgeId) := do
  let successors := (← get).successingEdge
  let mut edgeChain : Array LEdgeId := #[]
  let mut visited : Std.HashSet LEdgeId := {}
  let mut current := start
  while true do
    if visited.contains current then break
    visited := visited.insert current
    edgeChain := edgeChain.push current
    match successors[current]? with
    | some next => current := next
    | none => break
  return edgeChain

/-- `getSplinePath(start)`: the segments along the edge chain (each gets the current edge's ports);
marks the initial and last segment and their source/target node. Like `getEdgeChain`, the walk
stops at a repeated edge (Rust/Java do not terminate on a successor cycle). -/
def getSplinePath (start : LEdgeId) : RouterM (Array SplineSegmentId) := do
  let mut segmentChain : Array SplineSegmentId := #[]
  let mut visited : Std.HashSet LEdgeId := {}
  let mut current := start
  while true do
    if visited.contains current then break
    visited := visited.insert current
    let some segment := (← get).edgeToSegmentMap[current]? | break
    let ed ← getEdge current
    modifySegment segment fun x => { x with sourcePort := ed.source, targetPort := ed.target }
    segmentChain := segmentChain.push segment
    match (← get).successingEdge[current]? with
    | some next => current := next
    | none => break
  if let some first := segmentChain[0]? then
    let seg ← getSegment first
    let sourceNode ← match seg.edges[0]? with
      | some e => withArena fun a => (a.edge e).source.bind fun p => (a.port p).owner
      | none => pure seg.sourceNode
    modifySegment first fun x => { x with initialSegment := true, sourceNode := sourceNode }
  if let some last := segmentChain.back? then
    let seg ← getSegment last
    let targetNode ← match seg.edges[0]? with
      | some e => withArena fun a => (a.edge e).target.bind fun p => (a.port p).owner
      | none => pure seg.targetNode
    modifySegment last fun x => { x with lastSegment := true, targetNode := targetNode }
  return segmentChain

/-- The spacing values read by `process`. -/
structure Spacing where
  nodeNodeSpacing : Float
  edgeNodeSpacing : Float
  edgeEdgeSpacing : Float
  sloppyRouting : Bool
  sloppyLayerSpacingFactor : Float

/-- One iteration of the layer loop of `process`: routes the gap between `leftLayer` and
`rightLayer`, places `rightLayer` and returns the next `xpos`. -/
def processLayerPair (graph : LGraphId) (sp : Spacing) (leftLayer rightLayer firstLayer lastLayer : Option LayerId)
    (isLeftLayerExternal isRightLayerExternal : Bool) (xpos : Float) : RouterM Float := do
  clearThenFillMappings leftLayer rightLayer
  createSegmentsAndComputeRanking graph
  -- count the slots for vertical segments (straight segments have a rank but no slot)
  let mut slotMax : Option Int := none
  for id in (← get).splineSegmentsLayer do
    let seg ← getSegment id
    if !seg.isStraight then
      slotMax := some (match slotMax with
        | some m => max m (seg.rank + 1)
        | none => seg.rank + 1)
  let slotCount := slotMax.getD 0
  let mut xSegmentDelta := 0.0
  let mut rightLayerPosition := xpos
  let isSpecialLeftLayer := leftLayer.isNone || (isLeftLayerExternal && leftLayer.isSome && leftLayer == firstLayer)
  let isSpecialRightLayer := rightLayer.isNone || (isRightLayerExternal && rightLayer.isSome && rightLayer == lastLayer)
  if slotCount > 0 then
    let mut increment := 0.0
    if leftLayer.isSome then increment := increment + sp.edgeNodeSpacing
    increment := increment + Float.ofInt (slotCount - 1) * sp.edgeEdgeSpacing
    if rightLayer.isSome then increment := increment + sp.edgeNodeSpacing
    if sp.sloppyRouting then
      if let some right := rightLayer then
        increment := fmax increment
          (← computeSloppySpacing right sp.edgeEdgeSpacing sp.nodeNodeSpacing sp.sloppyLayerSpacingFactor)
    if increment < sp.nodeNodeSpacing && !isSpecialLeftLayer && !isSpecialRightLayer then
      xSegmentDelta := (sp.nodeNodeSpacing - increment) / 2.0
      increment := sp.nodeNodeSpacing
    rightLayerPosition := rightLayerPosition + increment
  else if !isSpecialLeftLayer && !isSpecialRightLayer then
    rightLayerPosition := rightLayerPosition + sp.nodeNodeSpacing
  if let some right := rightLayer then
    LGraphUtil.placeNodesHorizontally right rightLayerPosition
  let finalRight := rightLayerPosition
  let delta := xSegmentDelta
  let westOfInitial := leftLayer.isNone
  for id in (← get).splineSegmentsLayer do
    modifySegment id fun x => { x with
      boundingBox := { x.boundingBox with x := xpos, width := finalRight - xpos },
      xDelta := delta, isWestOfInitialLayer := westOfInitial }
  modify fun s => { s with allSplineSegments := s.allSplineSegments ++ s.splineSegmentsLayer }
  let mut nextXpos := rightLayerPosition
  if let some right := rightLayer then
    nextXpos := nextXpos + (← getLayer right).size.x
  return nextXpos

/-- The body of `process` on the router state: routes every layer gap (including the gaps before
the first and after the last layer), then records the spline routes of the start edges
(`SPLINE_EDGE_CHAIN` on the edge, `SPLINE_ROUTE_START` in `State.routeStarts`) and the graph width. -/
def routeGraph (graph : LGraphId) : RouterM Unit := do
  let gr ← getGraph graph
  if gr.layers.isEmpty then
    modifyGraph graph fun g => { g with size := { g.size with x := 0.0 } }
    return
  let sp : Spacing := {
    nodeNodeSpacing := gr.props.getD LayeredOptions.SPACING_NODE_NODE_BETWEEN_LAYERS 0.0
    edgeNodeSpacing := gr.props.getD LayeredOptions.SPACING_EDGE_NODE_BETWEEN_LAYERS 0.0
    edgeEdgeSpacing := gr.props.getD LayeredOptions.SPACING_EDGE_EDGE_BETWEEN_LAYERS 0.0
    sloppyRouting := gr.props.getD LayeredOptions.EDGE_ROUTING_SPLINES_MODE SplineRoutingMode.sloppy == .sloppy
    sloppyLayerSpacingFactor := gr.props.getD LayeredOptions.EDGE_ROUTING_SPLINES_SLOPPY_LAYER_SPACING_FACTOR 0.0 }
  match ← LayeredM.graphRandom? graph with
  | some r => modify fun s => { s with random := r, sharedRandom := true }
  | none => modify fun s => { s with random := Random.ofInt 0, sharedRandom := false }
  let layers := gr.layers
  let firstLayer := layers[0]?
  let lastLayer := layers.back?
  let allExternal (layer : Option LayerId) : LayeredM Bool := do
    match layer with
    | none => return false
    | some l =>
      let nodes := (← getLayer l).nodes
      withArena fun a => nodes.all fun n => isExternalWestOrEastPort (a.node n)
  let isLeftLayerExternal ← allExternal firstLayer
  let isRightLayerExternal ← allExternal lastLayer
  let mut leftLayer : Option LayerId := none
  let mut xpos := 0.0
  for idx in [0:layers.size + 1] do
    let rightLayer := layers[idx]?
    xpos ← processLayerPair graph sp leftLayer rightLayer firstLayer lastLayer isLeftLayerExternal isRightLayerExternal xpos
    leftLayer := rightLayer
  for edge in (← get).startEdges do
    let edgeChain ← getEdgeChain edge
    let spline ← getSplinePath edge
    modifyEdge edge fun e => { e with internal := { e.internal with splineEdgeChain := edgeChain } }
    modify fun s => { s with routeStarts := s.routeStarts.push (edge, spline) }
  let width := xpos
  modifyGraph graph fun g => { g with size := { g.size with x := width } }

/-- Runs the router on `graph` and returns the final router state (segment table, route starts). -/
def route (graph : LGraphId) : LayeredM State := do
  let existing := (← getGraph graph).internal.splineSegments
  let ((), st) ← (routeGraph graph).run { segments := existing }
  return st

/-- Persists the segment table (`LGraphInternals.splineSegments`) and the `SPLINE_ROUTE_START` lists
(`LEdgeInternals.splineRouteStart`). -/
def storeSplineRoutes (graph : LGraphId) (st : State) : LayeredM Unit := do
  modifyGraph graph fun g => { g with internal := { g.internal with splineSegments := st.segments } }
  for (edge, spline) in st.routeStarts do
    modifyEdge edge fun e => { e with internal := { e.internal with splineRouteStart := some spline } }

/-- `process(layeredGraph, monitor)`. -/
def process (graph : LGraphId) (monitor : ProgressMonitor) : LayeredM Unit := do
  let _ ← monitor.begin "Spline edge routing" 1.0
  let st ← route graph
  storeSplineRoutes graph st
  monitor.done

/-- The phase (`EdgeRouting.SPLINES`); the name is the elk-rs `type_name` (trace file names). -/
def phase : LayeredPhase :=
  { name := "SplineEdgeRouter"
    process := process
    getLayoutProcessorConfiguration := fun graph => do
      return some (layoutProcessorConfiguration (← getGraph graph).internal.graphProperties) }

end SplineEdgeRouter

builtin_initialize registerSplineEdgeRouter : Unit ←
  LayeredPhases.registerPhase .p5EdgeRouting (ElkEnum.ordinal EdgeRouting.splines) (pure SplineEdgeRouter.phase)

end Elk.Alg.Layered.P5Edges.Splines
