import Std.Data.HashMap
import Std.Data.HashSet
import Elk.Alg.Layered.LayeredPhases
import Elk.Alg.Layered.Graph.LGraphUtil
import Elk.Alg.Layered.Options.LayeredOptions
import Elk.Alg.Layered.P5Edges.Splines.SplineSegment
import Elk.Alg.Layered.P5Edges.Splines.SplinesMath
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
  `all_spline_segments` order); `DependencyRef` → `DependencyId` into `State.dependencies`.
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

/-- `LPort.getAbsoluteAnchor().y`, `0.0` for an unowned port (Rust `.map(|a| a.y).unwrap_or(0.0)`). -/
def absoluteAnchorY (a : LGraphArena) (port : LPortId) : Float :=
  ((a.portAbsoluteAnchor port).map (·.y)).getD 0.0

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
    { g with internal := { g.internal with splineSegments := g.internal.splineSegments.modify id.idx f } }

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

/-- Rust `SplineEdgeRouter` fields plus the segment and dependency tables. -/
structure State where
  /-- Segment table: `SplineSegmentId.idx` indexes it (creation order = `all_spline_segments`). -/
  segments : Array SplineSegment := #[]
  /-- Dependency table: `DependencyId.idx` indexes it. -/
  dependencies : Array Dependency := #[]
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
  modify fun s => { s with segments := s.segments.modify id.idx f }

/-- The dependency `id`. -/
@[inline] def getDependency (id : DependencyId) : RouterM Dependency := do
  return (← get).dependencies[id.idx]!

/-- Appends a segment to the table. -/
def addSegment (segment : SplineSegment) : RouterM SplineSegmentId :=
  modifyGet fun s => (⟨s.segments.size⟩, { s with segments := s.segments.push segment })

/-- `new Dependency(source, target, weight)`: registers it as outgoing of `source` and incoming
of `target`. -/
def newDependency (source target : SplineSegmentId) (weight : Int) : RouterM Unit :=
  modify fun s =>
    let id : DependencyId := ⟨s.dependencies.size⟩
    let segments := s.segments.modify source.idx fun x => { x with outgoing := x.outgoing.push id }
    let segments := segments.modify target.idx fun x => { x with incoming := x.incoming.push id }
    { s with dependencies := s.dependencies.push { source := source, target := target, weight := weight },
             segments := segments }

/-- `random.next_int(bound)`, written back to the graph when the generator is the graph's. -/
def nextInt (graph : LGraphId) (bound : Int) : RouterM Int := do
  let (v, r) := (← get).random.nextInt bound
  modify fun s => { s with random := r }
  if (← get).sharedRandom then
    LayeredM.setGraphRandom graph r
  return v

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

/-- The crossing counters of `createDependency`: for each segment, its right ports minus its left
ports whose absolute anchor lies within the other segment's hyperedge y-range. -/
def dependencyCounters (a : LGraphArena) (edge0 edge1 : SplineSegment) : Int × Int := Id.run do
  let mut edge0Counter : Int := 0
  let mut edge1Counter : Int := 0
  for port in edge0.rightPorts do
    if SplinesMath.isBetween (absoluteAnchorY a port) edge1.hyperEdgeTopYPos edge1.hyperEdgeBottomYPos then
      edge0Counter := edge0Counter + 1
  for port in edge0.leftPorts do
    if SplinesMath.isBetween (absoluteAnchorY a port) edge1.hyperEdgeTopYPos edge1.hyperEdgeBottomYPos then
      edge0Counter := edge0Counter - 1
  for port in edge1.rightPorts do
    if SplinesMath.isBetween (absoluteAnchorY a port) edge0.hyperEdgeTopYPos edge0.hyperEdgeBottomYPos then
      edge1Counter := edge1Counter + 1
  for port in edge1.leftPorts do
    if SplinesMath.isBetween (absoluteAnchorY a port) edge0.hyperEdgeTopYPos edge0.hyperEdgeBottomYPos then
      edge1Counter := edge1Counter - 1
  return (edge0Counter, edge1Counter)

/-- `createDependency(edge0, edge1)`: a weighted dependency between two vertically overlapping
segments (two zero-weight dependencies if the order does not matter). -/
def createDependency (edge0 edge1 : SplineSegmentId) : RouterM Unit := do
  let s0 ← getSegment edge0
  let s1 ← getSegment edge1
  if s0.hyperEdgeTopYPos > s1.hyperEdgeBottomYPos || s1.hyperEdgeTopYPos > s0.hyperEdgeBottomYPos then return
  let (edge0Counter, edge1Counter) ← withArena (dependencyCounters · s0 s1)
  if edge0Counter < edge1Counter then
    newDependency edge0 edge1 (edge1Counter - edge0Counter)
  else if edge1Counter < edge0Counter then
    newDependency edge1 edge0 (edge0Counter - edge1Counter)
  else
    newDependency edge1 edge0 0
    newDependency edge0 edge1 0

/-- `updateNeighbors(edge, sources, sinks)`: simulates removing `edge`; returns the new sources and
sinks (in push order). -/
def updateNeighbors (edge : SplineSegmentId) : RouterM (Array SplineSegmentId × Array SplineSegmentId) := do
  let seg ← getSegment edge
  let mut newSources : Array SplineSegmentId := #[]
  let mut newSinks : Array SplineSegmentId := #[]
  for d in seg.outgoing do
    let dep ← getDependency d
    if dep.weight > 0 then
      let target ← getSegment dep.target
      if target.mark < 0 then
        let inweight := target.inweight - dep.weight
        modifySegment dep.target fun x => { x with inweight := inweight }
        if inweight <= 0 && target.outweight > 0 then
          newSources := newSources.push dep.target
  for d in seg.incoming do
    let dep ← getDependency d
    if dep.weight > 0 then
      let source ← getSegment dep.source
      if source.mark < 0 then
        let outweight := source.outweight - dep.weight
        modifySegment dep.source fun x => { x with outweight := outweight }
        if outweight <= 0 && source.inweight > 0 then
          newSinks := newSinks.push dep.source
  return (newSources, newSinks)

/-- Initial marks (`-1, -2, …`) and in/out weights of `breakCycles`; returns the initial sources
and sinks. -/
def initCycleBreaking (edges : Array SplineSegmentId) : RouterM (Array SplineSegmentId × Array SplineSegmentId) := do
  let mut sources : Array SplineSegmentId := #[]
  let mut sinks : Array SplineSegmentId := #[]
  let mut nextMark : Int := -1
  for edge in edges do
    let seg ← getSegment edge
    let mut inweight : Int := 0
    let mut outweight : Int := 0
    for d in seg.outgoing do
      outweight := outweight + (← getDependency d).weight
    for d in seg.incoming do
      inweight := inweight + (← getDependency d).weight
    let mark := nextMark
    let inw := inweight
    let outw := outweight
    modifySegment edge fun x => { x with mark := mark, inweight := inw, outweight := outw }
    nextMark := nextMark - 1
    if outweight == 0 then sinks := sinks.push edge
    else if inweight == 0 then sources := sources.push edge
  return (sources, sinks)

/-- The final step of `breakCycles`: dependencies pointing from a higher to a lower mark are removed
(weight 0) or reversed. -/
def reverseLeftwardDependencies (edges : Array SplineSegmentId) : RouterM Unit := do
  for source in edges do
    let outgoing := (← getSegment source).outgoing
    for d in outgoing do
      let dep ← getDependency d
      let sourceMark := (← getSegment dep.source).mark
      let targetMark := (← getSegment dep.target).mark
      if sourceMark > targetMark then
        modifySegment dep.source fun x => { x with outgoing := x.outgoing.filter (· != d) }
        modifySegment dep.target fun x => { x with incoming := x.incoming.filter (· != d) }
        if dep.weight > 0 then
          modify fun s => { s with dependencies := s.dependencies.modify d.idx fun x =>
            { x with source := dep.target, target := dep.source } }
          modifySegment dep.target fun x => { x with outgoing := x.outgoing.push d }
          modifySegment dep.source fun x => { x with incoming := x.incoming.push d }

/-- `breakCycles(edges, random)`: Eades–Lin–Smyth style marking (sinks get decreasing marks below
`edges.size`, sources and the random max-outflow segments increasing marks above it), then the
leftward dependencies are removed or reversed. -/
def breakCycles (graph : LGraphId) (edges : Array SplineSegmentId) : RouterM Unit := do
  let (sources0, sinks0) ← initCycleBreaking edges
  let mut sources := sources0
  let mut sourcesHead := 0
  let mut sinks := sinks0
  let mut sinksHead := 0
  let mut unprocessed := edges
  let markBase : Int := edges.size
  let mut nextLeft := markBase + 1
  let mut nextRight := markBase - 1
  let mut maxEdges : Array SplineSegmentId := #[]
  while !unprocessed.isEmpty do
    while sinksHead < sinks.size do
      let sink := sinks[sinksHead]!
      sinksHead := sinksHead + 1
      unprocessed := unprocessed.erase sink
      let mark := nextRight
      modifySegment sink fun x => { x with mark := mark }
      nextRight := nextRight - 1
      let (newSources, newSinks) ← updateNeighbors sink
      sources := sources ++ newSources
      sinks := sinks ++ newSinks
    while sourcesHead < sources.size do
      let source := sources[sourcesHead]!
      sourcesHead := sourcesHead + 1
      unprocessed := unprocessed.erase source
      let mark := nextLeft
      modifySegment source fun x => { x with mark := mark }
      nextLeft := nextLeft + 1
      let (newSources, newSinks) ← updateNeighbors source
      sources := sources ++ newSources
      sinks := sinks ++ newSinks
    let mut maxOutflow : Int := -2147483648
    for edge in unprocessed do
      let seg ← getSegment edge
      let outflow := seg.outweight - seg.inweight
      if outflow >= maxOutflow then
        if outflow > maxOutflow then
          maxEdges := #[]
          maxOutflow := outflow
        maxEdges := maxEdges.push edge
    if !maxEdges.isEmpty then
      let index ← nextInt graph (maxEdges.size : Int)
      let maxEdge := maxEdges[index.toNat]!
      unprocessed := unprocessed.erase maxEdge
      let mark := nextLeft
      modifySegment maxEdge fun x => { x with mark := mark }
      nextLeft := nextLeft + 1
      let (newSources, newSinks) ← updateNeighbors maxEdge
      sources := sources ++ newSources
      sinks := sinks ++ newSinks
      maxEdges := #[]
  let shiftBase : Int := (edges.size : Int) + 1
  for edge in edges do
    modifySegment edge fun x => if x.mark < markBase then { x with mark := x.mark + shiftBase } else x
  reverseLeftwardDependencies edges

/-- `topologicalNumbering(edges)`: longest-path ranks from the sources; afterwards segments whose
horizontal parts all point right (no left ports) are moved as far right as possible. -/
def topologicalNumbering (edges : Array SplineSegmentId) : RouterM Unit := do
  let mut sources : Array SplineSegmentId := #[]
  let mut sourcesHead := 0
  let mut rightwardTargets : Array SplineSegmentId := #[]
  let mut rightwardHead := 0
  for edge in edges do
    let seg ← getSegment edge
    let inweight : Int := seg.incoming.size
    let outweight : Int := seg.outgoing.size
    modifySegment edge fun x => { x with rank := 0, inweight := inweight, outweight := outweight }
    if inweight == 0 then sources := sources.push edge
    if outweight == 0 && seg.leftPorts.isEmpty then rightwardTargets := rightwardTargets.push edge
  let mut maxRank : Int := -1
  while sourcesHead < sources.size do
    let edge := sources[sourcesHead]!
    sourcesHead := sourcesHead + 1
    let seg ← getSegment edge
    let edgeRank := seg.rank
    for d in seg.outgoing do
      let target := (← getDependency d).target
      let t ← getSegment target
      let rank := max t.rank (edgeRank + 1)
      maxRank := max maxRank rank
      let inweight := t.inweight - 1
      modifySegment target fun x => { x with rank := rank, inweight := inweight }
      if inweight == 0 then sources := sources.push target
  if maxRank > -1 then
    let finalMaxRank := maxRank
    for edge in rightwardTargets do
      modifySegment edge fun x => { x with rank := finalMaxRank }
    while rightwardHead < rightwardTargets.size do
      let edge := rightwardTargets[rightwardHead]!
      rightwardHead := rightwardHead + 1
      let seg ← getSegment edge
      let edgeRank := seg.rank
      for d in seg.incoming do
        let source := (← getDependency d).source
        let s ← getSegment source
        if !s.leftPorts.isEmpty then continue
        let rank := min s.rank (edgeRank - 1)
        let outweight := s.outweight - 1
        modifySegment source fun x => { x with rank := rank, outweight := outweight }
        if outweight == 0 then rightwardTargets := rightwardTargets.push source

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
  for i in [0:layerSegments.size] do
    for j in [i + 1:layerSegments.size] do
      createDependency layerSegments[i]! layerSegments[j]!
  breakCycles graph layerSegments
  topologicalNumbering layerSegments

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
