import Elk.Core.Math.ElkMath
import Elk.Alg.Layered.LayeredPhases
import Elk.Alg.Layered.Options.LayeredOptions
import Elk.Alg.Layered.P5Edges.Splines.NubSpline
import Elk.Alg.Layered.P5Edges.Splines.SplineEdgeRouter
import Elk.Core.Util.FloatConst
open Elk.Core.Util.FloatConst
/-!
# `org.eclipse.elk.alg.layered.intermediate.FinalSplineBendpointsCalculator`

Port of elk-rs `intermediate/final_spline_bendpoints_calculator.rs`. Turns the spline routes left by
the `SplineEdgeRouter` into the final Bezier bend points of the edges, in two passes over the
*start edges* (outgoing edges of the layer nodes, layer order → node order → `getOutgoingEdges`
order, without self loops, with `SPLINE_ROUTE_START`):

1. for every segment of each start edge's `SPLINE_ROUTE_START` chain (each segment once, marked
   `handled`) the NUB control points of every represented edge are stored as its bend points:
   a single halfway point for a straight non-hyperedge segment, `calculateControlPointsInvertedEdge`
   for edges at inverted (`WEST` source / `EAST` target) ports, `calculateControlPointsSloppy` for
   `SLOPPY` routing (at least one normal end node, `segmentAllowsSloppyRouting`, no hyperedge),
   otherwise `calculateControlPointsConservative` (hyperedges get an extra center point); segments
   with `inverseOrder` (wrapped graphs) reverse the bend points of their edges. The chain is removed
   from the edge (`SPLINE_ROUTE_START := null`).
2. for each start edge the control points of its `SPLINE_EDGE_CHAIN` are collected (source anchor,
   the `SPLINE_NS_PORT_Y_COORD` point for north/south ports, the bend points of the chain edges with
   a midpoint between every second pair of consecutive edges, the target side likewise; `CONSERVATIVE`
   inserts straightening points `NODE_TO_STRAIGHTENING_CP_GAP` away from the ports), the bend points
   of the chain edges are cleared and the Bezier control points of the clamped cubic `NubSpline`
   become the bend points of the `SPLINE_SURVIVING_EDGE` (default: the first chain edge). The chain
   is removed from the edge (`SPLINE_EDGE_CHAIN := null`, Lean: empty).

The node `id`s of each layer are set to their in-layer index (`indexNodesPerLayer`, kept after the
processor like in Rust/Java).

## Arena mapping
Segments are read and written through `getSplineSegment`/`modifySplineSegment` (the graph's
`LGraphInternals.splineSegments` table); Rust's `SegmentSnapshot` is the `SplineSegment` value read
when the segment is first handled (with `handled := true`); the edge information is looked up in it
(the segment's edges and edge information do not change while the processor runs).

## Rust vs Java (Rust followed)
- an edge without `EdgeInformation` in its segment is skipped (Java: `NullPointerException`);
- `calculateControlPointsSloppy`: a missing source/target port anchor is `(0, 0)` and an
  out-of-range neighbour index keeps the shortcut flag `false` (Java throws);
- `computeSloppyCenterY` tests the edge's *target* port before counting the target node's incoming
  edges and its *source* port before counting the source node's outgoing edges (Java tests them
  crosswise: source before the indegree, target before the outdegree);
- `SPLINE_NS_PORT_Y_COORD` falls back to the anchor's y (Java unboxes `null`);
- a start edge without source or target port stops `calculateBezierBendPoints` (Java throws); the
  non-qualified source node is an `IllegalArgumentException` like Java (Rust panics);
- `segmentAllowsSloppyRouting` skips the node checks for a missing source/target node.
-/

namespace Elk.Alg.Layered.Intermediate

open Elk.Graph Elk.Core Elk.Core.Alg Elk.Core.Math Elk.Core.Options Elk.Core.Util Elk.Alg.Layered
  Elk.Alg.Layered.Graph Elk.Alg.Layered.Options Elk.Alg.Layered.P5Edges.Splines LayeredM

namespace FinalSplineBendpointsCalculator

/-- `ONE_HALF` (`0.5`). -/
def ONE_HALF : Float := 0.5
/-- `NODE_TO_STRAIGHTENING_CP_GAP` (`5`): gap between a port anchor and the straightening control
point inserted for `CONSERVATIVE` routing. -/
def NODE_TO_STRAIGHTENING_CP_GAP : Float := 5.0
/-- `SLOPPY_CENTER_CP_MULTIPLIER` (`0.4`): curvature of sloppy splines. -/
def SLOPPY_CENTER_CP_MULTIPLIER : Float := 0.4

/-- The fields of the Rust struct, read from the graph at the start of `process`. -/
structure Config where
  /-- `edge_edge_spacing` (`SPACING_EDGE_EDGE_BETWEEN_LAYERS`). -/
  edgeEdgeSpacing : Float := fl0p0
  /-- `edge_node_spacing` (`SPACING_EDGE_NODE_BETWEEN_LAYERS`). -/
  edgeNodeSpacing : Float := fl0p0
  /-- `spline_routing_mode` (`EDGE_ROUTING_SPLINES_MODE`). -/
  splineRoutingMode : SplineRoutingMode := .sloppy
  /-- `compaction_strategy` (`COMPACTION_POST_COMPACTION_STRATEGY`). -/
  compactionStrategy : GraphCompactionStrategy := .none
  deriving Inhabited

/-- `indexNodesPerLayer(graph)`: `node.id := index in its layer`. -/
def indexNodesPerLayer (graph : LGraphId) : LayeredM Unit := do
  for layer in (← getGraph graph).layers do
    let nodes := (← getLayer layer).nodes
    for h : index in [0:nodes.size] do
      modifyNode nodes[index] fun n => { n with id := (index : Int) }

/-- Appends `points` to the bend points of `edge` (`getBendPoints().addAll(..)`). -/
def addBendPoints (edge : LEdgeId) (points : Array KVector) : LayeredM Unit :=
  modifyEdge edge fun e => { e with bendPoints := e.bendPoints ++ points }

/-- `calculateControlPointsStraight(segment)`: one control point halfway between the layers, added
to the segment's first edge. -/
def calculateControlPointsStraight (segment : SplineSegment) : LayeredM Unit := do
  let xStartPos := segment.boundingBox.x
  let xEndPos := segment.boundingBox.x + segment.boundingBox.width
  let halfway : KVector := ⟨xStartPos + (xEndPos - xStartPos) / fl2p0, segment.centerControlPointY⟩
  if let some edge := segment.edges[0]? then
    addBendPoints edge #[halfway]

/-- The x of the vertical part of a segment (shared by the inverted and the conservative variant):
`start (+ edgeNodeSpacing unless west of the initial layer) + (xDelta + rank · edgeEdgeSpacing)`. -/
def centerXPos (cfg : Config) (segment : SplineSegment) : Float := Id.run do
  let mut centerX := segment.boundingBox.x
  if !segment.isWestOfInitialLayer then
    centerX := centerX + cfg.edgeNodeSpacing
  centerX := centerX + (segment.xDelta + Float.ofInt segment.rank * cfg.edgeEdgeSpacing)
  return centerX

/-- The control points `sourceStraight, sourceVertical, (center), targetVertical, targetStraight`
of the inverted and the conservative variant (the center point only for hyperedges). -/
def addFourPointRoute (cfg : Config) (edge : LEdgeId) (segment : SplineSegment) (info : EdgeInformation)
    (sourceStraightCP targetStraightCP : KVector) : LayeredM Unit := do
  let centerX := centerXPos cfg segment
  let sourceVerticalCP : KVector := ⟨centerX, info.startY⟩
  let targetVerticalCP : KVector := ⟨centerX, info.endY⟩
  let mut points : Array KVector := #[sourceStraightCP, sourceVerticalCP]
  if segment.isHyperEdge then
    points := points.push ⟨centerX, segment.centerControlPointY⟩
  points := points ++ #[targetVerticalCP, targetStraightCP]
  addBendPoints edge points

/-- `calculateControlPointsInvertedEdge(edge, segment)`: for an edge at a `WEST` source port
(`invertedLeft`) the source straight point lies at the segment's right end, for an `EAST` target
port (`invertedRight`) the target straight point at its left end. -/
def calculateControlPointsInvertedEdge (cfg : Config) (edge : LEdgeId) (segment : SplineSegment)
    (info : EdgeInformation) : LayeredM Unit := do
  let startXPos := segment.boundingBox.x
  let endXPos := segment.boundingBox.x + segment.boundingBox.width
  let sourceStraightCP : KVector :=
    if info.invertedLeft then ⟨endXPos, info.startY⟩ else ⟨startXPos, info.startY⟩
  let targetStraightCP : KVector :=
    if info.invertedRight then ⟨startXPos, info.endY⟩ else ⟨endXPos, info.endY⟩
  addFourPointRoute cfg edge segment info sourceStraightCP targetStraightCP

/-- `calculateControlPointsConservative(edge, segment)`: the traditional four control points (plus
the center point of a hyperedge). -/
def calculateControlPointsConservative (cfg : Config) (edge : LEdgeId) (segment : SplineSegment)
    (info : EdgeInformation) : LayeredM Unit := do
  let startXPos := segment.boundingBox.x
  let endXPos := segment.boundingBox.x + segment.boundingBox.width
  addFourPointRoute cfg edge segment info ⟨startXPos, info.startY⟩ ⟨endXPos, info.endY⟩

/-- `nodeToBoundingBox(node)`: the node box including its margins. -/
def nodeToBoundingBox (a : LGraphArena) (node : LNodeId) : ElkRectangle :=
  let nd := a.node node
  let m := nd.margin
  { x := nd.position.x - m.left, y := nd.position.y - m.top,
    width := nd.size.x + m.left + m.right, height := nd.size.y + m.top + m.bottom }

/-- `computeSloppyCenterY(edge, ySourceAnchor, yTargetAnchor)`: the center y moved towards the
target (more outgoing than incoming edges) or the source (more incoming); the degrees are those of
the edge's current end nodes (`1` for a missing port, Rust order of the tests). -/
def computeSloppyCenterY (a : LGraphArena) (edge : LEdgeId) (ySourceAnchor yTargetAnchor : Float) : Float := Id.run do
  let ed := a.edge edge
  let mut indegree : Int := 0
  let mut outdegree : Int := 0
  match ed.target with
  | some targetPort =>
    if let some node := (a.port targetPort).owner then
      for port in (a.node node).ports do
        indegree := indegree + ((a.port port).incomingEdges.size : Int)
  | none => indegree := 1
  match ed.source with
  | some sourcePort =>
    if let some node := (a.port sourcePort).owner then
      for port in (a.node node).ports do
        outdegree := outdegree + ((a.port port).outgoingEdges.size : Int)
  | none => outdegree := 1
  let degreeDiff := Float.ofInt (outdegree - indegree).sign
  return (yTargetAnchor + ySourceAnchor) / 2.0
    + (yTargetAnchor - ySourceAnchor) * (SLOPPY_CENTER_CP_MULTIPLIER * degreeDiff)

/-- The shortcut test of `calculateControlPointsSloppy` for one end of the segment: `port`'s node
must be in a layer and normal (`normal`); if it has a neighbour in the direction of the edge
(`towardsNext`: the next node of the layer, else the previous one) the line `p`–`q` must neither
cross nor lie inside that neighbour's box. The source end checks downwards edges against the next
node, the target end against the previous node. -/
def shortCut (a : LGraphArena) (port : Option LPortId) (normal towardsNext : Bool) (p q : KVector) : Bool := Id.run do
  let some port := port | return false
  let some node := (a.port port).owner | return false
  let nd := a.node node
  let some layer := nd.layer | return false
  if !normal then return false
  let layerNodes := (a.layer layer).nodes
  let nodeId := nd.id
  let needToCheck := (towardsNext && nodeId < (layerNodes.size : Int) - 1) || (!towardsNext && nodeId > 0)
  if !needToCheck then return true
  let neighborIndex := if towardsNext then nodeId + 1 else nodeId - 1
  -- Rust `layer_nodes.get(index)`: an out-of-range neighbour keeps the flag `false`
  if neighborIndex < 0 then return false
  match layerNodes[neighborIndex.toNat]? with
  | some neighbor =>
    let box := nodeToBoundingBox a neighbor
    return !(ElkMath.intersectsRectLine box p q || ElkMath.containsRectLine box p q)
  | none => return false

/-- The control points of `calculateControlPointsSloppy` (read-only part). -/
def sloppyControlPoints (a : LGraphArena) (edge : LEdgeId) (segment : SplineSegment) (info : EdgeInformation) :
    Array KVector := Id.run do
  let startXPos := segment.boundingBox.x
  let endXPos := segment.boundingBox.x + segment.boundingBox.width
  let ySourceAnchor := info.startY
  let yTargetAnchor := info.endY
  let edgePointsDownwards := ySourceAnchor < yTargetAnchor
  let sourceStraightCP : KVector := ⟨startXPos, ySourceAnchor⟩
  let targetStraightCP : KVector := ⟨endXPos, yTargetAnchor⟩
  let centerX := (startXPos + endXPos) / 2.0
  let sourceVerticalCP : KVector := ⟨centerX, ySourceAnchor⟩
  let targetVerticalCP : KVector := ⟨centerX, yTargetAnchor⟩
  let centerYPos := computeSloppyCenterY a edge ySourceAnchor yTargetAnchor
  let v1 : KVector := (segment.sourcePort.bind a.portAbsoluteAnchor).getD KVector.zero
  let v2 : KVector := ⟨centerX, centerYPos⟩
  let v3 : KVector := (segment.targetPort.bind a.portAbsoluteAnchor).getD KVector.zero
  let approx := ElkMath.approximateBezierSegment 2 #[v1, v2, v3]
  let approxCenter := approx[0]?.getD v2
  let shortCutSource := shortCut a segment.sourcePort info.normalSourceNode edgePointsDownwards v1 approxCenter
  let shortCutTarget := shortCut a segment.targetPort info.normalTargetNode (!edgePointsDownwards) approxCenter v3
  let mut points : Array KVector := #[]
  if shortCutSource && shortCutTarget then
    points := points.push v2
  if !shortCutSource then
    points := points ++ #[sourceStraightCP, sourceVerticalCP]
  if !shortCutTarget then
    points := points ++ #[targetVerticalCP, targetStraightCP]
  return points

/-- `calculateControlPointsSloppy(edge, segment)`: tries to omit the source (`a, b`) and/or target
(`c, d`) pair of the conservative control points; if both can be omitted a single center point
(`computeSloppyCenterY`) is used. -/
def calculateControlPointsSloppy (edge : LEdgeId) (segment : SplineSegment) (info : EdgeInformation) :
    LayeredM Unit := do
  let points ← withArena fun a => sloppyControlPoints a edge segment info
  addBendPoints edge points

/-- `segmentNodeDistanceThreshold(node)`: `layer width - node width / 2`. -/
def segmentNodeDistanceThreshold (a : LGraphArena) (node : LNodeId) : Float :=
  let nd := a.node node
  let layerSize := (nd.layer.map fun l => (a.layer l).size.x).getD 0.0
  layerSize - nd.size.x / 2.0

/-- `segmentAllowsSloppyRouting(segment)`: with post-compaction the initial (last) segment must not
be farther from its source (target) node than `segmentNodeDistanceThreshold`. -/
def segmentAllowsSloppyRouting (cfg : Config) (a : LGraphArena) (segment : SplineSegment) : Bool := Id.run do
  if cfg.compactionStrategy == .none then return true
  let startXPos := segment.boundingBox.x
  let endXPos := segment.boundingBox.x + segment.boundingBox.width
  if segment.initialSegment then
    if let some node := segment.sourceNode then
      let threshold := segmentNodeDistanceThreshold a node
      let nd := a.node node
      let nodeSegmentDistance := startXPos - (nd.position.x + nd.size.x)
      if nodeSegmentDistance > threshold then return false
  if segment.lastSegment then
    if let some node := segment.targetNode then
      let threshold := segmentNodeDistanceThreshold a node
      let nodeSegmentDistance := (a.node node).position.x - endXPos
      if nodeSegmentDistance > threshold then return false
  return true

/-- `calculateControlPoints(segment)`: dispatches every represented edge of a not yet handled
segment to the variants (see the module doc); `inverseOrder` reverses the edges' bend points. -/
def calculateControlPoints (cfg : Config) (graph : LGraphId) (id : SplineSegmentId) : LayeredM Unit := do
  let segment ← getSplineSegment graph id
  if segment.handled then return
  modifySplineSegment graph id fun s => { s with handled := true }
  let segment := { segment with handled := true }
  for edge in segment.edges do
    if segment.isStraight && !segment.isHyperEdge then
      calculateControlPointsStraight segment
      continue
    let some info := segment.edgeInformationOf edge | continue
    if info.invertedLeft || info.invertedRight then
      calculateControlPointsInvertedEdge cfg edge segment info
      continue
    let allowsSloppy ← withArena fun a => segmentAllowsSloppyRouting cfg a segment
    let sloppy : Bool := cfg.splineRoutingMode == .sloppy
      && (info.normalSourceNode || info.normalTargetNode)
      && allowsSloppy
      && !segment.isHyperEdge
    if sloppy then
      calculateControlPointsSloppy edge segment info
    else
      calculateControlPointsConservative cfg edge segment info
  if segment.inverseOrder then
    for edge in segment.edges do
      modifyEdge edge fun e => { e with bendPoints := e.bendPoints.reverse }

/-- `absMin(d1, d2)`: the value with the smaller magnitude (`d2` on ties). -/
def absMin (d1 d2 : Float) : Float := if d1.abs < d2.abs then d1 else d2

/-- `insertStraighteningControlPoints(allCPs, srcPort, tgtPort)`: inserts a point at most
`NODE_TO_STRAIGHTENING_CP_GAP` from the first (last) control point in the outward direction of the
source (target) port side, after the first (before the last) control point. Needs at least two
control points (always the case: source and target anchor). -/
def insertStraighteningControlPoints (allCPs : KVectorChain) (srcSide tgtSide : PortSide) : KVectorChain := Id.run do
  let mut cps := allCPs
  let first := cps[0]?.getD KVector.zero
  let second := cps[1]?.getD KVector.zero
  let v := (KVector.fromAngle (SplinesMath.portSideToDirection srcSide)).scale NODE_TO_STRAIGHTENING_CP_GAP
  let v2 := second - first
  let straightenBeginning : KVector := (⟨absMin v.x v2.x, absMin v.y v2.y⟩ : KVector) + first
  cps := cps.insertIdxIfInBounds 1 straightenBeginning
  let last := cps.back?.getD KVector.zero
  let secondLast := cps[cps.size - 2]?.getD KVector.zero
  let w := (KVector.fromAngle (SplinesMath.portSideToDirection tgtSide)).scale NODE_TO_STRAIGHTENING_CP_GAP
  let w2 := secondLast - last
  let straightenEnding : KVector := (⟨absMin w.x w2.x, absMin w.y w2.y⟩ : KVector) + last
  cps := cps.insertIdxIfInBounds (cps.size - 1) straightenEnding
  return cps

/-- The extra control point of a north/south port (`SPLINE_NS_PORT_Y_COORD`, Rust falls back to the
anchor's y), `none` for other sides. -/
def northSouthControlPoint (a : LGraphArena) (port : LPortId) (anchor : KVector) : Option KVector :=
  let pt := a.port port
  if pt.side == .north || pt.side == .south then
    some ⟨anchor.x, (splineNsPortYCoordOf pt).getD anchor.y⟩
  else none

/-- `calculateBezierBendPoints(edgeChain, survivingEdge)`: collects the NUB control points of the
chain (see the module doc), clears the chain edges' bend points and appends the Bezier control
points to the surviving edge (default: the first chain edge). -/
def calculateBezierBendPoints (cfg : Config) (edgeChain : Array LEdgeId) (survivingEdge : Option LEdgeId) :
    LayeredM Unit := do
  let some firstEdge := edgeChain[0]? | return
  let edge := survivingEdge.getD firstEdge
  let some sourcePort := (← getEdge edge).source | return
  let qualified ← match (← getPort sourcePort).owner with
    | some node => pure (SplineEdgeRouter.isQualifiedAsStartingNode (← getNode node))
    | none => pure false
  if !qualified then
    throw (IO.userError
      "java.lang.IllegalArgumentException: The target node of the edge must be a normal node or a northSouthPort.")
  let sourceAnchor ← withArena fun a => (a.portAbsoluteAnchor sourcePort).getD KVector.zero
  let mut allCP : KVectorChain := #[sourceAnchor]
  if let some cp ← withArena fun a => northSouthControlPoint a sourcePort sourceAnchor then
    allCP := allCP.push cp
  let mut lastCP : Option KVector := none
  let mut addMidPoint := false
  for currentEdge in edgeChain do
    let currentBendPoints := (← getEdge currentEdge).bendPoints
    if currentBendPoints.isEmpty then continue
    if addMidPoint then
      if let some last := lastCP then
        allCP := allCP.push ((last + currentBendPoints[0]!).scale ONE_HALF)
      addMidPoint := false
    else
      addMidPoint := true
    lastCP := currentBendPoints.back?
    allCP := allCP ++ currentBendPoints
    modifyEdge currentEdge fun e => { e with bendPoints := #[] }
  let some targetPort := (← getEdge edge).target | return
  let targetAnchor ← withArena fun a => (a.portAbsoluteAnchor targetPort).getD KVector.zero
  if let some cp ← withArena fun a => northSouthControlPoint a targetPort targetAnchor then
    allCP := allCP.push cp
  allCP := allCP.push targetAnchor
  if cfg.splineRoutingMode == .conservative then
    let srcSide := (← getPort sourcePort).side
    let tgtSide := (← getPort targetPort).side
    allCP := insertStraighteningControlPoints allCP srcSide tgtSide
  match NubSpline.new true SplineEdgeRouter.SPLINE_DIMENSION allCP with
  | .ok nubSpline => addBendPoints edge nubSpline.getBezierCPDefault.1
  | .error e => throw (IO.userError e)

/-- The start edges: outgoing edges (not self loops) with `SPLINE_ROUTE_START` of the layer nodes,
in layer → node → `getOutgoingEdges` order. -/
def collectStartEdges (graph : LGraphId) : LayeredM (Array LEdgeId) := do
  let mut startEdges : Array LEdgeId := #[]
  for layer in (← getGraph graph).layers do
    for node in (← getLayer layer).nodes do
      let edges ← withArena fun a => (a.nodeOutgoingEdges node).filter fun edge =>
        !a.edgeIsSelfLoop edge && (a.edge edge).internal.splineRouteStart.isSome
      startEdges := startEdges ++ edges
  return startEdges

/-- `process(graph, monitor)` (no progress monitor calls, like Rust/Java). -/
def process (graph : LGraphId) (_monitor : ProgressMonitor) : LayeredM Unit := do
  let props := (← getGraph graph).props
  let cfg : Config :=
    { edgeEdgeSpacing := props.getD LayeredOptions.SPACING_EDGE_EDGE_BETWEEN_LAYERS 0.0
      edgeNodeSpacing := props.getD LayeredOptions.SPACING_EDGE_NODE_BETWEEN_LAYERS 0.0
      splineRoutingMode := props.getD LayeredOptions.EDGE_ROUTING_SPLINES_MODE .sloppy
      compactionStrategy := props.getD LayeredOptions.COMPACTION_POST_COMPACTION_STRATEGY .none }
  indexNodesPerLayer graph
  let startEdges ← collectStartEdges graph
  -- first determine the NUB control points
  for edge in startEdges do
    if let some spline := (← getEdge edge).internal.splineRouteStart then
      for segment in spline do
        calculateControlPoints cfg graph segment
      modifyEdge edge fun e => { e with internal := { e.internal with splineRouteStart := none } }
  -- then convert them to Bezier splines
  for edge in startEdges do
    let ed ← getEdge edge
    calculateBezierBendPoints cfg ed.internal.splineEdgeChain ed.internal.splineSurvivingEdge
    modifyEdge edge fun e => { e with internal := { e.internal with splineEdgeChain := #[] } }

/-- The processor; the name is the elk-rs `type_name` (trace file names). -/
def processor : LayeredProcessor := { name := "FinalSplineBendpointsCalculator", process := process }

end FinalSplineBendpointsCalculator

builtin_initialize registerFinalSplineBendpointsCalculator : Unit ←
  IntermediateProcessorStrategy.register .finalSplineBendpointsCalculator FinalSplineBendpointsCalculator.processor

end Elk.Alg.Layered.Intermediate
