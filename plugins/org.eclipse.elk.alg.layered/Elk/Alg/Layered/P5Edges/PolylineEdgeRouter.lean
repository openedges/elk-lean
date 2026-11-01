import Std.Data.HashMap
import Std.Data.HashSet
import Elk.Alg.Layered.LayeredPhases
import Elk.Alg.Layered.Graph
import Elk.Alg.Layered.Options.LayeredOptions
import Elk.Alg.Layered.Options.GraphProperties
import Elk.Alg.Layered.P5Edges.Orthogonal.Direction.BaseRoutingDirectionStrategy
import Elk.Core.Options
import Elk.Core.Util.FloatConst
open Elk.Core.Util.FloatConst
/-!
# `org.eclipse.elk.alg.layered.p5edges.PolylineEdgeRouter`

Port of elk-rs `p5edges/polyline_edge_router.rs`. Layers are placed left to right; the space between
two layers grows with the largest vertical distance an edge has to bridge (`LAYER_SPACE_FAC ×
min(1, edgeSpacing / nodeSpacing)` of it). A port whose anchor lies further than the sloped edge zone
width (`EDGE_ROUTING_POLYLINE_SLOPED_EDGE_ZONE_WIDTH`) away from its layer's border gets a bend point
on the border (junction points for ports with several edges), so that the sloped part of an edge
starts at the layer border; in-layer edges get one bend point beside the layer.

`ArenaSync` reads (elk-rs takes a snapshot at the start of `process`, see `PORTING.md` §15.1):
* the outgoing edges of a node are taken per port from the snapshot, i.e. only edges whose target is
  in the graph (`ArenaScope.portOutgoingEdges`); for those edges a self loop is `source port == target
  port`, and "target in the same layer" compares the snapshot layers;
* `processNode` uses the snapshot's **layer width** (`layerLeftXPos + arena.layer_size(layer).x`), which is
  stale when `placeNodesHorizontally` just computed the width of a layer whose width was `0` (Java reads
  the live width); the router keeps the widths captured at the start (`layerSizeX`);
* anchor `y` coordinates are read from the snapshot, which no step of the router changes, so live values
  are used.
Everything else (port anchors, connected edges, in-layer and self-loop tests of `addBendPoint`) is read
live, as in Rust.
-/

namespace Elk.Alg.Layered.P5Edges

open Elk.Graph Elk.Core Elk.Core.Alg Elk.Core.Math Elk.Core.Options Elk.Core.Util Elk.Alg.Layered
  Elk.Alg.Layered.Graph Elk.Alg.Layered.Options Elk.Alg.Layered.Intermediate LayeredM

namespace PolylineEdgeRouter

/-- `MIN_VERT_DIFF`: minimal vertical difference for creating bend points. -/
def MIN_VERT_DIFF : Float := 1.0

/-- `LAYER_SPACE_FAC`: factor for layer spacing. -/
def LAYER_SPACE_FAC : Float := 0.4

/-- `BASELINE_PROCESSOR_CONFIGURATION`: `INVERTED_PORT_PROCESSOR` before P3. -/
def BASELINE_PROCESSOR_CONFIGURATION : LayeredProcessorConfiguration :=
  (LayoutProcessorConfiguration.create : LayeredProcessorConfiguration).addBefore .p3NodeOrdering .invertedPortProcessor

/-- `NORTH_SOUTH_PORT_PROCESSING_ADDITIONS`. -/
def NORTH_SOUTH_PORT_PROCESSING_ADDITIONS : LayeredProcessorConfiguration :=
  (LayoutProcessorConfiguration.create : LayeredProcessorConfiguration)
    |>.addBefore .p3NodeOrdering .northSouthPortPreprocessor
    |>.addAfter .p5EdgeRouting .northSouthPortPostprocessor

/-- `SELF_LOOP_PROCESSING_ADDITIONS`. -/
def SELF_LOOP_PROCESSING_ADDITIONS : LayeredProcessorConfiguration :=
  (LayoutProcessorConfiguration.create : LayeredProcessorConfiguration)
    |>.addBefore .p1CycleBreaking .selfLoopPreprocessor
    |>.addAfter .p5EdgeRouting .selfLoopPostprocessor
    |>.addBefore .p4NodePlacement .selfLoopPortRestorer
    |>.addBefore .p4NodePlacement .selfLoopRouter

/-- `CENTER_EDGE_LABEL_PROCESSING_ADDITIONS`. -/
def CENTER_EDGE_LABEL_PROCESSING_ADDITIONS : LayeredProcessorConfiguration :=
  (LayoutProcessorConfiguration.create : LayeredProcessorConfiguration)
    |>.addBefore .p2Layering .labelDummyInserter
    |>.addBefore .p4NodePlacement .labelDummySwitcher
    |>.addBefore .p4NodePlacement .labelSideSelector
    |>.addAfter .p5EdgeRouting .labelDummyRemover

/-- `END_EDGE_LABEL_PROCESSING_ADDITIONS`. -/
def END_EDGE_LABEL_PROCESSING_ADDITIONS : LayeredProcessorConfiguration :=
  (LayoutProcessorConfiguration.create : LayeredProcessorConfiguration)
    |>.addBefore .p4NodePlacement .labelSideSelector
    |>.addBefore .p4NodePlacement .endLabelPreprocessor
    |>.addAfter .p5EdgeRouting .endLabelPostprocessor

/-- `PRED_EXTERNAL_WEST_OR_EAST_PORT` (Rust `is_external_west_or_east_port`): an external port dummy on
the west or east side. -/
def isExternalWestOrEastPort (node : LNodeId) : LayeredM Bool := do
  let nd ← getNode node
  if nd.type != .externalPort then return false
  return nd.internal.extPortSide == .west || nd.internal.extPortSide == .east

/-- `isInLayerDummy(node)`: a long edge dummy with an in-layer edge. -/
def isInLayerDummy (node : LNodeId) : LayeredM Bool := do
  if (← getNode node).type != .longEdge then return false
  let a ← get
  return (a.nodeConnectedEdges node).any a.edgeIsInLayerEdge

/-- `addBendPoint(edge, bendPoint, addJunctionPoint, currPort)`: prepends (edge leaves `currPort`) or
appends the bend point unless the edge is a self loop or, for edges between layers, the port anchor is
the bend point itself; adds a junction point once per position. -/
def addBendPoint (created : Std.HashSet KVector) (edge : LEdgeId) (bendPoint : KVector) (addJunctionPoint : Bool)
    (currPort : LPortId) : LayeredM (Std.HashSet KVector) := do
  let a ← get
  if a.edgeIsSelfLoop edge then return created
  if !a.edgeIsInLayerEdge edge then
    let anchorNeBend := match a.portAbsoluteAnchor currPort with
      | some anchor => anchor != bendPoint
      | none => true
    if !anchorNeBend then return created
  let isSource := (a.edge edge).source == some currPort
  modifyEdge edge fun ed => { ed with
    bendPoints := if isSource then ed.bendPoints.addFirst bendPoint else ed.bendPoints.push bendPoint }
  if addJunctionPoint && !created.contains bendPoint then
    modifyEdge edge fun ed =>
      let junctionPoints := ed.props.getD LayeredOptions.JUNCTION_POINTS #[]
      { ed with props := ed.props.set LayeredOptions.JUNCTION_POINTS (junctionPoints.push bendPoint) }
    return created.insert bendPoint
  return created

/-- `processNode(node, layerLeftXPos, maxAcceptableXDiff)`: bend points on the layer border for the
ports of `node` that lie outside the sloped edge zone (north/south port dummies first take the `x` of
the port they represent). -/
def processNode (created : Std.HashSet KVector) (node : LNodeId) (layerLeftXPos maxAcceptableXDiff : Float)
    (layerSizeX : Std.HashMap LayerId Float) : LayeredM (Std.HashSet KVector) := do
  let nd ← getNode node
  let layerWidth ← match nd.layer with
    | some l => match layerSizeX.get? l with
      | some w => pure w
      | none => pure (← getLayer l).size.x
    | none => pure 0.0
  let layerRightXPos := layerLeftXPos + layerWidth
  let isNsPort := nd.type == .northSouthPort
  let isInLayerDummy ← isInLayerDummy node
  let mut created := created
  for port in nd.ports do
    let pt ← getPort port
    let some anchor ← withArena (·.portAbsoluteAnchor port) | continue
    let mut absolutePortAnchor := anchor
    let addJunctionPoint := pt.incomingEdges.size + pt.outgoingEdges.size > 1
    if isNsPort then
      if let some (.lPort originPort) := pt.internal.origin then
        if let some originAnchor ← withArena (·.portAbsoluteAnchor originPort) then
          absolutePortAnchor := { absolutePortAnchor with x := originAnchor.x }
          modifyNode node fun x => { x with position := { x.position with x := originAnchor.x } }
    let bendX ← match pt.side with
      | .east => pure (some layerRightXPos)
      | .west => pure (some layerLeftXPos)
      | _ => pure none
    let some bendX := bendX | continue
    let bendPoint : KVector := ⟨bendX, absolutePortAnchor.y⟩
    let xDistance := (absolutePortAnchor.x - bendPoint.x).abs
    if xDistance <= maxAcceptableXDiff && !isInLayerDummy then continue
    for edge in pt.connectedEdges do
      let a ← get
      let ed := a.edge edge
      let otherPort := if ed.source == some port then ed.target else ed.source
      let otherAnchorY := ((otherPort.bind a.portAbsoluteAnchor).map (·.y)).getD absolutePortAnchor.y
      if (otherAnchorY - bendPoint.y).abs > MIN_VERT_DIFF then
        created ← addBendPoint created edge bendPoint addJunctionPoint port
  return created

/-- `processInLayerEdge(edge, layerXPos, edgeSpacing)`: one bend point beside the layer, half way between
the end points (east of the layer for an east source port, else west of it). -/
def processInLayerEdge (edge : LEdgeId) (layerXPos edgeSpacing : Float) : LayeredM Unit := do
  let a ← get
  let ed := a.edge edge
  let some sourcePort := ed.source | return
  let some targetPort := ed.target | return
  let sourceAnchorY := ((a.portAbsoluteAnchor sourcePort).map (·.y)).getD 0.0
  let sourceSide := (a.port sourcePort).side
  let sourceLayerWidth := (((a.port sourcePort).owner.bind fun n => (a.node n).layer).map fun l => (a.layer l).size.x).getD 0.0
  let targetAnchorY := ((a.portAbsoluteAnchor targetPort).map (·.y)).getD 0.0
  let midY := (sourceAnchorY + targetAnchorY) / 2.0
  let bendPoint : KVector := if sourceSide == .east then ⟨layerXPos + sourceLayerWidth + edgeSpacing, midY⟩
    else ⟨layerXPos - edgeSpacing, midY⟩
  modifyEdge edge fun x => { x with bendPoints := x.bendPoints.addFirst bendPoint }

/-- `calculateWestInLayerEdgeYDiff(layer)`: the largest vertical distance of an in-layer edge leaving a
west port of the layer. -/
def calculateWestInLayerEdgeYDiff (layer : LayerId) : LayeredM Float := do
  let a ← get
  let mut maxYDiff := fl0p0
  for node in (a.layer layer).nodes do
    for edge in a.nodeOutgoingEdges node do
      let ed := a.edge edge
      let some sourcePort := ed.source | continue
      let some targetPort := ed.target | continue
      let sourceSide := (a.port sourcePort).side
      let sourceAnchorY := ((a.portAbsoluteAnchor sourcePort).map (·.y)).getD fl0p0
      let targetInSameLayer := ((a.port targetPort).owner.bind fun n => (a.node n).layer) == some layer
      let targetAnchorY := ((a.portAbsoluteAnchor targetPort).map (·.y)).getD fl0p0
      if targetInSameLayer && sourceSide == .west then
        maxYDiff := fmax maxYDiff (targetAnchorY - sourceAnchorY).abs
  return maxYDiff

/-- Rust `process` outgoing edge loop data of an arena edge: `(source y, source side, target y,
target in the node's layer, self loop)`. -/
private def arenaEdgeData (edge : LEdgeId) (nodeLayer : Option LayerId) : LayeredM (Float × PortSide × Float × Bool × Bool) := do
  let a ← get
  let ed := a.edge edge
  match ed.source, ed.target with
  | some src, some tgt =>
    if src == tgt then return (fl0p0, .undefined, fl0p0, false, true)
    let srcAnchor := (a.portAbsoluteAnchor src).getD {}
    let tgtAnchor := (a.portAbsoluteAnchor tgt).getD {}
    let tgtLayer := (a.port tgt).owner.bind fun n => (a.node n).layer
    let inSameLayer := nodeLayer.isSome && tgtLayer.isSome && nodeLayer == tgtLayer
    return (srcAnchor.y, (a.port src).side, tgtAnchor.y, inSameLayer, false)
  | _, _ => return (fl0p0, .undefined, fl0p0, false, true)

/-- The outgoing-edge part of the per-node loop of `process`: in-layer edges get their bend point, and
the largest vertical distance of the node's other outgoing edges is returned. -/
private def processOutgoingEdges (node : LNodeId) (scope : ArenaScope) (xpos edgeSpaceFac : Float) : LayeredM Float := do
  let nd ← getNode node
  let outgoingEdges ← withArena fun a => nd.ports.foldl (fun acc p => acc ++ scope.portOutgoingEdges a p) #[]
  let mut maxCurrOutputYDiff := fl0p0
  for edge in outgoingEdges do
    let (sourcePos, sourceSide, targetPos, targetInSameLayer, isSelfLoop) ← arenaEdgeData edge nd.layer
    if targetInSameLayer && !isSelfLoop then
      let yDiff := (sourcePos - targetPos).abs
      processInLayerEdge edge xpos (LAYER_SPACE_FAC * edgeSpaceFac * yDiff)
      if sourceSide == .west then
        maxCurrOutputYDiff := fmax maxCurrOutputYDiff fl0p0
        continue
    maxCurrOutputYDiff := fmax maxCurrOutputYDiff (targetPos - sourcePos).abs
  return maxCurrOutputYDiff

/-- `process(layeredGraph, monitor)`. -/
def process (graph : LGraphId) (monitor : ProgressMonitor) : LayeredM Unit := do
  let _ ← monitor.begin "Polyline edge routing" fl1p0
  let gr ← getGraph graph
  let slopedEdgeZoneWidth := (gr.props.get LayeredOptions.EDGE_ROUTING_POLYLINE_SLOPED_EDGE_ZONE_WIDTH).getD fl0p0
  let nodeSpacing := (gr.props.get LayeredOptions.SPACING_NODE_NODE_BETWEEN_LAYERS).getD fl0p0
  let edgeSpacing := (gr.props.get LayeredOptions.SPACING_EDGE_EDGE_BETWEEN_LAYERS).getD fl0p0
  let edgeSpaceFac := if nodeSpacing.abs < Float.epsilon then fl0p0 else fmin (edgeSpacing / nodeSpacing) fl1p0
  let scope ← withArena (ArenaScope.ofGraph · graph)
  let layers := gr.layers
  let mut layerSizeX : Std.HashMap LayerId Float := {}
  for l in layers do
    layerSizeX := layerSizeX.insert l (← getLayer l).size.x
  let mut created : Std.HashSet KVector := {}
  let mut xpos := fl0p0
  if let some firstLayer := layers[0]? then
    let yDiff ← calculateWestInLayerEdgeYDiff firstLayer
    xpos := LAYER_SPACE_FAC * edgeSpaceFac * yDiff
  let mut layerIndex := 0
  while layerIndex < layers.size do
    let layer := layers[layerIndex]!
    let nodes := (← getLayer layer).nodes
    let externalLayer ← nodes.allM isExternalWestOrEastPort
    if externalLayer && xpos > fl0p0 then xpos := xpos - nodeSpacing
    LGraphUtil.placeNodesHorizontally layer xpos
    let mut maxVertDiff := fl0p0
    for node in nodes do
      let maxCurrOutputYDiff ← processOutgoingEdges node scope xpos edgeSpaceFac
      match (← getNode node).type with
      | .normal | .label | .longEdge | .northSouthPort | .breakingPoint =>
        created ← processNode created node xpos slopedEdgeZoneWidth layerSizeX
      | _ => pure ()
      maxVertDiff := fmax maxVertDiff maxCurrOutputYDiff
    if layerIndex + 1 < layers.size then
      let yDiff ← calculateWestInLayerEdgeYDiff layers[layerIndex + 1]!
      maxVertDiff := fmax maxVertDiff yDiff
    let mut layerSpacing := LAYER_SPACE_FAC * edgeSpaceFac * maxVertDiff
    if !externalLayer && layerIndex + 1 < layers.size then layerSpacing := layerSpacing + nodeSpacing
    let layerWidth := (← getLayer layer).size.x
    xpos := xpos + (layerWidth + layerSpacing)
    layerIndex := layerIndex + 1
  let finalX := xpos
  modifyGraph graph fun g => { g with size := { g.size with x := finalX } }
  monitor.done

/-- `getLayoutProcessorConfiguration(graph)`: the baseline plus the additions for north/south ports, self
loops, center and end labels. -/
def getLayoutProcessorConfiguration (graph : LGraphId) : LayeredM (Option LayeredProcessorConfiguration) := do
  let graphProperties := (← getGraph graph).internal.graphProperties
  let mut configuration := LayoutProcessorConfiguration.createFrom BASELINE_PROCESSOR_CONFIGURATION
  if graphProperties.contains .northSouthPorts then
    configuration := configuration.addAll NORTH_SOUTH_PORT_PROCESSING_ADDITIONS
  if graphProperties.contains .selfLoops then
    configuration := configuration.addAll SELF_LOOP_PROCESSING_ADDITIONS
  if graphProperties.contains .centerLabels then
    configuration := configuration.addAll CENTER_EDGE_LABEL_PROCESSING_ADDITIONS
  if graphProperties.contains .endLabels then
    configuration := configuration.addAll END_EDGE_LABEL_PROCESSING_ADDITIONS
  return some configuration

/-- The phase (`new PolylineEdgeRouter()`). -/
def phase : LayeredPhase :=
  { name := "PolylineEdgeRouter"
    process := process
    getLayoutProcessorConfiguration := getLayoutProcessorConfiguration }

end PolylineEdgeRouter

builtin_initialize registerPolylineEdgeRouter : Unit ←
  LayeredPhases.registerPhase .p5EdgeRouting (ElkEnum.ordinal EdgeRouting.polyline) (pure PolylineEdgeRouter.phase)

end Elk.Alg.Layered.P5Edges
