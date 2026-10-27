import Elk.Alg.Layered.Graph.Monad
import Elk.Alg.Layered.Options.LayeredOptions
import Elk.Alg.Layered.Options.Spacings
import Elk.Core.Util.Java
/-!
# `org.eclipse.elk.alg.layered.graph.LGraphUtil` (+ `LEdge.reverse`, `LNode.getInteractiveReferencePoint`)

Ported from elk-rs `l_graph_util.rs`; the Java `float` intermediates of `resizeNode` are
reproduced with `Float.toF32`.
-/
namespace Elk.Alg.Layered.Graph

open Elk.Graph Elk.Core Elk.Core.Math Elk.Core.Options Elk.Core.Util Elk.Alg.Layered.Options LayeredM

namespace LGraphUtil

/-- `resizeNode(node, newSize, movePorts, moveLabels)`: scales port and label positions
with the node and marks the node size as fixed. -/
def resizeNode (node : LNodeId) (newSize : KVector) (movePorts moveLabels : Bool) : LayeredM Unit := do
  let nd ← getNode node
  let oldSize := nd.size
  let fixedPorts := nd.props.getD CoreOptions.PORT_CONSTRAINTS PortConstraints.undefined == .fixedPos
  -- Java uses float for these variables
  let widthRatio := if oldSize.x == 0.0 then 1.0 else Float.toF32 (newSize.x / oldSize.x)
  let heightRatio := if oldSize.y == 0.0 then 1.0 else Float.toF32 (newSize.y / oldSize.y)
  let widthDiff := Float.toF32 (newSize.x - oldSize.x)
  let heightDiff := Float.toF32 (newSize.y - oldSize.y)
  if movePorts then
    for p in nd.ports do
      modifyPort p fun pt =>
        let pos := pt.position
        let pos := match pt.side with
          | .north => if !fixedPorts then { pos with x := pos.x * widthRatio } else pos
          | .east =>
            let pos := { pos with x := pos.x + widthDiff }
            if !fixedPorts then { pos with y := pos.y * heightRatio } else pos
          | .south =>
            let pos := if !fixedPorts then { pos with x := pos.x * widthRatio } else pos
            { pos with y := pos.y + heightDiff }
          | .west => if !fixedPorts then { pos with y := pos.y * heightRatio } else pos
          | .undefined => pos
        { pt with position := pos }
  -- relative label placement is undefined on a collapsed rectangle
  if moveLabels && oldSize.x != 0.0 && oldSize.y != 0.0 then
    for l in nd.labels do
      modifyLabel l fun lb =>
        let midx := lb.position.x + lb.size.x / 2.0
        let midy := lb.position.y + lb.size.y / 2.0
        let widthPercent := midx / oldSize.x
        let heightPercent := midy / oldSize.y
        if widthPercent + heightPercent >= 1.0 then
          if widthPercent - heightPercent > 0.0 && midy >= 0.0 then
            { lb with position := ⟨lb.position.x + widthDiff, lb.position.y + heightDiff * heightPercent⟩ }
          else if widthPercent - heightPercent < 0.0 && midx >= 0.0 then
            { lb with position := ⟨lb.position.x + widthDiff * widthPercent, lb.position.y + heightDiff⟩ }
          else lb
        else lb
  modifyNode node fun x => { x with size := newSize, props := x.props.set CoreOptions.NODE_SIZE_CONSTRAINTS SizeConstraint.fixed }

/-- `offsetGraph(graph, offsetx, offsety)`: moves the layerless nodes, their outgoing edges'
bend points, junction points and edge labels. -/
def offsetGraph (graph : LGraphId) (offsetx offsety : Float) : LayeredM Unit := do
  let graphOffset : KVector := ⟨offsetx, offsety⟩
  for n in (← getGraph graph).layerlessNodes do
    modifyNode n fun nd => { nd with position := nd.position + graphOffset }
    for p in (← getNode n).ports do
      for e in (← getPort p).outgoingEdges do
        modifyEdge e fun ed =>
          let ed := { ed with bendPoints := ed.bendPoints.offsetValues offsetx offsety }
          match ed.props.get CoreOptions.JUNCTION_POINTS with
          | some jps => { ed with props := ed.props.set CoreOptions.JUNCTION_POINTS (jps.offsetValues offsetx offsety) }
          | none => ed
        for l in (← getEdge e).labels do
          modifyLabel l fun lb => { lb with position := lb.position + graphOffset }

/-- `offsetGraphs(graphs, offsetx, offsety)`. -/
def offsetGraphs (graphs : Array LGraphId) (offsetx offsety : Float) : LayeredM Unit := do
  for g in graphs do offsetGraph g offsetx offsety

/-- `placeNodesHorizontally(layer, xoffset)`: x coordinates by alignment within the layer width. -/
def placeNodesHorizontally (layer : LayerId) (xoffset : Float) : LayeredM Unit := do
  let lay ← getLayer layer
  if lay.size.x <= 0.0 then
    let mut maxWidth := 0.0
    for n in lay.nodes do
      let nd ← getNode n
      let width := nd.size.x + nd.margin.left + nd.margin.right
      if width > maxWidth then maxWidth := width
    modifyLayer layer fun l => { l with size := { l.size with x := maxWidth } }
  let lay ← getLayer layer
  let layerSize := lay.size
  let mut maxLeftMargin := 0.0
  let mut maxRightMargin := 0.0
  for n in lay.nodes do
    let nd ← getNode n
    maxLeftMargin := fmax maxLeftMargin nd.margin.left
    maxRightMargin := fmax maxRightMargin nd.margin.right
  for n in lay.nodes do
    let nd ← getNode n
    let alignment := nd.props.getD CoreOptions.ALIGNMENT Alignment.center
    let ratio ← (do
      match alignment with
      | .left => pure 0.0
      | .right => pure 1.0
      | .center => pure 0.5
      | _ =>
        let mut inports := 0
        let mut outports := 0
        for p in nd.ports do
          let pt ← getPort p
          if !pt.incomingEdges.isEmpty then inports := inports + 1
          if !pt.outgoingEdges.isEmpty then outports := outports + 1
        if inports + outports == 0 then pure 0.5
        else pure (outports.toFloat / (inports + outports).toFloat))
    let mut xpos := (layerSize.x - nd.size.x) * ratio
    if ratio > 0.5 then xpos := xpos - maxRightMargin * 2.0 * (ratio - 0.5)
    else if ratio < 0.5 then xpos := xpos + maxLeftMargin * 2.0 * (0.5 - ratio)
    if xpos < nd.margin.left then xpos := nd.margin.left
    let maxX := layerSize.x - nd.margin.right - nd.size.x
    if xpos > maxX then xpos := maxX
    let finalX := xoffset + xpos
    modifyNode n fun x => { x with position := { x.position with x := finalX } }

/-- `findMaxNonDummyNodeWidth(layer, direction, respectNodeMargins)`. -/
def findMaxNonDummyNodeWidth (layer : LayerId) (direction : Direction) (respectNodeMargins : Bool) : LayeredM Float := do
  if direction.isVertical then return 0.0
  let mut maxWidth := 0.0
  for n in (← getLayer layer).nodes do
    let nd ← getNode n
    if nd.type == .normal then
      let width := if respectNodeMargins then nd.size.x + nd.margin.left + nd.margin.right else nd.size.x
      if width > maxWidth then maxWidth := width
  return maxWidth

/-- `getDirection(graph)`: the configured direction, else by aspect ratio (`RIGHT` for `≥ 1`). -/
def getDirection (graph : LGraphId) : LayeredM Direction := do
  let gr ← getGraph graph
  let direction := gr.props.getD CoreOptions.DIRECTION Direction.undefined
  if direction == .undefined then
    let aspectRatio := gr.props.getD CoreOptions.ASPECT_RATIO 1.0
    return if aspectRatio >= 1.0 then .right else .down
  return direction

/-- `computeGraphProperties(layeredGraph)`: sets the `GRAPH_PROPERTIES` flags from the
layerless nodes (and normalises `UNDEFINED` port constraints to `FREE`). -/
def computeGraphProperties (graph : LGraphId) : LayeredM Unit := do
  let direction ← getDirection graph
  let nodes := (← getGraph graph).layerlessNodes
  let mut props := (← getGraph graph).internal.graphProperties
  for n in nodes do
    let nd ← getNode n
    let isComment := nd.props.getD CoreOptions.COMMENT_BOX false
    let isHypernode := nd.props.getD CoreOptions.HYPERNODE false
    if isComment then props := props.insert .comments
    else if isHypernode then
      props := props.insert .hypernodes
      props := props.insert .hyperedges
    else if nd.type == .externalPort then props := props.insert .externalPorts
    let portConstraints := nd.props.getD CoreOptions.PORT_CONSTRAINTS PortConstraints.undefined
    let normalized ← (do
      if portConstraints == .undefined then
        setNodeProp n CoreOptions.PORT_CONSTRAINTS PortConstraints.free
        pure PortConstraints.free
      else pure portConstraints)
    if normalized != .free then props := props.insert .nonFreePorts
    for p in nd.ports do
      let pt ← getPort p
      if pt.incomingEdges.size + pt.outgoingEdges.size > 1 then props := props.insert .hyperedges
      match direction with
      | .up | .down => if pt.side == .east || pt.side == .west then props := props.insert .northSouthPorts
      | _ => if pt.side == .north || pt.side == .south then props := props.insert .northSouthPorts
      for e in pt.outgoingEdges do
        let ed ← getEdge e
        if let some t := ed.target then
          if (← getPort t).owner == some n then props := props.insert .selfLoops
        for l in ed.labels do
          match (← getLabel l).props.getD CoreOptions.EDGE_LABELS_PLACEMENT EdgeLabelPlacement.center with
          | .center => props := props.insert .centerLabels
          | .head | .tail => props := props.insert .endLabels
  let finalProps := props
  modifyGraph graph fun g => { g with internal := { g.internal with graphProperties := finalProps } }

/-- `calcPortSide(port, direction)`: the side a port (positioned relative to its node) lies on. -/
def calcPortSide (port : LPortId) (direction : Direction) : LayeredM PortSide := do
  let pt ← getPort port
  let some node := pt.owner | return .undefined
  let nodeSize := (← getNode node).size
  if nodeSize.x <= 0.0 && nodeSize.y <= 0.0 then return .undefined
  let pos := pt.position
  let size := pt.size
  match direction with
  | .left | .right =>
    if pos.x < 0.0 then return .west
    if pos.x + size.x > nodeSize.x then return .east
  | .up | .down =>
    if pos.y < 0.0 then return .north
    if pos.y + size.y > nodeSize.y then return .south
  | _ => pure ()
  let widthPercent := (pos.x + size.x / 2.0) / nodeSize.x
  let heightPercent := (pos.y + size.y / 2.0) / nodeSize.y
  if widthPercent + heightPercent <= 1.0 && widthPercent - heightPercent <= 0.0 then return .west
  else if widthPercent + heightPercent >= 1.0 && widthPercent - heightPercent >= 0.0 then return .east
  else if heightPercent < 0.5 then return .north
  else return .south

/-- `calcPortOffset(port, side)`: distance of the port from the node border on its side. -/
def calcPortOffset (port : LPortId) (side : PortSide) : LayeredM Float := do
  let pt ← getPort port
  let some node := pt.owner | return 0.0
  let nodeSize := (← getNode node).size
  let pos := pt.position
  let size := pt.size
  return match side with
    | .north => -(pos.y + size.y)
    | .east => pos.x - nodeSize.x
    | .south => pos.y - nodeSize.y
    | .west => -(pos.x + size.x)
    | .undefined => 0.0

/-- `centerPoint(point, boundary, side)`: the point on the middle of the given side of a
`boundary`-sized box (undefined side leaves the point unchanged). -/
def centerPoint (point boundary : KVector) (side : PortSide) : KVector :=
  match side with
  | .north => ⟨boundary.x / 2.0, 0.0⟩
  | .east => ⟨boundary.x, boundary.y / 2.0⟩
  | .south => ⟨boundary.x / 2.0, boundary.y⟩
  | .west => ⟨0.0, boundary.y / 2.0⟩
  | .undefined => point

/-- `provideCollectorPort(layeredGraph, node, type, side)`: the node's collector port of that
type, created on demand (an `UNDEFINED` type yields a fresh unattached port, as in Rust). -/
def provideCollectorPort (_graph : LGraphId) (node : LNodeId) (portType : PortType) (side : PortSide) : LayeredM LPortId := do
  let nd ← getNode node
  let existing : Option LPortId ← (do
    match portType with
    | .input =>
      for candidate in nd.ports do
        if (← getPort candidate).internal.inputCollect then return some candidate
      return none
    | .output =>
      for candidate in nd.ports do
        if (← getPort candidate).internal.outputCollect then return some candidate
      return none
    | .undefined => return none)
  if let some p := existing then return p
  match portType with
  | .undefined => createPort
  | _ =>
    let port ← createPort
    modifyPort port fun pt => { pt with internal := match portType with
      | .input => { pt.internal with inputCollect := true }
      | _ => { pt.internal with outputCollect := true } }
    setPortNode port (some node)
    let size := (← getNode node).size
    modifyPort port fun pt =>
      let pt := pt.setSide side
      { pt with position := centerPoint pt.position size side }
    return port

/-- `initializePort(port, portConstraints, direction, anchorPos)`: side, border offset,
ratio and anchor of an imported port. -/
def initializePort (port : LPortId) (portConstraints : PortConstraints) (direction : Direction) (anchorPos : Option KVector) : LayeredM Unit := do
  let mut portSide := (← getPort port).side
  if portSide == .undefined && portConstraints.isSideFixed then
    portSide ← calcPortSide port direction
    let side := portSide
    modifyPort port fun pt => pt.setSide side
    let pt ← getPort port
    let hasBorderOffset := pt.props.has CoreOptions.PORT_BORDER_OFFSET
    if !hasBorderOffset && portSide != .undefined && (pt.position.x != 0.0 || pt.position.y != 0.0) then
      let offset ← calcPortOffset port portSide
      setPortProp port CoreOptions.PORT_BORDER_OFFSET offset
  if portConstraints.isRatioFixed then
    let pt ← getPort port
    let nodeSize ← match pt.owner with
      | some n => pure (← getNode n).size
      | none => pure ({} : KVector)
    let ratio := match portSide with
      | .north | .south => if nodeSize.x > 0.0 then pt.position.x / nodeSize.x else 0.0
      | .east | .west => if nodeSize.y > 0.0 then pt.position.y / nodeSize.y else 0.0
      | .undefined => 0.0
    modifyPort port fun x => { x with internal := { x.internal with portRatioOrPosition := ratio } }
  let side := portSide
  modifyPort port fun pt =>
    let portSize := pt.size
    match anchorPos with
    | some a => { pt with anchor := a, explicitlySuppliedPortAnchor := true }
    | none =>
      if portConstraints.isSideFixed && side != .undefined then
        match side with
        | .north => { pt with anchor := { pt.anchor with x := portSize.x / 2.0 } }
        | .east => { pt with anchor := ⟨portSize.x, portSize.y / 2.0⟩ }
        | .south => { pt with anchor := ⟨portSize.x / 2.0, portSize.y⟩ }
        | .west => { pt with anchor := { pt.anchor with y := portSize.y / 2.0 } }
        | .undefined => pt
      else { pt with anchor := ⟨portSize.x / 2.0, portSize.y / 2.0⟩ }

/-- `createPort(node, endPoint, type, layeredGraph)`: a port for an edge end point; for
merged edges / hypernodes without fixed sides the node's collector port is reused. -/
def createPort (node : LNodeId) (endPoint : Option KVector) (portType : PortType) (graph : LGraphId) : LayeredM LPortId := do
  let direction ← getDirection graph
  let mergePorts := (← getGraph graph).props.getD LayeredOptions.MERGE_EDGES false
  let nd ← getNode node
  let nodeIsHyper := nd.props.getD CoreOptions.HYPERNODE false
  let portConstraints := nd.props.getD CoreOptions.PORT_CONSTRAINTS PortConstraints.undefined
  if (mergePorts || nodeIsHyper) && !portConstraints.isSideFixed then
    let defaultSide := PortSide.fromDirection direction
    let side := match portType with
      | .output => defaultSide
      | .input => defaultSide.opposed
      | .undefined => defaultSide
    return ← provideCollectorPort graph node portType side
  let port ← LayeredM.createPort
  setPortNode port (some node)
  match endPoint with
  | some endPoint =>
    let nd ← getNode node
    modifyPort port fun pt =>
      let pos : KVector := ⟨endPoint.x - nd.position.x, endPoint.y - nd.position.y⟩
      { pt with position := pos.bound 0.0 0.0 nd.size.x nd.size.y }
    let side ← calcPortSide port direction
    modifyPort port fun pt => pt.setSide side
  | none =>
    let defaultSide := PortSide.fromDirection direction
    let side := match portType with
      | .output => defaultSide
      | .input => defaultSide.opposed
      | .undefined => defaultSide
    modifyPort port fun pt => pt.setSide side
  let portSide := (← getPort port).side
  let northSouth : Bool := match direction with
    | .left | .right => portSide == .north || portSide == .south
    | .up | .down => portSide == .east || portSide == .west
    | .undefined => false
  if northSouth then
    modifyGraph graph fun g => { g with internal := { g.internal with graphProperties := g.internal.graphProperties.insert .northSouthPorts } }
  return port

/-- `createExternalPortDummy(propertyHolder, portConstraints, portSide, netFlow, portNodeSize,
portPosition, portSize, layoutDirection, layeredGraph)`: the dummy node representing an external
port; returns it with the (possibly updated: `PORT_SIDE`) property holder. -/
def createExternalPortDummy (propertyHolder : PropertyMap) (portConstraints : PortConstraints) (portSide : PortSide)
    (netFlow : Int) (portNodeSize portPosition portSize : KVector) (layoutDirection : Direction) (graph : LGraphId) :
    LayeredM (LNodeId × PropertyMap) := do
  let mut holder := propertyHolder
  let mut finalExternalPortSide := portSide
  let portBorderOffset := holder.getD CoreOptions.PORT_BORDER_OFFSET 0.0
  let dummy ← createNode graph { type := .externalPort }
  modifyNode dummy fun nd => { nd with
    internal := { nd.internal with extPortSize := portSize },
    props := (nd.props.set CoreOptions.PORT_CONSTRAINTS PortConstraints.fixedPos).set CoreOptions.PORT_BORDER_OFFSET portBorderOffset }
  let dummyPort ← LayeredM.createPort
  setPortNode dummyPort (some dummy)
  if !portConstraints.isSideFixed then
    finalExternalPortSide := if netFlow >= 0 then PortSide.fromDirection layoutDirection
      else (PortSide.fromDirection layoutDirection).opposed
    holder := holder.set CoreOptions.PORT_SIDE finalExternalPortSide
  let explicitAnchor := holder.has CoreOptions.PORT_ANCHOR
  let mut anchor : KVector := if explicitAnchor then holder.getD CoreOptions.PORT_ANCHOR {} else ⟨portSize.x / 2.0, portSize.y / 2.0⟩
  match finalExternalPortSide with
  | .west =>
    modifyNode dummy fun nd => { nd with
      props := nd.props.set LayeredOptions.LAYERING_LAYER_CONSTRAINT LayerConstraint.firstSeparate,
      internal := { nd.internal with edgeConstraint := .outgoingOnly },
      size := ⟨if portBorderOffset < 0.0 then -portBorderOffset else nd.size.x, portSize.y⟩ }
    modifyPort dummyPort fun pt => pt.setSide .east
    if !explicitAnchor then anchor := { anchor with x := portSize.x }
    anchor := { anchor with x := anchor.x - portSize.x }
  | .east =>
    modifyNode dummy fun nd => { nd with
      props := nd.props.set LayeredOptions.LAYERING_LAYER_CONSTRAINT LayerConstraint.lastSeparate,
      internal := { nd.internal with edgeConstraint := .incomingOnly },
      size := ⟨if portBorderOffset < 0.0 then -portBorderOffset else nd.size.x, portSize.y⟩ }
    modifyPort dummyPort fun pt => pt.setSide .west
    if !explicitAnchor then anchor := { anchor with x := 0.0 }
  | .north =>
    modifyNode dummy fun nd => { nd with
      internal := { nd.internal with inLayerConstraint := .top },
      size := ⟨portSize.x, if portBorderOffset < 0.0 then -portBorderOffset else nd.size.y⟩ }
    modifyPort dummyPort fun pt => pt.setSide .south
    if !explicitAnchor then anchor := { anchor with y := portSize.y }
    anchor := { anchor with y := anchor.y - portSize.y }
  | .south =>
    modifyNode dummy fun nd => { nd with
      internal := { nd.internal with inLayerConstraint := .bottom },
      size := ⟨portSize.x, if portBorderOffset < 0.0 then -portBorderOffset else nd.size.y⟩ }
    modifyPort dummyPort fun pt => pt.setSide .north
    if !explicitAnchor then anchor := { anchor with y := 0.0 }
  | .undefined => pure ()
  let finalAnchor := anchor
  modifyPort dummyPort fun pt => { pt with position := finalAnchor }
  setNodeProp dummy CoreOptions.PORT_ANCHOR finalAnchor
  if portConstraints.isOrderFixed then
    let mut infoValue := 0.0
    if portConstraints == .fixedOrder && holder.has CoreOptions.PORT_INDEX then
      let index := (holder.getD CoreOptions.PORT_INDEX 0).toFloat
      match finalExternalPortSide with
      | .north | .east => infoValue := index
      | .south | .west => infoValue := -index
      | .undefined => pure ()
    else
      match finalExternalPortSide with
      | .west | .east =>
        infoValue := portPosition.y
        if portConstraints.isRatioFixed && portNodeSize.y > 0.0 then infoValue := infoValue / portNodeSize.y
      | .north | .south =>
        infoValue := portPosition.x
        if portConstraints.isRatioFixed && portNodeSize.x > 0.0 then infoValue := infoValue / portNodeSize.x
      | .undefined => pure ()
    let v := infoValue
    modifyNode dummy fun nd => { nd with internal := { nd.internal with portRatioOrPosition := v } }
  let side := finalExternalPortSide
  modifyNode dummy fun nd => { nd with internal := { nd.internal with extPortSide := side } }
  return (dummy, holder)

/-- `getExternalPortPosition(graph, portDummy, portWidth, portHeight)`: the external port's
position in the parent's coordinates (also moves the dummy to the graph border). -/
def getExternalPortPosition (graph : LGraphId) (portDummy : LNodeId) (portWidth portHeight : Float) : LayeredM KVector := do
  let nd ← getNode portDummy
  let mut portPos : KVector := ⟨nd.position.x + nd.size.x / 2.0, nd.position.y + nd.size.y / 2.0⟩
  let portOffset := nd.props.getD CoreOptions.PORT_BORDER_OFFSET 0.0
  let extSide := nd.internal.extPortSide
  let gr ← getGraph graph
  let graphSize := gr.size
  let padding := gr.padding
  let graphOffset := gr.offset
  let connectedComponentsCompaction := gr.props.getD LayeredOptions.COMPACTION_CONNECTED_COMPONENTS false
  match extSide with
  | .north =>
    portPos := { portPos with x := portPos.x + padding.left + graphOffset.x - portWidth / 2.0 }
    -- Java's compactor can produce half-step northern external port coordinates for compacted
    -- connected-component layouts (elk-rs parity quirk)
    if connectedComponentsCompaction && Float.abs portWidth <= 1e-9 && Float.abs (portPos.x - Float.floor portPos.x) <= 1e-9 then
      portPos := { portPos with x := portPos.x + 0.5 }
    portPos := { portPos with y := -portHeight - portOffset }
    modifyNode portDummy fun x => { x with position := { x.position with y := -(padding.top + portOffset + graphOffset.y) } }
  | .east =>
    portPos := ⟨graphSize.x + padding.left + padding.right + portOffset, portPos.y + padding.top + graphOffset.y - portHeight / 2.0⟩
    modifyNode portDummy fun x => { x with position := { x.position with x := graphSize.x + padding.right + portOffset - graphOffset.x } }
  | .south =>
    portPos := ⟨portPos.x + padding.left + graphOffset.x - portWidth / 2.0, graphSize.y + padding.top + padding.bottom + portOffset⟩
    modifyNode portDummy fun x => { x with position := { x.position with y := graphSize.y + padding.bottom + portOffset - graphOffset.y } }
  | .west =>
    portPos := ⟨-portWidth - portOffset, portPos.y + padding.top + graphOffset.y - portHeight / 2.0⟩
    modifyNode portDummy fun x => { x with position := { x.position with x := -(padding.left + portOffset + graphOffset.x) } }
  | .undefined => pure ()
  return portPos

/-- `isDescendant(child, parent)`: whether `parent` is an ancestor node of `child` via nested graphs. -/
partial def isDescendant (child parent : LNodeId) : LayeredM Bool := do
  let next ← (do
    match ← nodeGraph child with
    | some g => pure (← getGraph g).parentNode
    | none => pure none)
  match next with
  | none => return false
  | some next => if next == parent then return true else isDescendant next parent

/-- `changeCoordSystem(point, oldGraph, newGraph)`: converts a point between the coordinate
systems of two graphs of the same hierarchy. -/
partial def changeCoordSystem (point : KVector) (oldGraph newGraph : LGraphId) : LayeredM KVector := do
  if oldGraph == newGraph then return point
  let rec up (point : KVector) (graph : LGraphId) : LayeredM KVector := do
    let gr ← getGraph graph
    let point := point + gr.offset
    match gr.parentNode with
    | some node =>
      let point := point.addValues gr.padding.left gr.padding.top
      let point := point + (← getNode node).position
      match ← nodeGraph node with
      | some parentGraph => up point parentGraph
      | none => return point
    | none => return point
  let rec down (point : KVector) (graph : LGraphId) : LayeredM KVector := do
    let gr ← getGraph graph
    let point := point - gr.offset
    match gr.parentNode with
    | some node =>
      let point := point.addValues (-gr.padding.left) (-gr.padding.top)
      let point := point - (← getNode node).position
      match ← nodeGraph node with
      | some parentGraph => down point parentGraph
      | none => return point
    | none => return point
  let point ← up point oldGraph
  down point newGraph

/-- `getIndividualOrInherited(node, property)`: the node's individual spacing if set, else the
node's graph value (stored or default). -/
def getIndividualOrInherited {α : Type} [PropCodec α] (node : LNodeId) (p : Property α) : LayeredM (Option α) := do
  let nd ← getNode node
  let mut result : Option α := none
  if nd.props.has CoreOptions.SPACING_INDIVIDUAL then
    if let some individual := nd.props.get CoreOptions.SPACING_INDIVIDUAL then
      if individual.props.has p then result := individual.props.get p
  if result.isNone then
    if let some g ← nodeGraph node then
      result := (← getGraph g).props.get p
  return result

/-- `getMinimalModelOrder(graph)`: the smallest `MODEL_ORDER` of the layerless nodes
(`Integer.MAX_VALUE` when none is set). -/
def getMinimalModelOrder (graph : LGraphId) : LayeredM Int := do
  let mut order : Int := 2147483647
  for n in (← getGraph graph).layerlessNodes do
    if let some value := (← getNode n).internal.modelOrder then
      if value < order then order := value
  return order

/-- `LEdge.reverse(layeredGraph, adaptPorts)`: swaps source and target (using collector ports
when `adaptPorts` and the ports are collectors), flips HEAD/TAIL labels, toggles `REVERSED`
and reverses the bend points. -/
def reverseEdge (edge : LEdgeId) (graph : LGraphId) (adaptPorts : Bool) : LayeredM Unit := do
  let ed ← getEdge edge
  let oldSource := ed.source
  let oldTarget := ed.target
  setEdgeSource edge none
  setEdgeTarget edge none
  if let some oldTarget := oldTarget then
    let useCollector := adaptPorts && (← getPort oldTarget).internal.inputCollect
    if useCollector then
      if let some node := (← getPort oldTarget).owner then
        let port ← provideCollectorPort graph node .output .east
        setEdgeSource edge (some port)
    else
      setEdgeSource edge (some oldTarget)
  if let some oldSource := oldSource then
    let useCollector := adaptPorts && (← getPort oldSource).internal.outputCollect
    if useCollector then
      if let some node := (← getPort oldSource).owner then
        let port ← provideCollectorPort graph node .input .west
        setEdgeTarget edge (some port)
    else
      setEdgeTarget edge (some oldSource)
  for l in (← getEdge edge).labels do
    modifyLabel l fun lb =>
      match lb.props.getD CoreOptions.EDGE_LABELS_PLACEMENT EdgeLabelPlacement.center with
      | .tail => { lb with props := lb.props.set CoreOptions.EDGE_LABELS_PLACEMENT EdgeLabelPlacement.head }
      | .head => { lb with props := lb.props.set CoreOptions.EDGE_LABELS_PLACEMENT EdgeLabelPlacement.tail }
      | .center => lb
  modifyEdge edge fun ed => { ed with
    internal := { ed.internal with reversed := !ed.internal.reversed },
    bendPoints := ed.bendPoints.reverse }

/-- `LNode.getInteractiveReferencePoint()`. -/
def interactiveReferencePoint (node : LNodeId) : LayeredM (Option KVector) := do
  let some g ← nodeGraph node | return none
  let reference := (← getGraph g).props.getD LayeredOptions.INTERACTIVE_REFERENCE_POINT InteractiveReferencePoint.center
  let nd ← getNode node
  return some (match reference with
    | .center => ⟨nd.position.x + nd.size.x / 2.0, nd.position.y + nd.size.y / 2.0⟩
    | .topLeft => nd.position)

/-- Draws from the graph's random generator (`InternalProperties.RANDOM`, shared by all users
in Java/elk-rs) and stores the advanced generator back; a missing generator starts at seed 0
like elk-rs `Random::default()`. -/
def drawRandom {α : Type} (graph : LGraphId) (f : Random → α × Random) : LayeredM α := do
  let random := (← getGraph graph).internal.random.getD (Random.ofInt 0)
  let (value, random') := f random
  modifyGraph graph fun g => { g with internal := { g.internal with random := some random' } }
  return value

/-- `Spacings.getHorizontalSpacing(n1, n2)` on arena nodes. -/
def horizontalSpacing (s : Spacings) (n1 n2 : LNodeId) : LayeredM Float := do
  let a ← getNode n1
  let b ← getNode n2
  s.getHorizontalSpacing a.type a.props b.type b.props

/-- `Spacings.getVerticalSpacing(n1, n2)` on arena nodes. -/
def verticalSpacing (s : Spacings) (n1 n2 : LNodeId) : LayeredM Float := do
  let a ← getNode n1
  let b ← getNode n2
  s.getVerticalSpacing a.type a.props b.type b.props

/-- `Spacings.getIndividualOrDefault(node, property)`: individual/inherited value, else the
property default; throws `UnspecifiedSpacingException` when neither exists. -/
def individualOrDefault {α : Type} [PropCodec α] (node : LNodeId) (p : Property α) : LayeredM α := do
  match ← getIndividualOrInherited node p with
  | some v => return v
  | none => match p.default with
    | some d => return d
    | none => throw (unspecifiedSpacing)

end LGraphUtil

end Elk.Alg.Layered.Graph
