import Std.Data.HashMap
import Std.Data.HashSet
import Elk.Graph.Monad
import Elk.Core.Math.KVectorChain
import Elk.Core.Options
import Elk.Core.Util.ElkUtil
import Elk.Alg.Disco.Graph.DCGraph
import Elk.Alg.Disco.Options.DisCoOptions
import Elk.Alg.Disco.Transform.IGraphTransformer
import Elk.Alg.Disco.Transform.ElkGraphComponentsProcessor
import Elk.Core.Util.FloatConst
open Elk.Core.Util.FloatConst
/-!
# `org.eclipse.elk.alg.disco.transform.ElkGraphTransformer`

Transformation between an `ElkNode` and the `DCGraph` (elk-rs `transform/elk_graph_transformer.rs`).

`importGraph` splits the children of the layout graph into connected components
(`ElkGraphComponentsProcessor.split`) and creates one `DCElement` per node, node label, port, port
label, edge and edge label. Shapes become rectangles enlarged by the component spacing, edges
become the contour polygon around their polyline (`getContour`). Edges that connect a child to the
inside of a port of the layout graph ('external' edges) become `DCExtension`s of the shape they
are attached to. `applyLayout` moves every mapped element by the offset of its component, scales
the parent's labels and ports to the new size and snaps the first segment of the extension edges
to the border of the parent.

State: Rust keeps `element_mapping`, `incoming_extensions` and `outgoing_extensions` as
`HashMap`s keyed by object address and iterates `values()`. The Lean port iterates in insertion
order. The result does not depend on the order except for ports with several extension edges
(the first edge visited decides the port coordinate, in Rust/Java an arbitrary one).

Deviations from Rust:
* the transformed graph is not stored in the transformer; `applyLayout` takes it as an argument;
* Rust panics with `Use import_elk_edge for ElkEdge instances.` for edges in `import_elk_shape`;
  Lean throws `IllegalArgumentException` with the Java message of `ElkGraphTransformer`.
-/

namespace Elk.Alg.Disco.Transform

open Elk.Graph Elk.Core Elk.Core.Math Elk.Core.Util Elk.Core.Options
open Elk.Alg.Disco.Graph Elk.Alg.Disco.Options Elk.Alg.Disco.Transform.ElkGraphComponentsProcessor

/-- State of an `ElkGraphTransformer` (`parent`, `element_mapping`, `incoming_extensions`,
`outgoing_extensions`, `component_spacing`) plus the arena of the created `DCElement`s. -/
structure ElkGraphTransformer where
  /-- The imported graph (`parent`). -/
  parent : Option NodeId := none
  /-- The created elements; `DCElementId` indexes this array. -/
  elements : Array DCElement := #[]
  /-- `element_mapping`: ElkGraph element → its `DCElement`. -/
  elementMapping : Std.HashMap ElementId DCElementId := {}
  /-- Keys of `elementMapping` in first insertion order. -/
  mappingOrder : Array ElementId := #[]
  /-- `incoming_extensions` in insertion order. -/
  incomingExtensions : Array (EdgeId × DCExtension) := #[]
  /-- `outgoing_extensions` in insertion order. -/
  outgoingExtensions : Array (EdgeId × DCExtension) := #[]
  /-- `component_spacing`. -/
  componentSpacing : Float := 0

/-- The monad of the transformer: its state on top of `ElkM`. -/
abbrev TransformM := StateRefT ElkGraphTransformer ElkM

namespace ElkGraphTransformer

/-- `HALF_PI`. -/
private def HALF_PI : Float := Float.pi / 2.0

/-! ### Pure geometry -/

/-- `get_orthogonal_points`: the two points at distance `radius` perpendicular to the direction
from `(curX, curY)` to `(nxtX, nxtY)`, counter-clockwise first. Note the argument order of
`atan2` (`Math.atan2(difX, difY)`). The reference JVM's `Math.atan2` (fdlibm) and `Math.sin`/`Math.cos`
(HotSpot stubs) are used (`Elk.Core.Util.Java`). -/
private def getOrthogonalPoints (curX curY nxtX nxtY radius : Float) : KVector × KVector :=
  let difX := nxtX - curX
  let difY := nxtY - curY
  let angleRadians := javaAtan2 difX difY
  let orthAngleCcw := angleRadians + HALF_PI
  let orthAngleCw := angleRadians - HALF_PI
  let xCcw := radius * javaSin orthAngleCcw + curX
  let yCcw := radius * javaCos orthAngleCcw + curY
  let xCw := radius * javaSin orthAngleCw + curX
  let yCw := radius * javaCos orthAngleCw + curY
  (KVector.mk' xCcw yCcw, KVector.mk' xCw yCw)

/-- `compute_intersection(p1, p2, p3, p4)`: intersection of the lines `p1p2` and `p3p4`
(non-finite for parallel lines). -/
private def computeIntersection (p1 p2 p3 p4 : KVector) : KVector :=
  let x1 := p1.x
  let y1 := p1.y
  let x2 := p2.x
  let y2 := p2.y
  let x3 := p3.x
  let y3 := p3.y
  let x4 := p4.x
  let y4 := p4.y
  let factor1 := x1 * y2 - y1 * x2
  let factor2 := x3 * y4 - y3 * x4
  let denominator := (x1 - x2) * (y3 - y4) - (y1 - y2) * (x3 - x4)
  let x := (factor1 * (x3 - x4) - factor2 * (x1 - x2)) / denominator
  let y := (factor1 * (y3 - y4) - factor2 * (y1 - y2)) / denominator
  KVector.mk' x y

/-- Merges the offset points of one side of the polyline: at every inner corner the two offset
segments are intersected (the segment end point is kept if they are parallel). -/
private def mergeSide (pts : Array KVector) : Array KVector := Id.run do
  let mut merged : Array KVector := #[pts[0]!]
  let mut i := 1
  while i + 2 < pts.size do
    let currentPoint := pts[i]!
    let intersection := computeIntersection pts[i - 1]! currentPoint pts[i + 1]! pts[i + 2]!
    if !intersection.x.isFinite || !intersection.y.isFinite then
      merged := merged.push currentPoint
    else
      merged := merged.push intersection
    i := i + 2
  return merged.push pts[pts.size - 1]!

/-- `get_contour(edge_points, thickness)`: the polygon around the polyline with the given width
(empty for fewer than two points): the merged counter-clockwise side followed by the reversed
clockwise side. -/
def getContour (edgePoints : Array KVector) (thickness : Float) : KVectorChain := Id.run do
  if edgePoints.size < 2 then return #[]
  let mut ccwPoints : Array KVector := #[]
  let mut cwPoints : Array KVector := #[]
  let radius := thickness / 2.0
  let mut current := edgePoints[0]!
  let mut successor := edgePoints[1]!
  let (o0, o1) := getOrthogonalPoints current.x current.y successor.x successor.y radius
  ccwPoints := ccwPoints.push o0
  cwPoints := cwPoints.push o1
  for i in [2:edgePoints.size] do
    let predecessor := current
    current := successor
    successor := edgePoints[i]!
    let (a0, a1) := getOrthogonalPoints current.x current.y predecessor.x predecessor.y radius
    ccwPoints := ccwPoints.push a1
    cwPoints := cwPoints.push a0
    let (b0, b1) := getOrthogonalPoints current.x current.y successor.x successor.y radius
    ccwPoints := ccwPoints.push b0
    cwPoints := cwPoints.push b1
  let (c0, c1) := getOrthogonalPoints successor.x successor.y current.x current.y radius
  ccwPoints := ccwPoints.push c1
  cwPoints := cwPoints.push c0
  return mergeSide ccwPoints ++ (mergeSide cwPoints).reverse

/-! ### ElkGraph access -/

/-- Local `first_edge_section(edge, false, false)`: the first section, created if missing. -/
private def firstSection (e : EdgeId) : ElkM SectionId :=
  modifyGet fun g =>
    let (g, s) := ElkGraphUtil.firstEdgeSection g e false false
    (s, g)

/-- `ElkUtil.createVectorChain(section)`. -/
private def sectionChain (s : SectionId) : ElkM KVectorChain := do
  return ElkUtil.createVectorChain (← get) s

/-- `get_edge_thickness(edge)`: `EDGE_THICKNESS` or `0`. -/
private def edgeThickness (e : EdgeId) : ElkM Float := do
  return ((← ElkM.getEdge e).props.get DisCoOptions.EDGE_THICKNESS).getD 0.0

/-- `nearest_side(point, node)`: the side of the node closest to the point (north, south, west,
east; ties favour the earlier one). -/
private def nearestSide (point : KVector) (node : NodeId) : ElkM DCDirection := do
  let nd ← ElkM.getNode node
  let mut result := DCDirection.north
  let mut shortestDistance := point.y.abs
  let mut distance := (nd.height - point.y).abs
  if distance < shortestDistance then
    shortestDistance := distance
    result := DCDirection.south
  distance := point.x.abs
  if distance < shortestDistance then
    shortestDistance := distance
    result := DCDirection.west
  distance := (nd.width - point.x).abs
  if distance < shortestDistance then
    result := DCDirection.east
  return result

/-! ### Import -/

/-- Adds a `DCElement` (properties copied from `props`) to the arena. -/
private def newElement (shape : KVectorChain) (props : PropertyMap) : TransformM DCElementId :=
  modifyGetThe ElkGraphTransformer fun st =>
    let e : DCElement := { DCElement.new shape with properties := PropertyMap.copyFrom {} props }
    (⟨st.elements.size⟩, { st with elements := st.elements.push e })

/-- Records `key ↦ elem` in the element mapping (`element_mapping.insert`). -/
private def registerMapping (key : ElementId) (elem : DCElementId) : TransformM Unit :=
  modifyThe ElkGraphTransformer fun st =>
    { st with
      elementMapping := st.elementMapping.insert key elem
      mappingOrder := if st.elementMapping.contains key then st.mappingOrder else st.mappingOrder.push key }

/-- `import_elk_shape(element, consider_when_applying_offset, offset_x, offset_y)`: a rectangle
around the node, port or label, enlarged by the component spacing on every side. -/
private def importElkShape (element : ElementId) (considerWhenApplyingOffset : Bool)
    (offsetX offsetY : Float) : TransformM DCElementId := do
  let (x, y, width, height, props) ← match element with
    | .node n => do
      let nd ← ElkM.getNode n
      pure (nd.x, nd.y, nd.width, nd.height, nd.props)
    | .port p => do
      let pd ← ElkM.getPort p
      pure (pd.x, pd.y, pd.width, pd.height, pd.props)
    | .label l => do
      let ld ← ElkM.getLabel l
      pure (ld.x, ld.y, ld.width, ld.height, ld.props)
    | .edge _ => throwIllegalArgument "Method only works for ElkNode-, ElkLabel and ElkPort-objects."
  let componentSpacing := (← getThe ElkGraphTransformer).componentSpacing
  let halfComponentSpacing := componentSpacing / 2.0
  let x0 := x + offsetX - halfComponentSpacing
  let y0 := y + offsetY - halfComponentSpacing
  let x1 := x0 + width + componentSpacing
  let y1 := y0 + height + componentSpacing
  let coords : KVectorChain :=
    #[KVector.mk' x0 y0, KVector.mk' x0 y1, KVector.mk' x1 y1, KVector.mk' x1 y0]
  let elem ← newElement coords props
  if considerWhenApplyingOffset then
    registerMapping element elem
  return elem

/-- Imports the labels of an edge as shapes that move with the component. -/
private def importEdgeLabels (edge : EdgeId) (newComponent : Array DCElementId) :
    TransformM (Array DCElementId) := do
  let mut comp := newComponent
  for label in (← ElkM.getEdge edge).labels do
    comp := comp.push (← importElkShape (.label label) true fl0p0 fl0p0)
  return comp

/-- `import_elk_edge(edge, new_component)`: the contour polygon of the edge (thickened by the
component spacing) and its labels. -/
private def importElkEdge (edge : EdgeId) (newComponent : Array DCElementId) :
    TransformM (Array DCElementId) := do
  let sec ← firstSection edge
  let points ← sectionChain sec
  let thickness ← edgeThickness edge
  let componentSpacing := (← getThe ElkGraphTransformer).componentSpacing
  let contour := getContour points (thickness + componentSpacing)
  let props := (← ElkM.getEdge edge).props
  let shape ← newElement contour props
  registerMapping (.edge edge) shape
  importEdgeLabels edge (newComponent.push shape)

/-- `import_extension(edge, new_component, outgoing_extension)`: an edge between a child and a
port of the layout graph becomes an extension of the shape it is attached to (a new contour if
the edge has bend points, else the shape of the child node). -/
private def importExtension (edge : EdgeId) (newComponent : Array DCElementId)
    (outgoingExtension : Bool) : TransformM (Array DCElementId) := do
  let sec ← firstSection edge
  let mut points ← sectionChain sec
  if outgoingExtension then
    points := points.reverse
  let thickness ← edgeThickness edge
  let componentSpacing := (← getThe ElkGraphTransformer).componentSpacing
  let mut comp := newComponent
  let shape ← if points.size > 2 then do
      let fixedEdgePoints := points.extract 1 points.size
      let contour := getContour fixedEdgePoints (thickness + componentSpacing)
      let props := (← ElkM.getEdge edge).props
      let s ← newElement contour props
      comp := comp.push s
      pure s
    else do
      let node ← if outgoingExtension then sourceNode edge else targetNode edge
      match (← getThe ElkGraphTransformer).elementMapping.get? (.node node) with
      | some s => pure s
      | none => throwIllegalState "missing node shape for extension"
  let outerPoint := points[0]!
  let innerPoint := points[1]!
  let extParent ← if outgoingExtension then targetNode edge else sourceNode edge
  let dir ← nearestSide outerPoint extParent
  let mut extensionWidth := thickness + componentSpacing
  let mut middlePos : KVector := {}
  if dir.isHorizontal then
    extensionWidth := extensionWidth + (outerPoint.y - innerPoint.y).abs
    middlePos := KVector.mk' innerPoint.x ((innerPoint.y + outerPoint.y) / fl2p0)
  else
    extensionWidth := extensionWidth + (outerPoint.x - innerPoint.x).abs
    middlePos := KVector.mk' ((innerPoint.x + outerPoint.x) / fl2p0) innerPoint.y
  let bounds := (← getThe ElkGraphTransformer).elements[shape.idx]!.bounds
  let extension := DCExtension.new bounds dir middlePos extensionWidth
  modifyThe ElkGraphTransformer fun st =>
    { st with elements := st.elements.modify shape.idx (·.addExtension extension) }
  if outgoingExtension then
    modifyThe ElkGraphTransformer fun st =>
      { st with outgoingExtensions := st.outgoingExtensions.push (edge, extension) }
  else
    modifyThe ElkGraphTransformer fun st =>
      { st with incomingExtensions := st.incomingExtensions.push (edge, extension) }
  registerMapping (.edge edge) shape
  importEdgeLabels edge comp

/-- `import_elk_edges(edges, new_component)`: edges within one hierarchy level become contours,
edges from the parent into the component and from the component to the parent become
extensions (each edge only once). -/
private def importElkEdges (edges : Array EdgeId) (newComponent : Array DCElementId) :
    TransformM (Array DCElementId) := do
  let mut comp := newComponent
  for edge in edges do
    if (← getThe ElkGraphTransformer).elementMapping.contains (.edge edge) then continue
    let sourceN ← sourceNode edge
    let targetN ← targetNode edge
    let sourceParent := (← ElkM.getNode sourceN).parent
    let targetParent := (← ElkM.getNode targetN).parent
    if sourceParent == targetParent then
      comp ← importElkEdge edge comp
    else
      if targetParent == some sourceN then
        let st ← getThe ElkGraphTransformer
        if !st.incomingExtensions.any (·.1 == edge) && st.elementMapping.contains (.node targetN) then
          comp ← importExtension edge comp false
        continue
      let st ← getThe ElkGraphTransformer
      if !st.outgoingExtensions.any (·.1 == edge) && st.elementMapping.contains (.node sourceN) then
        comp ← importExtension edge comp true
  return comp

/-- `import_graph(graph)`: builds the `DCGraph`. The elements of a component are (in this order)
for every node of the component (DFS order) the node, its labels, its ports each followed by the
port's labels, and after all nodes the elements of the edges incident to the nodes (outgoing
before incoming edges, each edge once). -/
def importGraph (graph : NodeId) : TransformM DCGraph := do
  modifyThe ElkGraphTransformer fun st =>
    { st with parent := some graph, elements := #[], elementMapping := {}, mappingOrder := #[],
              incomingExtensions := #[], outgoingExtensions := #[] }
  let components ← (ElkGraphComponentsProcessor.split graph : ElkM (Array (Array NodeId)))
  let mut result : Array (Array DCElementId) := #[]
  for component in components do
    let mut subResult : Array DCElementId := #[]
    let mut edgeIds : Std.HashSet EdgeId := {}
    let mut edges : Array EdgeId := #[]
    for node in component do
      let componentNode ← importElkShape (.node node) true fl0p0 fl0p0
      subResult := subResult.push componentNode
      let nd ← ElkM.getNode node
      let nodeX := nd.x
      let nodeY := nd.y
      let setParentCoords (e : DCElement) : DCElement :=
        { e with parentCoords := some (KVector.mk' nodeX nodeY) }
      modifyThe ElkGraphTransformer fun st =>
        { st with elements := st.elements.modifyIn componentNode.idx setParentCoords }
      for label in nd.labels do
        subResult := subResult.push (← importElkShape (.label label) false nodeX nodeY)
      for port in nd.ports do
        subResult := subResult.push (← importElkShape (.port port) false nodeX nodeY)
        let pd ← ElkM.getPort port
        let portX := pd.x + nodeX
        let portY := pd.y + nodeY
        for label in pd.labels do
          subResult := subResult.push (← importElkShape (.label label) false portX portY)
      for edge in ElkGraphUtil.allIncidentEdges (← getThe ElkGraph) node do
        if !edgeIds.contains edge then
          edgeIds := edgeIds.insert edge
          edges := edges.push edge
    subResult ← importElkEdges edges subResult
    result := result.push subResult
  let st ← getThe ElkGraphTransformer
  let props := (← ElkM.getNode graph).props
  let transformed := DCGraph.new st.elements result (st.componentSpacing / fl2p0)
  return transformed.copyProperties props

/-! ### Apply layout -/

/-- `adjust_related_port(port, edge_point, dir)`: centres the port on the edge point along the
border. -/
private def adjustRelatedPort (port : PortId) (edgePoint : KVector) (dir : DCDirection) : ElkM Unit :=
  ElkM.modifyPort port fun p =>
    if dir.isHorizontal then { p with y := edgePoint.y - (p.height / fl2p0) }
    else { p with x := edgePoint.x - (p.width / fl2p0) }

/-- `adjust_first_segment(source, chain, dir)`: moves the first point of the chain onto the
border of the node given by `dir`. -/
private def adjustFirstSegment (source : NodeId) (chain : KVectorChain) (dir : DCDirection) :
    ElkM KVectorChain := do
  if chain.isEmpty then return #[]
  let nd ← ElkM.getNode source
  let first := chain[0]!
  let first :=
    match dir with
    | .north => { first with y := 0.0 }
    | .south => { first with y := nd.height }
    | .west => { first with x := 0.0 }
    | .east => { first with x := nd.width }
  return chain.set! 0 first

/-- `apply_layout()`: resizes the parent to the graph dimensions (scaling its labels and its
ports with positive coordinates), moves every mapped element by the offset of its component and
fixes the first segment of the extension edges and their ports. -/
def applyLayout (graph : DCGraph) : TransformM Unit := do
  let st ← getThe ElkGraphTransformer
  let some parent := st.parent | return ()
  let graphDimensions := graph.dimensions
  let newWidth := graphDimensions.x
  let newHeight := graphDimensions.y
  let parentNode ← ElkM.getNode parent
  let oldWidth := parentNode.width
  let oldHeight := parentNode.height
  ElkM.modifyNode parent fun n => { n with width := newWidth, height := newHeight }
  let xFactor := newWidth / oldWidth
  let yFactor := newHeight / oldHeight
  for label in parentNode.labels do
    ElkM.modifyLabel label fun l => { l with x := l.x * xFactor, y := l.y * yFactor }
  for port in parentNode.ports do
    ElkM.modifyPort port fun p =>
      let p := if p.x > fl0p0 then { p with x := p.x * xFactor } else p
      if p.y > fl0p0 then { p with y := p.y * yFactor } else p
  for key in st.mappingOrder do
    let some elemId := st.elementMapping.get? key | continue
    let offset := graph.elementOffset elemId
    match key with
    | .edge edge =>
      let sec ← firstSection edge
      let points := (← sectionChain sec).offsetValues offset.x offset.y
      ElkUtil.applyVectorChain points sec
      let edgeData ← ElkM.getEdge edge
      if let some junctionPoints := edgeData.props.get CoreOptions.JUNCTION_POINTS then
        let moved := KVectorChain.offsetValues junctionPoints offset.x offset.y
        ElkM.modifyEdge edge fun e => { e with props := e.props.set CoreOptions.JUNCTION_POINTS moved }
    | .node n =>
      ElkM.modifyNode n fun nd => { nd with x := nd.x + offset.x, y := nd.y + offset.y }
    | .port p =>
      ElkM.modifyPort p fun pd => { pd with x := pd.x + offset.x, y := pd.y + offset.y }
    | .label l =>
      ElkM.modifyLabel l fun ld => { ld with x := ld.x + offset.x, y := ld.y + offset.y }
  let mut adjustedPorts : Std.HashSet PortId := {}
  for (edge, extension) in st.incomingExtensions do
    let dir := extension.direction
    let sec ← firstSection edge
    let points ← sectionChain sec
    let newPoints ← adjustFirstSegment (← sourceNode edge) points dir
    ElkUtil.applyVectorChain newPoints sec
    if let some port ← sourcePort edge then
      if !adjustedPorts.contains port then
        adjustedPorts := adjustedPorts.insert port
        adjustRelatedPort port newPoints[0]! dir
  for (edge, extension) in st.outgoingExtensions do
    let dir := extension.direction
    let sec ← firstSection edge
    let points ← sectionChain sec
    let reversed := points.reverse
    let newPoints := (← adjustFirstSegment (← targetNode edge) reversed dir).reverse
    ElkUtil.applyVectorChain newPoints sec
    if let some port ← targetPort edge then
      if !adjustedPorts.contains port then
        adjustedPorts := adjustedPorts.insert port
        adjustRelatedPort port newPoints[newPoints.size - 1]! dir

/-- The `IGraphTransformer` view of the transformer, run in `ElkM` with a fresh transformer state
for the given component spacing. -/
def toIGraphTransformer (componentSpacing : Float) : IGraphTransformer TransformM NodeId :=
  { importGraph := fun g => do
      modifyThe ElkGraphTransformer fun st => { st with componentSpacing }
      importGraph g
    applyLayout := applyLayout }

end ElkGraphTransformer

end Elk.Alg.Disco.Transform
