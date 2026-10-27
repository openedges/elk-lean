import Elk.Core.Util.Adapters.GraphAdapters
/-!
# `org.eclipse.elk.alg.common.nodespacing.NodeMarginCalculator`

Calculates node margins from the bounding box of the node, its labels, its ports, its port
labels and the head/tail labels of incident edges (elk-rs `nodespacing::node_margin_calculator`).
Java puts the class directly into `nodespacing`; the `Calculators` directory is only a file
grouping.

The Java/elk-rs calculator stores the `GraphAdapter` it was created for and offers a fluent
`exclude…()` builder; here the calculator is a plain record of the four flags and the adapters
and the graph are passed to `process` / `processNode`. Margins are written with
`NodeAdapter.setMargin`. The label spacing is the graph's `SPACING_LABEL_NODE`.
-/
namespace Elk.Alg.Common.NodeSpacing

open Elk Elk.Core.Math Elk.Core.Util Elk.Core.Options Elk.Core.Util.Adapters

/-- `NodeMarginCalculator`: which elements contribute to the node margins (all by default). -/
structure NodeMarginCalculator where
  /-- `includeLabels`: node labels. -/
  includeLabels : Bool := true
  /-- `includePorts`: ports. -/
  includePorts : Bool := true
  /-- `includePortLabels`: port labels. -/
  includePortLabels : Bool := true
  /-- `includeEdgeHeadTailLabels`: head labels of incoming and tail labels of outgoing edges. -/
  includeEdgeHeadTailLabels : Bool := true
  deriving Inhabited, Repr, BEq

namespace NodeMarginCalculator

/-- `new NodeMarginCalculator(adapter)` (elk-rs `NodeMarginCalculator::new`): everything included. -/
def new : NodeMarginCalculator := {}

/-- `excludeLabels()`: do not consider node labels. -/
def excludeLabels (c : NodeMarginCalculator) : NodeMarginCalculator := { c with includeLabels := false }

/-- `excludePorts()`: do not consider ports. -/
def excludePorts (c : NodeMarginCalculator) : NodeMarginCalculator := { c with includePorts := false }

/-- `excludePortLabels()`: do not consider port labels. -/
def excludePortLabels (c : NodeMarginCalculator) : NodeMarginCalculator := { c with includePortLabels := false }

/-- `excludeEdgeHeadTailLabels()`: do not consider the head and tail labels of edges. -/
def excludeEdgeHeadTailLabels (c : NodeMarginCalculator) : NodeMarginCalculator :=
  { c with includeEdgeHeadTailLabels := false }

variable {m : Type → Type} [Monad m] {G N P L E : Type}

/-- `computeLabelBox(labelBox, label, incomingEdge, node, port, portLabelSpace, labelSpacing)`
(elk-rs `compute_label_box`): a rough estimate of an edge end label's box. Without a port the box
is left of the node (incoming) or right of it (outgoing), at the node's top. With a port it starts
at the port and is moved past the port and its labels (`portLabelSpace`) on the port's side
(UNDEFINED like EAST); NORTH/SOUTH boxes also move right of the port. -/
def computeLabelBox (a : GraphAdapters m G N P L E) (label : L) (incomingEdge : Bool) (node : N)
    (port : Option P) (portLabelSpace : Option KVector) (labelSpacing : Float) : m ElkRectangle := do
  let nodePos ← a.node.getPosition node
  let mut x := nodePos.x
  let mut y := nodePos.y
  if let some p := port then
    let portPos ← a.port.getPosition p
    x := x + portPos.x
    y := y + portPos.y
  let labelSize ← a.label.getSize label
  let width := labelSize.x
  let height := labelSize.y
  match port with
  | none =>
    if incomingEdge then
      x := x - (labelSpacing + labelSize.x)
    else
      x := x + ((← a.node.getSize node).x + labelSpacing)
    return { x, y, width, height }
  | some p =>
    let portSize ← a.port.getSize p
    let portLabelSpace := portLabelSpace.getD KVector.zero
    match ← a.portSide p with
    | .undefined | .east =>
      x := x + (portSize.x + labelSpacing + portLabelSpace.x + labelSpacing)
    | .west =>
      x := x - (labelSpacing + portLabelSpace.x + labelSpacing + labelSize.x)
    | .north =>
      x := x + (portSize.x + labelSpacing)
      y := y - (labelSpacing + portLabelSpace.y + labelSpacing + labelSize.y)
    | .south =>
      x := x + (portSize.x + labelSpacing)
      y := y + (portSize.y + labelSpacing + portLabelSpace.y + labelSpacing)
    return { x, y, width, height }

/-- `processEdgeHeadTailLabels(boundingBox, outgoingEdges, incomingEdges, node, port,
portLabelSpace, labelSpacing)` (elk-rs `process_edge_head_tail_labels`): adds the boxes of the
`TAIL` labels of the outgoing edges and of the `HEAD` labels of the incoming edges (placement
default `CENTER`) to the bounding box. -/
def processEdgeHeadTailLabels (a : GraphAdapters m G N P L E) (boundingBox : ElkRectangle)
    (outgoingEdges incomingEdges : Array E) (node : N) (port : Option P) (portLabelSpace : Option KVector)
    (labelSpacing : Float) : m ElkRectangle := do
  let mut boundingBox := boundingBox
  for edge in outgoingEdges do
    for label in ← a.edgeLabels edge do
      let placement ← a.label.getPropertyD label CoreOptions.EDGE_LABELS_PLACEMENT EdgeLabelPlacement.center
      if placement == .tail then
        let labelBox ← computeLabelBox a label false node port portLabelSpace labelSpacing
        boundingBox := boundingBox.union labelBox
  for edge in incomingEdges do
    for label in ← a.edgeLabels edge do
      let placement ← a.label.getPropertyD label CoreOptions.EDGE_LABELS_PLACEMENT EdgeLabelPlacement.center
      if placement == .head then
        let labelBox ← computeLabelBox a label true node port portLabelSpace labelSpacing
        boundingBox := boundingBox.union labelBox
  return boundingBox

/-- The space the port's labels need next to the port for the edge end label estimate (elk-rs
inline block of `process_node_with_spacing`): `(-spacing, -spacing)` plus each label's size and
spacing if the node's port labels are placed `OUTSIDE`, clamped at `0`. -/
def requiredPortLabelSpace (a : GraphAdapters m G N P L E) (node : N) (port : P) (labelSpacing : Float) :
    m KVector := do
  let mut space : KVector := ⟨-labelSpacing, -labelSpacing⟩
  let placement ← a.node.getProperty node CoreOptions.PORT_LABELS_PLACEMENT
  if (placement.map (·.contains .outside)).getD false then
    for label in ← a.portLabels port do
      let labelSize ← a.label.getSize label
      space := ⟨space.x + (labelSize.x + labelSpacing), space.y + (labelSize.y + labelSpacing)⟩
  return ⟨fmax space.x 0.0, fmax space.y 0.0⟩

/-- Adds one port's box, its labels' boxes and its edge end label boxes to the bounding box (the
`for port in node.get_ports()` body of elk-rs `process_node_with_spacing`). -/
private def addPortBoxes (c : NodeMarginCalculator) (a : GraphAdapters m G N P L E) (node : N) (nodePos : KVector)
    (port : P) (labelSpacing : Float) (boundingBox : ElkRectangle) : m ElkRectangle := do
  let mut boundingBox := boundingBox
  let portPos ← a.port.getPosition port
  let portSize ← a.port.getSize port
  let portX := portPos.x + nodePos.x
  let portY := portPos.y + nodePos.y
  if c.includePorts then
    boundingBox := boundingBox.union { x := portX, y := portY, width := portSize.x, height := portSize.y }
  if c.includePortLabels then
    for label in ← a.portLabels port do
      let labelPos ← a.label.getPosition label
      let labelSize ← a.label.getSize label
      boundingBox := boundingBox.union
        { x := labelPos.x + portX, y := labelPos.y + portY, width := labelSize.x, height := labelSize.y }
  if c.includeEdgeHeadTailLabels then
    let requiredSpace ← requiredPortLabelSpace a node port labelSpacing
    boundingBox ← processEdgeHeadTailLabels a boundingBox (← a.portOutgoingEdges port)
      (← a.portIncomingEdges port) node (some port) (some requiredSpace) labelSpacing
  return boundingBox

/-- `processNode(node, labelSpacing)` (elk-rs `process_node_with_spacing`): the union of the node
bounds with the included elements (node labels, ports, port labels, edge end labels at ports and at
the node) gives the margin on each side (at least `0`), written with `NodeAdapter.setMargin`. -/
def processNodeWithSpacing (c : NodeMarginCalculator) (a : GraphAdapters m G N P L E) (node : N)
    (labelSpacing : Float) : m Unit := do
  let nodePos ← a.node.getPosition node
  let nodeSize ← a.node.getSize node
  let mut boundingBox := ElkRectangle.ofValues nodePos.x nodePos.y nodeSize.x nodeSize.y
  if c.includeLabels then
    for label in ← a.nodeLabels node do
      let labelPos ← a.label.getPosition label
      let labelSize ← a.label.getSize label
      boundingBox := boundingBox.union
        { x := labelPos.x + nodePos.x, y := labelPos.y + nodePos.y, width := labelSize.x, height := labelSize.y }
  for port in ← a.nodePorts node do
    boundingBox ← addPortBoxes c a node nodePos port labelSpacing boundingBox
  if c.includeEdgeHeadTailLabels then
    boundingBox ← processEdgeHeadTailLabels a boundingBox (← a.nodeOutgoingEdges node)
      (← a.nodeIncomingEdges node) node none none labelSpacing
  let margin ← a.getNodeMargin node
  let margin : ElkMargin := { margin with
    top := fmax (nodePos.y - boundingBox.y) 0.0
    bottom := fmax (boundingBox.y + boundingBox.height - (nodePos.y + nodeSize.y)) 0.0
    left := fmax (nodePos.x - boundingBox.x) 0.0
    right := fmax (boundingBox.x + boundingBox.width - (nodePos.x + nodeSize.x)) 0.0 }
  a.setNodeMargin node margin

/-- `process()`: calculates and assigns margins to all nodes of the graph (label spacing: the
graph's `SPACING_LABEL_NODE`). -/
def process (c : NodeMarginCalculator) (a : GraphAdapters m G N P L E) (graph : G) : m Unit := do
  let spacing ← a.graph.getPropertyD graph CoreOptions.SPACING_LABEL_NODE 0.0
  for node in ← a.getNodes graph do
    processNodeWithSpacing c a node spacing

/-- `processNode(node)`: calculates and assigns margins to the given node, which is expected to be
part of the graph (label spacing: the graph's `SPACING_LABEL_NODE`). -/
def processNode (c : NodeMarginCalculator) (a : GraphAdapters m G N P L E) (graph : G) (node : N) : m Unit := do
  let spacing ← a.graph.getPropertyD graph CoreOptions.SPACING_LABEL_NODE 0.0
  processNodeWithSpacing c a node spacing

end NodeMarginCalculator

end Elk.Alg.Common.NodeSpacing
