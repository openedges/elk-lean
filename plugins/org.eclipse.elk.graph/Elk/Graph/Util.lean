import Elk.Graph.Model
/-!
# `org.eclipse.elk.graph.util.ElkGraphUtil`

Pure graph utilities over the `ElkGraph` arena.
-/
namespace Elk.Graph

namespace ElkGraphUtil

open Elk.Core.Math

/-- `createGraph()`: a fresh arena with a root node. -/
def createGraph : ElkGraph × NodeId := ElkGraph.createNode {} none

/-- `createNode(parent)`. -/
@[inline] def createNode (g : ElkGraph) (parent : Option NodeId) : ElkGraph × NodeId := g.createNode parent

/-- `createPort(parent)`. -/
@[inline] def createPort (g : ElkGraph) (parent : Option NodeId) : ElkGraph × PortId := g.createPort parent

/-- `createEdge(containingNode)`. -/
@[inline] def createEdge (g : ElkGraph) (containingNode : Option NodeId) : ElkGraph × EdgeId := g.createEdge containingNode

/-- `createLabel(parent)` / `createLabel(text, parent)`. -/
@[inline] def createLabel (g : ElkGraph) (parent : Option ElementId) (text : String := "") : ElkGraph × LabelId :=
  g.createLabel parent text

/-- `connectableShapeToNode`: the node itself, or the port's parent node. -/
def connectableShapeToNode (g : ElkGraph) : ConnectableId → Option NodeId
  | .node n => some n
  | .port p => (g.port p).parent

/-- `connectableShapeToPort`. -/
def connectableShapeToPort : ConnectableId → Option PortId
  | .port p => some p
  | .node _ => none

/-- `isDescendant(child, ancestor)`: strict descendant test. -/
partial def isDescendant (g : ElkGraph) (child ancestor : NodeId) : Bool :=
  match (g.node child).parent with
  | none => false
  | some p => if p == ancestor then true else isDescendant g p ancestor

/-- Ancestors from the node (optionally included) up to the root. -/
partial def ancestorChain (g : ElkGraph) (n : NodeId) (includeNode : Bool) : Array NodeId :=
  let rec go (cur : Option NodeId) (acc : Array NodeId) : Array NodeId :=
    match cur with
    | none => acc
    | some c => go (g.node c).parent (acc.push c)
  go (if includeNode then some n else (g.node n).parent) #[]

/-- `findLowestCommonAncestor(node1, node2)`. -/
def findLowestCommonAncestor (g : ElkGraph) (n1 n2 : NodeId) : Option NodeId := Id.run do
  let a1 := (ancestorChain g n1 true).reverse
  let a2 := (ancestorChain g n2 true).reverse
  let mut common : Option NodeId := none
  let mut i := 0
  while i < a1.size && i < a2.size do
    if a1[i]! == a2[i]! then
      common := some a1[i]!
      i := i + 1
    else
      i := a1.size
  return common

/-- `allIncidentShapes(edge)`: sources then targets. -/
def allIncidentShapes (g : ElkGraph) (e : EdgeId) : Array ConnectableId :=
  (g.edge e).sources ++ (g.edge e).targets

/-- `findBestEdgeContainment(edge)`. Returns `none` for an unconnected edge
(Java throws `IllegalArgumentException`). -/
def findBestEdgeContainment (g : ElkGraph) (e : EdgeId) : Option NodeId := Id.run do
  let edge := g.edge e
  let sourceLen := edge.sources.size
  let targetLen := edge.targets.size
  if sourceLen + targetLen == 0 then return none
  if sourceLen + targetLen == 1 then
    let shape := if sourceLen == 0 then edge.targets[0]! else edge.sources[0]!
    return (connectableShapeToNode g shape).bind fun n => (g.node n).parent
  if sourceLen == 1 && targetLen == 1 then
    let some sourceNode := connectableShapeToNode g edge.sources[0]! | return none
    let some targetNode := connectableShapeToNode g edge.targets[0]! | return none
    let sourceParent := (g.node sourceNode).parent
    let targetParent := (g.node targetNode).parent
    if sourceParent == targetParent then return sourceParent
    if targetParent == some sourceNode then return some sourceNode
    if sourceParent == some targetNode then return some targetNode
  let shapes := allIncidentShapes g e
  if shapes.isEmpty then return none
  let some first := connectableShapeToNode g shapes[0]! | return none
  let mut commonAncestor := first
  for i in [1:shapes.size] do
    let some incidentNode := connectableShapeToNode g shapes[i]! | return none
    if incidentNode != commonAncestor && !isDescendant g incidentNode commonAncestor then
      let siblings := (g.node incidentNode).parent == (g.node commonAncestor).parent
      if siblings then
        match (g.node incidentNode).parent with
        | some p => commonAncestor := p
        | none => return none
      else
        match findLowestCommonAncestor g commonAncestor incidentNode with
        | some lca => commonAncestor := lca
        | none => return none
  return some commonAncestor

/-- `updateContainment(edge)`. -/
def updateContainment (g : ElkGraph) (e : EdgeId) : ElkGraph :=
  g.setEdgeContainingNode e (findBestEdgeContainment g e)

/-- `createSimpleEdge(source, target)`. -/
def createSimpleEdge (g : ElkGraph) (source target : ConnectableId) : ElkGraph × EdgeId :=
  let (g, e) := g.createEdge none
  let g := g.addEdgeSource e source
  let g := g.addEdgeTarget e target
  (updateContainment g e, e)

/-- `createHyperedge(sources, targets)`. -/
def createHyperedge (g : ElkGraph) (sources targets : Array ConnectableId) : ElkGraph × EdgeId :=
  let (g, e) := g.createEdge none
  let g := sources.foldl (fun acc s => acc.addEdgeSource e s) g
  let g := targets.foldl (fun acc t => acc.addEdgeTarget e t) g
  (updateContainment g e, e)

/-- `allIncomingEdges(node)`: edges into the node and into its ports. -/
def allIncomingEdges (g : ElkGraph) (n : NodeId) : Array EdgeId :=
  (g.node n).ports.foldl (fun acc p => acc ++ (g.port p).incomingEdges) (g.node n).incomingEdges

/-- `allOutgoingEdges(node)`. -/
def allOutgoingEdges (g : ElkGraph) (n : NodeId) : Array EdgeId :=
  (g.node n).ports.foldl (fun acc p => acc ++ (g.port p).outgoingEdges) (g.node n).outgoingEdges

/-- `allIncidentEdges(node)`: outgoing then incoming. -/
def allIncidentEdges (g : ElkGraph) (n : NodeId) : Array EdgeId :=
  allOutgoingEdges g n ++ allIncomingEdges g n

/-- `allIncidentEdges(shape)`. -/
def allIncidentEdgesForShape (g : ElkGraph) : ConnectableId → Array EdgeId
  | .node n => allIncidentEdges g n
  | .port p => (g.port p).outgoingEdges ++ (g.port p).incomingEdges

/-- `containingGraph(element)`: the node whose children/contained edges hold the element. -/
partial def containingGraph (g : ElkGraph) : ElementId → Option NodeId
  | .edge e => (g.edge e).containingNode
  | .node n => (g.node n).parent
  | .port p => (g.port p).parent
  | .label l => ((g.label l).parent).bind (containingGraph g)

/-- `ElkEdge.isSelfloop()`: all end points belong to the same node. -/
def isSelfloop (g : ElkGraph) (e : EdgeId) : Bool := Id.run do
  let edge := g.edge e
  if !edge.isConnected then return false
  let shapes := edge.sources ++ edge.targets
  let some first := connectableShapeToNode g shapes[0]! | return false
  for s in shapes do
    match connectableShapeToNode g s with
    | some n => if n != first then return false
    | none => return false
  return true

/-- `ElkEdge.isHierarchical()`: end points in different graphs. -/
def isHierarchicalEdge (g : ElkGraph) (e : EdgeId) : Bool := Id.run do
  let edge := g.edge e
  if edge.sources.isEmpty && edge.targets.isEmpty then return false
  let mut parent : Option NodeId := none
  let mut first := true
  for s in edge.sources ++ edge.targets do
    let some n := connectableShapeToNode g s | return true
    let np := (g.node n).parent
    if first then
      parent := np
      first := false
    else if np != parent then return true
  return false

/-- Descendant nodes in pre-order (excluding `root`). -/
partial def descendantNodes (g : ElkGraph) (root : NodeId) : Array NodeId :=
  let rec go (n : NodeId) (acc : Array NodeId) : Array NodeId :=
    (g.node n).children.foldl (fun acc c => go c (acc.push c)) acc
  go root #[]

/-- All nodes of the hierarchy in pre-order, root first (`ElkGraphUtil.allNodes`). -/
def allNodes (g : ElkGraph) (root : NodeId) : Array NodeId := #[root] ++ descendantNodes g root

/-- Edges contained in the node and all its descendants (`ElkGraphUtil.allEdges`). -/
def allEdges (g : ElkGraph) (root : NodeId) : Array EdgeId :=
  (allNodes g root).foldl (fun acc n => acc ++ (g.node n).containedEdges) #[]

/-- `firstEdgeSection(edge, resetSection, removeOtherSections)`: returns the
first section, creating it if necessary. -/
def firstEdgeSection (g : ElkGraph) (e : EdgeId) (resetSection removeOtherSections : Bool) : ElkGraph × SectionId :=
  let g := if removeOtherSections then g.retainLastEdgeSection e else g
  -- note: Java keeps the *first* section and removes the rest
  match (g.edge e).sections[0]? with
  | some s =>
    let g := if resetSection then g.modifySection s fun x =>
        { x with startX := 0, startY := 0, endX := 0, endY := 0, bendPoints := #[],
                 outgoingShape := none, incomingShape := none, outgoingSections := #[], incomingSections := #[] }
      else g
    (g, s)
  | none => g.createSection (some e)

/-- `createEdgeSection(edge)`. -/
@[inline] def createEdgeSection (g : ElkGraph) (e : EdgeId) : ElkGraph × SectionId := g.createSection (some e)

/-- `createBendPoint(section, x, y)`. -/
@[inline] def createBendPoint (g : ElkGraph) (s : SectionId) (x y : Float) : ElkGraph :=
  g.modifySection s fun sec => { sec with bendPoints := sec.bendPoints.push ⟨x, y⟩ }

/-- The node a label is attached to, through ports (used by node spacing). -/
partial def labelOwnerNode (g : ElkGraph) (l : LabelId) : Option NodeId :=
  match (g.label l).parent with
  | some (.node n) => some n
  | some (.port p) => (g.port p).parent
  | some (.edge e) => (g.edge e).containingNode
  | some (.label pl) => labelOwnerNode g pl
  | none => none

end ElkGraphUtil

end Elk.Graph
