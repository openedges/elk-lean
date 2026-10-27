import Elk.Graph.Ids
import Elk.Graph.Properties
/-!
# ElkGraph data model (`org.eclipse.elk.graph.{ElkNode, ElkPort, ElkEdge, ElkLabel, ElkEdgeSection}`)

All elements live in the arenas of `ElkGraph` and reference each other by id.
Containment is kept consistent by the operations in this file, mirroring the
EMF opposite references (`parent`/`children`, `sources`/`outgoingEdges`, ...).
The API is pure; `Elk.Graph.Monad` provides the `StateRefT` wrappers.
-/
namespace Elk.Graph

open Elk.Core.Math

/-- `ElkNode`. Geometry fields follow `ElkShape`. -/
structure ElkNode where
  identifier : Option String := none
  x : Float := 0
  y : Float := 0
  width : Float := 0
  height : Float := 0
  props : PropertyMap := {}
  labels : Array LabelId := #[]
  parent : Option NodeId := none
  children : Array NodeId := #[]
  ports : Array PortId := #[]
  containedEdges : Array EdgeId := #[]
  outgoingEdges : Array EdgeId := #[]
  incomingEdges : Array EdgeId := #[]
  deriving Inhabited

/-- `ElkPort`. -/
structure ElkPort where
  identifier : Option String := none
  x : Float := 0
  y : Float := 0
  width : Float := 0
  height : Float := 0
  props : PropertyMap := {}
  labels : Array LabelId := #[]
  parent : Option NodeId := none
  outgoingEdges : Array EdgeId := #[]
  incomingEdges : Array EdgeId := #[]
  deriving Inhabited

/-- `ElkEdge`. -/
structure ElkEdge where
  identifier : Option String := none
  props : PropertyMap := {}
  labels : Array LabelId := #[]
  containingNode : Option NodeId := none
  sources : Array ConnectableId := #[]
  targets : Array ConnectableId := #[]
  sections : Array SectionId := #[]
  deriving Inhabited

/-- `ElkLabel`. -/
structure ElkLabel where
  identifier : Option String := none
  x : Float := 0
  y : Float := 0
  width : Float := 0
  height : Float := 0
  props : PropertyMap := {}
  labels : Array LabelId := #[]
  parent : Option ElementId := none
  text : String := ""
  deriving Inhabited

/-- `ElkEdgeSection`. Bend points are stored inline. -/
structure ElkEdgeSection where
  identifier : Option String := none
  props : PropertyMap := {}
  startX : Float := 0
  startY : Float := 0
  endX : Float := 0
  endY : Float := 0
  bendPoints : Array KVector := #[]
  parent : Option EdgeId := none
  outgoingShape : Option ConnectableId := none
  incomingShape : Option ConnectableId := none
  outgoingSections : Array SectionId := #[]
  incomingSections : Array SectionId := #[]
  deriving Inhabited

/-- The arena holding a whole ELK graph (a root node plus everything below it). -/
structure ElkGraph where
  nodes : Array ElkNode := #[]
  ports : Array ElkPort := #[]
  edges : Array ElkEdge := #[]
  labels : Array ElkLabel := #[]
  sections : Array ElkEdgeSection := #[]
  deriving Inhabited

namespace ElkNode
@[inline] def position (n : ElkNode) : KVector := ⟨n.x, n.y⟩
@[inline] def size (n : ElkNode) : KVector := ⟨n.width, n.height⟩
@[inline] def isHierarchical (n : ElkNode) : Bool := !n.children.isEmpty
@[inline] def setPosition (n : ElkNode) (p : KVector) : ElkNode := { n with x := p.x, y := p.y }
@[inline] def setSize (n : ElkNode) (s : KVector) : ElkNode := { n with width := s.x, height := s.y }
end ElkNode

namespace ElkPort
@[inline] def position (p : ElkPort) : KVector := ⟨p.x, p.y⟩
@[inline] def size (p : ElkPort) : KVector := ⟨p.width, p.height⟩
@[inline] def setPosition (p : ElkPort) (v : KVector) : ElkPort := { p with x := v.x, y := v.y }
@[inline] def setSize (p : ElkPort) (s : KVector) : ElkPort := { p with width := s.x, height := s.y }
end ElkPort

namespace ElkLabel
@[inline] def position (l : ElkLabel) : KVector := ⟨l.x, l.y⟩
@[inline] def size (l : ElkLabel) : KVector := ⟨l.width, l.height⟩
@[inline] def setPosition (l : ElkLabel) (v : KVector) : ElkLabel := { l with x := v.x, y := v.y }
@[inline] def setSize (l : ElkLabel) (s : KVector) : ElkLabel := { l with width := s.x, height := s.y }
end ElkLabel

namespace ElkEdge
/-- `isHyperedge`: more than one source or target. -/
@[inline] def isHyperedge (e : ElkEdge) : Bool := e.sources.size > 1 || e.targets.size > 1
/-- `isConnected`: at least one source and one target. -/
@[inline] def isConnected (e : ElkEdge) : Bool := !e.sources.isEmpty && !e.targets.isEmpty
end ElkEdge

namespace ElkEdgeSection
@[inline] def startPoint (s : ElkEdgeSection) : KVector := ⟨s.startX, s.startY⟩
@[inline] def endPoint (s : ElkEdgeSection) : KVector := ⟨s.endX, s.endY⟩
@[inline] def setStartLocation (s : ElkEdgeSection) (x y : Float) : ElkEdgeSection := { s with startX := x, startY := y }
@[inline] def setEndLocation (s : ElkEdgeSection) (x y : Float) : ElkEdgeSection := { s with endX := x, endY := y }
end ElkEdgeSection

namespace ElkGraph

/-! ### Element access -/

@[inline] def node (g : ElkGraph) (n : NodeId) : ElkNode := g.nodes[n.idx]!
@[inline] def port (g : ElkGraph) (p : PortId) : ElkPort := g.ports[p.idx]!
@[inline] def edge (g : ElkGraph) (e : EdgeId) : ElkEdge := g.edges[e.idx]!
@[inline] def label (g : ElkGraph) (l : LabelId) : ElkLabel := g.labels[l.idx]!
@[inline] def edgeSection (g : ElkGraph) (s : SectionId) : ElkEdgeSection := g.sections[s.idx]!

@[inline] def modifyNode (g : ElkGraph) (n : NodeId) (f : ElkNode → ElkNode) : ElkGraph :=
  { g with nodes := g.nodes.modify n.idx f }
@[inline] def modifyPort (g : ElkGraph) (p : PortId) (f : ElkPort → ElkPort) : ElkGraph :=
  { g with ports := g.ports.modify p.idx f }
@[inline] def modifyEdge (g : ElkGraph) (e : EdgeId) (f : ElkEdge → ElkEdge) : ElkGraph :=
  { g with edges := g.edges.modify e.idx f }
@[inline] def modifyLabel (g : ElkGraph) (l : LabelId) (f : ElkLabel → ElkLabel) : ElkGraph :=
  { g with labels := g.labels.modify l.idx f }
@[inline] def modifySection (g : ElkGraph) (s : SectionId) (f : ElkEdgeSection → ElkEdgeSection) : ElkGraph :=
  { g with sections := g.sections.modify s.idx f }

@[inline] def nodeCount (g : ElkGraph) : Nat := g.nodes.size
@[inline] def portCount (g : ElkGraph) : Nat := g.ports.size
@[inline] def edgeCount (g : ElkGraph) : Nat := g.edges.size
@[inline] def labelCount (g : ElkGraph) : Nat := g.labels.size
@[inline] def sectionCount (g : ElkGraph) : Nat := g.sections.size

/-- `ElkGraphElement.getProperties()` for any element. -/
def props (g : ElkGraph) : ElementId → PropertyMap
  | .node n => (g.node n).props
  | .port p => (g.port p).props
  | .edge e => (g.edge e).props
  | .label l => (g.label l).props

def modifyProps (g : ElkGraph) (el : ElementId) (f : PropertyMap → PropertyMap) : ElkGraph :=
  match el with
  | .node n => g.modifyNode n fun x => { x with props := f x.props }
  | .port p => g.modifyPort p fun x => { x with props := f x.props }
  | .edge e => g.modifyEdge e fun x => { x with props := f x.props }
  | .label l => g.modifyLabel l fun x => { x with props := f x.props }

/-- `getLabels()` of any element. -/
def labelsOf (g : ElkGraph) : ElementId → Array LabelId
  | .node n => (g.node n).labels
  | .port p => (g.port p).labels
  | .edge e => (g.edge e).labels
  | .label l => (g.label l).labels

/-- `getIdentifier()` of any element. -/
def identifierOf (g : ElkGraph) : ElementId → Option String
  | .node n => (g.node n).identifier
  | .port p => (g.port p).identifier
  | .edge e => (g.edge e).identifier
  | .label l => (g.label l).identifier

/-! ### Creation -/

/-- `ElkGraphFactory.createElkNode()` + `setParent`. -/
def createNode (g : ElkGraph) (parent : Option NodeId := none) : ElkGraph × NodeId :=
  let id : NodeId := ⟨g.nodes.size⟩
  let g := { g with nodes := g.nodes.push { parent := parent } }
  let g := match parent with
    | some p => g.modifyNode p fun n => { n with children := n.children.push id }
    | none => g
  (g, id)

/-- `ElkGraphFactory.createElkPort()` + `setParent`. -/
def createPort (g : ElkGraph) (parent : Option NodeId := none) : ElkGraph × PortId :=
  let id : PortId := ⟨g.ports.size⟩
  let g := { g with ports := g.ports.push { parent := parent } }
  let g := match parent with
    | some p => g.modifyNode p fun n => { n with ports := n.ports.push id }
    | none => g
  (g, id)

/-- `ElkGraphFactory.createElkEdge()` + `setContainingNode`. -/
def createEdge (g : ElkGraph) (containingNode : Option NodeId := none) : ElkGraph × EdgeId :=
  let id : EdgeId := ⟨g.edges.size⟩
  let g := { g with edges := g.edges.push { containingNode := containingNode } }
  let g := match containingNode with
    | some p => g.modifyNode p fun n => { n with containedEdges := n.containedEdges.push id }
    | none => g
  (g, id)

private def addLabelToParent (g : ElkGraph) (parent : ElementId) (l : LabelId) : ElkGraph :=
  match parent with
  | .node n => g.modifyNode n fun x => { x with labels := x.labels.push l }
  | .port p => g.modifyPort p fun x => { x with labels := x.labels.push l }
  | .edge e => g.modifyEdge e fun x => { x with labels := x.labels.push l }
  | .label pl => g.modifyLabel pl fun x => { x with labels := x.labels.push l }

private def removeLabelFromParent (g : ElkGraph) (parent : ElementId) (l : LabelId) : ElkGraph :=
  match parent with
  | .node n => g.modifyNode n fun x => { x with labels := x.labels.erase l }
  | .port p => g.modifyPort p fun x => { x with labels := x.labels.erase l }
  | .edge e => g.modifyEdge e fun x => { x with labels := x.labels.erase l }
  | .label pl => g.modifyLabel pl fun x => { x with labels := x.labels.erase l }

/-- `ElkGraphFactory.createElkLabel()` + `setParent` + `setText`. -/
def createLabel (g : ElkGraph) (parent : Option ElementId := none) (text : String := "") : ElkGraph × LabelId :=
  let id : LabelId := ⟨g.labels.size⟩
  let g := { g with labels := g.labels.push { parent := parent, text := text } }
  let g := match parent with
    | some p => addLabelToParent g p id
    | none => g
  (g, id)

/-- `ElkGraphFactory.createElkEdgeSection()` + `setParent`. -/
def createSection (g : ElkGraph) (parent : Option EdgeId := none) : ElkGraph × SectionId :=
  let id : SectionId := ⟨g.sections.size⟩
  let g := { g with sections := g.sections.push { parent := parent } }
  let g := match parent with
    | some e => g.modifyEdge e fun x => { x with sections := x.sections.push id }
    | none => g
  (g, id)

/-! ### Containment (EMF opposite references) -/

/-- `ElkNode.setParent`. -/
def setNodeParent (g : ElkGraph) (n : NodeId) (parent : Option NodeId) : ElkGraph :=
  let current := (g.node n).parent
  if current == parent then g
  else
    let g := match current with
      | some c => g.modifyNode c fun x => { x with children := x.children.erase n }
      | none => g
    let g := g.modifyNode n fun x => { x with parent := parent }
    match parent with
    | some p => g.modifyNode p fun x => { x with children := x.children.push n }
    | none => g

/-- `ElkPort.setParent`. -/
def setPortParent (g : ElkGraph) (p : PortId) (parent : Option NodeId) : ElkGraph :=
  let current := (g.port p).parent
  if current == parent then g
  else
    let g := match current with
      | some c => g.modifyNode c fun x => { x with ports := x.ports.erase p }
      | none => g
    let g := g.modifyPort p fun x => { x with parent := parent }
    match parent with
    | some n => g.modifyNode n fun x => { x with ports := x.ports.push p }
    | none => g

/-- `ElkEdge.setContainingNode`. -/
def setEdgeContainingNode (g : ElkGraph) (e : EdgeId) (node : Option NodeId) : ElkGraph :=
  let current := (g.edge e).containingNode
  if current == node then g
  else
    let g := match current with
      | some c => g.modifyNode c fun x => { x with containedEdges := x.containedEdges.erase e }
      | none => g
    let g := g.modifyEdge e fun x => { x with containingNode := node }
    match node with
    | some n => g.modifyNode n fun x => { x with containedEdges := x.containedEdges.push e }
    | none => g

/-- `ElkLabel.setParent`. -/
def setLabelParent (g : ElkGraph) (l : LabelId) (parent : Option ElementId) : ElkGraph :=
  let current := (g.label l).parent
  if current == parent then g
  else
    let g := match current with
      | some c => removeLabelFromParent g c l
      | none => g
    let g := g.modifyLabel l fun x => { x with parent := parent }
    match parent with
    | some p => addLabelToParent g p l
    | none => g

/-- `ElkEdgeSection.setParent`. -/
def setSectionParent (g : ElkGraph) (s : SectionId) (parent : Option EdgeId) : ElkGraph :=
  let current := (g.edgeSection s).parent
  if current == parent then g
  else
    let g := match current with
      | some c => g.modifyEdge c fun x => { x with sections := x.sections.erase s }
      | none => g
    let g := g.modifySection s fun x => { x with parent := parent }
    match parent with
    | some e => g.modifyEdge e fun x => { x with sections := x.sections.push s }
    | none => g

private def addOutgoing (g : ElkGraph) (shape : ConnectableId) (e : EdgeId) : ElkGraph :=
  match shape with
  | .node n => g.modifyNode n fun x => if x.outgoingEdges.contains e then x else { x with outgoingEdges := x.outgoingEdges.push e }
  | .port p => g.modifyPort p fun x => if x.outgoingEdges.contains e then x else { x with outgoingEdges := x.outgoingEdges.push e }

private def addIncoming (g : ElkGraph) (shape : ConnectableId) (e : EdgeId) : ElkGraph :=
  match shape with
  | .node n => g.modifyNode n fun x => if x.incomingEdges.contains e then x else { x with incomingEdges := x.incomingEdges.push e }
  | .port p => g.modifyPort p fun x => if x.incomingEdges.contains e then x else { x with incomingEdges := x.incomingEdges.push e }

private def removeOutgoing (g : ElkGraph) (shape : ConnectableId) (e : EdgeId) : ElkGraph :=
  match shape with
  | .node n => g.modifyNode n fun x => { x with outgoingEdges := x.outgoingEdges.erase e }
  | .port p => g.modifyPort p fun x => { x with outgoingEdges := x.outgoingEdges.erase e }

private def removeIncoming (g : ElkGraph) (shape : ConnectableId) (e : EdgeId) : ElkGraph :=
  match shape with
  | .node n => g.modifyNode n fun x => { x with incomingEdges := x.incomingEdges.erase e }
  | .port p => g.modifyPort p fun x => { x with incomingEdges := x.incomingEdges.erase e }

/-- `edge.getSources().add(shape)`. -/
def addEdgeSource (g : ElkGraph) (e : EdgeId) (shape : ConnectableId) : ElkGraph :=
  if (g.edge e).sources.contains shape then g
  else
    let g := g.modifyEdge e fun x => { x with sources := x.sources.push shape }
    addOutgoing g shape e

/-- `edge.getTargets().add(shape)`. -/
def addEdgeTarget (g : ElkGraph) (e : EdgeId) (shape : ConnectableId) : ElkGraph :=
  if (g.edge e).targets.contains shape then g
  else
    let g := g.modifyEdge e fun x => { x with targets := x.targets.push shape }
    addIncoming g shape e

/-- `edge.getSources().remove(shape)`. -/
def removeEdgeSource (g : ElkGraph) (e : EdgeId) (shape : ConnectableId) : ElkGraph :=
  let g := g.modifyEdge e fun x => { x with sources := x.sources.erase shape }
  removeOutgoing g shape e

/-- `edge.getTargets().remove(shape)`. -/
def removeEdgeTarget (g : ElkGraph) (e : EdgeId) (shape : ConnectableId) : ElkGraph :=
  let g := g.modifyEdge e fun x => { x with targets := x.targets.erase shape }
  removeIncoming g shape e

/-- `edge.getSources().clear()`. -/
def clearEdgeSources (g : ElkGraph) (e : EdgeId) : ElkGraph :=
  (g.edge e).sources.foldl (fun acc s => acc.removeEdgeSource e s) g

/-- `edge.getTargets().clear()`. -/
def clearEdgeTargets (g : ElkGraph) (e : EdgeId) : ElkGraph :=
  (g.edge e).targets.foldl (fun acc t => acc.removeEdgeTarget e t) g

/-- `edge.getSections().clear()`: detaches all sections. -/
def clearEdgeSections (g : ElkGraph) (e : EdgeId) : ElkGraph :=
  let secs := (g.edge e).sections
  let g := secs.foldl (fun acc s => acc.modifySection s fun x => { x with parent := none }) g
  g.modifyEdge e fun x => { x with sections := #[] }

/-- Keeps only the last section of the edge (used when resetting layout). -/
def retainLastEdgeSection (g : ElkGraph) (e : EdgeId) : ElkGraph :=
  let secs := (g.edge e).sections
  if secs.size <= 1 then g
  else
    let last := secs[secs.size - 1]!
    let g := (secs.pop).foldl (fun acc s => acc.modifySection s fun x => { x with parent := none }) g
    g.modifyEdge e fun x => { x with sections := #[last] }

/-! ### Property helpers -/

@[inline] def getNodeProp {α : Type} [PropCodec α] (g : ElkGraph) (n : NodeId) (p : Property α) : Option α :=
  (g.node n).props.get p
@[inline] def setNodeProp {α : Type} [PropCodec α] (g : ElkGraph) (n : NodeId) (p : Property α) (v : α) : ElkGraph :=
  g.modifyNode n fun x => { x with props := x.props.set p v }
@[inline] def getPortProp {α : Type} [PropCodec α] (g : ElkGraph) (id : PortId) (p : Property α) : Option α :=
  (g.port id).props.get p
@[inline] def setPortProp {α : Type} [PropCodec α] (g : ElkGraph) (id : PortId) (p : Property α) (v : α) : ElkGraph :=
  g.modifyPort id fun x => { x with props := x.props.set p v }
@[inline] def getEdgeProp {α : Type} [PropCodec α] (g : ElkGraph) (id : EdgeId) (p : Property α) : Option α :=
  (g.edge id).props.get p
@[inline] def setEdgeProp {α : Type} [PropCodec α] (g : ElkGraph) (id : EdgeId) (p : Property α) (v : α) : ElkGraph :=
  g.modifyEdge id fun x => { x with props := x.props.set p v }
@[inline] def getLabelProp {α : Type} [PropCodec α] (g : ElkGraph) (id : LabelId) (p : Property α) : Option α :=
  (g.label id).props.get p
@[inline] def setLabelProp {α : Type} [PropCodec α] (g : ElkGraph) (id : LabelId) (p : Property α) (v : α) : ElkGraph :=
  g.modifyLabel id fun x => { x with props := x.props.set p v }
@[inline] def getProp {α : Type} [PropCodec α] (g : ElkGraph) (el : ElementId) (p : Property α) : Option α :=
  (g.props el).get p
@[inline] def setProp {α : Type} [PropCodec α] (g : ElkGraph) (el : ElementId) (p : Property α) (v : α) : ElkGraph :=
  g.modifyProps el (·.set p v)

end ElkGraph

end Elk.Graph
