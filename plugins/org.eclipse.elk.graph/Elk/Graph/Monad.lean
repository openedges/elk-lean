import Elk.Graph.Util
import Elk.Core.Exceptions
/-!
# `ElkM`: the ElkGraph state monad

`ElkM := StateRefT ElkGraph IO`. The helpers below are thin wrappers around the
pure `ElkGraph` API that keep the state uniquely referenced (`modify` takes
the graph out of the ref before updating it, so arrays update in place).

Rules (see `.rules`): never bind the whole graph (`let g ← get`) and keep it
alive across a `modify`; read what you need, then mutate through the helpers.
-/
namespace Elk.Graph

abbrev ElkM := StateRefT ElkGraph IO

namespace ElkM

/-- Runs an `ElkM` computation on a graph and returns the result with the final graph. -/
@[inline] def run {α : Type} (x : ElkM α) (g : ElkGraph) : IO (α × ElkGraph) := StateRefT'.run x g

/-- Read-only access to the whole graph (do not keep the result across writes). -/
@[inline] def withGraph {α : Type} (f : ElkGraph → α) : ElkM α := do return f (← get)

@[inline] def getNode (n : NodeId) : ElkM ElkNode := do return (← get).node n
@[inline] def getPort (p : PortId) : ElkM ElkPort := do return (← get).port p
@[inline] def getEdge (e : EdgeId) : ElkM ElkEdge := do return (← get).edge e
@[inline] def getLabel (l : LabelId) : ElkM ElkLabel := do return (← get).label l
@[inline] def getSection (s : SectionId) : ElkM ElkEdgeSection := do return (← get).edgeSection s

@[inline] def modifyNode (n : NodeId) (f : ElkNode → ElkNode) : ElkM Unit := modify (·.modifyNode n f)
@[inline] def modifyPort (p : PortId) (f : ElkPort → ElkPort) : ElkM Unit := modify (·.modifyPort p f)
@[inline] def modifyEdge (e : EdgeId) (f : ElkEdge → ElkEdge) : ElkM Unit := modify (·.modifyEdge e f)
@[inline] def modifyLabel (l : LabelId) (f : ElkLabel → ElkLabel) : ElkM Unit := modify (·.modifyLabel l f)
@[inline] def modifySection (s : SectionId) (f : ElkEdgeSection → ElkEdgeSection) : ElkM Unit := modify (·.modifySection s f)

@[inline] def createNode (parent : Option NodeId := none) : ElkM NodeId :=
  modifyGet fun g => let (g, n) := g.createNode parent; (n, g)
@[inline] def createPort (parent : Option NodeId := none) : ElkM PortId :=
  modifyGet fun g => let (g, p) := g.createPort parent; (p, g)
@[inline] def createEdge (containingNode : Option NodeId := none) : ElkM EdgeId :=
  modifyGet fun g => let (g, e) := g.createEdge containingNode; (e, g)
@[inline] def createLabel (parent : Option ElementId := none) (text : String := "") : ElkM LabelId :=
  modifyGet fun g => let (g, l) := g.createLabel parent text; (l, g)
@[inline] def createSection (parent : Option EdgeId := none) : ElkM SectionId :=
  modifyGet fun g => let (g, s) := g.createSection parent; (s, g)
@[inline] def createSimpleEdge (source target : ConnectableId) : ElkM EdgeId :=
  modifyGet fun g => let (g, e) := ElkGraphUtil.createSimpleEdge g source target; (e, g)

@[inline] def setNodeParent (n : NodeId) (parent : Option NodeId) : ElkM Unit := modify (·.setNodeParent n parent)
@[inline] def setPortParent (p : PortId) (parent : Option NodeId) : ElkM Unit := modify (·.setPortParent p parent)
@[inline] def setEdgeContainingNode (e : EdgeId) (n : Option NodeId) : ElkM Unit := modify (·.setEdgeContainingNode e n)
@[inline] def setLabelParent (l : LabelId) (parent : Option ElementId) : ElkM Unit := modify (·.setLabelParent l parent)
@[inline] def addEdgeSource (e : EdgeId) (s : ConnectableId) : ElkM Unit := modify (·.addEdgeSource e s)
@[inline] def addEdgeTarget (e : EdgeId) (t : ConnectableId) : ElkM Unit := modify (·.addEdgeTarget e t)
@[inline] def updateContainment (e : EdgeId) : ElkM Unit := modify (ElkGraphUtil.updateContainment · e)

@[inline] def getProp {α : Type} [PropCodec α] (el : ElementId) (p : Property α) : ElkM (Option α) :=
  do return (← get).getProp el p
@[inline] def setProp {α : Type} [PropCodec α] (el : ElementId) (p : Property α) (v : α) : ElkM Unit :=
  modify (·.setProp el p v)
@[inline] def getNodeProp {α : Type} [PropCodec α] (n : NodeId) (p : Property α) : ElkM (Option α) :=
  do return (← get).getNodeProp n p
@[inline] def setNodeProp {α : Type} [PropCodec α] (n : NodeId) (p : Property α) (v : α) : ElkM Unit :=
  modify (·.setNodeProp n p v)
@[inline] def getNodePropD {α : Type} [PropCodec α] (n : NodeId) (p : Property α) (d : α) : ElkM α :=
  do return ((← get).getNodeProp n p).getD d
@[inline] def hasNodeProp {α : Type} (n : NodeId) (p : Property α) : ElkM Bool :=
  do return ((← get).node n).props.has p

end ElkM

end Elk.Graph
