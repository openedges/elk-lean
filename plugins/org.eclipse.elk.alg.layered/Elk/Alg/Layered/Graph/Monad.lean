import Elk.Alg.Layered.Graph.LGraphQueries
import Elk.Core.Exceptions
/-!
# `LayeredM`: the layered algorithm monad

`LayeredM := StateRefT LGraphArena IO`. All element updates go through the helpers
below so the arena stays uniquely referenced (see `PORTING.md` §15); never bind the whole
arena across a `modify`.
-/
namespace Elk.Alg.Layered.Graph

open Elk.Graph Elk.Core Elk.Core.Math

abbrev LayeredM := StateRefT LGraphArena IO

namespace LayeredM

/-- Runs a computation on an arena (empty by default). -/
@[inline] def run {α : Type} (x : LayeredM α) (a : LGraphArena := {}) : IO (α × LGraphArena) := StateRefT'.run x a

/-- Read-only access to the arena (do not keep the result across writes). -/
@[inline] def withArena {α : Type} (f : LGraphArena → α) : LayeredM α := do return f (← get)

@[inline] def getGraph (g : LGraphId) : LayeredM LGraph := do return (← get).graph g
@[inline] def getNode (n : LNodeId) : LayeredM LNode := do return (← get).node n
@[inline] def getPort (p : LPortId) : LayeredM LPort := do return (← get).port p
@[inline] def getEdge (e : LEdgeId) : LayeredM LEdge := do return (← get).edge e
@[inline] def getLabel (l : LLabelId) : LayeredM LLabel := do return (← get).label l
@[inline] def getLayer (l : LayerId) : LayeredM Layer := do return (← get).layer l

@[inline] def modifyGraph (g : LGraphId) (f : LGraph → LGraph) : LayeredM Unit := modify (·.modifyGraph g f)
@[inline] def modifyNode (n : LNodeId) (f : LNode → LNode) : LayeredM Unit := modify (·.modifyNode n f)
@[inline] def modifyPort (p : LPortId) (f : LPort → LPort) : LayeredM Unit := modify (·.modifyPort p f)
@[inline] def modifyEdge (e : LEdgeId) (f : LEdge → LEdge) : LayeredM Unit := modify (·.modifyEdge e f)
@[inline] def modifyLabel (l : LLabelId) (f : LLabel → LLabel) : LayeredM Unit := modify (·.modifyLabel l f)
@[inline] def modifyLayer (l : LayerId) (f : Layer → Layer) : LayeredM Unit := modify (·.modifyLayer l f)

/-- `new LGraph()`. -/
@[inline] def createGraph (g : LGraph := {}) : LayeredM LGraphId :=
  modifyGet fun a => let (a, id) := a.createGraph g; (id, a)
/-- `new LNode(graph)`. -/
@[inline] def createNode (graph : LGraphId) (n : LNode := {}) : LayeredM LNodeId :=
  modifyGet fun a => let (a, id) := a.createNode graph n; (id, a)
/-- `new LPort()`. -/
@[inline] def createPort (p : LPort := {}) : LayeredM LPortId :=
  modifyGet fun a => let (a, id) := a.createPort p; (id, a)
/-- `new LEdge()`. -/
@[inline] def createEdge (e : LEdge := {}) : LayeredM LEdgeId :=
  modifyGet fun a => let (a, id) := a.createEdge e; (id, a)
/-- `new LLabel(text)`. -/
@[inline] def createLabel (text : String := "") (l : LLabel := {}) : LayeredM LLabelId :=
  modifyGet fun a => let (a, id) := a.createLabel text l; (id, a)
/-- `new Layer(graph)` (not added to `graph.layers`). -/
@[inline] def createLayer (graph : LGraphId) : LayeredM LayerId :=
  modifyGet fun a => let (a, id) := a.createLayer graph; (id, a)

/-- `LNode.getGraph()`. -/
@[inline] def nodeGraph (n : LNodeId) : LayeredM (Option LGraphId) := do return (← get).nodeGraph n

/-- `LNode.setLayer(layer)`. -/
@[inline] def setNodeLayer (n : LNodeId) (layer : Option LayerId) : LayeredM Unit := modify (·.setNodeLayer n layer)

/-- `LNode.setLayer(index, layer)`; throws `IllegalArgumentException` when `index` exceeds the layer size. -/
def setNodeLayerAtIndex (n : LNodeId) (index : Nat) (layer : Option LayerId) : LayeredM Unit := do
  if let some l := layer then
    if index > (← getLayer l).nodes.size then
      throwIllegalArgument "index must be >= 0 and <= layer node count"
  modify (·.setNodeLayerAtIndex n index layer)

/-- `LPort.setNode(node)`. -/
@[inline] def setPortNode (p : LPortId) (node : Option LNodeId) : LayeredM Unit := modify (·.setPortNode p node)

/-- `LEdge.setSource(port)`. -/
@[inline] def setEdgeSource (e : LEdgeId) (source : Option LPortId) : LayeredM Unit := modify (·.setEdgeSource e source)

/-- `LEdge.setTarget(port)`. -/
@[inline] def setEdgeTarget (e : LEdgeId) (target : Option LPortId) : LayeredM Unit := modify (·.setEdgeTarget e target)

/-- `LEdge.setTargetAndInsertAtIndex(port, index)`; throws when `index` exceeds the port's incoming edge count. -/
def setEdgeTargetAndInsertAtIndex (e : LEdgeId) (target : Option LPortId) (index : Nat) : LayeredM Unit := do
  if let some t := target then
    if index > (← getPort t).incomingEdges.size then
      throwIllegalArgument "index out of bounds"
  modify (·.setEdgeTargetAndInsertAtIndex e target index)

/-- `LNode.cachePortSides()`. -/
def cachePortSides (n : LNodeId) : LayeredM Unit := do
  let indices := (← get).findPortIndices n
  modifyNode n fun nd => { nd with portSidesCached := true, portSideIndices := some indices }

-- Typed access to the public option maps (`getProperty`/`setProperty` on `LGraphElement`).

@[inline] def getGraphProp {α : Type} [PropCodec α] (g : LGraphId) (p : Property α) : LayeredM (Option α) := do
  return (← getGraph g).props.get p
@[inline] def getGraphPropD {α : Type} [PropCodec α] (g : LGraphId) (p : Property α) (d : α) : LayeredM α := do
  return (← getGraph g).props.getD p d
@[inline] def setGraphProp {α : Type} [PropCodec α] (g : LGraphId) (p : Property α) (v : α) : LayeredM Unit :=
  modifyGraph g fun x => { x with props := x.props.set p v }
@[inline] def hasGraphProp {α : Type} (g : LGraphId) (p : Property α) : LayeredM Bool := do
  return (← getGraph g).props.has p

@[inline] def getNodeProp {α : Type} [PropCodec α] (n : LNodeId) (p : Property α) : LayeredM (Option α) := do
  return (← getNode n).props.get p
@[inline] def getNodePropD {α : Type} [PropCodec α] (n : LNodeId) (p : Property α) (d : α) : LayeredM α := do
  return (← getNode n).props.getD p d
@[inline] def setNodeProp {α : Type} [PropCodec α] (n : LNodeId) (p : Property α) (v : α) : LayeredM Unit :=
  modifyNode n fun x => { x with props := x.props.set p v }
@[inline] def hasNodeProp {α : Type} (n : LNodeId) (p : Property α) : LayeredM Bool := do
  return (← getNode n).props.has p

@[inline] def getPortProp {α : Type} [PropCodec α] (pt : LPortId) (p : Property α) : LayeredM (Option α) := do
  return (← getPort pt).props.get p
@[inline] def getPortPropD {α : Type} [PropCodec α] (pt : LPortId) (p : Property α) (d : α) : LayeredM α := do
  return (← getPort pt).props.getD p d
@[inline] def setPortProp {α : Type} [PropCodec α] (pt : LPortId) (p : Property α) (v : α) : LayeredM Unit :=
  modifyPort pt fun x => { x with props := x.props.set p v }
@[inline] def hasPortProp {α : Type} (pt : LPortId) (p : Property α) : LayeredM Bool := do
  return (← getPort pt).props.has p

@[inline] def getEdgeProp {α : Type} [PropCodec α] (e : LEdgeId) (p : Property α) : LayeredM (Option α) := do
  return (← getEdge e).props.get p
@[inline] def getEdgePropD {α : Type} [PropCodec α] (e : LEdgeId) (p : Property α) (d : α) : LayeredM α := do
  return (← getEdge e).props.getD p d
@[inline] def setEdgeProp {α : Type} [PropCodec α] (e : LEdgeId) (p : Property α) (v : α) : LayeredM Unit :=
  modifyEdge e fun x => { x with props := x.props.set p v }
@[inline] def hasEdgeProp {α : Type} (e : LEdgeId) (p : Property α) : LayeredM Bool := do
  return (← getEdge e).props.has p

@[inline] def getLabelProp {α : Type} [PropCodec α] (l : LLabelId) (p : Property α) : LayeredM (Option α) := do
  return (← getLabel l).props.get p
@[inline] def getLabelPropD {α : Type} [PropCodec α] (l : LLabelId) (p : Property α) (d : α) : LayeredM α := do
  return (← getLabel l).props.getD p d
@[inline] def setLabelProp {α : Type} [PropCodec α] (l : LLabelId) (p : Property α) (v : α) : LayeredM Unit :=
  modifyLabel l fun x => { x with props := x.props.set p v }
@[inline] def hasLabelProp {α : Type} (l : LLabelId) (p : Property α) : LayeredM Bool := do
  return (← getLabel l).props.has p

end LayeredM

end Elk.Alg.Layered.Graph
