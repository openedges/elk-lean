import Elk.Alg.Layered.Graph.LGraph
import Elk.Alg.Layered.Graph.Layer
import Elk.Alg.Layered.Graph.LNode
import Elk.Alg.Layered.Graph.LPort
import Elk.Alg.Layered.Graph.LEdge
import Elk.Alg.Layered.Graph.LLabel
import Elk.Graph.ArrayModify
/-!
# The layered graph arena

One arena per layered run holds every element of every nested `LGraph`. The pure
functions here are the building blocks of the `LayeredM` helpers; relation changes
(`setNodeLayer`, `setPortNode`, `setEdgeSource`, …) update both sides like the Java
setters do.
-/
namespace Elk.Alg.Layered.Graph

open Elk.Graph Elk.Core.Math

/-- All elements of a layered run.

Performance note: the update helpers take the element array out of the arena before changing it
(`let arr := a.nodes; let a := { a with nodes := #[] }; { a with nodes := arr.modify … }`), so the
array stays uniquely referenced and is updated in place; `{ a with nodes := a.nodes.modify … }`
keeps a second reference alive during the update and copies the whole array. -/
structure LGraphArena where
  graphs : Array LGraph := #[]
  nodes : Array LNode := #[]
  ports : Array LPort := #[]
  edges : Array LEdge := #[]
  labels : Array LLabel := #[]
  layers : Array Layer := #[]
  /-- The node a processor names in the exception it is about to throw (set right before the
  `throw`; `none` otherwise). Java names such nodes by `LNode.getDesignation()`, whose fallback is
  the identifier path of the origin `ElkNode`, which the arena does not know: the processors use
  `nodeDesignation` and `LayeredLayoutProvider.layout` puts the identifier path into the message
  (error path only). -/
  errorNode : Option LNodeId := none
  deriving Inhabited

namespace LGraphArena

@[inline] def graph (a : LGraphArena) (g : LGraphId) : LGraph := a.graphs[g.idx]!
@[inline] def node (a : LGraphArena) (n : LNodeId) : LNode := a.nodes[n.idx]!
@[inline] def port (a : LGraphArena) (p : LPortId) : LPort := a.ports[p.idx]!
@[inline] def edge (a : LGraphArena) (e : LEdgeId) : LEdge := a.edges[e.idx]!
@[inline] def label (a : LGraphArena) (l : LLabelId) : LLabel := a.labels[l.idx]!
@[inline] def layer (a : LGraphArena) (l : LayerId) : Layer := a.layers[l.idx]!

@[inline] def modifyGraph (a : LGraphArena) (g : LGraphId) (f : LGraph → LGraph) : LGraphArena :=
  let arr := a.graphs
  let a := { a with graphs := #[] }
  { a with graphs := arr.modifyIn g.idx f }
@[inline] def modifyNode (a : LGraphArena) (n : LNodeId) (f : LNode → LNode) : LGraphArena :=
  let arr := a.nodes
  let a := { a with nodes := #[] }
  { a with nodes := arr.modifyIn n.idx f }
@[inline] def modifyPort (a : LGraphArena) (p : LPortId) (f : LPort → LPort) : LGraphArena :=
  let arr := a.ports
  let a := { a with ports := #[] }
  { a with ports := arr.modifyIn p.idx f }
@[inline] def modifyEdge (a : LGraphArena) (e : LEdgeId) (f : LEdge → LEdge) : LGraphArena :=
  let arr := a.edges
  let a := { a with edges := #[] }
  { a with edges := arr.modifyIn e.idx f }
@[inline] def modifyLabel (a : LGraphArena) (l : LLabelId) (f : LLabel → LLabel) : LGraphArena :=
  let arr := a.labels
  let a := { a with labels := #[] }
  { a with labels := arr.modifyIn l.idx f }
@[inline] def modifyLayer (a : LGraphArena) (l : LayerId) (f : Layer → Layer) : LGraphArena :=
  let arr := a.layers
  let a := { a with layers := #[] }
  { a with layers := arr.modifyIn l.idx f }

/-- `new LGraph()`. -/
def createGraph (a : LGraphArena) (g : LGraph := {}) : LGraphArena × LGraphId :=
  let id := a.graphs.size
  let arr := a.graphs
  let a := { a with graphs := #[] }
  ({ a with graphs := arr.push g }, ⟨id⟩)

/-- `new LNode(graph)`: the node knows its graph but is not added to `layerlessNodes`. -/
def createNode (a : LGraphArena) (graph : LGraphId) (n : LNode := {}) : LGraphArena × LNodeId :=
  let id := a.nodes.size
  let arr := a.nodes
  let a := { a with nodes := #[] }
  ({ a with nodes := arr.push { n with graph := some graph } }, ⟨id⟩)

/-- `new LPort()`. -/
def createPort (a : LGraphArena) (p : LPort := {}) : LGraphArena × LPortId :=
  let id := a.ports.size
  let arr := a.ports
  let a := { a with ports := #[] }
  ({ a with ports := arr.push p }, ⟨id⟩)

/-- `new LEdge()`. -/
def createEdge (a : LGraphArena) (e : LEdge := {}) : LGraphArena × LEdgeId :=
  let id := a.edges.size
  let arr := a.edges
  let a := { a with edges := #[] }
  ({ a with edges := arr.push e }, ⟨id⟩)

/-- `new LLabel(text)`. -/
def createLabel (a : LGraphArena) (text : String := "") (l : LLabel := {}) : LGraphArena × LLabelId :=
  let id := a.labels.size
  let arr := a.labels
  let a := { a with labels := #[] }
  ({ a with labels := arr.push { l with text := text } }, ⟨id⟩)

/-- `new Layer(graph)`: not added to the graph's `layers` (callers do). -/
def createLayer (a : LGraphArena) (graph : LGraphId) : LGraphArena × LayerId :=
  let id := a.layers.size
  let arr := a.layers
  let a := { a with layers := #[] }
  ({ a with layers := arr.push { owner := graph } }, ⟨id⟩)

/-- `LNode.getGraph()`: the stored graph, else the layer's graph. -/
def nodeGraph (a : LGraphArena) (n : LNodeId) : Option LGraphId :=
  let nd := a.node n
  match nd.graph with
  | some g => some g
  | none => nd.layer.map fun l => (a.layer l).owner

/-- `LNode.setLayer(layer)`: removes the node from its current layer and appends it to the new one. -/
def setNodeLayer (a : LGraphArena) (n : LNodeId) (layer : Option LayerId) : LGraphArena :=
  let a := match (a.node n).layer with
    | some cur => a.modifyLayer cur fun l => { l with nodes := l.nodes.erase n }
    | none => a
  let a := a.modifyNode n fun x => { x with layer := layer }
  match layer with
  | some l => a.modifyLayer l fun x => { x with nodes := x.nodes.push n }
  | none => a

/-- `LNode.setLayer(index, layer)`: like `setNodeLayer` but inserts at `index`
(`index` must be `≤` the layer's node count; checked by the monadic wrapper). -/
def setNodeLayerAtIndex (a : LGraphArena) (n : LNodeId) (index : Nat) (layer : Option LayerId) : LGraphArena :=
  let a := match (a.node n).layer with
    | some cur => a.modifyLayer cur fun l => { l with nodes := l.nodes.erase n }
    | none => a
  let a := a.modifyNode n fun x => { x with layer := layer }
  match layer with
  | some l => a.modifyLayer l fun x => { x with nodes := x.nodes.insertIdx! index n }
  | none => a

/-- `LPort.setNode(node)`: moves the port between owners (no-op when unchanged). -/
def setPortNode (a : LGraphArena) (p : LPortId) (node : Option LNodeId) : LGraphArena :=
  let current := (a.port p).owner
  if current.isSome && current == node then a
  else
    let a := match current with
      | some owner => a.modifyNode owner fun x => { x with ports := x.ports.erase p }
      | none => a
    let a := a.modifyPort p fun x => { x with owner := node }
    match node with
    | some owner => a.modifyNode owner fun x => { x with ports := x.ports.push p }
    | none => a

/-- `LEdge.setSource(port)`. -/
def setEdgeSource (a : LGraphArena) (e : LEdgeId) (source : Option LPortId) : LGraphArena :=
  let a := match (a.edge e).source with
    | some cur => a.modifyPort cur fun x => { x with outgoingEdges := x.outgoingEdges.erase e }
    | none => a
  let a := match source with
    | some s => a.modifyPort s fun x => { x with outgoingEdges := x.outgoingEdges.push e }
    | none => a
  a.modifyEdge e fun x => { x with source := source }

/-- `LEdge.setTarget(port)`. -/
def setEdgeTarget (a : LGraphArena) (e : LEdgeId) (target : Option LPortId) : LGraphArena :=
  let a := match (a.edge e).target with
    | some cur => a.modifyPort cur fun x => { x with incomingEdges := x.incomingEdges.erase e }
    | none => a
  let a := match target with
    | some t => a.modifyPort t fun x => { x with incomingEdges := x.incomingEdges.push e }
    | none => a
  a.modifyEdge e fun x => { x with target := target }

/-- `LEdge.setTargetAndInsertAtIndex(port, index)` (index checked by the monadic wrapper). -/
def setEdgeTargetAndInsertAtIndex (a : LGraphArena) (e : LEdgeId) (target : Option LPortId) (index : Nat) : LGraphArena :=
  let a := match (a.edge e).target with
    | some cur => a.modifyPort cur fun x => { x with incomingEdges := x.incomingEdges.erase e }
    | none => a
  let a := match target with
    | some t => a.modifyPort t fun x => { x with incomingEdges := x.incomingEdges.insertIdx! index e }
    | none => a
  a.modifyEdge e fun x => { x with target := target }

end LGraphArena

end Elk.Alg.Layered.Graph
