import Elk.Alg.Layered.Graph.LGraph
import Elk.Alg.Layered.Graph.Layer
import Elk.Alg.Layered.Graph.LNode
import Elk.Alg.Layered.Graph.LPort
import Elk.Alg.Layered.Graph.LEdge
import Elk.Alg.Layered.Graph.LLabel
/-!
# The layered graph arena

One arena per layered run holds every element of every nested `LGraph`. The pure
functions here are the building blocks of the `LayeredM` helpers; relation changes
(`setNodeLayer`, `setPortNode`, `setEdgeSource`, …) update both sides like the Java
setters do.
-/
namespace Elk.Alg.Layered.Graph

open Elk.Graph Elk.Core.Math

/-- All elements of a layered run. -/
structure LGraphArena where
  graphs : Array LGraph := #[]
  nodes : Array LNode := #[]
  ports : Array LPort := #[]
  edges : Array LEdge := #[]
  labels : Array LLabel := #[]
  layers : Array Layer := #[]
  deriving Inhabited

namespace LGraphArena

@[inline] def graph (a : LGraphArena) (g : LGraphId) : LGraph := a.graphs[g.idx]!
@[inline] def node (a : LGraphArena) (n : LNodeId) : LNode := a.nodes[n.idx]!
@[inline] def port (a : LGraphArena) (p : LPortId) : LPort := a.ports[p.idx]!
@[inline] def edge (a : LGraphArena) (e : LEdgeId) : LEdge := a.edges[e.idx]!
@[inline] def label (a : LGraphArena) (l : LLabelId) : LLabel := a.labels[l.idx]!
@[inline] def layer (a : LGraphArena) (l : LayerId) : Layer := a.layers[l.idx]!

@[inline] def modifyGraph (a : LGraphArena) (g : LGraphId) (f : LGraph → LGraph) : LGraphArena :=
  { a with graphs := a.graphs.modify g.idx f }
@[inline] def modifyNode (a : LGraphArena) (n : LNodeId) (f : LNode → LNode) : LGraphArena :=
  { a with nodes := a.nodes.modify n.idx f }
@[inline] def modifyPort (a : LGraphArena) (p : LPortId) (f : LPort → LPort) : LGraphArena :=
  { a with ports := a.ports.modify p.idx f }
@[inline] def modifyEdge (a : LGraphArena) (e : LEdgeId) (f : LEdge → LEdge) : LGraphArena :=
  { a with edges := a.edges.modify e.idx f }
@[inline] def modifyLabel (a : LGraphArena) (l : LLabelId) (f : LLabel → LLabel) : LGraphArena :=
  { a with labels := a.labels.modify l.idx f }
@[inline] def modifyLayer (a : LGraphArena) (l : LayerId) (f : Layer → Layer) : LGraphArena :=
  { a with layers := a.layers.modify l.idx f }

/-- `new LGraph()`. -/
def createGraph (a : LGraphArena) (g : LGraph := {}) : LGraphArena × LGraphId :=
  ({ a with graphs := a.graphs.push g }, ⟨a.graphs.size⟩)

/-- `new LNode(graph)`: the node knows its graph but is not added to `layerlessNodes`. -/
def createNode (a : LGraphArena) (graph : LGraphId) (n : LNode := {}) : LGraphArena × LNodeId :=
  ({ a with nodes := a.nodes.push { n with graph := some graph } }, ⟨a.nodes.size⟩)

/-- `new LPort()`. -/
def createPort (a : LGraphArena) (p : LPort := {}) : LGraphArena × LPortId :=
  ({ a with ports := a.ports.push p }, ⟨a.ports.size⟩)

/-- `new LEdge()`. -/
def createEdge (a : LGraphArena) (e : LEdge := {}) : LGraphArena × LEdgeId :=
  ({ a with edges := a.edges.push e }, ⟨a.edges.size⟩)

/-- `new LLabel(text)`. -/
def createLabel (a : LGraphArena) (text : String := "") (l : LLabel := {}) : LGraphArena × LLabelId :=
  ({ a with labels := a.labels.push { l with text := text } }, ⟨a.labels.size⟩)

/-- `new Layer(graph)`: not added to the graph's `layers` (callers do). -/
def createLayer (a : LGraphArena) (graph : LGraphId) : LGraphArena × LayerId :=
  ({ a with layers := a.layers.push { owner := graph } }, ⟨a.layers.size⟩)

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
