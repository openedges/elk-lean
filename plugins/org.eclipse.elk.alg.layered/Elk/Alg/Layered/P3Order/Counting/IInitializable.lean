import Elk.Alg.Layered.Graph
/-!
# `org.eclipse.elk.alg.layered.p3order.counting.IInitializable`

Callbacks invoked by `Initializable.init` while traversing the current node order
(layers → nodes → ports → connected edges). Implementations keep their state behind
`IO.Ref`s created with the implementation object, so the callbacks are plain closures.
-/
namespace Elk.Alg.Layered.P3Order.Counting

open Elk.Alg.Layered.Graph LayeredM

/-- `IInitializable`: every callback defaults to a no-op. -/
structure Initializable where
  /-- `initAtLayerLevel(layerIndex, nodeOrder)`. -/
  initAtLayerLevel : Nat → Array (Array LNodeId) → LayeredM Unit := fun _ _ => pure ()
  /-- `initAtNodeLevel(layerIndex, nodeIndex, nodeOrder)`. -/
  initAtNodeLevel : Nat → Nat → Array (Array LNodeId) → LayeredM Unit := fun _ _ _ => pure ()
  /-- `initAtPortLevel(layerIndex, nodeIndex, portIndex, nodeOrder)`. -/
  initAtPortLevel : Nat → Nat → Nat → Array (Array LNodeId) → LayeredM Unit := fun _ _ _ _ => pure ()
  /-- `initAtEdgeLevel(layerIndex, nodeIndex, portIndex, edgeIndex, edge, nodeOrder)`. -/
  initAtEdgeLevel : Nat → Nat → Nat → Nat → LEdgeId → Array (Array LNodeId) → LayeredM Unit := fun _ _ _ _ _ _ => pure ()
  /-- `initAfterTraversal()`. -/
  initAfterTraversal : LayeredM Unit := pure ()
  /-- Lean only: `false` when `initAtPortLevel` is the no-op (the traversal then skips the call). -/
  usesPortLevel : Bool := true
  /-- Lean only: `false` when `initAtEdgeLevel` is the no-op. -/
  usesEdgeLevel : Bool := true

namespace Initializable

/-- `inits[k:]` at the layer level. -/
partial def layerLevel (inits : Array Initializable) (k l : Nat) (order : Array (Array LNodeId)) : LayeredM Unit := do
  if h : k < inits.size then
    inits[k].initAtLayerLevel l order
    layerLevel inits (k + 1) l order

/-- `inits[k:]` at the node level. -/
partial def nodeLevel (inits : Array Initializable) (k l n : Nat) (order : Array (Array LNodeId)) : LayeredM Unit := do
  if h : k < inits.size then
    inits[k].initAtNodeLevel l n order
    nodeLevel inits (k + 1) l n order

/-- `inits[k:]` at the port level. -/
partial def portLevel (inits : Array Initializable) (k l n p : Nat) (order : Array (Array LNodeId)) : LayeredM Unit := do
  if h : k < inits.size then
    inits[k].initAtPortLevel l n p order
    portLevel inits (k + 1) l n p order

/-- `inits[k:]` at the edge level. -/
partial def edgeLevel (inits : Array Initializable) (k l n p e : Nat) (edge : LEdgeId) (order : Array (Array LNodeId)) :
    LayeredM Unit := do
  if h : k < inits.size then
    inits[k].initAtEdgeLevel l n p e edge order
    edgeLevel inits (k + 1) l n p e edge order

/-- The edge level over `edges[k:]` (edge indices from `base + k`). -/
partial def edgeLoop (inits : Array Initializable) (l n p : Nat) (edges : Array LEdgeId) (base k : Nat)
    (order : Array (Array LNodeId)) : LayeredM Unit := do
  if h : k < edges.size then
    edgeLevel inits 0 l n p (base + k) edges[k] order
    edgeLoop inits l n p edges base (k + 1) order

/-- The port (and edge) levels over the ports `ports[p:]` of node `n` of layer `l`. -/
partial def portLoop (portInits edgeInits : Array Initializable) (l n : Nat) (ports : Array LPortId) (p : Nat)
    (order : Array (Array LNodeId)) : LayeredM Unit := do
  if h : p < ports.size then
    portLevel portInits 0 l n p order
    if !edgeInits.isEmpty then
      let pt ← getPort ports[p]
      -- `connectedEdges` (incoming, then outgoing) without building the concatenation
      let incoming := pt.incomingEdges
      let outgoing := pt.outgoingEdges
      edgeLoop edgeInits l n p incoming 0 0 order
      edgeLoop edgeInits l n p outgoing incoming.size 0 order
    portLoop portInits edgeInits l n ports (p + 1) order

/-- The node (and port) levels over the nodes `nodes[n:]` of layer `l`. -/
partial def nodeLoop (inits portInits edgeInits : Array Initializable) (l : Nat) (nodes : Array LNodeId) (n : Nat)
    (order : Array (Array LNodeId)) : LayeredM Unit := do
  if h : n < nodes.size then
    nodeLevel inits 0 l n order
    if !(portInits.isEmpty && edgeInits.isEmpty) then
      portLoop portInits edgeInits l n (← getNode nodes[n]).ports 0 order
    nodeLoop inits portInits edgeInits l nodes (n + 1) order

/-- The traversal from layer `l` on. -/
partial def layerLoop (inits portInits edgeInits : Array Initializable) (l : Nat) (order : Array (Array LNodeId)) :
    LayeredM Unit := do
  if h : l < order.size then
    layerLevel inits 0 l order
    nodeLoop inits portInits edgeInits l order[l] 0 order
    layerLoop inits portInits edgeInits (l + 1) order

/-- `IInitializable.init(initializables, order)`: the traversal (ports in node order, edges
in `connectedEdges` order = incoming then outgoing). Initializables whose port or edge level is the
no-op (`usesPortLevel`/`usesEdgeLevel`) are not called there, and the edge level is not traversed
when none uses it. The node's port list is read when its port loop starts (after the node level
of every initializable, which may change it). -/
def init (initializables : Array Initializable) (order : Array (Array LNodeId)) : LayeredM Unit := do
  let portInits := initializables.filter (·.usesPortLevel)
  let edgeInits := initializables.filter (·.usesEdgeLevel)
  layerLoop initializables portInits edgeInits 0 order
  for i in initializables do i.initAfterTraversal

end Initializable

end Elk.Alg.Layered.P3Order.Counting
