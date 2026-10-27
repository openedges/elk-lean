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

/-- `IInitializable.init(initializables, order)`: the traversal (ports in node order, edges
in `connectedEdges` order = incoming then outgoing). Initializables whose port or edge level is the
no-op (`usesPortLevel`/`usesEdgeLevel`) are not called there, and the edge level is not traversed
when none uses it. -/
def init (initializables : Array Initializable) (order : Array (Array LNodeId)) : LayeredM Unit := do
  let portInits := initializables.filter (·.usesPortLevel)
  let edgeInits := initializables.filter (·.usesEdgeLevel)
  for h : layerIndex in [0:order.size] do
    let layerNodes := order[layerIndex]
    for i in initializables do i.initAtLayerLevel layerIndex order
    for h2 : nodeIndex in [0:layerNodes.size] do
      let node := layerNodes[nodeIndex]
      for i in initializables do i.initAtNodeLevel layerIndex nodeIndex order
      if portInits.isEmpty && edgeInits.isEmpty then continue
      let ports := (← getNode node).ports
      for h3 : portIndex in [0:ports.size] do
        let port := ports[portIndex]
        for i in portInits do i.initAtPortLevel layerIndex nodeIndex portIndex order
        if edgeInits.isEmpty then continue
        let pt ← getPort port
        -- `connectedEdges` (incoming, then outgoing) without building the concatenation
        let incoming := pt.incomingEdges
        let outgoing := pt.outgoingEdges
        for h4 : edgeIndex in [0:incoming.size] do
          for i in edgeInits do i.initAtEdgeLevel layerIndex nodeIndex portIndex edgeIndex incoming[edgeIndex] order
        for h4 : k in [0:outgoing.size] do
          for i in edgeInits do i.initAtEdgeLevel layerIndex nodeIndex portIndex (incoming.size + k) outgoing[k] order
  for i in initializables do i.initAfterTraversal

end Initializable

end Elk.Alg.Layered.P3Order.Counting
