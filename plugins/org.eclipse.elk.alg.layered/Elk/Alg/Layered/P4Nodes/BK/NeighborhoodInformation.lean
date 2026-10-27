import Elk.Alg.Layered.P4Nodes.BK.BKUtil
import Elk.Core.Util.Sort
/-!
# `org.eclipse.elk.alg.layered.p4nodes.bk.NeighborhoodInformation` (elk-rs `neighborhood_information.rs`)

Neighborhood information for a layered graph that is used during BK node placing. Since this
information is required multiple times but does not change during processing it is
precalculated here.

The neighbor pairs `Pair<LNode, LEdge>` are stored as `(local node id, edge)` (Rust reads
`node_id(&pair.first)` wherever it uses the node).
-/
namespace Elk.Alg.Layered.P4Nodes.BK

open Elk.Graph Elk.Core.Math Elk.Core.Util Elk.Alg.Layered.Graph Elk.Alg.Layered.Options

/-- `NeighborhoodInformation`. -/
structure NeighborhoodInformation where
  /-- `nodeCount`: number of nodes in the layers of the graph. -/
  nodeCount : Nat := 0
  /-- `layerIndex[l.id]`: the index of layer `l`. -/
  layerIndex : Array Nat := #[]
  /-- `nodeIndex[n.id]`: the index of `n` within its layer. -/
  nodeIndex : Array Nat := #[]
  /-- `leftNeighbors[n.id]`: the left neighbors of `n` with an edge connecting them, sorted by
  the neighbors' in-layer index (only the edges of maximal `PRIORITY_STRAIGHTNESS`). -/
  leftNeighbors : Array (Array (Nat × LEdgeId)) := #[]
  /-- `rightNeighbors[n.id]`: see `leftNeighbors`. -/
  rightNeighbors : Array (Array (Nat × LEdgeId)) := #[]
  deriving Inhabited

namespace NeighborhoodInformation

/-- `node_index.get(id).unwrap_or(0)`. -/
@[inline] def nodeIndexOf (ni : NeighborhoodInformation) (id : Nat) : Nat := ni.nodeIndex.getD id 0

/-- `layer_index.get(id).unwrap_or(0)`. -/
@[inline] def layerIndexOf (ni : NeighborhoodInformation) (id : Nat) : Nat := ni.layerIndex.getD id 0

/-- `neighbor_cmp`: compares the neighbors' in-layer indices. -/
private def neighborCmp (ni : NeighborhoodInformation) (x y : Nat × LEdgeId) : Ordering :=
  compare (ni.nodeIndexOf x.1) (ni.nodeIndexOf y.1)

/-- One neighbor list of `build_for` (`determineAllRightNeighbors`/`determineAllLeftNeighbors`):
the edges of maximal straightness priority (self loops and in-layer edges skipped), paired with
the node at the other end (`outgoing`: the target, else the source) if that node has a local id
below `nodeCount`; sorted stably by the neighbors' in-layer index. -/
private def neighborsOf (a : LGraphArena) (ni : NeighborhoodInformation) (edges : Array LEdgeId)
    (outgoing : Bool) : Array (Nat × LEdgeId) := Id.run do
  let mut result : Array (Nat × LEdgeId) := #[]
  let mut maxPriority : Int := 0
  for e in edges do
    if a.edgeIsSelfLoop e || a.edgeIsInLayerEdge e then continue
    let ed := a.edge e
    let prio := (ed.props.get LayeredOptions.PRIORITY_STRAIGHTNESS).getD 0
    if prio > maxPriority then
      maxPriority := prio
      result := #[]
    if prio == maxPriority then
      let otherPort := if outgoing then ed.target else ed.source
      if let some other := otherPort.bind (fun p => (a.port p).owner) then
        let otherId := BKContext.idAsUsize (a.node other).id
        if otherId < ni.nodeCount then
          result := result.push (otherId, e)
  return stableSort result (neighborCmp ni)

/-- `NeighborhoodInformation.buildFor(graph)`: counts the nodes, assigns `layer.id` = layer
index and `node.id` = running node counter (layers in order, nodes in layer order; written to
the arena like Java/Rust), records each node's in-layer index and determines the left and right
neighbors of all nodes. -/
def buildFor (graph : LGraphId) : LayeredM NeighborhoodInformation := do
  let layers := (← LayeredM.getGraph graph).layers
  let mut nodeCount : Nat := 0
  for l in layers do
    nodeCount := nodeCount + (← LayeredM.getLayer l).nodes.size
  let mut layerIndex : Array Nat := Array.replicate layers.size 0
  let mut nodeIndex : Array Nat := Array.replicate nodeCount 0
  let mut counter : Nat := 0
  for li in [0:layers.size] do
    let l := layers[li]!
    LayeredM.modifyLayer l fun x => { x with id := (li : Int) }
    layerIndex := layerIndex.set! li li
    let nodes := (← LayeredM.getLayer l).nodes
    for k in [0:nodes.size] do
      LayeredM.modifyNode nodes[k]! fun x => { x with id := (counter : Int) }
      if counter ≥ nodeIndex.size then
        nodeIndex := nodeIndex ++ Array.replicate (counter + 1 - nodeIndex.size) 0
      nodeIndex := nodeIndex.set! counter k
      counter := counter + 1
  let ni : NeighborhoodInformation := { nodeCount, layerIndex, nodeIndex }
  let a ← get
  let mut left : Array (Array (Nat × LEdgeId)) := Array.replicate nodeCount #[]
  let mut right : Array (Array (Nat × LEdgeId)) := Array.replicate nodeCount #[]
  for l in layers do
    for n in (a.layer l).nodes do
      let id := BKContext.idAsUsize (a.node n).id
      if id ≥ nodeCount then continue
      right := right.set! id (neighborsOf a ni (a.nodeOutgoingEdges n) true)
      left := left.set! id (neighborsOf a ni (a.nodeIncomingEdges n) false)
  return { ni with leftNeighbors := left, rightNeighbors := right }

end NeighborhoodInformation

end Elk.Alg.Layered.P4Nodes.BK
