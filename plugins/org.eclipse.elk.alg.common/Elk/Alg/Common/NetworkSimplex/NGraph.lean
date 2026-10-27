import Elk.Alg.Common.NetworkSimplex.NEdge
import Elk.Graph.ArrayModify
/-!
# `org.eclipse.elk.alg.common.networksimplex.NGraph` (elk-rs `n_graph.rs`)

The graph structure used by the `NetworkSimplex` algorithm.

Representation (see `PORTING.md` §14):

* `nodes` / `edges` are arenas indexed by `NNodeId` / `NEdgeId`; ids stay valid
  for the lifetime of the graph (nothing is ever removed from an arena);
* `nodeList` is the Java `NGraph.nodes` list (Rust `NGraph::nodes`): the
  *ordered* sequence of graph nodes. Algorithms and callers iterate this list,
  never the arena. The network simplex temporarily removes subtree nodes from
  it and re-appends them afterwards, so after `NetworkSimplex.execute` its
  order generally differs from the creation order (the Rust `Vec` behaves the
  same way);
* edges are only reachable through the incoming/outgoing lists of nodes (as
  in Java/Rust, where nodes own their incident edges); the edge arena itself
  is never iterated.

Also defined here because they need the graph: `NNodeBuilder.create`,
`NEdgeBuilder.create`/`tryCreate` and `NEdge.reverse`.
-/
namespace Elk.Alg.Common.NetworkSimplex

/-- `NGraph`: a graph structure used by the `NetworkSimplex` algorithm. -/
structure NGraph (ο : Type) where
  /-- Arena of all nodes (index = `NNodeId.idx`). -/
  nodes : Array (NNode ο) := #[]
  /-- Arena of all edges (index = `NEdgeId.idx`). -/
  edges : Array (NEdge ο) := #[]
  /-- `NGraph.nodes`: the ordered node list of the graph. -/
  nodeList : Array NNodeId := #[]
  deriving Inhabited

namespace NGraph

/-- `new NGraph()` / Rust `NGraph::new`. -/
@[inline] def new {ο : Type} : NGraph ο := {}

/-- The node with id `n`. -/
@[inline] def node {ο : Type} (g : NGraph ο) (n : NNodeId) : NNode ο := g.nodes[n.idx]!

/-- The edge with id `e`. -/
@[inline] def edge {ο : Type} (g : NGraph ο) (e : NEdgeId) : NEdge ο := g.edges[e.idx]!

/-- In-place update of node `n`. -/
@[inline] def modifyNode {ο : Type} (g : NGraph ο) (n : NNodeId) (f : NNode ο → NNode ο) : NGraph ο :=
  { g with nodes := g.nodes.modifyIn n.idx f }

/-- In-place update of edge `e`. -/
@[inline] def modifyEdge {ο : Type} (g : NGraph ο) (e : NEdgeId) (f : NEdge ο → NEdge ο) : NGraph ο :=
  { g with edges := g.edges.modifyIn e.idx f }

/-- Adds a fully specified edge to the arena and appends it to the outgoing
edges of its source and the incoming edges of its target (the side effect of
`NEdgeBuilder.create`). No validation. -/
def addEdge {ο : Type} (g : NGraph ο) (e : NEdge ο) : NGraph ο × NEdgeId :=
  let id : NEdgeId := ⟨g.edges.size⟩
  let g := { g with edges := g.edges.push e }
  let g := g.modifyNode e.source fun n => { n with outgoingEdges := n.outgoingEdges.push id }
  let g := g.modifyNode e.target fun n => { n with incomingEdges := n.incomingEdges.push id }
  (g, id)

/-- `NGraph.writeDebugGraph(String)`: a no-op, as in the Rust port. -/
def writeDebugGraph {ο : Type} (_g : NGraph ο) (_filePath : String) : IO Unit := pure ()

/-- Sets `internalId` of every node to its position in `nodeList`. -/
private def indexNodes {ο : Type} (g : NGraph ο) : NGraph ο := Id.run do
  let order := g.nodeList
  let mut g := g
  for h : index in [0:order.size] do
    g := g.modifyNode order[index] fun n => { n with internalId := index }
  return g

/-- `NGraph.dfs(NNode, boolean[])`: marks the connected component of `node`.
Neighbours are visited incoming edges first, then outgoing edges (Java parity
order). An edge listed at a node it is not incident to (impossible for graphs
built through this API; Rust panics) is skipped. -/
partial def dfs {ο : Type} (g : NGraph ο) (node : NNodeId) (mark : Array Bool) : Array Bool := Id.run do
  let nd := g.node node
  let idx := nd.internalId
  if idx >= mark.size || mark[idx]! then
    return mark
  let mut mark := mark.set! idx true
  let mut neighbors : Array NNodeId := Array.mkEmpty nd.connectedEdgeCount
  for e in nd.incomingEdges do
    if let some o := (g.edge e).other? node then neighbors := neighbors.push o
  for e in nd.outgoingEdges do
    if let some o := (g.edge e).other? node then neighbors := neighbors.push o
  for other in neighbors do
    mark := dfs g other mark
  return mark

/-- `NGraph.findConCompRepresentatives()`: one representative node per
connected component, in `nodeList` order. Requires up-to-date `internalId`s. -/
def findConCompRepresentatives {ο : Type} (g : NGraph ο) : Array NNodeId := Id.run do
  let mut reps : Array NNodeId := #[]
  let mut mark := Array.replicate g.nodeList.size false
  for node in g.nodeList do
    let idx := (g.node node).internalId
    if idx < mark.size && !mark[idx]! then
      reps := reps.push node
      mark := dfs g node mark
  return reps

/-- `NNodeBuilder.create(NGraph)`: adds the node to the graph (arena and
`nodeList`) and returns its id. -/
def _root_.Elk.Alg.Common.NetworkSimplex.NNodeBuilder.create {ο : Type} (b : NNodeBuilder ο)
    (g : NGraph ο) : NGraph ο × NNodeId :=
  let id : NNodeId := ⟨g.nodes.size⟩
  ({ g with nodes := g.nodes.push b.node, nodeList := g.nodeList.push id }, id)

/-- `NGraph.createArtificialRootAndConnect(List)`: creates a new node and
connects it to every node of `nodesToConnect` with zero-weight, zero-delta edges. -/
def createArtificialRootAndConnect {ο : Type} (g : NGraph ο) (nodesToConnect : Array NNodeId) :
    NGraph ο × NNodeId := Id.run do
  let (g, root) := (NNode.of : NNodeBuilder ο).create g
  let mut g := g
  for n in nodesToConnect do
    -- `NEdge.of().delta(0).weight(0).source(root).target(n).create()`: the root is new, so never a self-loop
    let (g', _) := g.addEdge { delta := 0, weight := 0.0, source := root, target := n }
    g := g'
  return (g, root)

/-- `NGraph.makeConnected()`: checks whether the graph is connected. If not, one
representative per connected component is connected to a new artificial root
node, which is returned. Re-indexes `internalId` of all nodes. -/
def makeConnected {ο : Type} (g : NGraph ο) : NGraph ο × Option NNodeId :=
  let g := indexNodes g
  let ccRep := findConCompRepresentatives g
  if ccRep.size > 1 then
    let (g, root) := createArtificialRootAndConnect g ccRep
    (g, some root)
  else
    (g, none)

/-- `NGraph.isAcyclic()`: creates a topological ordering and checks for back
edges. Returns whether the graph is acyclic, and the graph with re-indexed
`internalId`s (the only state change). Follows the Rust port: the incident
counter saturates at zero (`usize`) instead of going negative. -/
def isAcyclic {ο : Type} (g : NGraph ο) : Bool × NGraph ο := Id.run do
  let g := indexNodes g
  let n := g.nodeList.size
  let mut incident := Array.replicate n 0
  let mut layer := Array.replicate n 0
  for node in g.nodeList do
    let nd := g.node node
    incident := incident.modify nd.internalId (· + nd.incomingEdges.size)
  let mut roots : Array NNodeId := #[]
  for node in g.nodeList do
    if (g.node node).incomingEdges.isEmpty then
      roots := roots.push node
  if roots.isEmpty && n != 0 then
    return (false, g)
  let mut head := 0
  while head < roots.size do
    let node := roots[head]!
    head := head + 1
    let nd := g.node node
    let nodeIdx := nd.internalId
    for e in nd.outgoingEdges do
      let target := (g.edge e).target
      let targetIdx := (g.node target).internalId
      layer := layer.set! targetIdx (max layer[targetIdx]! (layer[nodeIdx]! + 1))
      if incident[targetIdx]! > 0 then
        incident := incident.set! targetIdx (incident[targetIdx]! - 1)
      if incident[targetIdx]! == 0 then
        roots := roots.push target
  for node in g.nodeList do
    let nd := g.node node
    let sourceIdx := nd.internalId
    for e in nd.outgoingEdges do
      let targetIdx := (g.node (g.edge e).target).internalId
      if layer[targetIdx]! <= layer[sourceIdx]! then
        return (false, g)
  return (true, g)

end NGraph

namespace NEdgeBuilder

/-- `NEdgeBuilder.create()` as a pure function: validates the builder, adds the
edge to the graph and to the outgoing edges of the source and the incoming
edges of the target node. Fails with `IllegalStateException` if source or target
is missing, or if source equals target (self-loop). -/
def tryCreate {ο : Type} (b : NEdgeBuilder ο) (g : NGraph ο) : Except String (NGraph ο × NEdgeId) :=
  match b.source?, b.target? with
  | none, _ => .error "java.lang.IllegalStateException: source must be set"
  | _, none => .error "java.lang.IllegalStateException: target must be set"
  | some source, some target =>
    if source == target then
      .error "java.lang.IllegalStateException: Network simplex does not support self-loops"
    else
      .ok (g.addEdge { b.edge with source := source, target := target })

/-- `NEdgeBuilder.create()`: like `tryCreate`, throwing the exception in `IO`. -/
def create {ο : Type} (b : NEdgeBuilder ο) (g : NGraph ο) : IO (NGraph ο × NEdgeId) :=
  match b.tryCreate g with
  | .ok r => pure r
  | .error msg => throw (IO.userError msg)

end NEdgeBuilder

namespace NEdge

/-- `NEdge.reverse()` / Rust `NEdge::reverse`: swaps source and target and
updates the edge lists. As in Rust, the edge is removed from *all* positions of
the old source's outgoing and the old target's incoming list (`retain`), then
appended to the old target's outgoing and the old source's incoming list. -/
def reverse {ο : Type} (g : NGraph ο) (e : NEdgeId) : NGraph ο :=
  let ed := g.edge e
  let oldSource := ed.source
  let oldTarget := ed.target
  let g := g.modifyEdge e fun ed => { ed with source := oldTarget, target := oldSource }
  let g := g.modifyNode oldSource fun n => { n with outgoingEdges := n.outgoingEdges.filter (· != e) }
  let g := g.modifyNode oldTarget fun n => { n with incomingEdges := n.incomingEdges.filter (· != e) }
  let g := g.modifyNode oldTarget fun n => { n with outgoingEdges := n.outgoingEdges.push e }
  g.modifyNode oldSource fun n => { n with incomingEdges := n.incomingEdges.push e }

end NEdge

end Elk.Alg.Common.NetworkSimplex
