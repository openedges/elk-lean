/-!
# `org.eclipse.elk.alg.common.networksimplex.NNode` (elk-rs `n_node.rs`)

A node of the graph processed by the network simplex algorithm, plus the typed
arena ids of the network simplex graph.

Representation (see `PORTING.md` §14):

* nodes and edges live in the arenas `NGraph.nodes` / `NGraph.edges` and are
  referenced by `NNodeId` / `NEdgeId` (Rust `Arc<Mutex<NNode>>` /
  `Arc<Mutex<NEdge>>`, `Arc::ptr_eq` → id equality);
* the Java `Object origin` payload is the type parameter `ο`;
* `NNodeBuilder.create` needs the graph and therefore lives in
  `Elk.Alg.Common.NetworkSimplex.NGraph` (Lean imports must be acyclic).
-/
namespace Elk.Alg.Common.NetworkSimplex

/-- Index of an `NNode` in `NGraph.nodes` (Rust `NNodeRef`). -/
structure NNodeId where
  idx : Nat
  deriving BEq, Hashable, Repr, Inhabited, DecidableEq, Ord

/-- Index of an `NEdge` in `NGraph.edges` (Rust `NEdgeRef`). -/
structure NEdgeId where
  idx : Nat
  deriving BEq, Hashable, Repr, Inhabited, DecidableEq, Ord

instance : ToString NNodeId := ⟨fun i => s!"NN{i.idx}"⟩
instance : ToString NEdgeId := ⟨fun i => s!"NE{i.idx}"⟩

/-- `NNode`: a node used by the `NetworkSimplex` algorithm. It has a list of
incoming and a list of outgoing edges (kept in insertion order, like the Java
`ChangeAwareArrayList`s and the Rust `Vec`s). -/
structure NNode (ο : Type) where
  /-- `NNode.id`: a public id, unused internally. -/
  id : Int := 0
  /-- `NNode.internalId`: internally set and used id to index arrays. -/
  internalId : Nat := 0
  /-- `NNode.origin`: an object from which this node is derived. -/
  origin : Option ο := none
  /-- `NNode.type` (Rust `type_label`): a debug label without semantic meaning. -/
  type : String := ""
  /-- `NNode.layer`: the layer the node is currently assigned to. -/
  layer : Int := 0
  /-- `NNode.getOutgoingEdges()`. -/
  outgoingEdges : Array NEdgeId := #[]
  /-- `NNode.getIncomingEdges()`. -/
  incomingEdges : Array NEdgeId := #[]
  /-- `NNode.treeNode`: whether the node is part of the spanning tree (never
  written by the elk-rs algorithm, which keeps a dense cache instead). -/
  treeNode : Bool := false
  /-- `NNode.unknownCutvalues`: incident tree edges whose cut value is still
  unknown (only used by the reference cut value computation). -/
  unknownCutvalues : Array NEdgeId := #[]
  deriving Repr

instance {ο : Type} : Inhabited (NNode ο) := ⟨{}⟩

namespace NNode

/-- `NNode.getConnectedEdges()` / Rust `connected_edges`: incoming edges first,
then outgoing edges (Java parity order). -/
@[inline] def connectedEdges {ο : Type} (n : NNode ο) : Array NEdgeId :=
  n.incomingEdges ++ n.outgoingEdges

/-- Rust `connected_edge_count`: number of connected edges. -/
@[inline] def connectedEdgeCount {ο : Type} (n : NNode ο) : Nat :=
  n.incomingEdges.size + n.outgoingEdges.size

end NNode

/-- `NNode.NNodeBuilder`: builder for `NNode`s (`NNode.of().id(..).origin(..).type(..).create(graph)`). -/
structure NNodeBuilder (ο : Type) where
  /-- The node currently being constructed. -/
  node : NNode ο := {}

/-- `NNode.of()`: a builder to construct a new node. -/
@[inline] def NNode.of {ο : Type} : NNodeBuilder ο := {}

namespace NNodeBuilder

/-- `NNodeBuilder.id(int)`: sets the id field. -/
@[inline] def id {ο : Type} (b : NNodeBuilder ο) (id : Int) : NNodeBuilder ο :=
  { b with node := { b.node with id := id } }

/-- `NNodeBuilder.origin(Object)`: sets the origin field. -/
@[inline] def origin {ο : Type} (b : NNodeBuilder ο) (origin : ο) : NNodeBuilder ο :=
  { b with node := { b.node with origin := some origin } }

/-- `NNodeBuilder.type(String)` (Rust `type_label`): sets the type field. -/
@[inline] def type {ο : Type} (b : NNodeBuilder ο) (type : String) : NNodeBuilder ο :=
  { b with node := { b.node with type := type } }

end NNodeBuilder

end Elk.Alg.Common.NetworkSimplex
