import Std.Data.HashMap
import Elk.Graph.Properties
import Elk.Core.Util.JavaHashSet
import Elk.Alg.Common.Geometry.TEdge
import Elk.Alg.Common.Geometry.Tree
import Elk.Alg.Common.Spore.Node
import Elk.Alg.Common.Spore.InternalProperties
import Elk.Alg.Spore.Options.CompactionStrategy
import Elk.Alg.Spore.Options.SpanningTreeCostFunction
import Elk.Alg.Spore.Options.TreeConstructionStrategy
/-!
# `org.eclipse.elk.alg.spore.graph.Graph`

Port of `graph/graph.rs` (elk-rs) and `Graph.java`: the algorithm-internal graph of the SPOrE
algorithms. Vertices are an arena (`vertices`), referred to by index (`preferredRootIndex`,
`nodeIndexMap`); the spanning tree is the value tree of `alg.common` (`Tree Node`) whose nodes are
copies of the vertices, copied back by `syncVerticesFromTree`.

The graph lives in the algorithm's own monad, `SporeM = StateRefT Graph IO` (see `SporePhases`).

Order: `tEdges` (Java `Set<TEdge>`, a `HashSet`) is a `JavaHashSet` with Java's iteration order
(see `BowyerWatsonTriangulation`, `NaiveMinST`); elk-rs' set had a random order.
-/
namespace Elk.Alg.Spore.Graph

open Elk Elk.Graph Elk.Core.Math Elk.Alg.Common Elk.Alg.Common.Spore Elk.Alg.Spore.Options

/-- `org.eclipse.elk.alg.spore.graph.Graph`. -/
structure Graph where
  /-- Property holder (`DEBUG_SVG`, `OVERLAPS_EXISTED`). -/
  props : PropertyMap := {}
  /-- The vertices (nodes) of the graph. -/
  vertices : Array Node := #[]
  /-- The edges of the structure phase (`None` until the first structure phase ran). -/
  tEdges : Option (Elk.Core.Util.JavaHashSet TEdge) := none
  /-- The tree construction strategy (phase 2). -/
  treeConstructionStrategy : TreeConstructionStrategy
  /-- The spanning tree (phase 2 result). -/
  tree : Option (Tree Node) := none
  /-- The compaction strategy (phase 3). -/
  compactionStrategy : CompactionStrategy
  /-- The cost function of the spanning tree construction. -/
  costFunction : SpanningTreeCostFunction
  /-- Index into `vertices` of the preferred root node. -/
  preferredRootIndex : Option Nat := none
  /-- Whether the compaction is restricted to orthogonal translations. -/
  orthogonalCompaction : Bool := false
  /-- `originalVertex ↦ index into vertices` (`node_index_map`). -/
  nodeIndexMap : Std.HashMap KVector Nat := {}

namespace Graph

/-- `Graph::new(cost_function, tree_construction_strategy, compaction_strategy)`. -/
def new (costFunction : SpanningTreeCostFunction) (treeConstructionStrategy : TreeConstructionStrategy)
    (compactionStrategy : CompactionStrategy) : Graph :=
  { treeConstructionStrategy, compactionStrategy, costFunction }

/-- `rebuild_index_map`: maps every vertex' `originalVertex` to its index (later vertices with an
equal `originalVertex` overwrite earlier ones). -/
def rebuildIndexMap (g : Graph) : Graph := Id.run do
  let mut m : Std.HashMap KVector Nat := {}
  let mut idx := 0
  for node in g.vertices do
    m := m.insert node.originalVertex idx
    idx := idx + 1
  return { g with nodeIndexMap := m }

/-- `node_for_vertex(vertex)`. -/
def nodeForVertex (g : Graph) (vertex : KVector) : Option Node :=
  (g.nodeIndexMap.get? vertex).bind fun idx => g.vertices[idx]?

/-- `preferred_root()`. -/
def preferredRoot (g : Graph) : Option Node :=
  g.preferredRootIndex.bind fun idx => g.vertices[idx]?

/-- `sync_vertices_from_tree`: copies `vertex` and `rect` of every tree node (looked up by
`originalVertex`; the pre-order last node wins for equal keys) back to the vertices. No-op without
a tree. -/
def syncVerticesFromTree (g : Graph) : Graph :=
  match g.tree with
  | none => g
  | some tree =>
    let map : Std.HashMap KVector Node := tree.preorder.foldl
      (fun m n => m.insert n.originalVertex n) {}
    { g with vertices := g.vertices.map fun node =>
        match map.get? node.originalVertex with
        | some updated => { node with vertex := updated.vertex, rect := updated.rect }
        | none => node }

/-- `get_property(property)` (stored value, else the property default). -/
def getProperty {α : Type} [PropCodec α] (g : Graph) (p : Property α) : Option α := g.props.get p

/-- `set_property(property, Some(value))`. -/
def setProperty {α : Type} [PropCodec α] (g : Graph) (p : Property α) (v : α) : Graph :=
  { g with props := g.props.set p v }

end Graph

end Elk.Alg.Spore.Graph
