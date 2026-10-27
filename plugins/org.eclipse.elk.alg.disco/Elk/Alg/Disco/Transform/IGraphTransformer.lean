import Elk.Alg.Disco.Graph.DCGraph
/-!
# `org.eclipse.elk.alg.disco.transform.IGraphTransformer`

Interface of a transformer between a concrete graph type `G` and the `DCGraph` (elk-rs
`i_graph_transformer.rs`: `import_graph(&mut self, graph: &G) -> &mut DCGraph` and
`apply_layout(&mut self)`). The monad `m` carries the transformer state; the compacted graph is
passed to `applyLayout` explicitly instead of being kept inside the transformer.
-/
namespace Elk.Alg.Disco.Transform

open Elk.Alg.Disco.Graph

/-- `IGraphTransformer<G>`. -/
structure IGraphTransformer (m : Type → Type) (G : Type) where
  /-- `importGraph(graph)`: builds the `DCGraph` of the graph. -/
  importGraph : G → m DCGraph
  /-- `applyLayout()`: applies the offsets of the compacted `DCGraph` to the original graph. -/
  applyLayout : DCGraph → m Unit

end Elk.Alg.Disco.Transform
