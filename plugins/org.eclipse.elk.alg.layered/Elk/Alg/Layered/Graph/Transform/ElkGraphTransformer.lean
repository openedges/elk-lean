import Elk.Alg.Layered.Graph.Transform.IGraphTransformer
import Elk.Alg.Layered.Graph.Transform.ElkGraphImporter
/-!
# `org.eclipse.elk.alg.layered.graph.transform.ElkGraphTransformer`

Port of elk-rs `graph/transform/elk_graph_transformer.rs` (Java `ElkGraphTransformer`): "Manages
the transformation of ElkGraphs to LGraphs and back." The transformer owns the `OriginStore`
shared by its imports; every `importGraph` runs a fresh `ElkGraphImporter` on it (Rust
`ElkGraphImporter::new(&mut self.origin_store)`), and `applyLayout` runs the
`ElkGraphLayoutTransferrer` with it.

Use from the layout provider (Rust `LayeredLayoutProvider::layout`):
```
let transformer ← ElkGraphTransformer.new          -- IO
let (((), _arena), elkGraph) ← LImportM.run (do
    let lgraph ← transformer.importGraph root
    liftLayered (elkLayered.doLayout lgraph (some monitor))  -- or doCompoundLayout
    transformer.applyLayout lgraph) {} elkGraph
```
-/
namespace Elk.Alg.Layered.Graph.Transform

open Elk.Graph Elk.Alg.Layered.Graph

/-- `ElkGraphTransformer`: the origin store shared by the imports of one transformer. -/
structure ElkGraphTransformer where
  /-- Rust `origin_store` (only its `ledges` registry, see `OriginStore`). -/
  originStore : IO.Ref OriginStore

namespace ElkGraphTransformer

/-- Rust `ElkGraphTransformer::new()`: a transformer with an empty origin store. -/
def create : IO ElkGraphTransformer := do
  return { originStore := ← IO.mkRef {} }

/-- `importGraph(graph)` (Rust `import_graph`): a fresh `ElkGraphImporter` on the shared store. -/
def importGraph (t : ElkGraphTransformer) (graph : NodeId) : LImportM LGraphId := do
  let importer ← ElkGraphImporter.withOriginStore t.originStore
  importer.importGraph graph

/-- `applyLayout(layeredGraph)` (Rust `apply_layout`): the layout transferrer with the store. -/
def applyLayout (t : ElkGraphTransformer) (layeredGraph : LGraphId) : LImportM Unit := do
  let importer ← ElkGraphImporter.withOriginStore t.originStore
  importer.applyLayout layeredGraph

/-- The transformer as an `IGraphTransformer<ElkNode>`. -/
def toIGraphTransformer (t : ElkGraphTransformer) : IGraphTransformer NodeId where
  importGraph := t.importGraph
  applyLayout := t.applyLayout

/-- `new ElkGraphTransformer()` as an `IGraphTransformer<ElkNode>` (fresh origin store). -/
def new : IO (IGraphTransformer NodeId) := do
  return (← create).toIGraphTransformer

end ElkGraphTransformer

end Elk.Alg.Layered.Graph.Transform
