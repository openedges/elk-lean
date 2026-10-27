import Std.Data.HashMap
import Elk.Alg.Layered.Graph.Monad
/-!
# `org.eclipse.elk.alg.layered.graph.transform.IGraphTransformer`

Port of elk-rs `graph/transform/i_graph_transformer.rs` (Java `IGraphTransformer<T>`): "Interface
for graph transformers that import a graph into an `LGraph` and apply the layout back to the
original graph."

Besides the interface this module defines the monad all transformation code runs in:

* `LImportM := StateRefT LGraphArena ElkM`: the layered arena is the outer state, the ElkGraph
  (`ElkM`) the inner one. The importer reads and annotates the ElkGraph through lifted `ElkM`
  operations and builds the `LGraph` through lifted `LayeredM` operations (`liftLayered`, also
  available as an automatic `MonadLift LayeredM LImportM`; `ElkM` and `IO` lift automatically).
  Inside `LImportM`, `get`/`modify` refer to the **arena**.
* `OriginStore`: what remains of the Rust `OriginStore` (`elk_graph_transformer.rs`). The Rust
  store hands out numeric origin ids for ElkGraph elements; the Lean `Origin` constructors carry
  the ElkGraph ids directly, so only the `register_ledge` registry (`ElkEdge → LEdge`) is kept.
-/
namespace Elk.Alg.Layered.Graph.Transform

open Elk.Graph Elk.Alg.Layered.Graph

/-- The transformation monad: the layered arena on top of the ElkGraph state (see module doc). -/
abbrev LImportM := StateRefT LGraphArena ElkM

/-- Runs a `LayeredM` computation on the arena of `LImportM` (same state reference). -/
@[inline] def liftLayered {α : Type} (x : LayeredM α) : LImportM α :=
  fun ref => monadLift (x ref)

/-- Runs an `ElkM` computation on the ElkGraph of `LImportM`. -/
@[inline] def liftElk {α : Type} (x : ElkM α) : LImportM α := monadLift x

instance : MonadLift LayeredM LImportM := ⟨liftLayered⟩

namespace LImportM

/-- Runs a transformation on an arena and an ElkGraph; returns the result with both final states. -/
@[inline] def run {α : Type} (x : LImportM α) (a : LGraphArena) (g : ElkGraph) :
    IO ((α × LGraphArena) × ElkGraph) :=
  ElkM.run (StateRefT'.run x a) g

end LImportM

/-- Rust `OriginStore` (`elk_graph_transformer.rs`) reduced to its `ledges` registry
(`register_ledge` / `get_ledge`): the `LEdge` created for each imported `ElkEdge`. -/
abbrev OriginStore := Std.HashMap Elk.Graph.EdgeId LEdgeId

/-- `IGraphTransformer<T>` (Rust trait `IGraphTransformer<T>`): `importGraph(graph)` creates the
layered graph, `applyLayout(layeredGraph)` writes the computed layout back to the graph the layered
graph was created from. -/
structure IGraphTransformer (T : Type) where
  /-- `importGraph(graph)`: imports the graph into the arena and returns the top-level `LGraph`. -/
  importGraph : T → LImportM LGraphId
  /-- `applyLayout(layeredGraph)`: applies the layout of the `LGraph` to the original graph. -/
  applyLayout : LGraphId → LImportM Unit

end Elk.Alg.Layered.Graph.Transform
