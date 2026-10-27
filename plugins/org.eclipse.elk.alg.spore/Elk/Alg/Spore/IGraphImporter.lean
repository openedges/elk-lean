import Elk.Alg.Spore.Graph.Graph
/-!
# `org.eclipse.elk.alg.spore.IGraphImporter`

Port of `i_graph_importer.rs` (elk-rs) and `IGraphImporter.java`: an importer builds the SPOrE
`Graph` from an input graph of type `T`, can update it between overlap removal iterations, and
writes the final positions back. The importer value `σ` carries its own mutable state; the
operations run in the monad `m` that gives access to the input graph.
-/
namespace Elk.Alg.Spore

open Elk.Alg.Spore.Graph

/-- `IGraphImporter<T>`. -/
class IGraphImporter (σ : Type) (T : Type) (m : Type → Type) where
  /-- `importGraph(inputGraph)`: transforms the input graph to a SPOrE `Graph`. -/
  importGraph : σ → T → m Graph
  /-- `updateGraph(graph)`: updates the graph after an iteration (new original vertices). -/
  updateGraph : σ → Graph → m Graph
  /-- `applyPositions(graph)`: writes the node positions of `graph` back to the input graph. -/
  applyPositions : σ → Graph → m Unit

end Elk.Alg.Spore
