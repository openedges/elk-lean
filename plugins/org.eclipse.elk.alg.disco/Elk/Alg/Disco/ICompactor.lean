import Elk.Alg.Disco.Graph.DCGraph
/-!
# `org.eclipse.elk.alg.disco.ICompactor`

Interface of a compaction strategy for the `DCGraph` (elk-rs `i_compactor.rs`:
`fn compact(&mut self, graph: &mut DCGraph)`). Strategy interfaces are structures with a closure
field (PORTING.md, section 14); the updated graph is returned instead of mutated.
-/
namespace Elk.Alg.Disco

open Elk.Alg.Disco.Graph

/-- `ICompactor`: `compact(graph)` assigns an offset to every component and sets the graph
dimensions. -/
structure ICompactor where
  /-- `compact(graph)`. -/
  compact : DCGraph → IO DCGraph

end Elk.Alg.Disco
