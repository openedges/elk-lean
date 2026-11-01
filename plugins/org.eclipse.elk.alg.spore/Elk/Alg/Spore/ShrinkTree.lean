import Elk.Alg.Spore.PhaseFactories
import Elk.Core.Util.FloatConst
open Elk.Core.Util.FloatConst
/-!
# `org.eclipse.elk.alg.spore.ShrinkTree`

Port of `shrink_tree.rs` (elk-rs) and `ShrinkTree.java`: the compaction algorithm. Assembles the
three phases (Delaunay triangulation, the tree construction strategy of the graph, the compaction
strategy of the graph), runs them on the graph (only if it has more than one vertex), and copies
the positions of the tree nodes back to the vertices.

Rust quirk kept: when the monitor is canceled between two processors, `shrink` returns at once
without `sync_vertices_from_tree` and without `done`.
-/

namespace Elk.Alg.Spore

open Elk Elk.Core.Alg Elk.Core.Util Elk.Alg.Spore.Graph Elk.Alg.Spore.Options

/-- `org.eclipse.elk.alg.spore.ShrinkTree`. -/
structure ShrinkTree where
  /-- The algorithm assembler (`algorithm_assembler`). -/
  assembler : SporeAssembler

namespace ShrinkTree

/-- `ShrinkTree::new()`. -/
def new : IO ShrinkTree := return ⟨← SporeAssembler.create⟩

/-- `shrink(graph, progress_monitor)`: compacts the graph by contracting its spanning tree; returns
the graph with the updated vertices. -/
def shrink (st : ShrinkTree) (graph : Graph) (monitor : ProgressMonitor) : IO Graph := do
  let a := st.assembler
  a.reset
  a.setPhase .p1Structure StructureExtractionStrategy.delaunayTriangulation.factory
  a.setPhase .p2ProcessingOrder graph.treeConstructionStrategy.factory
  a.setPhase .p3Execution graph.compactionStrategy.factory
  let (algorithm, graph) ← SporeM.run (a.build ()) graph
  let total := (max algorithm.size 1).toFloat.toF32
  let _ ← monitor.begin "Compaction by shrinking a tree" total
  let mut graph := graph
  if graph.vertices.size > 1 then
    for processor in algorithm do
      if ← monitor.isCanceled then return graph
      let sub ← monitor.subTask fl1p0
      let ((), g) ← SporeM.run (processor.process () sub) graph
      graph := g
  graph := graph.syncVerticesFromTree
  monitor.done
  return graph

end ShrinkTree

end Elk.Alg.Spore
