import Elk.Core.LayoutProvider
import Elk.Alg.Common.Spore.ScanlineOverlapCheck
import Elk.Alg.Spore.ElkGraphImporter
import Elk.Alg.Spore.PhaseFactories
/-!
# `org.eclipse.elk.alg.spore.OverlapRemovalLayoutProvider`

Port of `overlap_removal_layout_provider.rs` (elk-rs) and `OverlapRemovalLayoutProvider.java`: the
layout provider of `org.eclipse.elk.sporeOverlap` (overlap removal by growing a tree, Nachmanson
et al.). If the option `underlyingLayoutAlgorithm` is set (and not blank), the algorithm with that
id (suffix) is applied first (an unknown one is silently ignored). Then the options of the spanning
tree are fixed (root = node closest to the center, cost `INVERTED_OVERLAP`, minimum spanning tree)
and the graph is imported. Up to `overlapRemoval.maxIterations` times (while overlaps existed): if
`overlapRemoval.runScanline`, a scanline overlap check collects the overlapping pairs as the
graph's edges (no overlap at all ends the loop); the phases Delaunay triangulation (which adds its
edges to the overlap edges), minimum spanning tree and grow tree run, the tree positions are
copied to the vertices and the importer updates the graph. Finally the positions are applied.

Order: the overlap edges are collected in the order the scanline reports them and the Delaunay
edges are appended (`TEdge.extendUnique`); the Rust `HashSet<TEdge>` iterates in random order, so
elk-rs is nondeterministic whenever edge costs tie (see `NaiveMinST`). The SVG debug output of the
scanline check is not ported (TODO(debug)).

Rust quirk kept: when the monitor is canceled between two processors, `layout` returns at once
without applying the positions and without `done`.
-/
namespace Elk.Alg.Spore

open Elk Elk.Graph Elk.Core Elk.Core.Alg Elk.Core.Util Elk.Core.Data Elk.Alg.Common
open Elk.Alg.Common.Spore Elk.Alg.Spore.Graph Elk.Alg.Spore.Options

namespace OverlapRemovalLayoutProvider

/-- The overlap handler of the scanline check: collects the pair of original vertices of two
overlapping nodes (`TEdge::new(n1.original_vertex, n2.original_vertex)`) into an insertion-ordered
duplicate-free edge list (`HashSet<TEdge>::insert`). -/
def overlapHandler : IOverlapHandler (Array TEdge) :=
  ⟨fun n1 n2 edges => TEdge.insertUnique edges (TEdge.new n1.originalVertex n2.originalVertex)⟩

/-- The sub-progress of each processor: `1 / n` in single precision (`1.0` for no processors). -/
def processorStep (count : Nat) : Float :=
  if count == 0 then 1.0 else (1.0 / count.toFloat).toF32

/-- `layout(layout_graph, progress_monitor)`. -/
def layout (layoutGraph : NodeId) (monitor : ProgressMonitor) : ElkM Unit := do
  if ← ElkM.hasNodeProp layoutGraph SporeOverlapRemovalOptions.UNDERLYING_LAYOUT_ALGORITHM then
    if let some requested := (← ElkM.getNode layoutGraph).props.get
        SporeOverlapRemovalOptions.UNDERLYING_LAYOUT_ALGORITHM then
      if !requested.trimAscii.toString.isEmpty then
        if let some algorithmData ← LayoutMetaDataService.getAlgorithmDataBySuffix requested then
          if let some provider ← LayoutProvider.create algorithmData.id then
            provider.layout layoutGraph (← monitor.subTask 1.0)
  ElkM.setNodeProp layoutGraph SporeCompactionOptions.PROCESSING_ORDER_ROOT_SELECTION
    RootSelection.centerNode
  ElkM.setNodeProp layoutGraph SporeCompactionOptions.PROCESSING_ORDER_SPANNING_TREE_COST_FUNCTION
    SpanningTreeCostFunction.invertedOverlap
  ElkM.setNodeProp layoutGraph SporeCompactionOptions.PROCESSING_ORDER_TREE_CONSTRUCTION
    TreeConstructionStrategy.minimumSpanningTree
  let maxIterations : Nat :=
    (max ((← ElkM.getNode layoutGraph).props.get
      SporeOverlapRemovalOptions.OVERLAP_REMOVAL_MAX_ITERATIONS |>.getD 0) 0).toNat
  let _ ← monitor.begin "Overlap removal" 1.0
  let importer ← ElkGraphImporter.new
  let mut graph ← importer.importGraph layoutGraph
  let assembler ← SporeAssembler.create
  let mut overlapsExisted := true
  let mut iteration := 0
  while iteration < maxIterations && overlapsExisted do
    let runScanline := ((← ElkM.getNode layoutGraph).props.get
      SporeOverlapRemovalOptions.OVERLAP_REMOVAL_RUN_SCANLINE).getD true
    if runScanline then
      let scanline := ScanlineOverlapCheck.new overlapHandler
      let edges := scanline.sweep graph.vertices #[]
      if edges.isEmpty then break
      graph := { graph with tEdges := some edges }
    assembler.reset
    assembler.setPhase .p1Structure StructureExtractionStrategy.delaunayTriangulation.factory
    assembler.setPhase .p2ProcessingOrder graph.treeConstructionStrategy.factory
    assembler.setPhase .p3Execution OverlapRemovalStrategy.growTree.factory
    let (algorithm, built) ← SporeM.run (assembler.build ()) graph
    graph := built
    let step := processorStep algorithm.size
    for processor in algorithm do
      if ← monitor.isCanceled then return
      let sub ← monitor.subTask step
      let ((), g) ← SporeM.run (processor.process () sub) graph
      graph := g
    graph := graph.syncVerticesFromTree
    graph ← importer.updateGraph graph
    overlapsExisted := (graph.getProperty InternalProperties.OVERLAPS_EXISTED).getD false
    iteration := iteration + 1
  importer.applyPositions graph
  monitor.done

/-- The `org.eclipse.elk.sporeOverlap` layout provider. -/
def provider : LayoutProvider := { id := SporeOverlapRemovalOptions.ALGORITHM_ID, layout := layout }

end OverlapRemovalLayoutProvider

builtin_initialize registerOverlapRemovalLayoutProvider : Unit ←
  LayoutProvider.register SporeOverlapRemovalOptions.ALGORITHM_ID
    (fun _ => OverlapRemovalLayoutProvider.provider)

end Elk.Alg.Spore
