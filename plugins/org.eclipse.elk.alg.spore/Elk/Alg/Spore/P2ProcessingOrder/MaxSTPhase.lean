import Elk.Alg.Spore.P2ProcessingOrder.MinSTPhase
/-!
# `org.eclipse.elk.alg.spore.p2processingorder.MaxSTPhase`

Port of `p2processingorder/max_st_phase.rs` (elk-rs) and `MaxSTPhase.java`: finds a maximum
spanning tree as the minimum spanning tree for the negated cost function
(`InvertedCostFunction`), and converts it with `MinSTPhase.convertTree`.

Rust difference to `MinSTPhase` kept: the root vertex is the preferred root's `vertex` (or the
first vertex' `vertex`), not its `originalVertex`; the two differ only after `update_graph` moved
the vertices. The SVG debug output is not ported (TODO(debug)).
-/
namespace Elk.Alg.Spore.P2ProcessingOrder

open Elk.Core.Alg Elk.Core.Util Elk.Alg.Common Elk.Alg.Spore.Graph

namespace MaxSTPhase

/-- `process(graph, progressMonitor)`: the maximum spanning tree phase. -/
def process (_graph : Unit) (monitor : ProgressMonitor) : SporeM Unit := do
  let _ ← monitor.begin "Maximum spanning tree construction" 1.0
  modify fun g =>
    match g.vertices[0]? with
    | none => g
    | some first =>
      let root := (g.preferredRoot.getD first).vertex
      match g.tEdges with
      | none => g
      | some edges =>
        let inverted := InvertedCostFunction.new (GraphCostFunction.new g)
        let tree := NaiveMinST.createSpanningTree edges root inverted
        MinSTPhase.convertTree tree g
  monitor.done

/-- The `MaxSTPhase` phase (no intermediate processors). -/
def phase : SporePhase :=
  { name := "MaxSTPhase", process := process, getLayoutProcessorConfiguration := fun _ => noProcessors }

end MaxSTPhase

end Elk.Alg.Spore.P2ProcessingOrder
