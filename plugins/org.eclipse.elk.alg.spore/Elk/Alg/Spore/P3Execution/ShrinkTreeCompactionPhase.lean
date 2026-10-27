import Elk.Alg.Common.Spore.DepthFirstCompaction
import Elk.Alg.Spore.SporePhases
/-!
# `org.eclipse.elk.alg.spore.p3execution.ShrinkTreeCompactionPhase`

Port of `p3execution/shrink_tree_compaction_phase.rs` (elk-rs) and `ShrinkTreeCompactionPhase.java`:
the execution phase of the compaction. Compacts the spanning tree depth first with
`DepthFirstCompaction` (`Graph.orthogonalCompaction` restricts the translations to the axes).
Without a tree nothing happens. The SVG debug output is not ported (TODO(debug)).
-/
namespace Elk.Alg.Spore.P3Execution

open Elk.Core.Alg Elk.Core.Util Elk.Alg.Common.Spore Elk.Alg.Spore.Graph

namespace ShrinkTreeCompactionPhase

/-- `process(graph, progressMonitor)`: the shrink tree compaction phase. -/
def process (_graph : Unit) (monitor : ProgressMonitor) : SporeM Unit := do
  let _ ← monitor.begin "Shrinking tree compaction" 1.0
  modify fun g =>
    match g.tree with
    | none => g
    | some tree =>
      { g with tree := some (DepthFirstCompaction.compactWithoutDebug tree g.orthogonalCompaction) }
  monitor.done

/-- The `ShrinkTreeCompactionPhase` phase (no intermediate processors). -/
def phase : SporePhase :=
  { name := "ShrinkTreeCompactionPhase", process := process,
    getLayoutProcessorConfiguration := fun _ => noProcessors }

end ShrinkTreeCompactionPhase

end Elk.Alg.Spore.P3Execution
