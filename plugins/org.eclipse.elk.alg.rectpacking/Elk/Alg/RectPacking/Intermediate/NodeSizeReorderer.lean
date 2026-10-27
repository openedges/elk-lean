import Elk.Core.Alg
import Elk.Core.Util.Sort
import Elk.Alg.RectPacking.Util.RectPackingArena
import Elk.Alg.RectPacking.Intermediate.NodeSizeComparator
/-!
# `org.eclipse.elk.alg.rectpacking.intermediate.NodeSizeReorderer`

Port of `intermediate/node_size_reorderer.rs` (elk-rs): sorts the children of the graph by
decreasing height (stable, `NodeSizeComparator`). Like Rust and Java the progress monitor is not
used.
-/
namespace Elk.Alg.RectPacking.Intermediate

open Elk.Graph Elk.Core.Util Elk.Core.Alg Elk.Alg.RectPacking.Util

namespace NodeSizeReorderer

/-- `process(graph, progress_monitor)` on the `ElkGraph`. -/
def run (graph : NodeId) : ElkM Unit := do
  let children := (← ElkM.getNode graph).children
  let g ← get
  let sorted := stableSort children (NodeSizeComparator.compare g)
  ElkM.modifyNode graph fun n => { n with children := sorted }

/-- `NodeSizeReorderer` as an `ILayoutProcessor<ElkNode>`. -/
def processor : LayoutProcessor RectPackingM NodeId :=
  { name := "NodeSizeReorderer", process := fun graph _ => run graph }

end NodeSizeReorderer

end Elk.Alg.RectPacking.Intermediate
