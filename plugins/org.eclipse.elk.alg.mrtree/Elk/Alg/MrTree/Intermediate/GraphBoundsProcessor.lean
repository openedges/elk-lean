import Elk.Core.Util.Java
import Elk.Alg.MrTree.Graph.TArena
/-!
# `org.eclipse.elk.alg.mrtree.intermediate.GraphBoundsProcessor`

Port of `intermediate/graph_bounds_processor.rs` (elk-rs): stores the bounding box of the node boxes
(`position` .. `position + size`) of the graph as `GRAPH_XMIN`, `GRAPH_YMIN`, `GRAPH_XMAX`,
`GRAPH_YMAX` (`f64::min`/`f64::max` starting at `f64::MAX`/`f64::MIN`; an empty graph keeps these
start values).
-/
namespace Elk.Alg.MrTree.Intermediate

open Elk.Core.Util Elk.Alg.MrTree.Graph

namespace GraphBoundsProcessor

/-- `GraphBoundsProcessor::process`. -/
def process (graph : TGraphId) (monitor : ProgressMonitor) : MrTreeM Unit := do
  discard <| monitor.begin "Process graph bounds" 1.0
  let mut xmin := Float.maxValue
  let mut ymin := Float.maxValue
  let mut xmax := Float.minValue
  let mut ymax := Float.minValue
  for node in (← MrTreeM.getGraph graph).nodes do
    let n ← MrTreeM.getNode node
    xmin := fmin xmin n.position.x
    ymin := fmin ymin n.position.y
    xmax := fmax xmax (n.position.x + n.size.x)
    ymax := fmax ymax (n.position.y + n.size.y)
  MrTreeM.modifyGraph graph fun g =>
    { g with internal.graphXmin := xmin, internal.graphYmin := ymin,
             internal.graphXmax := xmax, internal.graphYmax := ymax }
  monitor.done

/-- The `GraphBoundsProcessor` (`IntermediateProcessorStrategy.GRAPH_BOUNDS_PROC`). -/
def processor : TreeProcessor := { name := "GraphBoundsProcessor", process }

end GraphBoundsProcessor

end Elk.Alg.MrTree.Intermediate
