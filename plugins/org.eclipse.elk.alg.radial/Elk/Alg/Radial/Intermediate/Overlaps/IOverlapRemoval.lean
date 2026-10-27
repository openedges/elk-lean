import Elk.Graph
import Elk.Core.Util.ProgressMonitor
import Elk.Alg.Radial.InternalProperties
/-!
# `org.eclipse.elk.alg.radial.intermediate.overlaps.IOverlapRemoval`

Port of `i_overlap_removal.rs` (elk-rs).
-/
namespace Elk.Alg.Radial.Intermediate.Overlaps

open Elk.Graph Elk.Core.Util

/-- `IOverlapRemoval`. -/
structure IOverlapRemoval where
  /-- `remove_overlaps(graph, progress_monitor)`. -/
  removeOverlaps : NodeId → ProgressMonitor → RadialM Unit

end Elk.Alg.Radial.Intermediate.Overlaps
