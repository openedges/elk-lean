import Elk.Graph
import Elk.Alg.Radial.InternalProperties
/-!
# `org.eclipse.elk.alg.radial.intermediate.compaction.IRadialCompactor`

Port of `i_radial_compactor.rs` (elk-rs).
-/
namespace Elk.Alg.Radial.Intermediate.Compaction

open Elk.Graph

/-- `IRadialCompactor`: compacts the radial layout of a graph. -/
structure IRadialCompactor where
  /-- `compact(graph)`. -/
  compact : NodeId → RadialM Unit

end Elk.Alg.Radial.Intermediate.Compaction
