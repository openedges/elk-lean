import Elk.Graph
import Elk.Core.Math
/-!
# `org.eclipse.elk.alg.topdownpacking.INodeArranger`

Port of `i_node_arranger.rs` (elk-rs).
-/
namespace Elk.Alg.TopdownPacking

open Elk.Graph Elk.Core.Math

/-- `INodeArranger`: predicts the size of a graph once its children are arranged. -/
structure INodeArranger where
  /-- `get_predicted_size(graph)`. -/
  getPredictedSize : NodeId → ElkM KVector

end Elk.Alg.TopdownPacking
