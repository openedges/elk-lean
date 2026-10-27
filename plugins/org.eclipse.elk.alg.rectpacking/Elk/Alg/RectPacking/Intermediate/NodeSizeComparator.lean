import Elk.Graph
import Elk.Core.Util.Java
/-!
# `org.eclipse.elk.alg.rectpacking.intermediate.NodeSizeComparator`

Port of `intermediate/node_size_comparator.rs` (elk-rs): orders nodes by decreasing height.
-/
namespace Elk.Alg.RectPacking.Intermediate

open Elk.Graph Elk.Core.Util

namespace NodeSizeComparator

/-- `NodeSizeComparator::compare(node0, node1)`: `height1.partial_cmp(height0)` (`Equal` for
NaN), i.e. higher nodes first. -/
def compare (g : ElkGraph) (node0 node1 : NodeId) : Ordering :=
  Float.comparePartial (g.node node1).height (g.node node0).height

end NodeSizeComparator

end Elk.Alg.RectPacking.Intermediate
