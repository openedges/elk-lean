import Elk.Graph.Enum
/-!
# `org.eclipse.elk.alg.layered.options.LongEdgeOrderingStrategy`

Port of `options/long_edge_ordering_strategy.rs` (elk-rs) and `LongEdgeOrderingStrategy.java`.
-/
namespace Elk.Alg.Layered.Options

/-- `org.eclipse.elk.alg.layered.options.LongEdgeOrderingStrategy`: Strategy to sort dummy nodes
compared to nodes with no connection to the previous layer. Dummy nodes nodes are not part of the
input model and -/
elk_enum LongEdgeOrderingStrategy := dummyNodeOver dummyNodeUnder equal

namespace LongEdgeOrderingStrategy

/-- `LongEdgeOrderingStrategy.returnValue()`: the comparison result used when a long edge
dummy is compared with a regular node (`Integer.MAX_VALUE`, `Integer.MIN_VALUE` or `0`). -/
def returnValue : LongEdgeOrderingStrategy → Int
  | .dummyNodeOver => 2147483647
  | .dummyNodeUnder => -2147483648
  | .equal => 0

end LongEdgeOrderingStrategy

end Elk.Alg.Layered.Options
