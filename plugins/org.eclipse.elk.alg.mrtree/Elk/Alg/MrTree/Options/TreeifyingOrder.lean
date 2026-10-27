import Elk.Graph.Enum
/-!
# `org.eclipse.elk.alg.mrtree.options.TreeifyingOrder`

Port of `options/treeifying_order.rs` (elk-rs) and `TreeifyingOrder.java` (same constants, same ordinal order).
-/
namespace Elk.Alg.MrTree.Options

/-- `org.eclipse.elk.alg.mrtree.options.TreeifyingOrder`: the search order used to compute the spanning tree of `P1_TREEIFICATION`. -/
elk_enum TreeifyingOrder := dfs bfs

end Elk.Alg.MrTree.Options
