import Elk.Graph.Enum
/-!
# `org.eclipse.elk.alg.mrtree.options.OrderWeighting`

Port of `options/order_weighting.rs` (elk-rs) and `OrderWeighting.java` (same constants, same ordinal order).
-/
namespace Elk.Alg.MrTree.Options

/-- `org.eclipse.elk.alg.mrtree.options.OrderWeighting`: the weighting used to compute the node order of `P2_NODE_ORDERING`. -/
elk_enum OrderWeighting := modelOrder descendants fan constraint

end Elk.Alg.MrTree.Options
