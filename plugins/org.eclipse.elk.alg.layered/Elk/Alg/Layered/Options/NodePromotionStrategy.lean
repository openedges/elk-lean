import Elk.Graph.Enum
/-!
# `org.eclipse.elk.alg.layered.options.NodePromotionStrategy`

Port of `options/node_promotion_strategy.rs` (elk-rs) and `NodePromotionStrategy.java`.
-/
namespace Elk.Alg.Layered.Options

/-- `org.eclipse.elk.alg.layered.options.NodePromotionStrategy`: Definitions of strategies for the
node promotion heuristic. -/
elk_enum NodePromotionStrategy := none nikolov nikolovPixel nikolovImproved nikolovImprovedPixel dummynodePercentage nodecountPercentage noBoundary modelOrderLeftToRight modelOrderRightToLeft

end Elk.Alg.Layered.Options
