import Elk.Graph.Enum
/-!
# `org.eclipse.elk.alg.layered.options.CenterEdgeLabelPlacementStrategy`

Port of `options/center_edge_label_placement_strategy.rs` (elk-rs) and `CenterEdgeLabelPlacementStrategy.java`.
-/
namespace Elk.Alg.Layered.Options

/-- `org.eclipse.elk.alg.layered.options.CenterEdgeLabelPlacementStrategy`: Strategies regarding how
to place center edge labels. Implementation-wise, the placement strategy influences which layer a
center edge label dummy is moved into. -/
elk_enum CenterEdgeLabelPlacementStrategy := medianLayer tailLayer headLayer spaceEfficientLayer widestLayer centerLayer

namespace CenterEdgeLabelPlacementStrategy

/-- `CenterEdgeLabelPlacementStrategy.usesLabelSizeInformation()`: whether the strategy needs
the label sizes (`WIDEST_LAYER`, `CENTER_LAYER`, `SPACE_EFFICIENT_LAYER`). -/
def usesLabelSizeInformation : CenterEdgeLabelPlacementStrategy → Bool
  | .widestLayer | .centerLayer | .spaceEfficientLayer => true
  | _ => false

end CenterEdgeLabelPlacementStrategy

end Elk.Alg.Layered.Options
