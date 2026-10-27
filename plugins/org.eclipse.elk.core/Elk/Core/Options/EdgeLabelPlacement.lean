import Elk.Graph.Enum
/-!
# `org.eclipse.elk.core.options.EdgeLabelPlacement`
-/
namespace Elk.Core.Options

/-- `org.eclipse.elk.core.options.EdgeLabelPlacement`. -/
elk_enum EdgeLabelPlacement := center head tail

namespace EdgeLabelPlacement

/-- `EdgeLabelPlacement.isEndLabelPlacement()`. -/
def isEndLabelPlacement : EdgeLabelPlacement → Bool
  | .head | .tail => true
  | .center => false

end EdgeLabelPlacement

end Elk.Core.Options
