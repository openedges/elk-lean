import Elk.Graph.Enum
/-!
# `org.eclipse.elk.core.options.PortConstraints`
-/
namespace Elk.Core.Options

/-- `org.eclipse.elk.core.options.PortConstraints`. -/
elk_enum PortConstraints := undefined free fixedSide fixedOrder fixedRatio fixedPos

namespace PortConstraints

/-- `PortConstraints.isPosFixed()`. -/
def isPosFixed (c : PortConstraints) : Bool := c == .fixedPos

/-- `PortConstraints.isRatioFixed()`. -/
def isRatioFixed (c : PortConstraints) : Bool := c == .fixedRatio

/-- `PortConstraints.isOrderFixed()`. -/
def isOrderFixed : PortConstraints → Bool
  | .fixedOrder | .fixedRatio | .fixedPos => true
  | _ => false

/-- `PortConstraints.isSideFixed()`. -/
def isSideFixed : PortConstraints → Bool
  | .free | .undefined => false
  | _ => true

end PortConstraints

end Elk.Core.Options
