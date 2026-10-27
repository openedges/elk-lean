import Elk.Graph.Properties
/-!
# `org.eclipse.elk.core.options.LabelSide`
-/
namespace Elk.Core.Options

open Elk.Graph

/-- `org.eclipse.elk.core.options.LabelSide`. -/
elk_enum LabelSide := unknown above below inline

namespace LabelSide

/-- `LabelSide.LABEL_SIDE`: `org.eclipse.elk.labelSide`, default `UNKNOWN`. -/
def LABEL_SIDE : Property LabelSide := Property.withDefault "org.eclipse.elk.labelSide" .unknown

/-- `LabelSide.opposite()`. -/
def opposite : LabelSide → LabelSide
  | .above => .below
  | .below => .above
  | .inline => .inline
  | .unknown => .unknown

end LabelSide

end Elk.Core.Options
