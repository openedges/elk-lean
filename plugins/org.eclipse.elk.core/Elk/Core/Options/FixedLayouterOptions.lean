import Elk.Core.Options.CoreOptions
/-!
# `org.eclipse.elk.core.options.FixedLayouterOptions`

Option constants of the fixed layouter.
-/
namespace Elk.Core.Options

open Elk Elk.Graph Elk.Core.Math

namespace FixedLayouterOptions

/-- `FixedLayouterOptions.ALGORITHM_ID`. -/
def ALGORITHM_ID : String := "org.eclipse.elk.fixed"

/-- `FixedLayouterOptions.POSITION`. -/
def POSITION : Property KVector := CoreOptions.POSITION
/-- `FixedLayouterOptions.BEND_POINTS`. -/
def BEND_POINTS : Property KVectorChain := CoreOptions.BEND_POINTS
/-- `FixedLayouterOptions.NODE_SIZE_CONSTRAINTS`. -/
def NODE_SIZE_CONSTRAINTS : Property (EnumSet SizeConstraint) := CoreOptions.NODE_SIZE_CONSTRAINTS
/-- `FixedLayouterOptions.NODE_SIZE_MINIMUM`. -/
def NODE_SIZE_MINIMUM : Property KVector := CoreOptions.NODE_SIZE_MINIMUM
/-- `FixedLayouterOptions.NODE_SIZE_FIXED_GRAPH_SIZE`. -/
def NODE_SIZE_FIXED_GRAPH_SIZE : Property Bool := CoreOptions.NODE_SIZE_FIXED_GRAPH_SIZE
/-- `FixedLayouterOptions.PADDING`. -/
def PADDING : Property ElkPadding := CoreOptions.PADDING

end FixedLayouterOptions

end Elk.Core.Options
