import Elk.Core.Options.CoreOptions
/-!
# `org.eclipse.elk.core.options.RandomLayouterOptions`

Option constants of the random layouter.
-/
namespace Elk.Core.Options

open Elk Elk.Graph Elk.Core.Math

namespace RandomLayouterOptions

/-- `RandomLayouterOptions.ALGORITHM_ID`. -/
def ALGORITHM_ID : String := "org.eclipse.elk.random"

/-- `RandomLayouterOptions.PADDING`. -/
def PADDING : Property ElkPadding := CoreOptions.PADDING
/-- `RandomLayouterOptions.SPACING_NODE_NODE`. -/
def SPACING_NODE_NODE : Property Float := CoreOptions.SPACING_NODE_NODE
/-- `RandomLayouterOptions.RANDOM_SEED`. -/
def RANDOM_SEED : Property Int := CoreOptions.RANDOM_SEED
/-- `RandomLayouterOptions.ASPECT_RATIO`. -/
def ASPECT_RATIO : Property Float := CoreOptions.ASPECT_RATIO

end RandomLayouterOptions

end Elk.Core.Options
