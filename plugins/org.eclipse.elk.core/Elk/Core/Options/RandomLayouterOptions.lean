import Elk.Core.Options.CoreOptions
/-!
# `org.eclipse.elk.core.options.RandomLayouterOptions`

Option constants of the random layouter. Java redeclares the four supported core options with the
random layouter's defaults (`new Property<>(CoreOptions.X, X_DEFAULT)`: padding 15, node spacing 15,
random seed 0, aspect ratio `1.6f`); elk-rs aliases them to `CoreOptions` (followed before agent OPT).
-/
namespace Elk.Core.Options

open Elk Elk.Graph Elk.Core.Math Elk.Core.Util

namespace RandomLayouterOptions

/-- `RandomLayouterOptions.ALGORITHM_ID`. -/
def ALGORITHM_ID : String := "org.eclipse.elk.random"

/-- `RandomLayouterOptions.PADDING` (random layouter default `15` on every side). -/
def PADDING : Property ElkPadding := Property.ofProperty CoreOptions.PADDING (ElkPadding.ofAny 15.0)
/-- `RandomLayouterOptions.SPACING_NODE_NODE` (random layouter default `15`). -/
def SPACING_NODE_NODE : Property Float := Property.ofProperty CoreOptions.SPACING_NODE_NODE 15.0
/-- `RandomLayouterOptions.RANDOM_SEED` (random layouter default `0`: a time based seed). -/
def RANDOM_SEED : Property Int := Property.ofProperty CoreOptions.RANDOM_SEED 0
/-- `RandomLayouterOptions.ASPECT_RATIO` (random layouter default `1.6f`). -/
def ASPECT_RATIO : Property Float := Property.ofProperty CoreOptions.ASPECT_RATIO (Float.toF32 1.6)

end RandomLayouterOptions

end Elk.Core.Options
