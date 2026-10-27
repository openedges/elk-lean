import Elk.Core.Options.CoreOptions
/-!
# `org.eclipse.elk.core.options.BoxLayouterOptions`

Option constants of the box layouter. The metadata registration
(`ILayoutMetaDataProvider.apply`) is part of the metadata port
(`core_options_meta.rs`), not of this file.
-/
namespace Elk.Core.Options

open Elk Elk.Graph Elk.Core.Math

namespace BoxLayouterOptions

/-- `BoxLayouterOptions.ALGORITHM_ID`. -/
def ALGORITHM_ID : String := "org.eclipse.elk.box"

/-- `BoxLayouterOptions.PADDING`. -/
def PADDING : Property ElkPadding := CoreOptions.PADDING
/-- `BoxLayouterOptions.SPACING_NODE_NODE`. -/
def SPACING_NODE_NODE : Property Float := CoreOptions.SPACING_NODE_NODE
/-- `BoxLayouterOptions.PRIORITY`. -/
def PRIORITY : Property Int := CoreOptions.PRIORITY
/-- `BoxLayouterOptions.EXPAND_NODES`. -/
def EXPAND_NODES : Property Bool := CoreOptions.EXPAND_NODES
/-- `BoxLayouterOptions.INTERACTIVE`. -/
def INTERACTIVE : Property Bool := CoreOptions.INTERACTIVE
/-- `BoxLayouterOptions.NODE_SIZE_CONSTRAINTS`. -/
def NODE_SIZE_CONSTRAINTS : Property (EnumSet SizeConstraint) := CoreOptions.NODE_SIZE_CONSTRAINTS
/-- `BoxLayouterOptions.NODE_SIZE_OPTIONS`. -/
def NODE_SIZE_OPTIONS : Property (EnumSet SizeOptions) := CoreOptions.NODE_SIZE_OPTIONS
/-- `BoxLayouterOptions.ASPECT_RATIO`. -/
def ASPECT_RATIO : Property Float := CoreOptions.ASPECT_RATIO
/-- `BoxLayouterOptions.NODE_SIZE_MINIMUM`. -/
def NODE_SIZE_MINIMUM : Property KVector := CoreOptions.NODE_SIZE_MINIMUM
/-- `BoxLayouterOptions.BOX_PACKING_MODE`. -/
def BOX_PACKING_MODE : Property PackingMode := CoreOptions.BOX_PACKING_MODE

end BoxLayouterOptions

end Elk.Core.Options
