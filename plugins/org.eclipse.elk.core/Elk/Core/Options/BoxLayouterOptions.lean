import Elk.Core.Options.CoreOptions
import Elk.Core.Data.LayoutMetaDataService
/-!
# `org.eclipse.elk.core.options.BoxLayouterOptions`

Option constants of the box layouter and its `ILayoutMetaDataProvider`
(`metaDataProvider`), which re-registers the box packing mode option
(elk-rs `impl ILayoutMetaDataProvider for BoxLayouterOptions`).
-/
namespace Elk.Core.Options

open Elk Elk.Graph Elk.Core.Math Elk.Core.Data

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

/-- `BoxLayouterOptions.apply(registry)`: registers `BOX_PACKING_MODE` (enum, parents only,
default `SIMPLE`; name, description and group are intentionally empty like in elk-rs, where
this registration replaces the one of `CoreOptions`). -/
def metaDataProvider : LayoutMetaDataProvider where
  apply r :=
    r.registerOption
      { id := BOX_PACKING_MODE.id
        type := .enum
        targets := EnumSet.of #[.parents]
        defaultValue := BOX_PACKING_MODE.default.map PropCodec.enc
        choices := LayoutOptionData.enumChoices PackingMode
        parser := some (LayoutOptionData.enumParser PackingMode) }

end BoxLayouterOptions

end Elk.Core.Options
