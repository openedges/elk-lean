import Elk.Graph
/-!
# `org.eclipse.elk.alg.rectpacking.options.InternalProperties`

Port of `options/internal_properties.rs` (elk-rs). Rectangle packing has no graph structure of its
own: like Rust and Java it works on the `ElkGraph` directly and keeps its internal properties in
the property map of the laid-out parent node (`ElkNode.props`), under the Rust ids
(`"additionalHeight"`, ...). They are therefore ordinary `Property` constants here, not typed
fields.

`ROWS`: Rust stores a `usize` key (the address of the graph node) that indexes the thread-local
`rows_storage`; elk-lean stores the parent node's arena index (`NodeId.idx`) as an `Int`, the key
of `Elk.Alg.RectPacking.Util.RowsStorage`.
-/
namespace Elk.Alg.RectPacking.Options

open Elk.Graph

namespace InternalProperties

/-- `InternalProperties.ADDITIONAL_HEIGHT` (no default). -/
def ADDITIONAL_HEIGHT : Property Float := Property.mk' "additionalHeight"
/-- `InternalProperties.DRAWING_HEIGHT` (no default). -/
def DRAWING_HEIGHT : Property Float := Property.mk' "drawingHeight"
/-- `InternalProperties.DRAWING_WIDTH` (no default). -/
def DRAWING_WIDTH : Property Float := Property.mk' "drawingWidth"
/-- `InternalProperties.MIN_HEIGHT` (no default). -/
def MIN_HEIGHT : Property Float := Property.mk' "minHeight"
/-- `InternalProperties.MIN_WIDTH` (no default). -/
def MIN_WIDTH : Property Float := Property.mk' "minWidth"
/-- `InternalProperties.ROWS` (no default): the `RowsStorage` key (see the module doc). -/
def ROWS : Property Int := Property.mk' "rows"
/-- `InternalProperties.TARGET_WIDTH` (no default). -/
def TARGET_WIDTH : Property Float := Property.mk' "targetWidth"
/-- `InternalProperties.MIN_ROW_INCREASE` (default `0.0`). -/
def MIN_ROW_INCREASE : Property Float := Property.withDefault "minRowIncrease" 0.0
/-- `InternalProperties.MAX_ROW_INCREASE` (default `0.0`). -/
def MAX_ROW_INCREASE : Property Float := Property.withDefault "maxRowIncrease" 0.0
/-- `InternalProperties.MIN_ROW_DECREASE` (default `0.0`). -/
def MIN_ROW_DECREASE : Property Float := Property.withDefault "minRowDecrease" 0.0
/-- `InternalProperties.MAX_ROW_DECREASE` (default `0.0`). -/
def MAX_ROW_DECREASE : Property Float := Property.withDefault "maxRowDecrease" 0.0

end InternalProperties

end Elk.Alg.RectPacking.Options
