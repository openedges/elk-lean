import Elk.Core.Options
import Elk.Alg.RectPacking.Options.OptimizationGoal
import Elk.Alg.RectPacking.P1WidthApproximation.WidthApproximationStrategy
import Elk.Alg.RectPacking.P2Packing.PackingStrategy
import Elk.Alg.RectPacking.P3WhitespaceElimination.WhiteSpaceEliminationStrategy
/-!
# `org.eclipse.elk.alg.rectpacking.options.RectPackingOptions`

Port of `options/rect_packing_options.rs` (elk-rs), the counterpart of the Java class generated
from `RectPacking.melk`: the option constants of the rectangle packing algorithm (ids and defaults
as in Rust). The core options it re-exports are aliases of the `CoreOptions` constants (so
`ASPECT_RATIO` has no property default, like `CoreOptions.ASPECT_RATIO`).
-/
namespace Elk.Alg.RectPacking.Options

open Elk Elk.Graph Elk.Core.Math Elk.Core.Options
open Elk.Alg.RectPacking.P1WidthApproximation Elk.Alg.RectPacking.P2Packing
open Elk.Alg.RectPacking.P3WhitespaceElimination

namespace RectPackingOptions

/-- `RectPackingOptions.ALGORITHM_ID`. -/
def ALGORITHM_ID : String := "org.eclipse.elk.rectpacking"

/-- `RectPackingOptions.WIDTH_APPROXIMATION_STRATEGY` (default `GREEDY`). -/
def WIDTH_APPROXIMATION_STRATEGY : Property WidthApproximationStrategy :=
  Property.withDefault "org.eclipse.elk.rectpacking.widthApproximation.strategy" .greedy

/-- `RectPackingOptions.WIDTH_APPROXIMATION_TARGET_WIDTH` (default `-1.0`). -/
def WIDTH_APPROXIMATION_TARGET_WIDTH : Property Float :=
  Property.withDefault "org.eclipse.elk.rectpacking.widthApproximation.targetWidth" (-1.0)

/-- `RectPackingOptions.WIDTH_APPROXIMATION_OPTIMIZATION_GOAL` (default `MAX_SCALE_DRIVEN`). -/
def WIDTH_APPROXIMATION_OPTIMIZATION_GOAL : Property OptimizationGoal :=
  Property.withDefault "org.eclipse.elk.rectpacking.widthApproximation.optimizationGoal" .maxScaleDriven

/-- `RectPackingOptions.WIDTH_APPROXIMATION_LAST_PLACE_SHIFT` (default `true`). -/
def WIDTH_APPROXIMATION_LAST_PLACE_SHIFT : Property Bool :=
  Property.withDefault "org.eclipse.elk.rectpacking.widthApproximation.lastPlaceShift" true

/-- `RectPackingOptions.PACKING_STRATEGY` (default `COMPACTION`). -/
def PACKING_STRATEGY : Property PackingStrategy :=
  Property.withDefault "org.eclipse.elk.rectpacking.packing.strategy" .compaction

/-- `RectPackingOptions.PACKING_COMPACTION_ROW_HEIGHT_REEVALUATION` (default `false`). -/
def PACKING_COMPACTION_ROW_HEIGHT_REEVALUATION : Property Bool :=
  Property.withDefault "org.eclipse.elk.rectpacking.packing.compaction.rowHeightReevaluation" false

/-- `RectPackingOptions.PACKING_COMPACTION_ITERATIONS` (default `1`, Rust `i32`). -/
def PACKING_COMPACTION_ITERATIONS : Property Int :=
  Property.withDefault "org.eclipse.elk.rectpacking.packing.compaction.iterations" 1

/-- `RectPackingOptions.WHITE_SPACE_ELIMINATION_STRATEGY` (default `NONE`). -/
def WHITE_SPACE_ELIMINATION_STRATEGY : Property WhiteSpaceEliminationStrategy :=
  Property.withDefault "org.eclipse.elk.rectpacking.whiteSpaceElimination.strategy" .none

/-- `RectPackingOptions.TRYBOX` (default `false`). -/
def TRYBOX : Property Bool :=
  Property.withDefault "org.eclipse.elk.rectpacking.trybox" false

/-- `RectPackingOptions.CURRENT_POSITION` (default `-1`, Rust `i32`). -/
def CURRENT_POSITION : Property Int :=
  Property.withDefault "org.eclipse.elk.rectpacking.currentPosition" (-1)

/-- `RectPackingOptions.DESIRED_POSITION` (default `-1`, Rust `i32`). -/
def DESIRED_POSITION : Property Int :=
  Property.withDefault "org.eclipse.elk.rectpacking.desiredPosition" (-1)

/-- `RectPackingOptions.IN_NEW_ROW` (default `false`). -/
def IN_NEW_ROW : Property Bool :=
  Property.withDefault "org.eclipse.elk.rectpacking.inNewRow" false

/-- `RectPackingOptions.ORDER_BY_SIZE` (default `false`). -/
def ORDER_BY_SIZE : Property Bool :=
  Property.withDefault "org.eclipse.elk.rectpacking.orderBySize" false

/-- `RectPackingOptions.PADDING` (`CoreOptions.PADDING`). -/
def PADDING : Property ElkPadding := CoreOptions.PADDING
/-- `RectPackingOptions.SPACING_NODE_NODE` (`CoreOptions.SPACING_NODE_NODE`). -/
def SPACING_NODE_NODE : Property Float := CoreOptions.SPACING_NODE_NODE
/-- `RectPackingOptions.ASPECT_RATIO` (`CoreOptions.ASPECT_RATIO`, no property default). -/
def ASPECT_RATIO : Property Float := CoreOptions.ASPECT_RATIO
/-- `RectPackingOptions.CONTENT_ALIGNMENT` (`CoreOptions.CONTENT_ALIGNMENT`). -/
def CONTENT_ALIGNMENT : Property (EnumSet ContentAlignment) := CoreOptions.CONTENT_ALIGNMENT
/-- `RectPackingOptions.NODE_SIZE_CONSTRAINTS` (`CoreOptions.NODE_SIZE_CONSTRAINTS`). -/
def NODE_SIZE_CONSTRAINTS : Property (EnumSet SizeConstraint) := CoreOptions.NODE_SIZE_CONSTRAINTS
/-- `RectPackingOptions.NODE_SIZE_MINIMUM` (`CoreOptions.NODE_SIZE_MINIMUM`). -/
def NODE_SIZE_MINIMUM : Property KVector := CoreOptions.NODE_SIZE_MINIMUM
/-- `RectPackingOptions.NODE_SIZE_OPTIONS` (`CoreOptions.NODE_SIZE_OPTIONS`). -/
def NODE_SIZE_OPTIONS : Property (EnumSet SizeOptions) := CoreOptions.NODE_SIZE_OPTIONS
/-- `RectPackingOptions.NODE_LABELS_PLACEMENT` (`CoreOptions.NODE_LABELS_PLACEMENT`). -/
def NODE_LABELS_PLACEMENT : Property (EnumSet NodeLabelPlacement) := CoreOptions.NODE_LABELS_PLACEMENT
/-- `RectPackingOptions.OMIT_NODE_MICRO_LAYOUT` (`CoreOptions.OMIT_NODE_MICRO_LAYOUT`). -/
def OMIT_NODE_MICRO_LAYOUT : Property Bool := CoreOptions.OMIT_NODE_MICRO_LAYOUT
/-- `RectPackingOptions.PORT_LABELS_PLACEMENT` (`CoreOptions.PORT_LABELS_PLACEMENT`). -/
def PORT_LABELS_PLACEMENT : Property (EnumSet PortLabelPlacement) := CoreOptions.PORT_LABELS_PLACEMENT
/-- `RectPackingOptions.NODE_SIZE_FIXED_GRAPH_SIZE` (`CoreOptions.NODE_SIZE_FIXED_GRAPH_SIZE`). -/
def NODE_SIZE_FIXED_GRAPH_SIZE : Property Bool := CoreOptions.NODE_SIZE_FIXED_GRAPH_SIZE
/-- `RectPackingOptions.INTERACTIVE` (`CoreOptions.INTERACTIVE`). -/
def INTERACTIVE : Property Bool := CoreOptions.INTERACTIVE
/-- `RectPackingOptions.INTERACTIVE_LAYOUT` (`CoreOptions.INTERACTIVE_LAYOUT`). -/
def INTERACTIVE_LAYOUT : Property Bool := CoreOptions.INTERACTIVE_LAYOUT

end RectPackingOptions

end Elk.Alg.RectPacking.Options
