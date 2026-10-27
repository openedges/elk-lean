import Elk.Core.Options
import Elk.Alg.Radial.Options.AnnulusWedgeCriteria
import Elk.Alg.Radial.Options.CompactionStrategy
import Elk.Alg.Radial.Options.RadialTranslationStrategy
import Elk.Alg.Radial.Options.SortingStrategy
/-!
# `org.eclipse.elk.alg.radial.options.RadialOptions`

Port of `radial_options.rs` (elk-rs): the option constants of the radial algorithm (ids and
defaults of the Java `RadialOptions`). The core options it re-exports are aliases of the
`CoreOptions` constants.
-/
namespace Elk.Alg.Radial.Options

open Elk Elk.Graph Elk.Core.Math Elk.Core.Options

namespace RadialOptions

/-- `RadialOptions.ALGORITHM_ID`. -/
def ALGORITHM_ID : String := "org.eclipse.elk.radial"

/-- `RadialOptions.CENTER_ON_ROOT`. -/
def CENTER_ON_ROOT : Property Bool :=
  Property.withDefault "org.eclipse.elk.radial.centerOnRoot" false
/-- `RadialOptions.ORDER_ID` (`i32`). -/
def ORDER_ID : Property Int :=
  Property.withDefault "org.eclipse.elk.radial.orderId" 0
/-- `RadialOptions.RADIUS`. -/
def RADIUS : Property Float :=
  Property.withDefault "org.eclipse.elk.radial.radius" 0.0
/-- `RadialOptions.ROTATE`. -/
def ROTATE : Property Bool :=
  Property.withDefault "org.eclipse.elk.radial.rotate" false
/-- `RadialOptions.ROTATION_TARGET_ANGLE`. -/
def ROTATION_TARGET_ANGLE : Property Float :=
  Property.withDefault "org.eclipse.elk.radial.rotation.targetAngle" 0.0
/-- `RadialOptions.ROTATION_COMPUTE_ADDITIONAL_WEDGE_SPACE`. -/
def ROTATION_COMPUTE_ADDITIONAL_WEDGE_SPACE : Property Bool :=
  Property.withDefault "org.eclipse.elk.radial.rotation.computeAdditionalWedgeSpace" false
/-- `RadialOptions.ROTATION_OUTGOING_EDGE_ANGLES`. -/
def ROTATION_OUTGOING_EDGE_ANGLES : Property Bool :=
  Property.withDefault "org.eclipse.elk.radial.rotation.outgoingEdgeAngles" false
/-- `RadialOptions.COMPACTOR`. -/
def COMPACTOR : Property CompactionStrategy :=
  Property.withDefault "org.eclipse.elk.radial.compactor" CompactionStrategy.none
/-- `RadialOptions.COMPACTION_STEP_SIZE` (`i32`). -/
def COMPACTION_STEP_SIZE : Property Int :=
  Property.withDefault "org.eclipse.elk.radial.compactionStepSize" 1
/-- `RadialOptions.SORTER`. -/
def SORTER : Property SortingStrategy :=
  Property.withDefault "org.eclipse.elk.radial.sorter" SortingStrategy.none
/-- `RadialOptions.WEDGE_CRITERIA`. -/
def WEDGE_CRITERIA : Property AnnulusWedgeCriteria :=
  Property.withDefault "org.eclipse.elk.radial.wedgeCriteria" AnnulusWedgeCriteria.nodeSize
/-- `RadialOptions.OPTIMIZATION_CRITERIA`. -/
def OPTIMIZATION_CRITERIA : Property RadialTranslationStrategy :=
  Property.withDefault "org.eclipse.elk.radial.optimizationCriteria" RadialTranslationStrategy.none

/-- `RadialOptions.POSITION` (alias of `CoreOptions.POSITION`). -/
def POSITION : Property KVector := CoreOptions.POSITION
/-- `RadialOptions.SPACING_NODE_NODE`. -/
def SPACING_NODE_NODE : Property Float := CoreOptions.SPACING_NODE_NODE
/-- `RadialOptions.NODE_SIZE_CONSTRAINTS`. -/
def NODE_SIZE_CONSTRAINTS : Property (EnumSet SizeConstraint) := CoreOptions.NODE_SIZE_CONSTRAINTS
/-- `RadialOptions.NODE_SIZE_MINIMUM`. -/
def NODE_SIZE_MINIMUM : Property KVector := CoreOptions.NODE_SIZE_MINIMUM
/-- `RadialOptions.NODE_SIZE_OPTIONS`. -/
def NODE_SIZE_OPTIONS : Property (EnumSet SizeOptions) := CoreOptions.NODE_SIZE_OPTIONS
/-- `RadialOptions.NODE_LABELS_PLACEMENT`. -/
def NODE_LABELS_PLACEMENT : Property (EnumSet NodeLabelPlacement) := CoreOptions.NODE_LABELS_PLACEMENT
/-- `RadialOptions.OMIT_NODE_MICRO_LAYOUT`. -/
def OMIT_NODE_MICRO_LAYOUT : Property Bool := CoreOptions.OMIT_NODE_MICRO_LAYOUT
/-- `RadialOptions.PORT_LABELS_PLACEMENT`. -/
def PORT_LABELS_PLACEMENT : Property (EnumSet PortLabelPlacement) := CoreOptions.PORT_LABELS_PLACEMENT
/-- `RadialOptions.NODE_SIZE_FIXED_GRAPH_SIZE`. -/
def NODE_SIZE_FIXED_GRAPH_SIZE : Property Bool := CoreOptions.NODE_SIZE_FIXED_GRAPH_SIZE
/-- `RadialOptions.PADDING`. -/
def PADDING : Property ElkPadding := CoreOptions.PADDING
/-- `RadialOptions.MARGINS`. -/
def MARGINS : Property ElkMargin := CoreOptions.MARGINS
/-- `RadialOptions.CHILD_AREA_WIDTH`. -/
def CHILD_AREA_WIDTH : Property Float := CoreOptions.CHILD_AREA_WIDTH
/-- `RadialOptions.CHILD_AREA_HEIGHT`. -/
def CHILD_AREA_HEIGHT : Property Float := CoreOptions.CHILD_AREA_HEIGHT

end RadialOptions

end Elk.Alg.Radial.Options
