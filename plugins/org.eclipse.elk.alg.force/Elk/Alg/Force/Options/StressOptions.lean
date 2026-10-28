import Elk.Graph
import Elk.Core.Options
import Elk.Alg.Force.Stress.Dimension
/-!
# `org.eclipse.elk.alg.force.options.StressOptions`

Port of `stress_options.rs` (elk-rs), the counterpart of the Java `StressOptions` generated from
`Stress.melk`. The re-exported core options are aliases of the `CoreOptions` constants.
-/
namespace Elk.Alg.Force.Options

open Elk Elk.Graph Elk.Core.Math Elk.Core.Options Elk.Alg.Force.Stress

namespace StressOptions

/-- `StressOptions.ALGORITHM_ID`. -/
def ALGORITHM_ID : String := "org.eclipse.elk.stress"

/-- `StressOptions.FIXED`: prevents a node from being moved (default `false`). -/
def FIXED : Property Bool := Property.withDefault "org.eclipse.elk.stress.fixed" false

/-- `StressOptions.DESIRED_EDGE_LENGTH` (default 100.0). -/
def DESIRED_EDGE_LENGTH : Property Float :=
  Property.withDefault "org.eclipse.elk.stress.desiredEdgeLength" 100.0

/-- `StressOptions.DIMENSION` (default `XY`). -/
def DIMENSION : Property Dimension :=
  Property.withDefault "org.eclipse.elk.stress.dimension" Dimension.xy

/-- `StressOptions.EPSILON` (default `10e-4`, i.e. 0.001). -/
def EPSILON : Property Float := Property.withDefault "org.eclipse.elk.stress.epsilon" 0.001

/-- `StressOptions.ITERATION_LIMIT` (default `Integer.MAX_VALUE`). -/
def ITERATION_LIMIT : Property Int :=
  Property.withDefault "org.eclipse.elk.stress.iterationLimit" 2147483647

/-- `StressOptions.INTERACTIVE`. -/
def INTERACTIVE : Property Bool := CoreOptions.INTERACTIVE
/-- `StressOptions.EDGE_LABELS_INLINE`: redeclared with the stress default `true` (no Java read site
uses it: the label placement of `FLabel` reads `ForceOptions.EDGE_LABELS_INLINE`, default `false`). -/
def EDGE_LABELS_INLINE : Property Bool := Property.ofProperty CoreOptions.EDGE_LABELS_INLINE true
/-- `StressOptions.OMIT_NODE_MICRO_LAYOUT`. -/
def OMIT_NODE_MICRO_LAYOUT : Property Bool := CoreOptions.OMIT_NODE_MICRO_LAYOUT
/-- `StressOptions.NODE_SIZE_CONSTRAINTS`. -/
def NODE_SIZE_CONSTRAINTS : Property (EnumSet SizeConstraint) := CoreOptions.NODE_SIZE_CONSTRAINTS
/-- `StressOptions.NODE_SIZE_MINIMUM`. -/
def NODE_SIZE_MINIMUM : Property KVector := CoreOptions.NODE_SIZE_MINIMUM
/-- `StressOptions.NODE_SIZE_OPTIONS`. -/
def NODE_SIZE_OPTIONS : Property (EnumSet SizeOptions) := CoreOptions.NODE_SIZE_OPTIONS
/-- `StressOptions.NODE_LABELS_PLACEMENT`. -/
def NODE_LABELS_PLACEMENT : Property (EnumSet NodeLabelPlacement) := CoreOptions.NODE_LABELS_PLACEMENT
/-- `StressOptions.PORT_LABELS_PLACEMENT`. -/
def PORT_LABELS_PLACEMENT : Property (EnumSet PortLabelPlacement) := CoreOptions.PORT_LABELS_PLACEMENT

end StressOptions

end Elk.Alg.Force.Options
