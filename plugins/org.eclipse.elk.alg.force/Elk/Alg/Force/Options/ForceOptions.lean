import Elk.Graph
import Elk.Core.Options
import Elk.Alg.Force.Options.ForceModelStrategy
/-!
# `org.eclipse.elk.alg.force.options.ForceOptions`

Port of `force_options.rs` (elk-rs), the counterpart of the Java `ForceOptions` generated from
`Force.melk`. The re-exported core options are plain aliases of the `CoreOptions` constants (same id,
same default); Java redeclares some of them with force specific defaults (for example
`SPACING_NODE_NODE = 80`), elk-rs encodes those as algorithm specific defaults in
`ForceMetaDataProvider` instead and the models fall back to their literals only when the property has
no default.
-/
namespace Elk.Alg.Force.Options

open Elk Elk.Graph Elk.Core.Math Elk.Core.Options

namespace ForceOptions

/-- `ForceOptions.ALGORITHM_ID`. -/
def ALGORITHM_ID : String := "org.eclipse.elk.force"

/-- `ForceOptions.MODEL`: the force model (default `FRUCHTERMAN_REINGOLD`). -/
def MODEL : Property ForceModelStrategy :=
  Property.withDefault "org.eclipse.elk.force.model" ForceModelStrategy.fruchtermanReingold

/-- `ForceOptions.ITERATIONS` (default 300). -/
def ITERATIONS : Property Int := Property.withDefault "org.eclipse.elk.force.iterations" 300

/-- `ForceOptions.REPULSIVE_POWER`: number of bend points added to an edge (default 0). -/
def REPULSIVE_POWER : Property Int := Property.withDefault "org.eclipse.elk.force.repulsivePower" 0

/-- `ForceOptions.TEMPERATURE` (default 0.001). -/
def TEMPERATURE : Property Float := Property.withDefault "org.eclipse.elk.force.temperature" 0.001

/-- `ForceOptions.REPULSION`: repulsion factor of Eades' model (default 5.0). -/
def REPULSION : Property Float := Property.withDefault "org.eclipse.elk.force.repulsion" 5.0

/-- `ForceOptions.PRIORITY`. -/
def PRIORITY : Property Int := CoreOptions.PRIORITY
/-- `ForceOptions.SPACING_NODE_NODE`. -/
def SPACING_NODE_NODE : Property Float := CoreOptions.SPACING_NODE_NODE
/-- `ForceOptions.SPACING_EDGE_LABEL`. -/
def SPACING_EDGE_LABEL : Property Float := CoreOptions.SPACING_EDGE_LABEL
/-- `ForceOptions.ASPECT_RATIO`. -/
def ASPECT_RATIO : Property Float := CoreOptions.ASPECT_RATIO
/-- `ForceOptions.RANDOM_SEED`. -/
def RANDOM_SEED : Property Int := CoreOptions.RANDOM_SEED
/-- `ForceOptions.SEPARATE_CONNECTED_COMPONENTS`. -/
def SEPARATE_CONNECTED_COMPONENTS : Property Bool := CoreOptions.SEPARATE_CONNECTED_COMPONENTS
/-- `ForceOptions.PADDING`. -/
def PADDING : Property ElkPadding := CoreOptions.PADDING
/-- `ForceOptions.INTERACTIVE`. -/
def INTERACTIVE : Property Bool := CoreOptions.INTERACTIVE
/-- `ForceOptions.PORT_CONSTRAINTS`. -/
def PORT_CONSTRAINTS : Property PortConstraints := CoreOptions.PORT_CONSTRAINTS
/-- `ForceOptions.EDGE_LABELS_INLINE`. -/
def EDGE_LABELS_INLINE : Property Bool := CoreOptions.EDGE_LABELS_INLINE
/-- `ForceOptions.OMIT_NODE_MICRO_LAYOUT`. -/
def OMIT_NODE_MICRO_LAYOUT : Property Bool := CoreOptions.OMIT_NODE_MICRO_LAYOUT
/-- `ForceOptions.NODE_SIZE_FIXED_GRAPH_SIZE`. -/
def NODE_SIZE_FIXED_GRAPH_SIZE : Property Bool := CoreOptions.NODE_SIZE_FIXED_GRAPH_SIZE
/-- `ForceOptions.NODE_SIZE_OPTIONS`. -/
def NODE_SIZE_OPTIONS : Property (EnumSet SizeOptions) := CoreOptions.NODE_SIZE_OPTIONS
/-- `ForceOptions.NODE_SIZE_CONSTRAINTS`. -/
def NODE_SIZE_CONSTRAINTS : Property (EnumSet SizeConstraint) := CoreOptions.NODE_SIZE_CONSTRAINTS
/-- `ForceOptions.NODE_LABELS_PLACEMENT`. -/
def NODE_LABELS_PLACEMENT : Property (EnumSet NodeLabelPlacement) := CoreOptions.NODE_LABELS_PLACEMENT
/-- `ForceOptions.PORT_LABELS_PLACEMENT`. -/
def PORT_LABELS_PLACEMENT : Property (EnumSet PortLabelPlacement) := CoreOptions.PORT_LABELS_PLACEMENT
/-- `ForceOptions.TOPDOWN_LAYOUT`. -/
def TOPDOWN_LAYOUT : Property Bool := CoreOptions.TOPDOWN_LAYOUT
/-- `ForceOptions.TOPDOWN_SCALE_FACTOR`. -/
def TOPDOWN_SCALE_FACTOR : Property Float := CoreOptions.TOPDOWN_SCALE_FACTOR
/-- `ForceOptions.TOPDOWN_HIERARCHICAL_NODE_WIDTH`. -/
def TOPDOWN_HIERARCHICAL_NODE_WIDTH : Property Float := CoreOptions.TOPDOWN_HIERARCHICAL_NODE_WIDTH
/-- `ForceOptions.TOPDOWN_HIERARCHICAL_NODE_ASPECT_RATIO`. -/
def TOPDOWN_HIERARCHICAL_NODE_ASPECT_RATIO : Property Float :=
  CoreOptions.TOPDOWN_HIERARCHICAL_NODE_ASPECT_RATIO
/-- `ForceOptions.TOPDOWN_NODE_TYPE`. -/
def TOPDOWN_NODE_TYPE : Property TopdownNodeTypes := CoreOptions.TOPDOWN_NODE_TYPE
/-- `ForceOptions.NODE_SIZE_MINIMUM`. -/
def NODE_SIZE_MINIMUM : Property KVector := CoreOptions.NODE_SIZE_MINIMUM

end ForceOptions

end Elk.Alg.Force.Options
