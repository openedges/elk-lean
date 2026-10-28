import Elk.Graph
import Elk.Core.Options
import Elk.Alg.Force.Options.ForceModelStrategy
/-!
# `org.eclipse.elk.alg.force.options.ForceOptions`

The counterpart of the Java `ForceOptions` generated from `Force.melk`. A `supports <option>` without
a value re-exports the `CoreOptions` constant; a `supports <option> = <value>` makes the generator
redeclare the constant as `new Property<>(CoreOptions.X, X_DEFAULT)` (same id, the algorithm's
default), so every `getProperty(ForceOptions.X)` of an unset option yields the force default while
`getProperty(CoreOptions.X)` of the same element still yields the core default. The redeclared
constants here are `Property.ofProperty` copies with the Java values (`1.6f` widened to double for
the aspect ratio). elk-rs aliases all of them to `CoreOptions` (core defaults: padding 12, node
spacing 20, edge label spacing 2), which elk-lean followed before (agent OPT).
-/
namespace Elk.Alg.Force.Options

open Elk Elk.Graph Elk.Core.Math Elk.Core.Options Elk.Core.Util

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

/-- `ForceOptions.PRIORITY` (force default `1`). -/
def PRIORITY : Property Int := Property.ofProperty CoreOptions.PRIORITY 1
/-- `ForceOptions.SPACING_NODE_NODE` (force default `80`). -/
def SPACING_NODE_NODE : Property Float := Property.ofProperty CoreOptions.SPACING_NODE_NODE 80.0
/-- `ForceOptions.SPACING_EDGE_LABEL` (force default `5`). -/
def SPACING_EDGE_LABEL : Property Float := Property.ofProperty CoreOptions.SPACING_EDGE_LABEL 5.0
/-- `ForceOptions.ASPECT_RATIO` (force default `1.6f`). -/
def ASPECT_RATIO : Property Float := Property.ofProperty CoreOptions.ASPECT_RATIO (Float.toF32 1.6)
/-- `ForceOptions.RANDOM_SEED` (force default `1`). -/
def RANDOM_SEED : Property Int := Property.ofProperty CoreOptions.RANDOM_SEED 1
/-- `ForceOptions.SEPARATE_CONNECTED_COMPONENTS` (force default `true`). -/
def SEPARATE_CONNECTED_COMPONENTS : Property Bool :=
  Property.ofProperty CoreOptions.SEPARATE_CONNECTED_COMPONENTS true
/-- `ForceOptions.PADDING` (force default `50` on every side). -/
def PADDING : Property ElkPadding := Property.ofProperty CoreOptions.PADDING (ElkPadding.ofAny 50.0)
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
/-- `ForceOptions.TOPDOWN_NODE_TYPE` (force default `HIERARCHICAL_NODE`). -/
def TOPDOWN_NODE_TYPE : Property TopdownNodeTypes :=
  Property.ofProperty CoreOptions.TOPDOWN_NODE_TYPE TopdownNodeTypes.hierarchicalNode
/-- `ForceOptions.NODE_SIZE_MINIMUM`. -/
def NODE_SIZE_MINIMUM : Property KVector := CoreOptions.NODE_SIZE_MINIMUM

end ForceOptions

end Elk.Alg.Force.Options
