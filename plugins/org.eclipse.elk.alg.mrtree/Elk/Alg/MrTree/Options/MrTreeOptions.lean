import Elk.Graph
import Elk.Core.Options
import Elk.Alg.MrTree.Options.EdgeRoutingMode
import Elk.Alg.MrTree.Options.GraphProperties
import Elk.Alg.MrTree.Options.OrderWeighting
import Elk.Alg.MrTree.Options.TreeifyingOrder
/-!
# `org.eclipse.elk.alg.mrtree.options.MrTreeOptions`

Port of `options/mrtree_options.rs` (elk-rs), the counterpart of the Java `MrTreeOptions` generated
from `Tree.melk`. The eight mrtree options carry the Rust ids and defaults; the re-exported core
options are plain aliases of the `CoreOptions` constants (same id, same default). Java redeclares some
of them with algorithm specific defaults (for example `PADDING = 20`); elk-rs encodes those as option
supports of `MrTreeMetaDataProvider` instead.
-/
namespace Elk.Alg.MrTree.Options

open Elk Elk.Graph Elk.Core.Math Elk.Core.Util Elk.Core.Options

namespace MrTreeOptions

/-- `MrTreeOptions.ALGORITHM_ID`. -/
def ALGORITHM_ID : String := "org.eclipse.elk.mrtree"

/-- `MrTreeOptions.GRAPH_PROPERTIES` (default: empty set). -/
def GRAPH_PROPERTIES : Property (EnumSet GraphProperties) :=
  Property.withDefault "org.eclipse.elk.mrtree.graphProperties" EnumSet.empty

/-- `MrTreeOptions.COMPACTION` (default `false`). -/
def COMPACTION : Property Bool := Property.withDefault "org.eclipse.elk.mrtree.compaction" false

/-- `MrTreeOptions.EDGE_END_TEXTURE_LENGTH` (default 7.0). -/
def EDGE_END_TEXTURE_LENGTH : Property Float :=
  Property.withDefault "org.eclipse.elk.mrtree.edgeEndTextureLength" 7.0

/-- `MrTreeOptions.TREE_LEVEL` (default 0). -/
def TREE_LEVEL : Property Int := Property.withDefault "org.eclipse.elk.mrtree.treeLevel" 0

/-- `MrTreeOptions.POSITION_CONSTRAINT` (default -1). -/
def POSITION_CONSTRAINT : Property Int :=
  Property.withDefault "org.eclipse.elk.mrtree.positionConstraint" (-1)

/-- `MrTreeOptions.WEIGHTING` (default `MODEL_ORDER`). -/
def WEIGHTING : Property OrderWeighting :=
  Property.withDefault "org.eclipse.elk.mrtree.weighting" OrderWeighting.modelOrder

/-- `MrTreeOptions.EDGE_ROUTING_MODE` (default `AVOID_OVERLAP`). -/
def EDGE_ROUTING_MODE : Property EdgeRoutingMode :=
  Property.withDefault "org.eclipse.elk.mrtree.edgeRoutingMode" EdgeRoutingMode.avoidOverlap

/-- `MrTreeOptions.SEARCH_ORDER` (default `DFS`). -/
def SEARCH_ORDER : Property TreeifyingOrder :=
  Property.withDefault "org.eclipse.elk.mrtree.searchOrder" TreeifyingOrder.dfs

/-- `MrTreeOptions.PADDING`. -/
def PADDING : Property ElkPadding := CoreOptions.PADDING
/-- `MrTreeOptions.SPACING_NODE_NODE`. -/
def SPACING_NODE_NODE : Property Float := CoreOptions.SPACING_NODE_NODE
/-- `MrTreeOptions.SPACING_EDGE_NODE`. -/
def SPACING_EDGE_NODE : Property Float := CoreOptions.SPACING_EDGE_NODE
/-- `MrTreeOptions.SPACING_INDIVIDUAL`. -/
def SPACING_INDIVIDUAL : Property IndividualSpacings := CoreOptions.SPACING_INDIVIDUAL
/-- `MrTreeOptions.ASPECT_RATIO`. -/
def ASPECT_RATIO : Property Float := CoreOptions.ASPECT_RATIO
/-- `MrTreeOptions.PRIORITY`. -/
def PRIORITY : Property Int := CoreOptions.PRIORITY
/-- `MrTreeOptions.SEPARATE_CONNECTED_COMPONENTS`. -/
def SEPARATE_CONNECTED_COMPONENTS : Property Bool := CoreOptions.SEPARATE_CONNECTED_COMPONENTS
/-- `MrTreeOptions.DEBUG_MODE`. -/
def DEBUG_MODE : Property Bool := CoreOptions.DEBUG_MODE
/-- `MrTreeOptions.DIRECTION`. -/
def DIRECTION : Property Direction := CoreOptions.DIRECTION
/-- `MrTreeOptions.INTERACTIVE`. -/
def INTERACTIVE : Property Bool := CoreOptions.INTERACTIVE
/-- `MrTreeOptions.INTERACTIVE_LAYOUT`. -/
def INTERACTIVE_LAYOUT : Property Bool := CoreOptions.INTERACTIVE_LAYOUT
/-- `MrTreeOptions.NODE_SIZE_CONSTRAINTS`. -/
def NODE_SIZE_CONSTRAINTS : Property (EnumSet SizeConstraint) := CoreOptions.NODE_SIZE_CONSTRAINTS
/-- `MrTreeOptions.NODE_SIZE_FIXED_GRAPH_SIZE`. -/
def NODE_SIZE_FIXED_GRAPH_SIZE : Property Bool := CoreOptions.NODE_SIZE_FIXED_GRAPH_SIZE
/-- `MrTreeOptions.NODE_SIZE_MINIMUM`. -/
def NODE_SIZE_MINIMUM : Property KVector := CoreOptions.NODE_SIZE_MINIMUM
/-- `MrTreeOptions.NODE_SIZE_OPTIONS`. -/
def NODE_SIZE_OPTIONS : Property (EnumSet SizeOptions) := CoreOptions.NODE_SIZE_OPTIONS
/-- `MrTreeOptions.NODE_LABELS_PLACEMENT`. -/
def NODE_LABELS_PLACEMENT : Property (EnumSet NodeLabelPlacement) := CoreOptions.NODE_LABELS_PLACEMENT
/-- `MrTreeOptions.PORT_LABELS_PLACEMENT`. -/
def PORT_LABELS_PLACEMENT : Property (EnumSet PortLabelPlacement) := CoreOptions.PORT_LABELS_PLACEMENT
/-- `MrTreeOptions.OMIT_NODE_MICRO_LAYOUT`. -/
def OMIT_NODE_MICRO_LAYOUT : Property Bool := CoreOptions.OMIT_NODE_MICRO_LAYOUT
/-- `MrTreeOptions.TOPDOWN_LAYOUT`. -/
def TOPDOWN_LAYOUT : Property Bool := CoreOptions.TOPDOWN_LAYOUT
/-- `MrTreeOptions.TOPDOWN_SCALE_FACTOR`. -/
def TOPDOWN_SCALE_FACTOR : Property Float := CoreOptions.TOPDOWN_SCALE_FACTOR
/-- `MrTreeOptions.TOPDOWN_HIERARCHICAL_NODE_WIDTH`. -/
def TOPDOWN_HIERARCHICAL_NODE_WIDTH : Property Float := CoreOptions.TOPDOWN_HIERARCHICAL_NODE_WIDTH
/-- `MrTreeOptions.TOPDOWN_HIERARCHICAL_NODE_ASPECT_RATIO`. -/
def TOPDOWN_HIERARCHICAL_NODE_ASPECT_RATIO : Property Float :=
  CoreOptions.TOPDOWN_HIERARCHICAL_NODE_ASPECT_RATIO
/-- `MrTreeOptions.TOPDOWN_NODE_TYPE`. -/
def TOPDOWN_NODE_TYPE : Property TopdownNodeTypes := CoreOptions.TOPDOWN_NODE_TYPE

end MrTreeOptions

end Elk.Alg.MrTree.Options
