import Elk.Graph.Properties
import Elk.Core.Math.KVector
import Elk.Core.Math.KVectorChain
import Elk.Core.Math.Spacing
import Elk.Core.Util.IndividualSpacings
import Elk.Core.Options.Alignment
import Elk.Core.Options.ContentAlignment
import Elk.Core.Options.Direction
import Elk.Core.Options.EdgeCoords
import Elk.Core.Options.EdgeLabelPlacement
import Elk.Core.Options.EdgeRouting
import Elk.Core.Options.EdgeType
import Elk.Core.Options.HierarchyHandling
import Elk.Core.Options.NodeLabelPlacement
import Elk.Core.Options.PackingMode
import Elk.Core.Options.PortAlignment
import Elk.Core.Options.PortConstraints
import Elk.Core.Options.PortLabelPlacement
import Elk.Core.Options.PortSide
import Elk.Core.Options.ShapeCoords
import Elk.Core.Options.SizeConstraint
import Elk.Core.Options.SizeOptions
import Elk.Core.Options.TopdownNodeTypes
import Elk.Core.Options.TopdownSizeApproximator
/-!
# `org.eclipse.elk.core.options.CoreOptions`

The core layout options. Every `*_PROPERTY` static of the Rust port is a `def`
of the Java constant name inside `namespace CoreOptions`. Option ids and
defaults are taken from `core_options.rs`; bounds and option metadata
(`core_options_meta.rs`) are registered elsewhere.

Type mapping decisions:
* `LayoutAlgorithmData` (`RESOLVED_ALGORITHM`) is stored as the algorithm id (`String`).
* `ILabelManager` (`LABEL_MANAGER`) is `Dynamic`.
* `ITopdownSizeApproximator` (`TOPDOWN_SIZE_APPROXIMATOR`) is the `TopdownSizeApproximator` enum.
* `IndividualSpacings` (`SPACING_INDIVIDUAL`) is `Elk.Core.Util.IndividualSpacings`.
-/
namespace Elk.Core.Options

open Elk Elk.Graph Elk.Core.Math Elk.Core.Util

namespace CoreOptions

/-- `CoreOptions.ALGORITHM`. -/
def ALGORITHM : Property String :=
  Property.mk' "org.eclipse.elk.algorithm"

/-- `CoreOptions.RESOLVED_ALGORITHM`. -/
def RESOLVED_ALGORITHM : Property String :=
  Property.mk' "org.eclipse.elk.resolvedAlgorithm"

/-- `CoreOptions.ALIGNMENT`. -/
def ALIGNMENT : Property Alignment :=
  Property.withDefault "org.eclipse.elk.alignment" Alignment.automatic

/-- `CoreOptions.ASPECT_RATIO`. -/
def ASPECT_RATIO : Property Float :=
  Property.mk' "org.eclipse.elk.aspectRatio"

/-- `CoreOptions.BEND_POINTS`. -/
def BEND_POINTS : Property KVectorChain :=
  Property.mk' "org.eclipse.elk.bendPoints"

/-- `CoreOptions.CONTENT_ALIGNMENT`. -/
def CONTENT_ALIGNMENT : Property (EnumSet ContentAlignment) :=
  Property.withDefault "org.eclipse.elk.contentAlignment" ContentAlignment.topLeft

/-- `CoreOptions.DEBUG_MODE`. -/
def DEBUG_MODE : Property Bool :=
  Property.withDefault "org.eclipse.elk.debugMode" false

/-- `CoreOptions.DIRECTION`. -/
def DIRECTION : Property Direction :=
  Property.withDefault "org.eclipse.elk.direction" Direction.undefined

/-- `CoreOptions.EDGE_ROUTING`. -/
def EDGE_ROUTING : Property EdgeRouting :=
  Property.withDefault "org.eclipse.elk.edgeRouting" EdgeRouting.undefined

/-- `CoreOptions.EXPAND_NODES`. -/
def EXPAND_NODES : Property Bool :=
  Property.withDefault "org.eclipse.elk.expandNodes" false

/-- `CoreOptions.HIERARCHY_HANDLING`. -/
def HIERARCHY_HANDLING : Property HierarchyHandling :=
  Property.withDefault "org.eclipse.elk.hierarchyHandling" HierarchyHandling.inherit

/-- `CoreOptions.PADDING`. -/
def PADDING : Property ElkPadding :=
  Property.withDefault "org.eclipse.elk.padding" (ElkPadding.ofAny 12.0)

/-- `CoreOptions.INTERACTIVE`. -/
def INTERACTIVE : Property Bool :=
  Property.withDefault "org.eclipse.elk.interactive" false

/-- `CoreOptions.INTERACTIVE_LAYOUT`. -/
def INTERACTIVE_LAYOUT : Property Bool :=
  Property.withDefault "org.eclipse.elk.interactiveLayout" false

/-- `CoreOptions.OMIT_NODE_MICRO_LAYOUT`. -/
def OMIT_NODE_MICRO_LAYOUT : Property Bool :=
  Property.withDefault "org.eclipse.elk.omitNodeMicroLayout" false

/-- `CoreOptions.BOX_PACKING_MODE`. -/
def BOX_PACKING_MODE : Property PackingMode :=
  Property.withDefault "org.eclipse.elk.box.packingMode" PackingMode.simple

/-- `CoreOptions.JSON_SHAPE_COORDS`. -/
def JSON_SHAPE_COORDS : Property ShapeCoords :=
  Property.withDefault "org.eclipse.elk.json.shapeCoords" ShapeCoords.inherit

/-- `CoreOptions.JSON_EDGE_COORDS`. -/
def JSON_EDGE_COORDS : Property EdgeCoords :=
  Property.withDefault "org.eclipse.elk.json.edgeCoords" EdgeCoords.inherit

/-- `CoreOptions.SPACING_COMMENT_COMMENT`. -/
def SPACING_COMMENT_COMMENT : Property Float :=
  Property.withDefault "org.eclipse.elk.spacing.commentComment" 10.0

/-- `CoreOptions.SPACING_COMMENT_NODE`. -/
def SPACING_COMMENT_NODE : Property Float :=
  Property.withDefault "org.eclipse.elk.spacing.commentNode" 10.0

/-- `CoreOptions.SPACING_COMPONENT_COMPONENT`. -/
def SPACING_COMPONENT_COMPONENT : Property Float :=
  Property.withDefault "org.eclipse.elk.spacing.componentComponent" 20.0

/-- `CoreOptions.SPACING_EDGE_EDGE`. -/
def SPACING_EDGE_EDGE : Property Float :=
  Property.withDefault "org.eclipse.elk.spacing.edgeEdge" 10.0

/-- `CoreOptions.SPACING_EDGE_LABEL`. -/
def SPACING_EDGE_LABEL : Property Float :=
  Property.withDefault "org.eclipse.elk.spacing.edgeLabel" 2.0

/-- `CoreOptions.SPACING_EDGE_NODE`. -/
def SPACING_EDGE_NODE : Property Float :=
  Property.withDefault "org.eclipse.elk.spacing.edgeNode" 10.0

/-- `CoreOptions.SPACING_LABEL_LABEL`. -/
def SPACING_LABEL_LABEL : Property Float :=
  Property.withDefault "org.eclipse.elk.spacing.labelLabel" 0.0

/-- `CoreOptions.SPACING_LABEL_NODE`. -/
def SPACING_LABEL_NODE : Property Float :=
  Property.withDefault "org.eclipse.elk.spacing.labelNode" 5.0

/-- `CoreOptions.SPACING_LABEL_PORT_HORIZONTAL`. -/
def SPACING_LABEL_PORT_HORIZONTAL : Property Float :=
  Property.withDefault "org.eclipse.elk.spacing.labelPortHorizontal" 1.0

/-- `CoreOptions.SPACING_LABEL_PORT_VERTICAL`. -/
def SPACING_LABEL_PORT_VERTICAL : Property Float :=
  Property.withDefault "org.eclipse.elk.spacing.labelPortVertical" 1.0

/-- `CoreOptions.SPACING_NODE_NODE`. -/
def SPACING_NODE_NODE : Property Float :=
  Property.withDefault "org.eclipse.elk.spacing.nodeNode" 20.0

/-- `CoreOptions.SPACING_NODE_SELF_LOOP`. -/
def SPACING_NODE_SELF_LOOP : Property Float :=
  Property.withDefault "org.eclipse.elk.spacing.nodeSelfLoop" 10.0

/-- `CoreOptions.SPACING_PORT_PORT`. -/
def SPACING_PORT_PORT : Property Float :=
  Property.withDefault "org.eclipse.elk.spacing.portPort" 10.0

/-- `CoreOptions.SPACING_INDIVIDUAL`. -/
def SPACING_INDIVIDUAL : Property IndividualSpacings :=
  Property.mk' "org.eclipse.elk.spacing.individual"

/-- `CoreOptions.SPACING_PORTS_SURROUNDING`. -/
def SPACING_PORTS_SURROUNDING : Property ElkMargin :=
  Property.withDefault "org.eclipse.elk.spacing.portsSurrounding" (({} : ElkMargin))

/-- `CoreOptions.PARTITIONING_PARTITION`. -/
def PARTITIONING_PARTITION : Property Int :=
  Property.mk' "org.eclipse.elk.partitioning.partition"

/-- `CoreOptions.PARTITIONING_ACTIVATE`. -/
def PARTITIONING_ACTIVATE : Property Bool :=
  Property.withDefault "org.eclipse.elk.partitioning.activate" false

/-- `CoreOptions.NODE_LABELS_PADDING`. -/
def NODE_LABELS_PADDING : Property ElkPadding :=
  Property.withDefault "org.eclipse.elk.nodeLabels.padding" (ElkPadding.ofAny 5.0)

/-- `CoreOptions.NODE_LABELS_PLACEMENT`. -/
def NODE_LABELS_PLACEMENT : Property (EnumSet NodeLabelPlacement) :=
  Property.withDefault "org.eclipse.elk.nodeLabels.placement" NodeLabelPlacement.fixed

/-- `CoreOptions.PORT_ALIGNMENT_DEFAULT`. -/
def PORT_ALIGNMENT_DEFAULT : Property PortAlignment :=
  Property.withDefault "org.eclipse.elk.portAlignment.default" PortAlignment.distributed

/-- `CoreOptions.PORT_ALIGNMENT_NORTH`. -/
def PORT_ALIGNMENT_NORTH : Property PortAlignment :=
  Property.mk' "org.eclipse.elk.portAlignment.north"

/-- `CoreOptions.PORT_ALIGNMENT_SOUTH`. -/
def PORT_ALIGNMENT_SOUTH : Property PortAlignment :=
  Property.mk' "org.eclipse.elk.portAlignment.south"

/-- `CoreOptions.PORT_ALIGNMENT_WEST`. -/
def PORT_ALIGNMENT_WEST : Property PortAlignment :=
  Property.mk' "org.eclipse.elk.portAlignment.west"

/-- `CoreOptions.PORT_ALIGNMENT_EAST`. -/
def PORT_ALIGNMENT_EAST : Property PortAlignment :=
  Property.mk' "org.eclipse.elk.portAlignment.east"

/-- `CoreOptions.PORT_CONSTRAINTS`. -/
def PORT_CONSTRAINTS : Property PortConstraints :=
  Property.withDefault "org.eclipse.elk.portConstraints" PortConstraints.undefined

/-- `CoreOptions.POSITION`. -/
def POSITION : Property KVector :=
  Property.mk' "org.eclipse.elk.position"

/-- `CoreOptions.PRIORITY`. -/
def PRIORITY : Property Int :=
  Property.mk' "org.eclipse.elk.priority"

/-- `CoreOptions.RANDOM_SEED`. -/
def RANDOM_SEED : Property Int :=
  Property.mk' "org.eclipse.elk.randomSeed"

/-- `CoreOptions.SEPARATE_CONNECTED_COMPONENTS`. -/
def SEPARATE_CONNECTED_COMPONENTS : Property Bool :=
  Property.mk' "org.eclipse.elk.separateConnectedComponents"

/-- `CoreOptions.NODE_SIZE_CONSTRAINTS`. -/
def NODE_SIZE_CONSTRAINTS : Property (EnumSet SizeConstraint) :=
  Property.withDefault "org.eclipse.elk.nodeSize.constraints" EnumSet.noneOf

/-- `CoreOptions.NODE_SIZE_OPTIONS`. -/
def NODE_SIZE_OPTIONS : Property (EnumSet SizeOptions) :=
  Property.withDefault "org.eclipse.elk.nodeSize.options" (EnumSet.of #[SizeOptions.defaultMinimumSize])

/-- `CoreOptions.NODE_SIZE_MINIMUM`. -/
def NODE_SIZE_MINIMUM : Property KVector :=
  Property.withDefault "org.eclipse.elk.nodeSize.minimum" KVector.zero

/-- `CoreOptions.NODE_SIZE_FIXED_GRAPH_SIZE`. -/
def NODE_SIZE_FIXED_GRAPH_SIZE : Property Bool :=
  Property.withDefault "org.eclipse.elk.nodeSize.fixedGraphSize" false

/-- `CoreOptions.JUNCTION_POINTS`. -/
def JUNCTION_POINTS : Property KVectorChain :=
  Property.withDefault "org.eclipse.elk.junctionPoints" #[]

/-- `CoreOptions.COMMENT_BOX`. -/
def COMMENT_BOX : Property Bool :=
  Property.withDefault "org.eclipse.elk.commentBox" false

/-- `CoreOptions.EDGE_LABELS_PLACEMENT`. -/
def EDGE_LABELS_PLACEMENT : Property EdgeLabelPlacement :=
  Property.withDefault "org.eclipse.elk.edgeLabels.placement" EdgeLabelPlacement.center

/-- `CoreOptions.EDGE_LABELS_INLINE`. -/
def EDGE_LABELS_INLINE : Property Bool :=
  Property.withDefault "org.eclipse.elk.edgeLabels.inline" false

/-- `CoreOptions.FONT_NAME`. -/
def FONT_NAME : Property String :=
  Property.mk' "org.eclipse.elk.font.name"

/-- `CoreOptions.FONT_SIZE`. -/
def FONT_SIZE : Property Int :=
  Property.mk' "org.eclipse.elk.font.size"

/-- `CoreOptions.HYPERNODE`. -/
def HYPERNODE : Property Bool :=
  Property.withDefault "org.eclipse.elk.hypernode" false

/-- `CoreOptions.LABEL_MANAGER`. -/
def LABEL_MANAGER : Property Dynamic :=
  Property.mk' "org.eclipse.elk.labelManager"

/-- `CoreOptions.SOFTWRAPPING_FUZZINESS`. -/
def SOFTWRAPPING_FUZZINESS : Property Float :=
  Property.withDefault "org.eclipse.elk.softwrappingFuzziness" 0.0

/-- `CoreOptions.MARGINS`. -/
def MARGINS : Property ElkMargin :=
  Property.withDefault "org.eclipse.elk.margins" (({} : ElkMargin))

/-- `CoreOptions.NO_LAYOUT`. -/
def NO_LAYOUT : Property Bool :=
  Property.withDefault "org.eclipse.elk.noLayout" false

/-- `CoreOptions.PORT_ANCHOR`. -/
def PORT_ANCHOR : Property KVector :=
  Property.mk' "org.eclipse.elk.port.anchor"

/-- `CoreOptions.PORT_INDEX`. -/
def PORT_INDEX : Property Int :=
  Property.mk' "org.eclipse.elk.port.index"

/-- `CoreOptions.PORT_SIDE`. -/
def PORT_SIDE : Property PortSide :=
  Property.withDefault "org.eclipse.elk.port.side" PortSide.undefined

/-- `CoreOptions.PORT_BORDER_OFFSET`. -/
def PORT_BORDER_OFFSET : Property Float :=
  Property.mk' "org.eclipse.elk.port.borderOffset"

/-- `CoreOptions.PORT_LABELS_PLACEMENT`. -/
def PORT_LABELS_PLACEMENT : Property (EnumSet PortLabelPlacement) :=
  Property.withDefault "org.eclipse.elk.portLabels.placement" PortLabelPlacement.outsideSet

/-- `CoreOptions.PORT_LABELS_NEXT_TO_PORT_IF_POSSIBLE`. -/
def PORT_LABELS_NEXT_TO_PORT_IF_POSSIBLE : Property Bool :=
  Property.withDefault "org.eclipse.elk.portLabels.nextToPortIfPossible" false

/-- `CoreOptions.PORT_LABELS_TREAT_AS_GROUP`. -/
def PORT_LABELS_TREAT_AS_GROUP : Property Bool :=
  Property.withDefault "org.eclipse.elk.portLabels.treatAsGroup" true

/-- `CoreOptions.SCALE_FACTOR`. -/
def SCALE_FACTOR : Property Float :=
  Property.withDefault "org.eclipse.elk.scaleFactor" 1.0

/-- `CoreOptions.CHILD_AREA_WIDTH`. -/
def CHILD_AREA_WIDTH : Property Float :=
  Property.mk' "org.eclipse.elk.childAreaWidth"

/-- `CoreOptions.CHILD_AREA_HEIGHT`. -/
def CHILD_AREA_HEIGHT : Property Float :=
  Property.mk' "org.eclipse.elk.childAreaHeight"

/-- `CoreOptions.TOPDOWN_LAYOUT`. -/
def TOPDOWN_LAYOUT : Property Bool :=
  Property.withDefault "org.eclipse.elk.topdownLayout" false

/-- `CoreOptions.TOPDOWN_SIZE_CATEGORIES`. -/
def TOPDOWN_SIZE_CATEGORIES : Property Int :=
  Property.withDefault "org.eclipse.elk.topdown.sizeCategories" 3

/-- `CoreOptions.TOPDOWN_SIZE_CATEGORIES_HIERARCHICAL_NODE_WEIGHT`. -/
def TOPDOWN_SIZE_CATEGORIES_HIERARCHICAL_NODE_WEIGHT : Property Int :=
  Property.withDefault "org.eclipse.elk.topdown.sizeCategoriesHierarchicalNodeWeight" 4

/-- `CoreOptions.TOPDOWN_SCALE_FACTOR`. -/
def TOPDOWN_SCALE_FACTOR : Property Float :=
  Property.withDefault "org.eclipse.elk.topdown.scaleFactor" 1.0

/-- `CoreOptions.TOPDOWN_SIZE_APPROXIMATOR`. -/
def TOPDOWN_SIZE_APPROXIMATOR : Property TopdownSizeApproximator :=
  Property.mk' "org.eclipse.elk.topdown.sizeApproximator"

/-- `CoreOptions.TOPDOWN_HIERARCHICAL_NODE_WIDTH`. -/
def TOPDOWN_HIERARCHICAL_NODE_WIDTH : Property Float :=
  Property.withDefault "org.eclipse.elk.topdown.hierarchicalNodeWidth" 150.0

/-- `CoreOptions.TOPDOWN_HIERARCHICAL_NODE_ASPECT_RATIO`. -/
def TOPDOWN_HIERARCHICAL_NODE_ASPECT_RATIO : Property Float :=
  Property.withDefault "org.eclipse.elk.topdown.hierarchicalNodeAspectRatio" 1.414

/-- `CoreOptions.TOPDOWN_NODE_TYPE`. -/
def TOPDOWN_NODE_TYPE : Property TopdownNodeTypes :=
  Property.mk' "org.eclipse.elk.topdown.nodeType"

/-- `CoreOptions.TOPDOWN_SCALE_CAP`. -/
def TOPDOWN_SCALE_CAP : Property Float :=
  Property.withDefault "org.eclipse.elk.topdown.scaleCap" 1.0

/-- `CoreOptions.INSIDE_SELF_LOOPS_ACTIVATE`. -/
def INSIDE_SELF_LOOPS_ACTIVATE : Property Bool :=
  Property.withDefault "org.eclipse.elk.insideSelfLoops.activate" false

/-- `CoreOptions.INSIDE_SELF_LOOPS_YO`. -/
def INSIDE_SELF_LOOPS_YO : Property Bool :=
  Property.withDefault "org.eclipse.elk.insideSelfLoops.yo" false

/-- `CoreOptions.EDGE_THICKNESS`. -/
def EDGE_THICKNESS : Property Float :=
  Property.withDefault "org.eclipse.elk.edge.thickness" 1.0

/-- `CoreOptions.EDGE_TYPE`. -/
def EDGE_TYPE : Property EdgeType :=
  Property.withDefault "org.eclipse.elk.edge.type" EdgeType.none

/-- `CoreOptions.ANIMATE`. -/
def ANIMATE : Property Bool :=
  Property.withDefault "org.eclipse.elk.animate" true

/-- `CoreOptions.ANIM_TIME_FACTOR`. -/
def ANIM_TIME_FACTOR : Property Int :=
  Property.withDefault "org.eclipse.elk.animTimeFactor" 100

/-- `CoreOptions.LAYOUT_ANCESTORS`. -/
def LAYOUT_ANCESTORS : Property Bool :=
  Property.withDefault "org.eclipse.elk.layoutAncestors" false

/-- `CoreOptions.MAX_ANIM_TIME`. -/
def MAX_ANIM_TIME : Property Int :=
  Property.withDefault "org.eclipse.elk.maxAnimTime" 4000

/-- `CoreOptions.MIN_ANIM_TIME`. -/
def MIN_ANIM_TIME : Property Int :=
  Property.withDefault "org.eclipse.elk.minAnimTime" 400

/-- `CoreOptions.PROGRESS_BAR`. -/
def PROGRESS_BAR : Property Bool :=
  Property.withDefault "org.eclipse.elk.progressBar" false

/-- `CoreOptions.VALIDATE_GRAPH`. -/
def VALIDATE_GRAPH : Property Bool :=
  Property.withDefault "org.eclipse.elk.validateGraph" false

/-- `CoreOptions.VALIDATE_OPTIONS`. -/
def VALIDATE_OPTIONS : Property Bool :=
  Property.withDefault "org.eclipse.elk.validateOptions" true

/-- `CoreOptions.ZOOM_TO_FIT`. -/
def ZOOM_TO_FIT : Property Bool :=
  Property.withDefault "org.eclipse.elk.zoomToFit" false

end CoreOptions

end Elk.Core.Options
