import Elk.Core.Options
import Elk.Alg.Layered.Options.CenterEdgeLabelPlacementStrategy
import Elk.Alg.Layered.Options.ConstraintCalculationStrategy
import Elk.Alg.Layered.Options.CrossingMinimizationStrategy
import Elk.Alg.Layered.Options.CuttingStrategy
import Elk.Alg.Layered.Options.CycleBreakingStrategy
import Elk.Alg.Layered.Options.DirectionCongruency
import Elk.Alg.Layered.Options.EdgeLabelSideSelection
import Elk.Alg.Layered.Options.EdgeStraighteningStrategy
import Elk.Alg.Layered.Options.FixedAlignment
import Elk.Alg.Layered.Options.GraphCompactionStrategy
import Elk.Alg.Layered.Options.GreedySwitchType
import Elk.Alg.Layered.Options.GroupOrderStrategy
import Elk.Alg.Layered.Options.InteractiveReferencePoint
import Elk.Alg.Layered.Options.LayerConstraint
import Elk.Alg.Layered.Options.LayerUnzippingStrategy
import Elk.Alg.Layered.Options.LayeringStrategy
import Elk.Alg.Layered.Options.LongEdgeOrderingStrategy
import Elk.Alg.Layered.Options.NodeFlexibility
import Elk.Alg.Layered.Options.NodePlacementStrategy
import Elk.Alg.Layered.Options.NodePromotionStrategy
import Elk.Alg.Layered.Options.OrderingStrategy
import Elk.Alg.Layered.Options.PortSortingStrategy
import Elk.Alg.Layered.Options.SelfLoopDistributionStrategy
import Elk.Alg.Layered.Options.SelfLoopOrderingStrategy
import Elk.Alg.Layered.Options.SplineRoutingMode
import Elk.Alg.Layered.Options.ValidifyStrategy
import Elk.Alg.Layered.Options.WrappingStrategy
import Elk.Alg.Layered.Components.ComponentOrderingStrategy
/-!
# `org.eclipse.elk.alg.layered.options.LayeredOptions`

Port of `layered_options.rs` (elk-rs), the counterpart of the Java `LayeredOptions` class that is
generated from `Layered.melk`. Every `*_PROPERTY` static of the Rust port is a `def` of the Java
constant name inside `namespace LayeredOptions`; the core options re-exported by `LayeredOptions`
are plain aliases of the `CoreOptions` constants (same id, same default). The declaration order
is the order of the Rust `impl LayeredOptions` block.

Notes:
* The option ids follow elk-rs: `org.eclipse.elk.alg.layered.*` (the Java ids
  `org.eclipse.elk.layered.*` are registered as legacy ids by `LayeredMetaDataProvider`).
* As in elk-rs, the re-exported core options keep the *core* defaults (Java `LayeredOptions`
  redeclares some of them with layered defaults; elk-rs encodes those as algorithm-specific
  defaults in `LayeredMetaDataProvider` instead).
* `Vec<i32>` options are `Property (Array Int)`; `i32` options are `Property Int`.
* The Rust `ElkReflect::register` calls (clone support for `Arc<dyn Any>` values) have no
  counterpart: `PropValue` is a closed value type.
-/
namespace Elk.Alg.Layered.Options

open Elk Elk.Graph Elk.Core.Math Elk.Core.Util Elk.Core.Options Elk.Alg.Layered.Components

namespace LayeredOptions

/-- `LayeredOptions.ALGORITHM_ID`: the id of the layered algorithm. -/
def ALGORITHM_ID : String := "org.eclipse.elk.layered"

/-- `LayeredOptions.SPACING_BASE_VALUE`. -/
def SPACING_BASE_VALUE : Property Float :=
  Property.mk' "org.eclipse.elk.alg.layered.spacing.baseValue"

/-- `LayeredOptions.SPACING_EDGE_NODE_BETWEEN_LAYERS`. -/
def SPACING_EDGE_NODE_BETWEEN_LAYERS : Property Float :=
  Property.withDefault "org.eclipse.elk.alg.layered.spacing.edgeNodeBetweenLayers" 10.0

/-- `LayeredOptions.SPACING_EDGE_EDGE_BETWEEN_LAYERS`. -/
def SPACING_EDGE_EDGE_BETWEEN_LAYERS : Property Float :=
  Property.withDefault "org.eclipse.elk.alg.layered.spacing.edgeEdgeBetweenLayers" 10.0

/-- `LayeredOptions.SPACING_NODE_NODE_BETWEEN_LAYERS`. -/
def SPACING_NODE_NODE_BETWEEN_LAYERS : Property Float :=
  Property.withDefault "org.eclipse.elk.alg.layered.spacing.nodeNodeBetweenLayers" 20.0

/-- `LayeredOptions.SPACING_COMMENT_COMMENT` (re-export of `CoreOptions.SPACING_COMMENT_COMMENT`). -/
def SPACING_COMMENT_COMMENT : Property Float := CoreOptions.SPACING_COMMENT_COMMENT

/-- `LayeredOptions.SPACING_COMMENT_NODE` (re-export of `CoreOptions.SPACING_COMMENT_NODE`). -/
def SPACING_COMMENT_NODE : Property Float := CoreOptions.SPACING_COMMENT_NODE

/-- `LayeredOptions.SPACING_COMPONENT_COMPONENT` (re-export of `CoreOptions.SPACING_COMPONENT_COMPONENT`). -/
def SPACING_COMPONENT_COMPONENT : Property Float := CoreOptions.SPACING_COMPONENT_COMPONENT

/-- `LayeredOptions.SPACING_EDGE_EDGE` (re-export of `CoreOptions.SPACING_EDGE_EDGE`). -/
def SPACING_EDGE_EDGE : Property Float := CoreOptions.SPACING_EDGE_EDGE

/-- `LayeredOptions.SPACING_EDGE_LABEL` (re-export of `CoreOptions.SPACING_EDGE_LABEL`). -/
def SPACING_EDGE_LABEL : Property Float := CoreOptions.SPACING_EDGE_LABEL

/-- `LayeredOptions.SPACING_EDGE_NODE` (re-export of `CoreOptions.SPACING_EDGE_NODE`). -/
def SPACING_EDGE_NODE : Property Float := CoreOptions.SPACING_EDGE_NODE

/-- `LayeredOptions.SPACING_LABEL_LABEL` (re-export of `CoreOptions.SPACING_LABEL_LABEL`). -/
def SPACING_LABEL_LABEL : Property Float := CoreOptions.SPACING_LABEL_LABEL

/-- `LayeredOptions.SPACING_LABEL_NODE` (re-export of `CoreOptions.SPACING_LABEL_NODE`). -/
def SPACING_LABEL_NODE : Property Float := CoreOptions.SPACING_LABEL_NODE

/-- `LayeredOptions.SPACING_LABEL_PORT_HORIZONTAL` (re-export of `CoreOptions.SPACING_LABEL_PORT_HORIZONTAL`). -/
def SPACING_LABEL_PORT_HORIZONTAL : Property Float := CoreOptions.SPACING_LABEL_PORT_HORIZONTAL

/-- `LayeredOptions.SPACING_LABEL_PORT_VERTICAL` (re-export of `CoreOptions.SPACING_LABEL_PORT_VERTICAL`). -/
def SPACING_LABEL_PORT_VERTICAL : Property Float := CoreOptions.SPACING_LABEL_PORT_VERTICAL

/-- `LayeredOptions.SPACING_NODE_NODE` (re-export of `CoreOptions.SPACING_NODE_NODE`). -/
def SPACING_NODE_NODE : Property Float := CoreOptions.SPACING_NODE_NODE

/-- `LayeredOptions.SPACING_NODE_SELF_LOOP` (re-export of `CoreOptions.SPACING_NODE_SELF_LOOP`). -/
def SPACING_NODE_SELF_LOOP : Property Float := CoreOptions.SPACING_NODE_SELF_LOOP

/-- `LayeredOptions.SPACING_PORT_PORT` (re-export of `CoreOptions.SPACING_PORT_PORT`). -/
def SPACING_PORT_PORT : Property Float := CoreOptions.SPACING_PORT_PORT

/-- `LayeredOptions.SPACING_INDIVIDUAL` (re-export of `CoreOptions.SPACING_INDIVIDUAL`). -/
def SPACING_INDIVIDUAL : Property IndividualSpacings := CoreOptions.SPACING_INDIVIDUAL

/-- `LayeredOptions.SPACING_PORTS_SURROUNDING` (re-export of `CoreOptions.SPACING_PORTS_SURROUNDING`). -/
def SPACING_PORTS_SURROUNDING : Property ElkMargin := CoreOptions.SPACING_PORTS_SURROUNDING

/-- `LayeredOptions.PRIORITY` (re-export of `CoreOptions.PRIORITY`). -/
def PRIORITY : Property Int := CoreOptions.PRIORITY

/-- `LayeredOptions.PRIORITY_DIRECTION`. -/
def PRIORITY_DIRECTION : Property Int :=
  Property.withDefault "org.eclipse.elk.alg.layered.priority.direction" 0

/-- `LayeredOptions.PRIORITY_SHORTNESS`. -/
def PRIORITY_SHORTNESS : Property Int :=
  Property.withDefault "org.eclipse.elk.alg.layered.priority.shortness" 0

/-- `LayeredOptions.PRIORITY_STRAIGHTNESS`. -/
def PRIORITY_STRAIGHTNESS : Property Int :=
  Property.withDefault "org.eclipse.elk.alg.layered.priority.straightness" 0

/-- `LayeredOptions.WRAPPING_STRATEGY`. -/
def WRAPPING_STRATEGY : Property WrappingStrategy :=
  Property.withDefault "org.eclipse.elk.alg.layered.wrapping.strategy" WrappingStrategy.off

/-- `LayeredOptions.WRAPPING_ADDITIONAL_EDGE_SPACING`. -/
def WRAPPING_ADDITIONAL_EDGE_SPACING : Property Float :=
  Property.withDefault "org.eclipse.elk.alg.layered.wrapping.additionalEdgeSpacing" 10.0

/-- `LayeredOptions.WRAPPING_CORRECTION_FACTOR`. -/
def WRAPPING_CORRECTION_FACTOR : Property Float :=
  Property.withDefault "org.eclipse.elk.alg.layered.wrapping.correctionFactor" 1.0

/-- `LayeredOptions.WRAPPING_CUTTING_STRATEGY`. -/
def WRAPPING_CUTTING_STRATEGY : Property CuttingStrategy :=
  Property.withDefault "org.eclipse.elk.alg.layered.wrapping.cutting.strategy" CuttingStrategy.msd

/-- `LayeredOptions.WRAPPING_CUTTING_CUTS`. -/
def WRAPPING_CUTTING_CUTS : Property (Array Int) :=
  Property.mk' "org.eclipse.elk.alg.layered.wrapping.cutting.cuts"

/-- `LayeredOptions.WRAPPING_CUTTING_MSD_FREEDOM`. -/
def WRAPPING_CUTTING_MSD_FREEDOM : Property Int :=
  Property.withDefault "org.eclipse.elk.alg.layered.wrapping.cutting.msd.freedom" 1

/-- `LayeredOptions.WRAPPING_VALIDIFY_STRATEGY`. -/
def WRAPPING_VALIDIFY_STRATEGY : Property ValidifyStrategy :=
  Property.withDefault "org.eclipse.elk.alg.layered.wrapping.validify.strategy" ValidifyStrategy.greedy

/-- `LayeredOptions.WRAPPING_VALIDIFY_FORBIDDEN_INDICES`. -/
def WRAPPING_VALIDIFY_FORBIDDEN_INDICES : Property (Array Int) :=
  Property.mk' "org.eclipse.elk.alg.layered.wrapping.validify.forbiddenIndices"

/-- `LayeredOptions.WRAPPING_MULTI_EDGE_IMPROVE_CUTS`. -/
def WRAPPING_MULTI_EDGE_IMPROVE_CUTS : Property Bool :=
  Property.withDefault "org.eclipse.elk.alg.layered.wrapping.multiEdge.improveCuts" true

/-- `LayeredOptions.WRAPPING_MULTI_EDGE_DISTANCE_PENALTY`. -/
def WRAPPING_MULTI_EDGE_DISTANCE_PENALTY : Property Float :=
  Property.withDefault "org.eclipse.elk.alg.layered.wrapping.multiEdge.distancePenalty" 2.0

/-- `LayeredOptions.WRAPPING_MULTI_EDGE_IMPROVE_WRAPPED_EDGES`. -/
def WRAPPING_MULTI_EDGE_IMPROVE_WRAPPED_EDGES : Property Bool :=
  Property.withDefault "org.eclipse.elk.alg.layered.wrapping.multiEdge.improveWrappedEdges" true

/-- `LayeredOptions.LAYER_UNZIPPING_STRATEGY`. -/
def LAYER_UNZIPPING_STRATEGY : Property LayerUnzippingStrategy :=
  Property.withDefault "org.eclipse.elk.alg.layered.layerUnzipping.strategy" LayerUnzippingStrategy.none

/-- `LayeredOptions.LAYER_UNZIPPING_MINIMIZE_EDGE_LENGTH`. -/
def LAYER_UNZIPPING_MINIMIZE_EDGE_LENGTH : Property Bool :=
  Property.withDefault "org.eclipse.elk.alg.layered.layerUnzipping.minimizeEdgeLength" false

/-- `LayeredOptions.LAYER_UNZIPPING_LAYER_SPLIT`. -/
def LAYER_UNZIPPING_LAYER_SPLIT : Property Int :=
  Property.withDefault "org.eclipse.elk.alg.layered.layerUnzipping.layerSplit" 2

/-- `LayeredOptions.LAYER_UNZIPPING_RESET_ON_LONG_EDGES`. -/
def LAYER_UNZIPPING_RESET_ON_LONG_EDGES : Property Bool :=
  Property.withDefault "org.eclipse.elk.alg.layered.layerUnzipping.resetOnLongEdges" true

/-- `LayeredOptions.CYCLE_BREAKING_STRATEGY`. -/
def CYCLE_BREAKING_STRATEGY : Property CycleBreakingStrategy :=
  Property.withDefault "org.eclipse.elk.alg.layered.cycleBreaking.strategy" CycleBreakingStrategy.greedy

/-- `LayeredOptions.LAYERING_STRATEGY`. -/
def LAYERING_STRATEGY : Property LayeringStrategy :=
  Property.withDefault "org.eclipse.elk.alg.layered.layering.strategy" LayeringStrategy.networkSimplex

/-- `LayeredOptions.LAYERING_LAYER_CONSTRAINT`. -/
def LAYERING_LAYER_CONSTRAINT : Property LayerConstraint :=
  Property.withDefault "org.eclipse.elk.alg.layered.layering.layerConstraint" LayerConstraint.none

/-- `LayeredOptions.LAYERING_LAYER_CHOICE_CONSTRAINT`. -/
def LAYERING_LAYER_CHOICE_CONSTRAINT : Property Int :=
  Property.mk' "org.eclipse.elk.alg.layered.layering.layerChoiceConstraint"

/-- `LayeredOptions.LAYERING_LAYER_ID`. -/
def LAYERING_LAYER_ID : Property Int :=
  Property.withDefault "org.eclipse.elk.alg.layered.layering.layerId" (-1)

/-- `LayeredOptions.LAYERING_MIN_WIDTH_UPPER_BOUND_ON_WIDTH`. -/
def LAYERING_MIN_WIDTH_UPPER_BOUND_ON_WIDTH : Property Int :=
  Property.withDefault "org.eclipse.elk.alg.layered.layering.minWidth.upperBoundOnWidth" 4

/-- `LayeredOptions.LAYERING_MIN_WIDTH_UPPER_LAYER_ESTIMATION_SCALING_FACTOR`. -/
def LAYERING_MIN_WIDTH_UPPER_LAYER_ESTIMATION_SCALING_FACTOR : Property Int :=
  Property.withDefault "org.eclipse.elk.alg.layered.layering.minWidth.upperLayerEstimationScalingFactor" 2

/-- `LayeredOptions.LAYERING_NODE_PROMOTION_STRATEGY`. -/
def LAYERING_NODE_PROMOTION_STRATEGY : Property NodePromotionStrategy :=
  Property.withDefault "org.eclipse.elk.alg.layered.layering.nodePromotion.strategy" NodePromotionStrategy.none

/-- `LayeredOptions.LAYERING_NODE_PROMOTION_MAX_ITERATIONS`. -/
def LAYERING_NODE_PROMOTION_MAX_ITERATIONS : Property Int :=
  Property.withDefault "org.eclipse.elk.alg.layered.layering.nodePromotion.maxIterations" 0

/-- `LayeredOptions.LAYERING_COFFMAN_GRAHAM_LAYER_BOUND`. -/
def LAYERING_COFFMAN_GRAHAM_LAYER_BOUND : Property Int :=
  Property.withDefault "org.eclipse.elk.alg.layered.layering.coffmanGraham.layerBound" 2147483647

/-- `LayeredOptions.CROSSING_MINIMIZATION_STRATEGY`. -/
def CROSSING_MINIMIZATION_STRATEGY : Property CrossingMinimizationStrategy :=
  Property.withDefault "org.eclipse.elk.alg.layered.crossingMinimization.strategy" CrossingMinimizationStrategy.layerSweep

/-- `LayeredOptions.CROSSING_MINIMIZATION_FORCE_NODE_MODEL_ORDER`. -/
def CROSSING_MINIMIZATION_FORCE_NODE_MODEL_ORDER : Property Bool :=
  Property.withDefault "org.eclipse.elk.alg.layered.crossingMinimization.forceNodeModelOrder" false

/-- `LayeredOptions.CROSSING_MINIMIZATION_HIERARCHICAL_SWEEPINESS`. -/
def CROSSING_MINIMIZATION_HIERARCHICAL_SWEEPINESS : Property Float :=
  Property.withDefault "org.eclipse.elk.alg.layered.crossingMinimization.hierarchicalSweepiness" 0.1

/-- `LayeredOptions.CROSSING_MINIMIZATION_GREEDY_SWITCH_ACTIVATION_THRESHOLD`. -/
def CROSSING_MINIMIZATION_GREEDY_SWITCH_ACTIVATION_THRESHOLD : Property Int :=
  Property.withDefault "org.eclipse.elk.alg.layered.crossingMinimization.greedySwitch.activationThreshold" 40

/-- `LayeredOptions.CROSSING_MINIMIZATION_GREEDY_SWITCH_TYPE`. -/
def CROSSING_MINIMIZATION_GREEDY_SWITCH_TYPE : Property GreedySwitchType :=
  Property.withDefault "org.eclipse.elk.alg.layered.crossingMinimization.greedySwitch.type" GreedySwitchType.twoSided

/-- `LayeredOptions.CROSSING_MINIMIZATION_GREEDY_SWITCH_HIERARCHICAL_TYPE`. -/
def CROSSING_MINIMIZATION_GREEDY_SWITCH_HIERARCHICAL_TYPE : Property GreedySwitchType :=
  Property.withDefault "org.eclipse.elk.alg.layered.crossingMinimization.greedySwitchHierarchical.type" GreedySwitchType.off

/-- `LayeredOptions.CROSSING_MINIMIZATION_SEMI_INTERACTIVE`. -/
def CROSSING_MINIMIZATION_SEMI_INTERACTIVE : Property Bool :=
  Property.withDefault "org.eclipse.elk.alg.layered.crossingMinimization.semiInteractive" false

/-- `LayeredOptions.CROSSING_MINIMIZATION_IN_LAYER_PRED_OF`. -/
def CROSSING_MINIMIZATION_IN_LAYER_PRED_OF : Property String :=
  Property.mk' "org.eclipse.elk.alg.layered.crossingMinimization.inLayerPredOf"

/-- `LayeredOptions.CROSSING_MINIMIZATION_IN_LAYER_SUCC_OF`. -/
def CROSSING_MINIMIZATION_IN_LAYER_SUCC_OF : Property String :=
  Property.mk' "org.eclipse.elk.alg.layered.crossingMinimization.inLayerSuccOf"

/-- `LayeredOptions.CROSSING_MINIMIZATION_POSITION_CHOICE_CONSTRAINT`. -/
def CROSSING_MINIMIZATION_POSITION_CHOICE_CONSTRAINT : Property Int :=
  Property.mk' "org.eclipse.elk.alg.layered.crossingMinimization.positionChoiceConstraint"

/-- `LayeredOptions.CROSSING_MINIMIZATION_POSITION_ID`. -/
def CROSSING_MINIMIZATION_POSITION_ID : Property Int :=
  Property.withDefault "org.eclipse.elk.alg.layered.crossingMinimization.positionId" (-1)

/-- `LayeredOptions.NODE_PLACEMENT_STRATEGY`. -/
def NODE_PLACEMENT_STRATEGY : Property NodePlacementStrategy :=
  Property.withDefault "org.eclipse.elk.alg.layered.nodePlacement.strategy" NodePlacementStrategy.brandesKoepf

/-- `LayeredOptions.NODE_PLACEMENT_FAVOR_STRAIGHT_EDGES`. -/
def NODE_PLACEMENT_FAVOR_STRAIGHT_EDGES : Property Bool :=
  Property.mk' "org.eclipse.elk.alg.layered.nodePlacement.favorStraightEdges"

/-- `LayeredOptions.NODE_PLACEMENT_BK_EDGE_STRAIGHTENING`. -/
def NODE_PLACEMENT_BK_EDGE_STRAIGHTENING : Property EdgeStraighteningStrategy :=
  Property.withDefault "org.eclipse.elk.alg.layered.nodePlacement.bk.edgeStraightening" EdgeStraighteningStrategy.improveStraightness

/-- `LayeredOptions.NODE_PLACEMENT_BK_FIXED_ALIGNMENT`. -/
def NODE_PLACEMENT_BK_FIXED_ALIGNMENT : Property FixedAlignment :=
  Property.withDefault "org.eclipse.elk.alg.layered.nodePlacement.bk.fixedAlignment" FixedAlignment.none

/-- `LayeredOptions.NODE_PLACEMENT_LINEAR_SEGMENTS_DEFLECTION_DAMPENING`. -/
def NODE_PLACEMENT_LINEAR_SEGMENTS_DEFLECTION_DAMPENING : Property Float :=
  Property.withDefault "org.eclipse.elk.alg.layered.nodePlacement.linearSegments.deflectionDampening" 0.3

/-- `LayeredOptions.NODE_PLACEMENT_NETWORK_SIMPLEX_NODE_FLEXIBILITY`. -/
def NODE_PLACEMENT_NETWORK_SIMPLEX_NODE_FLEXIBILITY : Property NodeFlexibility :=
  Property.mk' "org.eclipse.elk.alg.layered.nodePlacement.networkSimplex.nodeFlexibility"

/-- `LayeredOptions.NODE_PLACEMENT_NETWORK_SIMPLEX_NODE_FLEXIBILITY_DEFAULT`. -/
def NODE_PLACEMENT_NETWORK_SIMPLEX_NODE_FLEXIBILITY_DEFAULT : Property NodeFlexibility :=
  Property.withDefault "org.eclipse.elk.alg.layered.nodePlacement.networkSimplex.nodeFlexibility.default" NodeFlexibility.none

/-- `LayeredOptions.NODE_PLACEMENT_NETWORK_SIMPLEX_NODE_FLEXIBILITY_RECOMPUTE_NODE_PLACEMENT`. -/
def NODE_PLACEMENT_NETWORK_SIMPLEX_NODE_FLEXIBILITY_RECOMPUTE_NODE_PLACEMENT : Property NodePlacementStrategy :=
  Property.mk' "org.eclipse.elk.alg.layered.nodePlacement.networkSimplex.nodeFlexibility.recomputeNodePlacement"

/-- `LayeredOptions.EDGE_ROUTING_SPLINES_MODE`. -/
def EDGE_ROUTING_SPLINES_MODE : Property SplineRoutingMode :=
  Property.withDefault "org.eclipse.elk.alg.layered.edgeRouting.splines.mode" SplineRoutingMode.sloppy

/-- `LayeredOptions.EDGE_ROUTING_SPLINES_SLOPPY_LAYER_SPACING_FACTOR`. -/
def EDGE_ROUTING_SPLINES_SLOPPY_LAYER_SPACING_FACTOR : Property Float :=
  Property.withDefault "org.eclipse.elk.alg.layered.edgeRouting.splines.sloppy.layerSpacingFactor" 0.2

/-- `LayeredOptions.EDGE_ROUTING_POLYLINE_SLOPED_EDGE_ZONE_WIDTH`. -/
def EDGE_ROUTING_POLYLINE_SLOPED_EDGE_ZONE_WIDTH : Property Float :=
  Property.withDefault "org.eclipse.elk.alg.layered.edgeRouting.polyline.slopedEdgeZoneWidth" 2.0

/-- `LayeredOptions.EDGE_ROUTING_SELF_LOOP_DISTRIBUTION`. -/
def EDGE_ROUTING_SELF_LOOP_DISTRIBUTION : Property SelfLoopDistributionStrategy :=
  Property.withDefault "org.eclipse.elk.alg.layered.edgeRouting.selfLoopDistribution" SelfLoopDistributionStrategy.north

/-- `LayeredOptions.EDGE_ROUTING_SELF_LOOP_ORDERING`. -/
def EDGE_ROUTING_SELF_LOOP_ORDERING : Property SelfLoopOrderingStrategy :=
  Property.withDefault "org.eclipse.elk.alg.layered.edgeRouting.selfLoopOrdering" SelfLoopOrderingStrategy.stacked

/-- `LayeredOptions.COMPACTION_POST_COMPACTION_STRATEGY`. -/
def COMPACTION_POST_COMPACTION_STRATEGY : Property GraphCompactionStrategy :=
  Property.withDefault "org.eclipse.elk.alg.layered.compaction.postCompaction.strategy" GraphCompactionStrategy.none

/-- `LayeredOptions.COMPACTION_POST_COMPACTION_CONSTRAINTS`. -/
def COMPACTION_POST_COMPACTION_CONSTRAINTS : Property ConstraintCalculationStrategy :=
  Property.withDefault "org.eclipse.elk.alg.layered.compaction.postCompaction.constraints" ConstraintCalculationStrategy.scanline

/-- `LayeredOptions.COMPACTION_CONNECTED_COMPONENTS`. -/
def COMPACTION_CONNECTED_COMPONENTS : Property Bool :=
  Property.withDefault "org.eclipse.elk.alg.layered.compaction.connectedComponents" false

/-- `LayeredOptions.HIGH_DEGREE_NODES_TREATMENT`. -/
def HIGH_DEGREE_NODES_TREATMENT : Property Bool :=
  Property.withDefault "org.eclipse.elk.alg.layered.highDegreeNodes.treatment" false

/-- `LayeredOptions.HIGH_DEGREE_NODES_THRESHOLD`. -/
def HIGH_DEGREE_NODES_THRESHOLD : Property Int :=
  Property.withDefault "org.eclipse.elk.alg.layered.highDegreeNodes.threshold" 16

/-- `LayeredOptions.HIGH_DEGREE_NODES_TREE_HEIGHT`. -/
def HIGH_DEGREE_NODES_TREE_HEIGHT : Property Int :=
  Property.withDefault "org.eclipse.elk.alg.layered.highDegreeNodes.treeHeight" 5

/-- `LayeredOptions.DIRECTION_CONGRUENCY`. -/
def DIRECTION_CONGRUENCY : Property DirectionCongruency :=
  Property.withDefault "org.eclipse.elk.alg.layered.directionCongruency" DirectionCongruency.readingDirection

/-- `LayeredOptions.FEEDBACK_EDGES`. -/
def FEEDBACK_EDGES : Property Bool :=
  Property.withDefault "org.eclipse.elk.alg.layered.feedbackEdges" false

/-- `LayeredOptions.MERGE_HIERARCHY_EDGES`. -/
def MERGE_HIERARCHY_EDGES : Property Bool :=
  Property.withDefault "org.eclipse.elk.alg.layered.mergeHierarchyEdges" true

/-- `LayeredOptions.ALLOW_NON_FLOW_PORTS_TO_SWITCH_SIDES`. -/
def ALLOW_NON_FLOW_PORTS_TO_SWITCH_SIDES : Property Bool :=
  Property.withDefault "org.eclipse.elk.alg.layered.allowNonFlowPortsToSwitchSides" false

/-- `LayeredOptions.PORT_SORTING_STRATEGY`. -/
def PORT_SORTING_STRATEGY : Property PortSortingStrategy :=
  Property.withDefault "org.eclipse.elk.alg.layered.portSortingStrategy" PortSortingStrategy.inputOrder

/-- `LayeredOptions.THOROUGHNESS`. -/
def THOROUGHNESS : Property Int :=
  Property.withDefault "org.eclipse.elk.alg.layered.thoroughness" 7

/-- `LayeredOptions.UNNECESSARY_BENDPOINTS`. -/
def UNNECESSARY_BENDPOINTS : Property Bool :=
  Property.withDefault "org.eclipse.elk.alg.layered.unnecessaryBendpoints" false

/-- `LayeredOptions.GENERATE_POSITION_AND_LAYER_IDS`. -/
def GENERATE_POSITION_AND_LAYER_IDS : Property Bool :=
  Property.withDefault "org.eclipse.elk.alg.layered.generatePositionAndLayerIds" false

/-- `LayeredOptions.EDGE_LABELS_SIDE_SELECTION`. -/
def EDGE_LABELS_SIDE_SELECTION : Property EdgeLabelSideSelection :=
  Property.withDefault "org.eclipse.elk.alg.layered.edgeLabels.sideSelection" EdgeLabelSideSelection.smartDown

/-- `LayeredOptions.EDGE_LABELS_CENTER_LABEL_PLACEMENT_STRATEGY`. -/
def EDGE_LABELS_CENTER_LABEL_PLACEMENT_STRATEGY : Property CenterEdgeLabelPlacementStrategy :=
  Property.withDefault "org.eclipse.elk.alg.layered.edgeLabels.centerLabelPlacementStrategy" CenterEdgeLabelPlacementStrategy.medianLayer

/-- `LayeredOptions.EDGE_LABELS_PLACEMENT` (re-export of `CoreOptions.EDGE_LABELS_PLACEMENT`). -/
def EDGE_LABELS_PLACEMENT : Property EdgeLabelPlacement := CoreOptions.EDGE_LABELS_PLACEMENT

/-- `LayeredOptions.EDGE_LABELS_INLINE` (re-export of `CoreOptions.EDGE_LABELS_INLINE`). -/
def EDGE_LABELS_INLINE : Property Bool := CoreOptions.EDGE_LABELS_INLINE

/-- `LayeredOptions.INTERACTIVE_REFERENCE_POINT`. -/
def INTERACTIVE_REFERENCE_POINT : Property InteractiveReferencePoint :=
  Property.withDefault "org.eclipse.elk.alg.layered.interactiveReferencePoint" InteractiveReferencePoint.center

/-- `LayeredOptions.ALIGNMENT` (re-export of `CoreOptions.ALIGNMENT`). -/
def ALIGNMENT : Property Alignment := CoreOptions.ALIGNMENT

/-- `LayeredOptions.ASPECT_RATIO` (re-export of `CoreOptions.ASPECT_RATIO`). -/
def ASPECT_RATIO : Property Float := CoreOptions.ASPECT_RATIO

/-- `LayeredOptions.COMMENT_BOX` (re-export of `CoreOptions.COMMENT_BOX`). -/
def COMMENT_BOX : Property Bool := CoreOptions.COMMENT_BOX

/-- `LayeredOptions.DIRECTION` (re-export of `CoreOptions.DIRECTION`). -/
def DIRECTION : Property Direction := CoreOptions.DIRECTION

/-- `LayeredOptions.EDGE_ROUTING` (re-export of `CoreOptions.EDGE_ROUTING`). -/
def EDGE_ROUTING : Property EdgeRouting := CoreOptions.EDGE_ROUTING

/-- `LayeredOptions.HYPERNODE` (re-export of `CoreOptions.HYPERNODE`). -/
def HYPERNODE : Property Bool := CoreOptions.HYPERNODE

/-- `LayeredOptions.HIERARCHY_HANDLING` (re-export of `CoreOptions.HIERARCHY_HANDLING`). -/
def HIERARCHY_HANDLING : Property HierarchyHandling := CoreOptions.HIERARCHY_HANDLING

/-- `LayeredOptions.INTERACTIVE_LAYOUT` (re-export of `CoreOptions.INTERACTIVE_LAYOUT`). -/
def INTERACTIVE_LAYOUT : Property Bool := CoreOptions.INTERACTIVE_LAYOUT

/-- `LayeredOptions.JUNCTION_POINTS` (re-export of `CoreOptions.JUNCTION_POINTS`). -/
def JUNCTION_POINTS : Property KVectorChain := CoreOptions.JUNCTION_POINTS

/-- `LayeredOptions.NODE_LABELS_PADDING` (re-export of `CoreOptions.NODE_LABELS_PADDING`). -/
def NODE_LABELS_PADDING : Property ElkPadding := CoreOptions.NODE_LABELS_PADDING

/-- `LayeredOptions.NODE_LABELS_PLACEMENT` (re-export of `CoreOptions.NODE_LABELS_PLACEMENT`). -/
def NODE_LABELS_PLACEMENT : Property (EnumSet NodeLabelPlacement) := CoreOptions.NODE_LABELS_PLACEMENT

/-- `LayeredOptions.NODE_SIZE_CONSTRAINTS` (re-export of `CoreOptions.NODE_SIZE_CONSTRAINTS`). -/
def NODE_SIZE_CONSTRAINTS : Property (EnumSet SizeConstraint) := CoreOptions.NODE_SIZE_CONSTRAINTS

/-- `LayeredOptions.NODE_SIZE_MINIMUM` (re-export of `CoreOptions.NODE_SIZE_MINIMUM`). -/
def NODE_SIZE_MINIMUM : Property KVector := CoreOptions.NODE_SIZE_MINIMUM

/-- `LayeredOptions.POSITION` (re-export of `CoreOptions.POSITION`). -/
def POSITION : Property KVector := CoreOptions.POSITION

/-- `LayeredOptions.SEPARATE_CONNECTED_COMPONENTS` (re-export of `CoreOptions.SEPARATE_CONNECTED_COMPONENTS`). -/
def SEPARATE_CONNECTED_COMPONENTS : Property Bool := CoreOptions.SEPARATE_CONNECTED_COMPONENTS

/-- `LayeredOptions.TOPDOWN_NODE_TYPE` (re-export of `CoreOptions.TOPDOWN_NODE_TYPE`). -/
def TOPDOWN_NODE_TYPE : Property TopdownNodeTypes := CoreOptions.TOPDOWN_NODE_TYPE

/-- `LayeredOptions.PORT_ANCHOR` (re-export of `CoreOptions.PORT_ANCHOR`). -/
def PORT_ANCHOR : Property KVector := CoreOptions.PORT_ANCHOR

/-- `LayeredOptions.PORT_BORDER_OFFSET` (re-export of `CoreOptions.PORT_BORDER_OFFSET`). -/
def PORT_BORDER_OFFSET : Property Float := CoreOptions.PORT_BORDER_OFFSET

/-- `LayeredOptions.PORT_CONSTRAINTS` (re-export of `CoreOptions.PORT_CONSTRAINTS`). -/
def PORT_CONSTRAINTS : Property PortConstraints := CoreOptions.PORT_CONSTRAINTS

/-- `LayeredOptions.PORT_INDEX` (re-export of `CoreOptions.PORT_INDEX`). -/
def PORT_INDEX : Property Int := CoreOptions.PORT_INDEX

/-- `LayeredOptions.PORT_SIDE` (re-export of `CoreOptions.PORT_SIDE`). -/
def PORT_SIDE : Property PortSide := CoreOptions.PORT_SIDE

/-- `LayeredOptions.RANDOM_SEED` (re-export of `CoreOptions.RANDOM_SEED`). -/
def RANDOM_SEED : Property Int := CoreOptions.RANDOM_SEED

/-- `LayeredOptions.MERGE_EDGES`. -/
def MERGE_EDGES : Property Bool :=
  Property.withDefault "org.eclipse.elk.alg.layered.mergeEdges" false

/-- `LayeredOptions.CONSIDER_MODEL_ORDER_STRATEGY`. -/
def CONSIDER_MODEL_ORDER_STRATEGY : Property OrderingStrategy :=
  Property.withDefault "org.eclipse.elk.alg.layered.considerModelOrder.strategy" OrderingStrategy.none

/-- `LayeredOptions.CONSIDER_MODEL_ORDER_PORT_MODEL_ORDER`. -/
def CONSIDER_MODEL_ORDER_PORT_MODEL_ORDER : Property Bool :=
  Property.withDefault "org.eclipse.elk.alg.layered.considerModelOrder.portModelOrder" false

/-- `LayeredOptions.CONSIDER_MODEL_ORDER_NO_MODEL_ORDER`. -/
def CONSIDER_MODEL_ORDER_NO_MODEL_ORDER : Property Bool :=
  Property.withDefault "org.eclipse.elk.alg.layered.considerModelOrder.noModelOrder" false

/-- `LayeredOptions.CONSIDER_MODEL_ORDER_COMPONENTS`. -/
def CONSIDER_MODEL_ORDER_COMPONENTS : Property ComponentOrderingStrategy :=
  Property.withDefault "org.eclipse.elk.alg.layered.considerModelOrder.components" ComponentOrderingStrategy.none

/-- `LayeredOptions.CONSIDER_MODEL_ORDER_LONG_EDGE_STRATEGY`. -/
def CONSIDER_MODEL_ORDER_LONG_EDGE_STRATEGY : Property LongEdgeOrderingStrategy :=
  Property.withDefault "org.eclipse.elk.alg.layered.considerModelOrder.longEdgeStrategy" LongEdgeOrderingStrategy.dummyNodeOver

/-- `LayeredOptions.CONSIDER_MODEL_ORDER_CROSSING_COUNTER_NODE_INFLUENCE`. -/
def CONSIDER_MODEL_ORDER_CROSSING_COUNTER_NODE_INFLUENCE : Property Float :=
  Property.withDefault "org.eclipse.elk.alg.layered.considerModelOrder.crossingCounterNodeInfluence" 0.0

/-- `LayeredOptions.CONSIDER_MODEL_ORDER_CROSSING_COUNTER_PORT_INFLUENCE`. -/
def CONSIDER_MODEL_ORDER_CROSSING_COUNTER_PORT_INFLUENCE : Property Float :=
  Property.withDefault "org.eclipse.elk.alg.layered.considerModelOrder.crossingCounterPortInfluence" 0.0

/-- `LayeredOptions.GROUP_MODEL_ORDER_CYCLE_BREAKING_ID`. -/
def GROUP_MODEL_ORDER_CYCLE_BREAKING_ID : Property Int :=
  Property.withDefault "org.eclipse.elk.alg.layered.considerModelOrder.groupModelOrder.cycleBreakingId" 0

/-- `LayeredOptions.GROUP_MODEL_ORDER_CROSSING_MINIMIZATION_ID`. -/
def GROUP_MODEL_ORDER_CROSSING_MINIMIZATION_ID : Property Int :=
  Property.withDefault "org.eclipse.elk.alg.layered.considerModelOrder.groupModelOrder.crossingMinimizationId" 0

/-- `LayeredOptions.GROUP_MODEL_ORDER_COMPONENT_GROUP_ID`. -/
def GROUP_MODEL_ORDER_COMPONENT_GROUP_ID : Property Int :=
  Property.withDefault "org.eclipse.elk.alg.layered.considerModelOrder.groupModelOrder.componentGroupId" 0

/-- `LayeredOptions.GROUP_MODEL_ORDER_CB_GROUP_ORDER_STRATEGY`. -/
def GROUP_MODEL_ORDER_CB_GROUP_ORDER_STRATEGY : Property GroupOrderStrategy :=
  Property.withDefault "org.eclipse.elk.alg.layered.considerModelOrder.groupModelOrder.cbGroupOrderStrategy" GroupOrderStrategy.onlyWithinGroup

/-- `LayeredOptions.GROUP_MODEL_ORDER_CB_PREFERRED_SOURCE_ID`. -/
def GROUP_MODEL_ORDER_CB_PREFERRED_SOURCE_ID : Property Int :=
  Property.mk' "org.eclipse.elk.alg.layered.considerModelOrder.groupModelOrder.cbPreferredSourceId"

/-- `LayeredOptions.GROUP_MODEL_ORDER_CB_PREFERRED_TARGET_ID`. -/
def GROUP_MODEL_ORDER_CB_PREFERRED_TARGET_ID : Property Int :=
  Property.mk' "org.eclipse.elk.alg.layered.considerModelOrder.groupModelOrder.cbPreferredTargetId"

/-- `LayeredOptions.GROUP_MODEL_ORDER_CM_GROUP_ORDER_STRATEGY`. -/
def GROUP_MODEL_ORDER_CM_GROUP_ORDER_STRATEGY : Property GroupOrderStrategy :=
  Property.withDefault "org.eclipse.elk.alg.layered.considerModelOrder.groupModelOrder.cmGroupOrderStrategy" GroupOrderStrategy.onlyWithinGroup

/-- `LayeredOptions.GROUP_MODEL_ORDER_CM_ENFORCED_GROUP_ORDERS`. -/
def GROUP_MODEL_ORDER_CM_ENFORCED_GROUP_ORDERS : Property (Array Int) :=
  Property.withDefault "org.eclipse.elk.alg.layered.considerModelOrder.groupModelOrder.cmEnforcedGroupOrders" #[1, 2, 6, 7, 10, 11]

end LayeredOptions

end Elk.Alg.Layered.Options
