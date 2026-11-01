import Elk.Alg.Layered.LayeredPhases
import Elk.Alg.Layered.Graph.LGraphUtil
import Elk.Alg.Layered.P5Edges.EdgeRouterFactory
import Elk.Alg.Layered.Options
import Elk.Core.Labels.LabelManagementOptions
/-!
# `org.eclipse.elk.alg.layered.GraphConfigurator`

Configures the graph properties (edge spacing minimum, direction inference, random seed,
favor-straight-edges default, original port constraints, `Spacings`) and assembles the
processor list from the phase strategies and the option-dependent intermediate processors.
`prepareGraphForLayout` returns the processors (Java stores them in `PROCESSORS`).
-/
namespace Elk.Alg.Layered

open Elk.Graph Elk.Core Elk.Core.Options Elk.Core.Util Elk.Core.Alg Elk.Core.Labels
open Elk.Alg.Layered.Graph Elk.Alg.Layered.Options Elk.Alg.Layered.Intermediate Elk.Alg.Layered.P5Edges LayeredM

/-- `ELK_DISABLE_GREEDY_SWITCH` (elk-rs debugging switch), read once. -/
builtin_initialize disableGreedySwitch : Bool ← do return (← IO.getEnv "ELK_DISABLE_GREEDY_SWITCH").isSome

namespace GraphConfigurator

/-- `MIN_EDGE_SPACING`. -/
def MIN_EDGE_SPACING : Float := 2.0

/-- `BASELINE_PROCESSING_CONFIGURATION`. -/
def baselineProcessingConfiguration : LayeredProcessorConfiguration :=
  (LayoutProcessorConfiguration.create : LayeredProcessorConfiguration)
    |>.addBefore .p4NodePlacement .innermostNodeMarginCalculator
    |>.addBefore .p4NodePlacement .labelAndNodeSizeProcessor
    |>.addBefore .p5EdgeRouting .layerSizeAndGraphHeightCalculator
    |>.addAfter .p5EdgeRouting .endLabelSorter

/-- `LABEL_MANAGEMENT_ADDITIONS`. -/
def labelManagementAdditions : LayeredProcessorConfiguration :=
  (LayoutProcessorConfiguration.create : LayeredProcessorConfiguration)
    |>.addBefore .p4NodePlacement .centerLabelManagementProcessor
    |>.addBefore .p4NodePlacement .endNodePortLabelManagementProcessor

/-- `HIERARCHICAL_ADDITIONS`. -/
def hierarchicalAdditions : LayeredProcessorConfiguration :=
  (LayoutProcessorConfiguration.create : LayeredProcessorConfiguration)
    |>.addAfter .p5EdgeRouting .hierarchicalNodeResizer

end GraphConfigurator

/-- `GraphConfigurator`: owns the algorithm assembler (and its caches). -/
structure GraphConfigurator where
  assembler : LayeredAssembler

namespace GraphConfigurator

/-- `new GraphConfigurator()`. -/
def new : IO GraphConfigurator := do
  return ⟨← AlgorithmAssembler.create IntermediateProcessorStrategy.create⟩

private def isHierarchicalLayout (gr : LGraph) : Bool :=
  gr.props.getD CoreOptions.HIERARCHY_HANDLING HierarchyHandling.inherit == .includeChildren

/-- `activateGreedySwitchFor(graph)`. -/
def activateGreedySwitchFor (gr : LGraph) : Bool :=
  if isHierarchicalLayout gr then
    let greedyType := gr.props.getD LayeredOptions.CROSSING_MINIMIZATION_GREEDY_SWITCH_HIERARCHICAL_TYPE GreedySwitchType.off
    gr.parentNode.isNone && greedyType != .off
  else
    let greedyType := gr.props.getD LayeredOptions.CROSSING_MINIMIZATION_GREEDY_SWITCH_TYPE GreedySwitchType.off
    let interactiveCrossmin := gr.props.getD LayeredOptions.CROSSING_MINIMIZATION_SEMI_INTERACTIVE false
      || gr.props.getD LayeredOptions.CROSSING_MINIMIZATION_STRATEGY CrossingMinimizationStrategy.layerSweep == .interactive
    let activationThreshold := gr.props.getD LayeredOptions.CROSSING_MINIMIZATION_GREEDY_SWITCH_ACTIVATION_THRESHOLD 0
    let graphSize : Int := gr.layerlessNodes.size
    !interactiveCrossmin && greedyType != .off && (activationThreshold == 0 || activationThreshold > graphSize)

/-- `getPhaseIndependentLayoutProcessorConfiguration(graph)`. -/
def getPhaseIndependentLayoutProcessorConfiguration (graph : LGraphId) : LayeredM LayeredProcessorConfiguration := do
  let gr ← getGraph graph
  let graphProperties := gr.internal.graphProperties
  let mut configuration := LayoutProcessorConfiguration.createFrom baselineProcessingConfiguration
  if isHierarchicalLayout gr then
    configuration := configuration.addAll hierarchicalAdditions
  if gr.props.getD LayeredOptions.FEEDBACK_EDGES false then
    configuration := configuration.addBefore .p1CycleBreaking .portSideProcessor
  else
    configuration := configuration.addBefore .p3NodeOrdering .portSideProcessor
  if gr.props.has LabelManagementOptions.LABEL_MANAGER then
    configuration := configuration.addAll labelManagementAdditions
  if gr.props.getD CoreOptions.INTERACTIVE_LAYOUT false || gr.props.getD LayeredOptions.GENERATE_POSITION_AND_LAYER_IDS false then
    configuration := configuration.addAfter .p5EdgeRouting .constraintsPostprocessor
  match gr.props.getD CoreOptions.DIRECTION Direction.right with
  | .left | .down | .up =>
    configuration := configuration.addBefore .p1CycleBreaking .directionPreprocessor
      |>.addAfter .p5EdgeRouting .directionPostprocessor
  | _ => pure ()
  if graphProperties.contains .comments then
    configuration := configuration.addBefore .p1CycleBreaking .commentPreprocessor
      |>.addBefore .p4NodePlacement .commentNodeMarginCalculator
      |>.addAfter .p5EdgeRouting .commentPostprocessor
  if gr.props.getD LayeredOptions.LAYERING_NODE_PROMOTION_STRATEGY NodePromotionStrategy.none != .none then
    configuration := configuration.addBefore .p3NodeOrdering .nodePromotion
  if graphProperties.contains .partitions then
    configuration := configuration.addBefore .p1CycleBreaking .partitionPreprocessor
      |>.addBefore .p2Layering .partitionMidprocessor
      |>.addBefore .p3NodeOrdering .partitionPostprocessor
  if gr.props.getD LayeredOptions.COMPACTION_POST_COMPACTION_STRATEGY GraphCompactionStrategy.none != .none
      && gr.props.getD CoreOptions.EDGE_ROUTING EdgeRouting.undefined != .polyline then
    configuration := configuration.addAfter .p5EdgeRouting .horizontalCompactor
  if gr.props.getD LayeredOptions.HIGH_DEGREE_NODES_TREATMENT false then
    configuration := configuration.addBefore .p3NodeOrdering .highDegreeNodeLayerProcessor
  if gr.props.getD LayeredOptions.CROSSING_MINIMIZATION_SEMI_INTERACTIVE false then
    configuration := configuration.addBefore .p3NodeOrdering .semiInteractiveCrossminProcessor
  if activateGreedySwitchFor gr && !disableGreedySwitch then
    let greedyType := if isHierarchicalLayout gr then
        gr.props.getD LayeredOptions.CROSSING_MINIMIZATION_GREEDY_SWITCH_HIERARCHICAL_TYPE GreedySwitchType.off
      else gr.props.getD LayeredOptions.CROSSING_MINIMIZATION_GREEDY_SWITCH_TYPE GreedySwitchType.off
    let internalStrategy := if greedyType == .oneSided then IntermediateProcessorStrategy.oneSidedGreedySwitch
      else IntermediateProcessorStrategy.twoSidedGreedySwitch
    configuration := configuration.addBefore .p4NodePlacement internalStrategy
  if gr.props.getD LayeredOptions.LAYER_UNZIPPING_STRATEGY LayerUnzippingStrategy.none == .alternating then
    configuration := configuration.addBefore .p4NodePlacement .alternatingLayerUnzipper
  match gr.props.getD LayeredOptions.WRAPPING_STRATEGY WrappingStrategy.off with
  | .singleEdge => configuration := configuration.addBefore .p4NodePlacement .singleEdgeGraphWrapper
  | .multiEdge =>
    configuration := configuration.addBefore .p3NodeOrdering .breakingPointInserter
      |>.addBefore .p4NodePlacement .breakingPointProcessor
      |>.addAfter .p5EdgeRouting .breakingPointRemover
  | _ => pure ()
  if gr.props.getD LayeredOptions.CONSIDER_MODEL_ORDER_STRATEGY OrderingStrategy.none != .none then
    configuration := configuration.addBefore .p3NodeOrdering .sortByInputOrderOfModel
  -- NONE is a non-null flexibility value too, just as in Java: only the optional second placer
  -- decides whether the repeater is requested.
  if (gr.props.get LayeredOptions.NODE_PLACEMENT_NETWORK_SIMPLEX_NODE_FLEXIBILITY_RECOMPUTE_NODE_PLACEMENT).isSome then
    let mut anyFlexible := false
    for n in gr.layerlessNodes do
      let nd ← getNode n
      let flexibility := match nd.props.get LayeredOptions.NODE_PLACEMENT_NETWORK_SIMPLEX_NODE_FLEXIBILITY with
        | some f => some f
        | none => gr.props.get LayeredOptions.NODE_PLACEMENT_NETWORK_SIMPLEX_NODE_FLEXIBILITY_DEFAULT
      if flexibility.isSome then anyFlexible := true
    if anyFlexible then
      configuration := configuration.addAfter .p4NodePlacement .nodePlacementRepeater
  return configuration

/-- `copyPortConstraints(graph)`: remembers the user-set port constraints (recursively). -/
partial def copyPortConstraints (graph : LGraphId) : LayeredM Unit := do
  let gr ← getGraph graph
  let mut nodes := gr.layerlessNodes
  for l in gr.layers do nodes := nodes ++ (← getLayer l).nodes
  for n in nodes do
    let nd ← getNode n
    let original := nd.props.get CoreOptions.PORT_CONSTRAINTS
    -- read before the update: a live `nd` would make `modifyNode` copy the node (PLAN 7.1 item 27)
    let nested := nd.nestedGraph
    modifyNode n fun x => { x with internal := { x.internal with originalPortConstraints := original } }
    if let some nested := nested then copyPortConstraints nested

/-- `configureGraphProperties(graph)`. -/
def configureGraphProperties (graph : LGraphId) : LayeredM Unit := do
  let gr ← getGraph graph
  let edgeSpacing := gr.props.getD CoreOptions.SPACING_EDGE_EDGE 0.0
  let direction := gr.props.getD CoreOptions.DIRECTION Direction.undefined
  let randomSeed := gr.props.getD CoreOptions.RANDOM_SEED 1
  let edgeRouting := gr.props.getD CoreOptions.EDGE_ROUTING EdgeRouting.undefined
  let favorStraightness := gr.props.get LayeredOptions.NODE_PLACEMENT_FAVOR_STRAIGHT_EDGES
  if edgeSpacing < MIN_EDGE_SPACING then
    setGraphProp graph CoreOptions.SPACING_EDGE_EDGE MIN_EDGE_SPACING
  if direction == .undefined then
    let inferred ← LGraphUtil.getDirection graph
    setGraphProp graph CoreOptions.DIRECTION inferred
  -- Random::default() of elk-rs seeds with 0; Java's `new Random()` would be time based
  let random := if randomSeed == 0 then Random.ofInt 0 else Random.ofInt randomSeed
  modifyGraph graph fun g => { g with internal := { g.internal with random := some random, randomOwner := none } }
  if favorStraightness.isNone then
    -- Java metadata defaults edge routing to ORTHOGONAL for layered; UNDEFINED counts as orthogonal here too
    let favor := edgeRouting == .orthogonal || edgeRouting == .undefined
    setGraphProp graph LayeredOptions.NODE_PLACEMENT_FAVOR_STRAIGHT_EDGES favor
  copyPortConstraints graph
  let spacings := Spacings.new (← getGraph graph).props
  modifyGraph graph fun g => { g with internal := { g.internal with spacings := some spacings } }

/-- `prepareGraphForLayout(graph)`: configures the properties and assembles the processors
(returned instead of being stored in the `PROCESSORS` property). -/
def prepareGraphForLayout (c : GraphConfigurator) (graph : LGraphId) : LayeredM (Array LayeredProcessor) := do
  configureGraphProperties graph
  let gr ← getGraph graph
  let cycleBreaking := gr.props.getD LayeredOptions.CYCLE_BREAKING_STRATEGY CycleBreakingStrategy.greedy
  let layering := gr.props.getD LayeredOptions.LAYERING_STRATEGY LayeringStrategy.networkSimplex
  let crossingMinimization := gr.props.getD LayeredOptions.CROSSING_MINIMIZATION_STRATEGY CrossingMinimizationStrategy.layerSweep
  let nodePlacement := gr.props.getD LayeredOptions.NODE_PLACEMENT_STRATEGY NodePlacementStrategy.brandesKoepf
  let edgeRouting := gr.props.getD CoreOptions.EDGE_ROUTING EdgeRouting.undefined
  c.assembler.reset
  c.assembler.setPhase .p1CycleBreaking (LayeredPhases.strategyFactory .p1CycleBreaking "CycleBreakingStrategy" (ElkEnum.ordinal cycleBreaking) (ElkEnum.javaName cycleBreaking))
  c.assembler.setPhase .p2Layering (LayeredPhases.strategyFactory .p2Layering "LayeringStrategy" (ElkEnum.ordinal layering) (ElkEnum.javaName layering))
  c.assembler.setPhase .p3NodeOrdering (LayeredPhases.strategyFactory .p3NodeOrdering "CrossingMinimizationStrategy" (ElkEnum.ordinal crossingMinimization) (ElkEnum.javaName crossingMinimization))
  c.assembler.setPhase .p4NodePlacement (LayeredPhases.strategyFactory .p4NodePlacement "NodePlacementStrategy" (ElkEnum.ordinal nodePlacement) (ElkEnum.javaName nodePlacement))
  c.assembler.setPhase .p5EdgeRouting (EdgeRouterFactory.factoryFor edgeRouting)
  let processorConfig ← getPhaseIndependentLayoutProcessorConfiguration graph
  c.assembler.addProcessorConfiguration processorConfig
  c.assembler.build graph

end GraphConfigurator

end Elk.Alg.Layered
