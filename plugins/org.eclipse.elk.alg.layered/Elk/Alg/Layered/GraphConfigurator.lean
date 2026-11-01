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

/-! ### Processor assembly fast path (FIX)

The generic `AlgorithmAssembler` path keeps the factories of every slot in insertion-ordered lists
(`doAdd` = `contains` + `push`), sorts each slot with `EnumBasedFactoryComparator` and creates the
processors through the assembler's caches. A slot therefore ends up as the *set* of its factories
in ascending enum ordinal (`doAdd` drops duplicates by `==`, i.e. ordinal identity; the stable sort
orders by ordinal), which is what a bit set over the `IntermediateProcessorStrategy` ordinals
(61 < 64) holds. Every layered phase and processor is an immutable value of the registries
(`pure X.phase`, `register s X.processor`), so the list holds the same values. -/

/-- The six slots of a layered processor configuration as bit sets over the
`IntermediateProcessorStrategy` ordinals: slot `k < 5` = before phase `k`, slot 5 = after the last
phase (`LayoutProcessorConfiguration.processorsBefore`/`processorsAfter`). -/
structure SlotBits where
  s0 : UInt64 := 0
  s1 : UInt64 := 0
  s2 : UInt64 := 0
  s3 : UInt64 := 0
  s4 : UInt64 := 0
  s5 : UInt64 := 0
  deriving BEq, Inhabited, Repr

namespace SlotBits

/-- `doAdd(index, processor)`: sets the processor's bit in slot `index` (slots beyond 5 are never
read by `AlgorithmAssembler.build`, so they are dropped). -/
@[inline] def add (b : SlotBits) (index : Nat) (p : IntermediateProcessorStrategy) : SlotBits :=
  let bit : UInt64 := (1 : UInt64) <<< (ElkEnum.ordinal p).toUInt64
  match index with
  | 0 => { b with s0 := b.s0 ||| bit }
  | 1 => { b with s1 := b.s1 ||| bit }
  | 2 => { b with s2 := b.s2 ||| bit }
  | 3 => { b with s3 := b.s3 ||| bit }
  | 4 => { b with s4 := b.s4 ||| bit }
  | 5 => { b with s5 := b.s5 ||| bit }
  | _ => b

/-- `addBefore(phase, processor)`. -/
@[inline] def addBefore (b : SlotBits) (phase : LayeredPhases) (p : IntermediateProcessorStrategy) : SlotBits :=
  b.add (ElkEnum.ordinal phase) p

/-- `addAfter(phase, processor)`. -/
@[inline] def addAfter (b : SlotBits) (phase : LayeredPhases) (p : IntermediateProcessorStrategy) : SlotBits :=
  b.add (ElkEnum.ordinal phase + 1) p

/-- `addAll(configuration)` of a generic configuration. -/
def addConfiguration (b : SlotBits) (c : LayeredProcessorConfiguration) : SlotBits := Id.run do
  let mut b := b
  for h : i in [0:c.list.size] do
    for p in c.list[i] do b := b.add i p
  return b

/-- The slot sets of a generic configuration (what the assembler would sort). -/
def ofConfiguration (c : LayeredProcessorConfiguration) : SlotBits := ({} : SlotBits).addConfiguration c

/-- Slot-wise union. -/
@[inline] def union (a b : SlotBits) : SlotBits :=
  ⟨a.s0 ||| b.s0, a.s1 ||| b.s1, a.s2 ||| b.s2, a.s3 ||| b.s3, a.s4 ||| b.s4, a.s5 ||| b.s5⟩

end SlotBits

/-- `getPhaseIndependentLayoutProcessorConfiguration(graph)` as slot bit sets: the same option reads
and conditions in the same order (differential test `layered.graphConfigurator.fastAssembly`
against `SlotBits.ofConfiguration` of the generic configuration). -/
def phaseIndependentSlotBits (graph : LGraphId) : LayeredM SlotBits := do
  let gr ← getGraph graph
  let graphProperties := gr.internal.graphProperties
  let hierarchical := isHierarchicalLayout gr
  -- BASELINE_PROCESSING_CONFIGURATION
  let mut b : SlotBits := ({} : SlotBits)
    |>.addBefore .p4NodePlacement .innermostNodeMarginCalculator
    |>.addBefore .p4NodePlacement .labelAndNodeSizeProcessor
    |>.addBefore .p5EdgeRouting .layerSizeAndGraphHeightCalculator
    |>.addAfter .p5EdgeRouting .endLabelSorter
  if hierarchical then
    b := b.addAfter .p5EdgeRouting .hierarchicalNodeResizer
  if gr.props.getD LayeredOptions.FEEDBACK_EDGES false then
    b := b.addBefore .p1CycleBreaking .portSideProcessor
  else
    b := b.addBefore .p3NodeOrdering .portSideProcessor
  if gr.props.has LabelManagementOptions.LABEL_MANAGER then
    b := b.addBefore .p4NodePlacement .centerLabelManagementProcessor
      |>.addBefore .p4NodePlacement .endNodePortLabelManagementProcessor
  if gr.props.getD CoreOptions.INTERACTIVE_LAYOUT false || gr.props.getD LayeredOptions.GENERATE_POSITION_AND_LAYER_IDS false then
    b := b.addAfter .p5EdgeRouting .constraintsPostprocessor
  match gr.props.getD CoreOptions.DIRECTION Direction.right with
  | .left | .down | .up =>
    b := b.addBefore .p1CycleBreaking .directionPreprocessor
      |>.addAfter .p5EdgeRouting .directionPostprocessor
  | _ => pure ()
  if graphProperties.contains .comments then
    b := b.addBefore .p1CycleBreaking .commentPreprocessor
      |>.addBefore .p4NodePlacement .commentNodeMarginCalculator
      |>.addAfter .p5EdgeRouting .commentPostprocessor
  if gr.props.getD LayeredOptions.LAYERING_NODE_PROMOTION_STRATEGY NodePromotionStrategy.none != .none then
    b := b.addBefore .p3NodeOrdering .nodePromotion
  if graphProperties.contains .partitions then
    b := b.addBefore .p1CycleBreaking .partitionPreprocessor
      |>.addBefore .p2Layering .partitionMidprocessor
      |>.addBefore .p3NodeOrdering .partitionPostprocessor
  if gr.props.getD LayeredOptions.COMPACTION_POST_COMPACTION_STRATEGY GraphCompactionStrategy.none != .none
      && gr.props.getD CoreOptions.EDGE_ROUTING EdgeRouting.undefined != .polyline then
    b := b.addAfter .p5EdgeRouting .horizontalCompactor
  if gr.props.getD LayeredOptions.HIGH_DEGREE_NODES_TREATMENT false then
    b := b.addBefore .p3NodeOrdering .highDegreeNodeLayerProcessor
  if gr.props.getD LayeredOptions.CROSSING_MINIMIZATION_SEMI_INTERACTIVE false then
    b := b.addBefore .p3NodeOrdering .semiInteractiveCrossminProcessor
  if activateGreedySwitchFor gr && !disableGreedySwitch then
    let greedyType := if hierarchical then
        gr.props.getD LayeredOptions.CROSSING_MINIMIZATION_GREEDY_SWITCH_HIERARCHICAL_TYPE GreedySwitchType.off
      else gr.props.getD LayeredOptions.CROSSING_MINIMIZATION_GREEDY_SWITCH_TYPE GreedySwitchType.off
    let internalStrategy := if greedyType == .oneSided then IntermediateProcessorStrategy.oneSidedGreedySwitch
      else IntermediateProcessorStrategy.twoSidedGreedySwitch
    b := b.addBefore .p4NodePlacement internalStrategy
  if gr.props.getD LayeredOptions.LAYER_UNZIPPING_STRATEGY LayerUnzippingStrategy.none == .alternating then
    b := b.addBefore .p4NodePlacement .alternatingLayerUnzipper
  match gr.props.getD LayeredOptions.WRAPPING_STRATEGY WrappingStrategy.off with
  | .singleEdge => b := b.addBefore .p4NodePlacement .singleEdgeGraphWrapper
  | .multiEdge =>
    b := b.addBefore .p3NodeOrdering .breakingPointInserter
      |>.addBefore .p4NodePlacement .breakingPointProcessor
      |>.addAfter .p5EdgeRouting .breakingPointRemover
  | _ => pure ()
  if gr.props.getD LayeredOptions.CONSIDER_MODEL_ORDER_STRATEGY OrderingStrategy.none != .none then
    b := b.addBefore .p3NodeOrdering .sortByInputOrderOfModel
  if (gr.props.get LayeredOptions.NODE_PLACEMENT_NETWORK_SIMPLEX_NODE_FLEXIBILITY_RECOMPUTE_NODE_PLACEMENT).isSome then
    let mut anyFlexible := false
    for n in gr.layerlessNodes do
      let nd ← getNode n
      let flexibility := match nd.props.get LayeredOptions.NODE_PLACEMENT_NETWORK_SIMPLEX_NODE_FLEXIBILITY with
        | some f => some f
        | none => gr.props.get LayeredOptions.NODE_PLACEMENT_NETWORK_SIMPLEX_NODE_FLEXIBILITY_DEFAULT
      if flexibility.isSome then anyFlexible := true
    if anyFlexible then
      b := b.addAfter .p4NodePlacement .nodePlacementRepeater
  return b

/-- Appends the registered processors of the set bits of `bits` (bit `i` = ordinal `i`) in
ascending ordinal, the `EnumBasedFactoryComparator` order of `retrieveProcessors`; `none` when one
is not registered (the generic path then throws the Java message). -/
private def pushSlot (registry : Array (Option LayeredProcessor)) (bits : UInt64) (i : Nat)
    (acc : Array LayeredProcessor) : Option (Array LayeredProcessor) :=
  if i < 64 then
    if bits >>> i.toUInt64 == 0 then some acc
    else if (bits >>> i.toUInt64) &&& 1 == 0 then pushSlot registry bits (i + 1) acc
    else match registry[i]? with
      | some (some p) => pushSlot registry bits (i + 1) (acc.push p)
      | _ => none
  else some acc
termination_by 64 - i

/-- The registered phase of strategy constant `ordinal` of `phase` (`LayeredPhases.strategyFactory`
without its unported fallbacks). -/
private def registeredPhase (registry : Array (Array (Option (IO LayeredPhase)))) (phase : LayeredPhases)
    (ordinal : Nat) : IO (Option LayeredPhase) := do
  match ((registry[ElkEnum.ordinal phase]?).bind (·[ordinal]?)).bind id with
  | some create => return some (← create)
  | none => return none

/-- `AlgorithmAssembler.build` for the layered phases without the assembler: the registered
phases, the slot sets of their configurations (in phase order) and of `additional`, and per phase
the processors of its slot in ordinal order followed by the phase itself, then the slot after the
last phase. `none` (generic path) when a phase or processor is not registered or the processor or
phase traces are on (the generic path wraps the processors, `AlgorithmAssembler.traced`). -/
def assembleFast (graph : LGraphId) (cycleBreaking : CycleBreakingStrategy) (layering : LayeringStrategy)
    (crossingMinimization : CrossingMinimizationStrategy) (nodePlacement : NodePlacementStrategy)
    (edgeRouting : EdgeRouting) (additional : SlotBits) : LayeredM (Option (Array LayeredProcessor)) := do
  let t := ElkTrace.global
  if t.phases || t.processors || t.phaseTiming || t.processorTiming then return none
  if ElkEnum.count (α := IntermediateProcessorStrategy) > 64 then return none
  let phaseRegistry ← LayeredPhases.phaseRegistry.get
  -- `EdgeRouterFactory.factoryFor`
  let routing := match edgeRouting with
    | .polyline => EdgeRouting.polyline
    | .splines => EdgeRouting.splines
    | _ => EdgeRouting.orthogonal
  let some p1 ← registeredPhase phaseRegistry .p1CycleBreaking (ElkEnum.ordinal cycleBreaking) | return none
  let some p2 ← registeredPhase phaseRegistry .p2Layering (ElkEnum.ordinal layering) | return none
  let some p3 ← registeredPhase phaseRegistry .p3NodeOrdering (ElkEnum.ordinal crossingMinimization) | return none
  let some p4 ← registeredPhase phaseRegistry .p4NodePlacement (ElkEnum.ordinal nodePlacement) | return none
  let some p5 ← registeredPhase phaseRegistry .p5EdgeRouting (ElkEnum.ordinal routing) | return none
  -- the phase configurations in phase order, then the additional processors (`build`)
  let mut bits : SlotBits := {}
  for p in #[p1, p2, p3, p4, p5] do
    if let some config ← p.getLayoutProcessorConfiguration graph then
      bits := bits.addConfiguration config
  bits := bits.union additional
  let registry ← Intermediate.IntermediateProcessorStrategy.registry.get
  let some acc := pushSlot registry bits.s0 0 (Array.mkEmpty 32) | return none
  let some acc := pushSlot registry bits.s1 0 (acc.push p1.toProcessor) | return none
  let some acc := pushSlot registry bits.s2 0 (acc.push p2.toProcessor) | return none
  let some acc := pushSlot registry bits.s3 0 (acc.push p3.toProcessor) | return none
  let some acc := pushSlot registry bits.s4 0 (acc.push p4.toProcessor) | return none
  let some acc := pushSlot registry bits.s5 0 (acc.push p5.toProcessor) | return none
  return some acc

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

/-- The generic assembly of `prepareGraphForLayout` through the configurator's `AlgorithmAssembler`
(`reset`, `setPhase` ×5, `addProcessorConfiguration`, `build`): the reference of `assembleFast` and
its fallback. -/
def assembleGeneric (c : GraphConfigurator) (graph : LGraphId) (cycleBreaking : CycleBreakingStrategy)
    (layering : LayeringStrategy) (crossingMinimization : CrossingMinimizationStrategy)
    (nodePlacement : NodePlacementStrategy) (edgeRouting : EdgeRouting) : LayeredM (Array LayeredProcessor) := do
  c.assembler.reset
  c.assembler.setPhase .p1CycleBreaking (LayeredPhases.strategyFactory .p1CycleBreaking "CycleBreakingStrategy" (ElkEnum.ordinal cycleBreaking) (ElkEnum.javaName cycleBreaking))
  c.assembler.setPhase .p2Layering (LayeredPhases.strategyFactory .p2Layering "LayeringStrategy" (ElkEnum.ordinal layering) (ElkEnum.javaName layering))
  c.assembler.setPhase .p3NodeOrdering (LayeredPhases.strategyFactory .p3NodeOrdering "CrossingMinimizationStrategy" (ElkEnum.ordinal crossingMinimization) (ElkEnum.javaName crossingMinimization))
  c.assembler.setPhase .p4NodePlacement (LayeredPhases.strategyFactory .p4NodePlacement "NodePlacementStrategy" (ElkEnum.ordinal nodePlacement) (ElkEnum.javaName nodePlacement))
  c.assembler.setPhase .p5EdgeRouting (EdgeRouterFactory.factoryFor edgeRouting)
  let processorConfig ← getPhaseIndependentLayoutProcessorConfiguration graph
  c.assembler.addProcessorConfiguration processorConfig
  c.assembler.build graph

/-- `prepareGraphForLayout(graph)`: configures the properties and assembles the processors
(returned instead of being stored in the `PROCESSORS` property). With `fast` (the default) the
processors come from `assembleFast` (same list; the generic assembler only when it declines). -/
def prepareGraphForLayout (c : GraphConfigurator) (graph : LGraphId) (fast : Bool := true) :
    LayeredM (Array LayeredProcessor) := do
  configureGraphProperties graph
  let gr ← getGraph graph
  let cycleBreaking := gr.props.getD LayeredOptions.CYCLE_BREAKING_STRATEGY CycleBreakingStrategy.greedy
  let layering := gr.props.getD LayeredOptions.LAYERING_STRATEGY LayeringStrategy.networkSimplex
  let crossingMinimization := gr.props.getD LayeredOptions.CROSSING_MINIMIZATION_STRATEGY CrossingMinimizationStrategy.layerSweep
  let nodePlacement := gr.props.getD LayeredOptions.NODE_PLACEMENT_STRATEGY NodePlacementStrategy.brandesKoepf
  let edgeRouting := gr.props.getD CoreOptions.EDGE_ROUTING EdgeRouting.undefined
  if fast then
    let additional ← phaseIndependentSlotBits graph
    if let some processors ←
        assembleFast graph cycleBreaking layering crossingMinimization nodePlacement edgeRouting additional then
      return processors
  assembleGeneric c graph cycleBreaking layering crossingMinimization nodePlacement edgeRouting

end GraphConfigurator

end Elk.Alg.Layered
