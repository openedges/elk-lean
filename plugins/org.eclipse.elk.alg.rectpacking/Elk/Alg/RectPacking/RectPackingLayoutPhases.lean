import Elk.Core.Alg
import Elk.Alg.RectPacking.Util.RectPackingArena
import Elk.Alg.RectPacking.Intermediate.IntermediateProcessorStrategy
/-!
# `org.eclipse.elk.alg.rectpacking.RectPackingLayoutPhases`

Port of `rect_packing_layout_phases.rs` (elk-rs): the phase enumeration `P` of the rectangle
packing `AlgorithmAssembler`, plus the phase/processor types of the plugin. Phases and processors
run in `RectPackingM` (arena over `ElkM`) on the laid-out parent node (`NodeId`, Java `ElkNode`).
-/
namespace Elk.Alg.RectPacking

open Elk.Graph Elk.Core.Alg Elk.Alg.RectPacking.Util Elk.Alg.RectPacking.Intermediate

/-- `RectPackingLayoutPhases`: `P1_WIDTH_APPROXIMATION`, `P2_PACKING`,
`P3_WHITESPACE_ELIMINATION`. -/
elk_enum RectPackingLayoutPhases := p1WidthApproximation p2Packing p3WhitespaceElimination

/-- `ILayoutProcessor<ElkNode>` of the rectangle packing. -/
abbrev RectPackingProcessor := LayoutProcessor RectPackingM NodeId

/-- `ILayoutPhase<RectPackingLayoutPhases, ElkNode>`. -/
abbrev RectPackingPhase :=
  LayoutPhase RectPackingM RectPackingLayoutPhases NodeId IntermediateProcessorStrategy

/-- `ILayoutPhaseFactory<RectPackingLayoutPhases, ElkNode>`. -/
abbrev RectPackingPhaseFactory :=
  LayoutPhaseFactory RectPackingM RectPackingLayoutPhases NodeId IntermediateProcessorStrategy

/-- `AlgorithmAssembler<RectPackingLayoutPhases, ElkNode>`. -/
abbrev RectPackingAlgorithmAssembler :=
  AlgorithmAssembler RectPackingM RectPackingLayoutPhases NodeId IntermediateProcessorStrategy

/-- `LayoutProcessorConfiguration<RectPackingLayoutPhases, ElkNode>`. -/
abbrev RectPackingProcessorConfiguration :=
  LayoutProcessorConfiguration RectPackingLayoutPhases IntermediateProcessorStrategy

end Elk.Alg.RectPacking
