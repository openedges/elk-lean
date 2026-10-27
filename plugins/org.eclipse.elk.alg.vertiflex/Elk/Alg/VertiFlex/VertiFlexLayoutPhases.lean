import Elk.Core.Alg
import Elk.Alg.VertiFlex.InternalProperties
/-!
# `org.eclipse.elk.alg.vertiflex.VertiFlexLayoutPhases`

Port of `vertiflex_layout_phases.rs` (elk-rs) plus the phase type abbreviations of the
`AlgorithmAssembler<VertiFlexLayoutPhases, ElkNodeRef>`: the graph type `G` is the `NodeId` of
the layout graph, the monad is `VertiFlexM`.
-/
namespace Elk.Alg.VertiFlex

open Elk.Graph Elk.Core.Alg

/-- `VertiFlexLayoutPhases`: the four phases of the algorithm. -/
elk_enum VertiFlexLayoutPhases := p1NodeYPlacement p2NodeRelativePlacement p3NodeAbsolutePlacement p4EdgeRouting

/-- Factory enumeration `F` of the assembler. VertiFlex has no intermediate processors, so the
enumeration only needs a placeholder constant (never requested by a phase). -/
elk_enum VertiFlexProcessors := noProcessor

/-- `ILayoutPhase<VertiFlexLayoutPhases, ElkNodeRef>`. -/
abbrev VertiFlexPhase := LayoutPhase VertiFlexM VertiFlexLayoutPhases NodeId VertiFlexProcessors

/-- `ILayoutPhaseFactory<VertiFlexLayoutPhases, ElkNodeRef>`. -/
abbrev VertiFlexPhaseFactory := LayoutPhaseFactory VertiFlexM VertiFlexLayoutPhases NodeId VertiFlexProcessors

end Elk.Alg.VertiFlex
