import Elk.Graph.Enum
/-!
# `org.eclipse.elk.alg.topdownpacking.TopdownPackingPhases`

Port of `topdown_packing_phases.rs` (elk-rs).
-/
namespace Elk.Alg.TopdownPacking

/-- `TopdownPackingPhases`: `P1_NODE_ARRANGEMENT`, `P2_WHITESPACE_ELIMINATION`. -/
elk_enum TopdownPackingPhases := p1NodeArrangement p2WhitespaceElimination

/-- Factory enumeration `F` of the `AlgorithmAssembler<TopdownPackingPhases, GridElkNode>`.
Java/Rust use a generic processor factory; topdown packing has no intermediate processors,
so the enumeration only needs a placeholder constant (never requested by a phase). -/
elk_enum TopdownPackingProcessors := noProcessor

end Elk.Alg.TopdownPacking
