import Elk.Core.Alg.AlgorithmAssembler
import Elk.Alg.MrTree.Graph.TArena
import Elk.Alg.MrTree.Intermediate.IntermediateProcessorStrategy
/-!
# `org.eclipse.elk.alg.mrtree.TreeLayoutPhases`

Port of the phase enumeration of `tree_layout_phases.rs` (elk-rs), plus the phase and assembler type
abbreviations of the tree layout. The phase factory (`create_phase`: `DFSTreeifyer`, `NodeOrderer`,
`NodePlacer`, `EdgeRouter`) belongs to the phase packages ported separately.
-/
namespace Elk.Alg.MrTree

open Elk.Core.Alg Elk.Alg.MrTree.Graph Elk.Alg.MrTree.Intermediate

/-- `org.eclipse.elk.alg.mrtree.TreeLayoutPhases`: the four phases of the tree layout. -/
elk_enum TreeLayoutPhases := p1Treeification p2NodeOrdering p3NodePlacement p4EdgeRouting

/-- `ILayoutPhase<TreeLayoutPhases, TGraph>`. -/
abbrev TreePhase := LayoutPhase MrTreeM TreeLayoutPhases TGraphId IntermediateProcessorStrategy

/-- `ILayoutPhaseFactory<TreeLayoutPhases, TGraph>`. -/
abbrev TreePhaseFactory := LayoutPhaseFactory MrTreeM TreeLayoutPhases TGraphId IntermediateProcessorStrategy

/-- `LayoutProcessorConfiguration<TreeLayoutPhases, TGraph>`. -/
abbrev TreeProcessorConfiguration := LayoutProcessorConfiguration TreeLayoutPhases IntermediateProcessorStrategy

/-- `AlgorithmAssembler<TreeLayoutPhases, TGraph>`. -/
abbrev TreeAssembler := AlgorithmAssembler MrTreeM TreeLayoutPhases TGraphId IntermediateProcessorStrategy

/-- `AlgorithmAssembler::create()` with the intermediate processor factory of the tree layout. -/
def TreeAssembler.create : IO TreeAssembler := AlgorithmAssembler.create IntermediateProcessorStrategy.factory

end Elk.Alg.MrTree
