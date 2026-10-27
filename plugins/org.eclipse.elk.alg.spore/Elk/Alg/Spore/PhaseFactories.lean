import Elk.Alg.Spore.Options
import Elk.Alg.Spore.P1Structure.DelaunayTriangulationPhase
import Elk.Alg.Spore.P2ProcessingOrder.MaxSTPhase
import Elk.Alg.Spore.P3Execution.GrowTreePhase
import Elk.Alg.Spore.P3Execution.ShrinkTreeCompactionPhase
/-!
# `ILayoutPhaseFactory` of the SPOrE strategy enumerations

In Java and elk-rs the strategy enumerations of the options package (`StructureExtractionStrategy`,
`TreeConstructionStrategy`, `CompactionStrategy`, `OverlapRemovalStrategy`) implement
`ILayoutPhaseFactory<SPOrEPhases, Graph>` (`create_phase`/`enum_ordinal`). The options package
cannot import the phases here (the phases import `Graph`, which imports the enumerations), so the
factories are defined in this module. The factory key is the Java enum class name and the ordinal
(`enum_type_id`, `enum_ordinal`), used by the assembler's phase cache.
-/
namespace Elk.Alg.Spore.Options

open Elk Elk.Core.Alg Elk.Alg.Spore

/-- `StructureExtractionStrategy.create()`. -/
def StructureExtractionStrategy.factory (s : StructureExtractionStrategy) : SporePhaseFactory :=
  LayoutPhaseFactory.ofEnum "StructureExtractionStrategy" s
    (match s with
     | .delaunayTriangulation => pure P1Structure.DelaunayTriangulationPhase.phase)

/-- `TreeConstructionStrategy.create()`. -/
def TreeConstructionStrategy.factory (s : TreeConstructionStrategy) : SporePhaseFactory :=
  LayoutPhaseFactory.ofEnum "TreeConstructionStrategy" s
    (match s with
     | .minimumSpanningTree => pure P2ProcessingOrder.MinSTPhase.phase
     | .maximumSpanningTree => pure P2ProcessingOrder.MaxSTPhase.phase)

/-- `CompactionStrategy.create()`. -/
def CompactionStrategy.factory (s : CompactionStrategy) : SporePhaseFactory :=
  LayoutPhaseFactory.ofEnum "CompactionStrategy" s
    (match s with
     | .depthFirst => pure P3Execution.ShrinkTreeCompactionPhase.phase)

/-- `OverlapRemovalStrategy.create()`. -/
def OverlapRemovalStrategy.factory (s : OverlapRemovalStrategy) : SporePhaseFactory :=
  LayoutPhaseFactory.ofEnum "OverlapRemovalStrategy" s
    (match s with
     | .growTree => pure P3Execution.GrowTreePhase.phase)

end Elk.Alg.Spore.Options
