import Elk.Graph.Enum
/-!
# `org.eclipse.elk.alg.spore.options.TreeConstructionStrategy`

Port of `options/tree_construction_strategy.rs` (elk-rs) and `TreeConstructionStrategy.java`.

The Java enum implements `ILayoutPhaseFactory` (`create()` builds the phase of
`p2processingorder`); that factory is not part of this module: see `Elk.Alg.Spore.PhaseFactories`.
-/
namespace Elk.Alg.Spore.Options

/-- `org.eclipse.elk.alg.spore.options.TreeConstructionStrategy`: whether a minimum spanning tree
or a maximum spanning tree should be constructed. -/
elk_enum TreeConstructionStrategy := minimumSpanningTree maximumSpanningTree

end Elk.Alg.Spore.Options
