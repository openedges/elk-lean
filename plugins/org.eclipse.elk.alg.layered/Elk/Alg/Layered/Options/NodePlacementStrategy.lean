import Elk.Graph.Enum
/-!
# `org.eclipse.elk.alg.layered.options.NodePlacementStrategy`

Port of `options/node_placement_strategy.rs` (elk-rs) and `NodePlacementStrategy.java`.

The Java enum implements `ILayoutPhaseFactory` (`create()` builds the node placer (`p4nodes`));
that factory is not part of this module: the phase package adds `createPhase` once
the phase implementations are ported.
-/
namespace Elk.Alg.Layered.Options

/-- `org.eclipse.elk.alg.layered.options.NodePlacementStrategy`: Definition of the available node
placement strategies for the layered layout approach. -/
elk_enum NodePlacementStrategy := simple interactive linearSegments brandesKoepf networkSimplex

end Elk.Alg.Layered.Options
