import Elk.Alg.Layered.P4Nodes.SimpleNodePlacer
import Elk.Alg.Layered.P4Nodes.InteractiveNodePlacer
import Elk.Alg.Layered.P4Nodes.LinearSegmentsNodePlacer
import Elk.Alg.Layered.P4Nodes.NetworkSimplexPlacer
/-! Node placers of `org.eclipse.elk.alg.layered.p4nodes` other than Brandes-Köpf: `SimpleNodePlacer`,
`InteractiveNodePlacer`, `LinearSegmentsNodePlacer` and `NetworkSimplexPlacer`. Each module registers its
phase for the corresponding `NodePlacementStrategy` constant (`LayeredPhases.registerPhase .p4NodePlacement`).
The package aggregator `Elk.Alg.Layered.P4Nodes` imports this module. -/
