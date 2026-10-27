import Elk.Graph.Enum
/-!
# `org.eclipse.elk.alg.topdownpacking.NodeArrangementStrategy`

Port of `node_arrangement_strategy.rs` (elk-rs). The factory half of the Rust enum
(`create_arranger`, `create_phase`) lives in `Elk.Alg.TopdownPacking.TopdownpackingLayoutProvider`
because it depends on the placer, which in turn depends on the options.
-/
namespace Elk.Alg.TopdownPacking

/-- `NodeArrangementStrategy`: the node arrangement (phase 1) implementations. -/
elk_enum NodeArrangementStrategy := leftRightTopDownNodePlacer

end Elk.Alg.TopdownPacking
