import Elk.Graph.Enum
/-!
# `org.eclipse.elk.alg.layered.options.EdgeStraighteningStrategy`

Port of `options/edge_straightening_strategy.rs` (elk-rs) and `EdgeStraighteningStrategy.java`.
-/
namespace Elk.Alg.Layered.Options

/-- `org.eclipse.elk.alg.layered.options.EdgeStraighteningStrategy`: Specifies how the compaction
step of the `BKNodePlacer` should be executed. -/
elk_enum EdgeStraighteningStrategy := none improveStraightness

end Elk.Alg.Layered.Options
