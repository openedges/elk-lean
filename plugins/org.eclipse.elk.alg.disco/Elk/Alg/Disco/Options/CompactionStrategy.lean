import Elk.Graph.Enum
/-!
# `org.eclipse.elk.alg.disco.options.CompactionStrategy`

Strategy for packing the connected components (elk-rs `options/compaction_strategy.rs`,
`CompactionStrategy.java`). `POLYOMINO` is the only constructor and the Rust `#[default]`.
-/
namespace Elk.Alg.Disco.Options

/-- `org.eclipse.elk.alg.disco.options.CompactionStrategy`: `POLYOMINO` uses the polyomino
packing of Freivalds et al. -/
elk_enum CompactionStrategy := polyomino

end Elk.Alg.Disco.Options
