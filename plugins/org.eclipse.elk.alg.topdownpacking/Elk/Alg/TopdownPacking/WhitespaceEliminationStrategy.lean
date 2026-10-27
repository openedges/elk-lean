import Elk.Graph.Enum
/-!
# `org.eclipse.elk.alg.topdownpacking.WhitespaceEliminationStrategy`

Port of `whitespace_elimination_strategy.rs` (elk-rs). The phase factory half lives in
`Elk.Alg.TopdownPacking.TopdownpackingLayoutProvider`.
-/
namespace Elk.Alg.TopdownPacking

/-- `WhitespaceEliminationStrategy`: the whitespace elimination (phase 2) implementations. -/
elk_enum WhitespaceEliminationStrategy := bottomRowEqualWhitespaceEliminator

end Elk.Alg.TopdownPacking
