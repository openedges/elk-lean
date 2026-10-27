import Elk.Graph.Enum
/-!
# `org.eclipse.elk.alg.rectpacking.p3whitespaceelimination.WhiteSpaceEliminationStrategy`

Port of the enumeration of `p3whitespaceelimination/white_space_elimination_strategy.rs`
(elk-rs), needed by the options. The factory half (`create_phase`: `EqualWhitespaceEliminator`,
`ToAspectratioNodeExpander`, the no-op `EqualWhitespaceEliminator`) belongs to the whitespace
elimination port (F8b).
-/
namespace Elk.Alg.RectPacking.P3WhitespaceElimination

/-- `WhiteSpaceEliminationStrategy`: `EQUAL_BETWEEN_STRUCTURES`, `TO_ASPECT_RATIO`, `NONE`
(default). -/
elk_enum WhiteSpaceEliminationStrategy := equalBetweenStructures toAspectRatio none

end Elk.Alg.RectPacking.P3WhitespaceElimination
