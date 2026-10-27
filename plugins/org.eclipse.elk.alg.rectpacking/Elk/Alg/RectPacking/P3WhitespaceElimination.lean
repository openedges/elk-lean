import Elk.Alg.RectPacking.P3WhitespaceElimination.WhiteSpaceEliminationStrategy
import Elk.Alg.RectPacking.P3WhitespaceElimination.RectangleExpansion
import Elk.Alg.RectPacking.P3WhitespaceElimination.EqualWhitespaceEliminator
import Elk.Alg.RectPacking.P3WhitespaceElimination.ToAspectratioNodeExpander
/-!
# Whitespace elimination package (`org.eclipse.elk.alg.rectpacking.p3whitespaceelimination`)

Aggregates the phase-3 modules and defines the factory half of `WhiteSpaceEliminationStrategy`
(Rust `impl ILayoutPhaseFactory for WhiteSpaceEliminationStrategy`), which cannot live next to the
enumeration because the options depend on the enumeration and the phases on the options.
-/
namespace Elk.Alg.RectPacking.P3WhitespaceElimination

open Elk.Core.Alg Elk.Alg.RectPacking

namespace WhiteSpaceEliminationStrategy

/-- `create_phase()`: `EQUAL_BETWEEN_STRUCTURES` → `EqualWhitespaceEliminator`,
`TO_ASPECT_RATIO` → `ToAspectratioNodeExpander`, `NONE` → the no-op eliminator. -/
def createPhase : WhiteSpaceEliminationStrategy → RectPackingPhase
  | .equalBetweenStructures => EqualWhitespaceEliminator.phase
  | .toAspectRatio => ToAspectratioNodeExpander.phase
  | .none => EqualWhitespaceEliminator.noop

/-- `WhiteSpaceEliminationStrategy` as `ILayoutPhaseFactory` (cached by enum identity). -/
def phaseFactory (s : WhiteSpaceEliminationStrategy) : RectPackingPhaseFactory :=
  LayoutPhaseFactory.ofEnum "WhiteSpaceEliminationStrategy" s (pure (createPhase s))

end WhiteSpaceEliminationStrategy

end Elk.Alg.RectPacking.P3WhitespaceElimination
