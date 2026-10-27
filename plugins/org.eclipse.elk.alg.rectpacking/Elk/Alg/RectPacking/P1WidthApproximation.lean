import Elk.Alg.RectPacking.P1WidthApproximation.WidthApproximationStrategy
import Elk.Alg.RectPacking.P1WidthApproximation.BestCandidateFilter
import Elk.Alg.RectPacking.P1WidthApproximation.AreaFilter
import Elk.Alg.RectPacking.P1WidthApproximation.AspectRatioFilter
import Elk.Alg.RectPacking.P1WidthApproximation.ScaleMeasureFilter
import Elk.Alg.RectPacking.P1WidthApproximation.Calculations
import Elk.Alg.RectPacking.P1WidthApproximation.AreaApproximation
import Elk.Alg.RectPacking.P1WidthApproximation.GreedyWidthApproximator
import Elk.Alg.RectPacking.P1WidthApproximation.TargetWidthWidthApproximator
/-!
# Width approximation package (`org.eclipse.elk.alg.rectpacking.p1widthapproximation`)

Aggregates the phase-1 modules and defines the factory half of `WidthApproximationStrategy`
(Rust `impl ILayoutPhaseFactory for WidthApproximationStrategy`), which cannot live next to the
enumeration because the options depend on the enumeration and the approximators on the options.
-/
namespace Elk.Alg.RectPacking.P1WidthApproximation

open Elk.Core.Alg Elk.Alg.RectPacking

namespace WidthApproximationStrategy

/-- `create_phase()`: `GREEDY` → `GreedyWidthApproximator`, `TARGET_WIDTH` →
`TargetWidthWidthApproximator`. -/
def createPhase : WidthApproximationStrategy → RectPackingPhase
  | .greedy => GreedyWidthApproximator.phase
  | .targetWidth => TargetWidthWidthApproximator.phase

/-- `WidthApproximationStrategy` as `ILayoutPhaseFactory` (cached by enum identity). -/
def phaseFactory (s : WidthApproximationStrategy) : RectPackingPhaseFactory :=
  LayoutPhaseFactory.ofEnum "WidthApproximationStrategy" s (pure (createPhase s))

end WidthApproximationStrategy

end Elk.Alg.RectPacking.P1WidthApproximation
