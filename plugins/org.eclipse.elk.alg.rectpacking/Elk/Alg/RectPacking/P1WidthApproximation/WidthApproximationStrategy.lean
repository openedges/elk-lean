import Elk.Graph.Enum
/-!
# `org.eclipse.elk.alg.rectpacking.p1widthapproximation.WidthApproximationStrategy`

Port of `p1widthapproximation/width_approximation_strategy.rs` (elk-rs). Only the enumeration is
defined here (the options depend on it); the factory half of the Rust enum
(`ILayoutPhaseFactory::create_phase`) is `WidthApproximationStrategy.phaseFactory` in the package
module `Elk.Alg.RectPacking.P1WidthApproximation`, because it depends on the approximators, which
in turn depend on the options.
-/
namespace Elk.Alg.RectPacking.P1WidthApproximation

/-- `WidthApproximationStrategy`: `GREEDY` (default), `TARGET_WIDTH`. -/
elk_enum WidthApproximationStrategy := greedy targetWidth

end Elk.Alg.RectPacking.P1WidthApproximation
