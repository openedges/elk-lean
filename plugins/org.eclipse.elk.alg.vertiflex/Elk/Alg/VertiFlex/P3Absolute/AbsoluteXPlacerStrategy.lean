import Elk.Alg.VertiFlex.P3Absolute.AbsoluteXPlacer
/-!
# `org.eclipse.elk.alg.vertiflex.p3absolute.AbsoluteXPlacerStrategy`

Port of `absolute_x_placer_strategy.rs` (elk-rs): the absolute x placement (phase 3)
implementations and the `ILayoutPhaseFactory` that creates them.
-/
namespace Elk.Alg.VertiFlex.P3Absolute

open Elk.Core.Alg

/-- `AbsoluteXPlacerStrategy`. -/
elk_enum AbsoluteXPlacerStrategy := absoluteXPlacing

namespace AbsoluteXPlacerStrategy

/-- `AbsoluteXPlacerStrategy` as `ILayoutPhaseFactory` (`create_phase`). -/
def phaseFactory (s : AbsoluteXPlacerStrategy) : VertiFlexPhaseFactory :=
  LayoutPhaseFactory.ofEnum "AbsoluteXPlacerStrategy" s
    (match s with | .absoluteXPlacing => pure AbsoluteXPlacer.phase)

end AbsoluteXPlacerStrategy

end Elk.Alg.VertiFlex.P3Absolute
