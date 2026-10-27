import Elk.Alg.VertiFlex.P2Relative.RelativeXPlacer
/-!
# `org.eclipse.elk.alg.vertiflex.p2relative.RelativeXPlacerStrategy`

Port of `relative_x_placer_strategy.rs` (elk-rs): the relative x placement (phase 2)
implementations and the `ILayoutPhaseFactory` that creates them.
-/
namespace Elk.Alg.VertiFlex.P2Relative

open Elk.Core.Alg

/-- `RelativeXPlacerStrategy`. -/
elk_enum RelativeXPlacerStrategy := simpleXPlacing

namespace RelativeXPlacerStrategy

/-- `RelativeXPlacerStrategy` as `ILayoutPhaseFactory` (`create_phase`). -/
def phaseFactory (s : RelativeXPlacerStrategy) : VertiFlexPhaseFactory :=
  LayoutPhaseFactory.ofEnum "RelativeXPlacerStrategy" s
    (match s with | .simpleXPlacing => pure RelativeXPlacer.phase)

end RelativeXPlacerStrategy

end Elk.Alg.VertiFlex.P2Relative
