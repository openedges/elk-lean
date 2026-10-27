import Elk.Alg.VertiFlex.P1YPlacement.NodeYPlacer
/-!
# `org.eclipse.elk.alg.vertiflex.p1yplacement.NodeYPlacerStrategy`

Port of `node_y_placer_strategy.rs` (elk-rs): the y placement (phase 1) implementations and the
`ILayoutPhaseFactory` that creates them.
-/
namespace Elk.Alg.VertiFlex.P1YPlacement

open Elk.Core.Alg

/-- `NodeYPlacerStrategy`. -/
elk_enum NodeYPlacerStrategy := simpleYPlacing

namespace NodeYPlacerStrategy

/-- `NodeYPlacerStrategy` as `ILayoutPhaseFactory` (`create_phase`). -/
def phaseFactory (s : NodeYPlacerStrategy) : VertiFlexPhaseFactory :=
  LayoutPhaseFactory.ofEnum "NodeYPlacerStrategy" s
    (match s with | .simpleYPlacing => pure NodeYPlacer.phase)

end NodeYPlacerStrategy

end Elk.Alg.VertiFlex.P1YPlacement
