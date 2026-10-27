import Elk.Alg.VertiFlex.P4EdgeRouting.StraightEdgeRouter
import Elk.Alg.VertiFlex.P4EdgeRouting.BendEdgeRouter
/-!
# `org.eclipse.elk.alg.vertiflex.p4edgerouting.EdgerouterStrategy`

Port of `edgerouter_strategy.rs` (elk-rs): the edge routing (phase 4) implementations and the
`ILayoutPhaseFactory` that creates them.
-/
namespace Elk.Alg.VertiFlex.P4EdgeRouting

open Elk.Core.Alg

/-- `EdgerouterStrategy`: `DIRECT_ROUTING` (straight) or `BEND_ROUTING`. -/
elk_enum EdgerouterStrategy := directRouting bendRouting

namespace EdgerouterStrategy

/-- `EdgerouterStrategy` as `ILayoutPhaseFactory` (`create_phase`). -/
def phaseFactory (s : EdgerouterStrategy) : VertiFlexPhaseFactory :=
  LayoutPhaseFactory.ofEnum "EdgerouterStrategy" s
    (match s with
      | .directRouting => pure StraightEdgeRouter.phase
      | .bendRouting => pure BendEdgeRouter.phase)

end EdgerouterStrategy

end Elk.Alg.VertiFlex.P4EdgeRouting
