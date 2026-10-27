import Elk.Alg.RectPacking.RectPackingLayoutPhases
import Elk.Alg.RectPacking.Options.RectPackingOptions
import Elk.Alg.RectPacking.Options.InternalProperties
/-!
# `org.eclipse.elk.alg.rectpacking.p1widthapproximation.TargetWidthWidthApproximator`

Port of `p1widthapproximation/target_width_width_approximator.rs` (elk-rs): copies
`WIDTH_APPROXIMATION_TARGET_WIDTH` to `TARGET_WIDTH`.

Rust deviation from Java kept: Rust reads the option with `get_property`, which yields the
property default `-1` when the option is unset, so the "target width has to be set" error is
unreachable and `TARGET_WIDTH` becomes `-1`. Java checks `hasProperty` and throws an
`UnsupportedConfigurationException`.
-/
namespace Elk.Alg.RectPacking.P1WidthApproximation

open Elk.Graph Elk.Core.Util Elk.Core.Alg
open Elk.Alg.RectPacking Elk.Alg.RectPacking.Util Elk.Alg.RectPacking.Options

namespace TargetWidthWidthApproximator

/-- `process(graph, progress_monitor)` on the `ElkGraph`. -/
def run (graph : NodeId) (monitor : ProgressMonitor) : ElkM Unit := do
  let _ ← monitor.begin "Target Width Setter" 1.0
  match (← ElkM.getNode graph).props.get RectPackingOptions.WIDTH_APPROXIMATION_TARGET_WIDTH with
  | some targetWidth => ElkM.setNodeProp graph InternalProperties.TARGET_WIDTH targetWidth
  | none =>
    -- unreachable: the option has a property default (Rust `panic!`)
    throw (IO.userError "org.eclipse.elk.core.UnsupportedConfigurationException: A target width has to be set if the TargetWidthWidthApproximator should be used.")
  monitor.done

/-- `TargetWidthWidthApproximator` as an `ILayoutPhase` (no processor configuration). -/
def phase : RectPackingPhase :=
  { name := "TargetWidthWidthApproximator"
    process := fun graph monitor => run graph monitor
    getLayoutProcessorConfiguration := fun _ => pure none }

end TargetWidthWidthApproximator

end Elk.Alg.RectPacking.P1WidthApproximation
