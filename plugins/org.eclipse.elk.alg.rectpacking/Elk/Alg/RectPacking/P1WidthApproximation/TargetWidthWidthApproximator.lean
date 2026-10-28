import Elk.Alg.RectPacking.RectPackingLayoutPhases
import Elk.Alg.RectPacking.Options.RectPackingOptions
import Elk.Alg.RectPacking.Options.InternalProperties
/-!
# `org.eclipse.elk.alg.rectpacking.p1widthapproximation.TargetWidthWidthApproximator`

Port of `p1widthapproximation/target_width_width_approximator.rs` (elk-rs): copies
`WIDTH_APPROXIMATION_TARGET_WIDTH` to `TARGET_WIDTH`.

Java checks `hasProperty` and throws an `UnsupportedConfigurationException` when the option is
unset (agent OPT; elk-rs reads it with `get_property`, which yields the property default `-1`, so
its error is unreachable and `TARGET_WIDTH` becomes `-1`; elk-lean followed that before).
-/
namespace Elk.Alg.RectPacking.P1WidthApproximation

open Elk.Graph Elk.Core.Util Elk.Core.Alg
open Elk.Alg.RectPacking Elk.Alg.RectPacking.Util Elk.Alg.RectPacking.Options

namespace TargetWidthWidthApproximator

/-- `process(graph, progress_monitor)` on the `ElkGraph`. -/
def run (graph : NodeId) (monitor : ProgressMonitor) : ElkM Unit := do
  let _ ← monitor.begin "Target Width Setter" 1.0
  let props := (← ElkM.getNode graph).props
  match props.get RectPackingOptions.WIDTH_APPROXIMATION_TARGET_WIDTH with
  | some targetWidth =>
    if !props.has RectPackingOptions.WIDTH_APPROXIMATION_TARGET_WIDTH then
      throw (IO.userError "org.eclipse.elk.core.UnsupportedConfigurationException: A target width has to be set if the TargetWidthWidthApproximator should be used.")
    ElkM.setNodeProp graph InternalProperties.TARGET_WIDTH targetWidth
  | none =>
    throw (IO.userError "org.eclipse.elk.core.UnsupportedConfigurationException: A target width has to be set if the TargetWidthWidthApproximator should be used.")
  monitor.done

/-- `TargetWidthWidthApproximator` as an `ILayoutPhase` (no processor configuration). -/
def phase : RectPackingPhase :=
  { name := "TargetWidthWidthApproximator"
    process := fun graph monitor => run graph monitor
    getLayoutProcessorConfiguration := fun _ => pure none }

end TargetWidthWidthApproximator

end Elk.Alg.RectPacking.P1WidthApproximation
