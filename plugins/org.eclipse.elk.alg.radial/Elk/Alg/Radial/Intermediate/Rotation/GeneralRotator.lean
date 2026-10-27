import Elk.Graph
import Elk.Core.Alg
import Elk.Core.Util.ProgressMonitor
import Elk.Alg.Radial.InternalProperties
import Elk.Alg.Radial.Intermediate.Rotation.IRadialRotator
import Elk.Alg.Radial.Intermediate.Rotation.AngleRotation
/-!
# `org.eclipse.elk.alg.radial.intermediate.rotation.GeneralRotator`

Port of `general_rotator.rs` (elk-rs): runs the `AngleRotation` (the only rotator).
-/
namespace Elk.Alg.Radial.Intermediate.Rotation

open Elk.Graph Elk.Core.Alg Elk.Core.Util

namespace GeneralRotator

/-- `process(graph, progress_monitor)`. -/
def process (graph : NodeId) (monitor : ProgressMonitor) : RadialM Unit := do
  let _ ← monitor.begin "General Rotator" 1.0
  if ← monitor.isLoggingEnabled then monitor.logGraph "Before"
  AngleRotation.rotator.rotate graph
  if ← monitor.isLoggingEnabled then monitor.logGraph "After"

/-- The processor (`ILayoutProcessor`). -/
def processor : LayoutProcessor RadialM NodeId :=
  { name := "GeneralRotator", process := process }

end GeneralRotator

end Elk.Alg.Radial.Intermediate.Rotation
