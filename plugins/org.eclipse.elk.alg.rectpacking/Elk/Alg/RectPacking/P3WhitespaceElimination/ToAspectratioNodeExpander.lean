import Elk.Alg.RectPacking.P3WhitespaceElimination.EqualWhitespaceEliminator
/-!
# `org.eclipse.elk.alg.rectpacking.p3whitespaceelimination.ToAspectratioNodeExpander`

Port of `p3whitespaceelimination/to_aspectratio_node_expander.rs` (elk-rs): grows the drawing
width (if the drawing is narrower than the desired aspect ratio) or the additional height (if it
is wider) to reach the aspect ratio, then runs the `EqualWhitespaceEliminator` with the same
progress monitor (its second `begin` is ignored).
-/
namespace Elk.Alg.RectPacking.P3WhitespaceElimination

open Elk.Graph Elk.Core.Util Elk.Core.Alg
open Elk.Alg.RectPacking Elk.Alg.RectPacking.Util Elk.Alg.RectPacking.Options

namespace ToAspectratioNodeExpander

/-- `process(graph, progress_monitor)` (Rust `run`). -/
def run (graph : NodeId) (monitor : ProgressMonitor) : RectPackingM Unit := do
  let _ ← monitor.begin "To Aspect Ratio Whitesapce Eliminator" 1.0
  let props := (← ElkM.getNode graph).props
  let mut width := props.getD InternalProperties.DRAWING_WIDTH 0.0
  let mut height := props.getD InternalProperties.DRAWING_HEIGHT 0.0
  let desiredAspectRatio := props.getD RectPackingOptions.ASPECT_RATIO 1.0
  let mut additionalHeight := props.getD InternalProperties.ADDITIONAL_HEIGHT 0.0
  let aspectRatio := if height.abs > Float.epsilon then width / height else 0.0
  if aspectRatio < desiredAspectRatio then
    width := height * desiredAspectRatio
    ElkM.setNodeProp graph InternalProperties.DRAWING_WIDTH width
  else
    additionalHeight := additionalHeight + ((width / desiredAspectRatio) - height)
    height := height + additionalHeight
    ElkM.setNodeProp graph InternalProperties.ADDITIONAL_HEIGHT additionalHeight
    ElkM.setNodeProp graph InternalProperties.DRAWING_HEIGHT height
  EqualWhitespaceEliminator.run graph monitor
  monitor.done

/-- `ToAspectratioNodeExpander` as an `ILayoutPhase` (no processor configuration). -/
def phase : RectPackingPhase :=
  { name := "ToAspectratioNodeExpander"
    process := fun graph monitor => run graph monitor
    getLayoutProcessorConfiguration := fun _ => pure none }

end ToAspectratioNodeExpander

end Elk.Alg.RectPacking.P3WhitespaceElimination
