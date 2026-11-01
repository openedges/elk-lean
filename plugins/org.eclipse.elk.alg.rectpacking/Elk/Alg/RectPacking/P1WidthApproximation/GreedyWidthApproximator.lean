import Elk.Core.Data
import Elk.Alg.RectPacking.RectPackingLayoutPhases
import Elk.Alg.RectPacking.Options.RectPackingOptions
import Elk.Alg.RectPacking.Options.InternalProperties
import Elk.Alg.RectPacking.P1WidthApproximation.AreaApproximation
import Elk.Core.Util.FloatConst
open Elk.Core.Util.FloatConst
/-!
# `org.eclipse.elk.alg.rectpacking.p1widthapproximation.GreedyWidthApproximator`

Port of `p1widthapproximation/greedy_width_approximator.rs` (elk-rs): runs the greedy
`AreaApproximation` on the children (after moving them to `(0, 0)`) and stores the resulting
drawing width as `TARGET_WIDTH`.

Java reads `ASPECT_RATIO`, `PADDING` and `SPACING_NODE_NODE` through the redeclared
`RectPackingOptions` constants (rectangle packing defaults 1.3, 15, 15). elk-rs falls back to the
algorithm default of the metadata registry for the aspect ratio and relies on the provider storing
the other two on the graph (followed before agent OPT).
-/
/-! Float literals as global constants (FL): inside branches, loops and specialised code the compiler
shares a literal's `Nat`/`Bool` arguments with unrelated variables (CSE) and then parses it on every
evaluation (`FastFloat.ofScientificImpl`); a top-level constant is a load (PLAN §7.1 items 17, 22). -/
private def fl1p3 : Float := 1.3

namespace Elk.Alg.RectPacking.P1WidthApproximation

open Elk.Graph Elk.Core.Util Elk.Core.Math Elk.Core.Data Elk.Core.Alg
open Elk.Alg.RectPacking Elk.Alg.RectPacking.Util Elk.Alg.RectPacking.Options

namespace GreedyWidthApproximator

/-- `process(graph, progress_monitor)` on the `ElkGraph`. -/
def run (graph : NodeId) (monitor : ProgressMonitor) : ElkM Unit := do
  let _ ← monitor.begin "Greedy Width Approximator" fl1p0
  let props := (← ElkM.getNode graph).props
  let aspectRatio := props.getD RectPackingOptions.ASPECT_RATIO fl1p3
  let padding := props.getD RectPackingOptions.PADDING {}
  let goal := props.getD RectPackingOptions.WIDTH_APPROXIMATION_OPTIMIZATION_GOAL .maxScaleDriven
  let lastPlaceShift := props.getD RectPackingOptions.WIDTH_APPROXIMATION_LAST_PLACE_SHIFT true
  let nodeNodeSpacing := props.getD RectPackingOptions.SPACING_NODE_NODE fl0p0
  let rectangles := (← ElkM.getNode graph).children
  DrawingUtil.resetCoordinates rectangles
  let firstIt := AreaApproximation.new aspectRatio goal lastPlaceShift
  let drawing ← firstIt.approxBoundingBox rectangles nodeNodeSpacing padding
  ElkM.setNodeProp graph InternalProperties.TARGET_WIDTH drawing.drawingWidth
  monitor.done

/-- `GreedyWidthApproximator` as an `ILayoutPhase` (no processor configuration). -/
def phase : RectPackingPhase :=
  { name := "GreedyWidthApproximator"
    process := fun graph monitor => run graph monitor
    getLayoutProcessorConfiguration := fun _ => pure none }

end GreedyWidthApproximator

end Elk.Alg.RectPacking.P1WidthApproximation
