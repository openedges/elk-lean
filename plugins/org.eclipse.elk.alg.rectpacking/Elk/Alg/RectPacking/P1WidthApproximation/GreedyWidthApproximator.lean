import Elk.Core.Data
import Elk.Alg.RectPacking.RectPackingLayoutPhases
import Elk.Alg.RectPacking.Options.RectPackingOptions
import Elk.Alg.RectPacking.Options.InternalProperties
import Elk.Alg.RectPacking.P1WidthApproximation.AreaApproximation
/-!
# `org.eclipse.elk.alg.rectpacking.p1widthapproximation.GreedyWidthApproximator`

Port of `p1widthapproximation/greedy_width_approximator.rs` (elk-rs): runs the greedy
`AreaApproximation` on the children (after moving them to `(0, 0)`) and stores the resulting
drawing width as `TARGET_WIDTH`.

Option lookup as in Rust: `ASPECT_RATIO` has no property default, so a missing value falls back
to the algorithm default registered by the metadata provider (1.3), then to 1.3; `PADDING`,
`SPACING_NODE_NODE` and the width approximation options use the property defaults (12, 20, …:
the provider sets the rectangle packing defaults 15/15/1.3 on the graph beforehand).
-/
/-! Float literals as global constants (FL): inside branches, loops and specialised code the compiler
shares a literal's `Nat`/`Bool` arguments with unrelated variables (CSE) and then parses it on every
evaluation (`FastFloat.ofScientificImpl`); a top-level constant is a load (PLAN §7.1 items 17, 22). -/
private def fl0p0 : Float := 0.0
private def fl1p0 : Float := 1.0
private def fl1p3 : Float := 1.3

namespace Elk.Alg.RectPacking.P1WidthApproximation

open Elk.Graph Elk.Core.Util Elk.Core.Math Elk.Core.Data Elk.Core.Alg
open Elk.Alg.RectPacking Elk.Alg.RectPacking.Util Elk.Alg.RectPacking.Options

namespace GreedyWidthApproximator

/-- `process(graph, progress_monitor)` on the `ElkGraph`. -/
def run (graph : NodeId) (monitor : ProgressMonitor) : ElkM Unit := do
  let _ ← monitor.begin "Greedy Width Approximator" fl1p0
  let props := (← ElkM.getNode graph).props
  let aspectRatio ← match props.get RectPackingOptions.ASPECT_RATIO with
    | some ar => pure ar
    | none => do
      let algo ← LayoutMetaDataService.getAlgorithmData RectPackingOptions.ALGORITHM_ID
      pure ((algo.bind fun a => a.defaultValue RectPackingOptions.ASPECT_RATIO).getD fl1p3)
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
