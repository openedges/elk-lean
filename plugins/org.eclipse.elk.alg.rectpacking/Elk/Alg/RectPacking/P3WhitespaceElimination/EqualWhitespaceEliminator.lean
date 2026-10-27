import Elk.Alg.RectPacking.RectPackingLayoutPhases
import Elk.Alg.RectPacking.Options.InternalProperties
import Elk.Alg.RectPacking.Options.RectPackingOptions
import Elk.Alg.RectPacking.P3WhitespaceElimination.RectangleExpansion
/-!
# `org.eclipse.elk.alg.rectpacking.p3whitespaceelimination.EqualWhitespaceEliminator`

Port of `p3whitespaceelimination/equal_whitespace_eliminator.rs` (elk-rs): takes the rows stored
by the packing phase (`ROWS` / `RowsStorage`) and expands them to the drawing width and the
additional height (`RectangleExpansion`). Missing rows are an `UnsupportedConfigurationException`
(Rust `panic!`, e.g. after the `NONE` packing strategy).

Also holds the no-op phase of the `NONE` whitespace elimination strategy (Rust
`NoopWhitespaceEliminator`, created by `EqualWhitespaceEliminator::noop()`).
-/
namespace Elk.Alg.RectPacking.P3WhitespaceElimination

open Elk.Graph Elk.Core.Util Elk.Core.Alg
open Elk.Alg.RectPacking Elk.Alg.RectPacking.Util Elk.Alg.RectPacking.Options

namespace EqualWhitespaceEliminator

/-- The error of a graph without stored rows. -/
private def noRowsError : IO.Error :=
  IO.userError "org.eclipse.elk.core.UnsupportedConfigurationException: The graph does not contain rows."

/-- `process(graph, progress_monitor)`. -/
def run (graph : NodeId) (monitor : ProgressMonitor) : RectPackingM Unit := do
  let _ ← monitor.begin "Equal Whitespace Eliminator" 1.0
  match (← ElkM.getNode graph).props.get InternalProperties.ROWS with
  | some rowsKey =>
    match ← RowsStorage.takeRows rowsKey with
    | some rows =>
      let props := (← ElkM.getNode graph).props
      let drawingWidth := props.getD InternalProperties.DRAWING_WIDTH 0.0
      let additionalHeight := props.getD InternalProperties.ADDITIONAL_HEIGHT 0.0
      let nodeNodeSpacing := props.getD RectPackingOptions.SPACING_NODE_NODE 0.0
      RectangleExpansion.expand rows drawingWidth additionalHeight nodeNodeSpacing
    | none => throw noRowsError
  | none => throw noRowsError
  monitor.done

/-- `EqualWhitespaceEliminator` as an `ILayoutPhase` (no processor configuration). -/
def phase : RectPackingPhase :=
  { name := "EqualWhitespaceEliminator"
    process := fun graph monitor => run graph monitor
    getLayoutProcessorConfiguration := fun _ => pure none }

/-- `EqualWhitespaceEliminator::noop()`: the `NoopWhitespaceEliminator` phase (does nothing, not
even the progress monitor). -/
def noop : RectPackingPhase :=
  { name := "NoopWhitespaceEliminator"
    process := fun _ _ => pure ()
    getLayoutProcessorConfiguration := fun _ => pure none }

end EqualWhitespaceEliminator

end Elk.Alg.RectPacking.P3WhitespaceElimination
