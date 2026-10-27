import Elk.Alg.MrTree.Graph.TArena
import Elk.Alg.MrTree.Options.MrTreeOptions
/-!
# `org.eclipse.elk.alg.mrtree.intermediate.DirectionProcessor`

Port of `intermediate/direction_processor.rs` (elk-rs): unless the graph's `DIRECTION`
(`unwrap_or(Undefined)`) is `DOWN`, the integer coordinates `(XCOOR, YCOOR)` of every node are
transformed: `UP` negates y, `RIGHT` swaps x and y, `LEFT` swaps and negates the new x; `UNDEFINED`
leaves them unchanged.
-/
namespace Elk.Alg.MrTree.Intermediate

open Elk.Core.Util Elk.Core.Options Elk.Alg.MrTree.Graph Elk.Alg.MrTree.Options

namespace DirectionProcessor

/-- The coordinate transformation of one node. -/
def transform (direction : Direction) (x y : Int) : Int × Int :=
  match direction with
  | .up => (x, -y)
  | .right => (y, x)
  | .left => (-y, x)
  | _ => (x, y)

/-- `DirectionProcessor::process`. -/
def process (graph : TGraphId) (monitor : ProgressMonitor) : MrTreeM Unit := do
  discard <| monitor.begin "Process directions" 1.0
  let g ← MrTreeM.getGraph graph
  let direction := (g.props.get MrTreeOptions.DIRECTION).getD .undefined
  if direction != .down then
    for node in g.nodes do
      MrTreeM.modifyNode node fun n =>
        let (x, y) := transform direction n.internal.xcoor n.internal.ycoor
        { n with internal.xcoor := x, internal.ycoor := y }
  monitor.done

/-- The `DirectionProcessor` (`IntermediateProcessorStrategy.DIRECTION_PROC`). -/
def processor : TreeProcessor := { name := "DirectionProcessor", process }

end DirectionProcessor

end Elk.Alg.MrTree.Intermediate
