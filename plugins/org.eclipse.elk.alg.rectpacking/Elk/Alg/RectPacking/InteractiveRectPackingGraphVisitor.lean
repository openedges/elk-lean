import Elk.Graph
import Elk.Core.Options
import Elk.Core.Util.GraphElementVisitor
import Elk.Alg.RectPacking.Options.RectPackingOptions
/-!
# `org.eclipse.elk.alg.rectpacking.InteractiveRectPackingGraphVisitor`

Port of `interactive_rect_packing_graph_visitor.rs` (elk-rs): a graph element visitor that
switches every node using the rectangle packing (its `ALGORITHM` is a suffix of
`org.eclipse.elk.rectpacking`) and having children to interactive mode (`INTERACTIVE := true`).
Not used by the layout itself (as in Rust and Java).
-/
namespace Elk.Alg.RectPacking

open Elk.Graph Elk.Core.Options Elk.Core.Util Elk.Alg.RectPacking.Options

namespace InteractiveRectPackingGraphVisitor

/-- `set_interactive_options(root)`. -/
def setInteractiveOptions (root : NodeId) : ElkM Unit := do
  let n ← ElkM.getNode root
  if let some algorithm := n.props.get CoreOptions.ALGORITHM then
    if RectPackingOptions.ALGORITHM_ID.endsWith algorithm && !n.children.isEmpty then
      ElkM.setNodeProp root RectPackingOptions.INTERACTIVE true

/-- The visitor (`IGraphElementVisitor::visit`: nodes only). -/
def visitor : GraphElementVisitor :=
  GraphElementVisitor.ofFn fun
    | .node n => setInteractiveOptions n
    | _ => pure ()

end InteractiveRectPackingGraphVisitor

end Elk.Alg.RectPacking
