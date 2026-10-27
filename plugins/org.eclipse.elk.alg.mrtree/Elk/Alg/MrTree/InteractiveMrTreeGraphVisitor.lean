import Elk.Graph
import Elk.Core.Options
import Elk.Core.Util.GraphElementVisitor
import Elk.Alg.MrTree.Options.MrTreeOptions
/-!
# `org.eclipse.elk.alg.mrtree.InteractiveMrTreeGraphVisitor`

Port of `interactive_mrtree_graph_visitor.rs` (elk-rs): a graph element visitor that switches every
node using the tree layout (its `ALGORITHM` is a suffix of `org.eclipse.elk.mrtree`) and having
children to interactive mode: `INTERACTIVE := true`, `WEIGHTING := CONSTRAINT`.
-/
namespace Elk.Alg.MrTree

open Elk.Graph Elk.Core.Options Elk.Core.Util Elk.Alg.MrTree.Options

namespace InteractiveMrTreeGraphVisitor

/-- `set_interactive_options(root)`. -/
def setInteractiveOptions (root : NodeId) : ElkM Unit := do
  let n ← ElkM.getNode root
  if let some algorithm := n.props.get CoreOptions.ALGORITHM then
    if MrTreeOptions.ALGORITHM_ID.endsWith algorithm && !n.children.isEmpty then
      ElkM.setNodeProp root CoreOptions.INTERACTIVE true
      ElkM.setNodeProp root MrTreeOptions.WEIGHTING OrderWeighting.constraint

/-- The visitor (`IGraphElementVisitor::visit`: nodes only). -/
def visitor : GraphElementVisitor :=
  GraphElementVisitor.ofFn fun
    | .node n => setInteractiveOptions n
    | _ => pure ()

end InteractiveMrTreeGraphVisitor

end Elk.Alg.MrTree
