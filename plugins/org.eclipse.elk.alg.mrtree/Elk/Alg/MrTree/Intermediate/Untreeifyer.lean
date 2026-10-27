import Elk.Alg.MrTree.Graph.TArena
/-!
# `org.eclipse.elk.alg.mrtree.intermediate.Untreeifyer`

Port of `intermediate/untreeifyer.rs` (elk-rs): re-inserts the edges removed by the treeifyer
(`REMOVABLE_EDGES` of the graph, in list order) into the outgoing edges of their source and the
incoming edges of their target (`add_outgoing`/`add_incoming`, which ignore edges already present).
-/
namespace Elk.Alg.MrTree.Intermediate

open Elk.Core.Util Elk.Alg.MrTree.Graph

namespace Untreeifyer

/-- `Untreeifyer::process`. -/
def process (graph : TGraphId) (monitor : ProgressMonitor) : MrTreeM Unit := do
  discard <| monitor.begin "Untreeify" 1.0
  for edge in (← MrTreeM.getGraph graph).internal.removableEdges do
    let e ← MrTreeM.getEdge edge
    if let some source := e.source then MrTreeM.addOutgoing source edge
    if let some target := e.target then MrTreeM.addIncoming target edge
  monitor.done

/-- The `Untreeifyer` (`IntermediateProcessorStrategy.DETREEIFYING_PROC`). -/
def processor : TreeProcessor := { name := "Untreeifyer", process }

end Untreeifyer

end Elk.Alg.MrTree.Intermediate
