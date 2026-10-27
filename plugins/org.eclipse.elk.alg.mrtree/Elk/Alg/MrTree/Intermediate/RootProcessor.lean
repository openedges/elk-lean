import Elk.Alg.MrTree.Graph.TArena
/-!
# `org.eclipse.elk.alg.mrtree.intermediate.RootProcessor`

Port of `intermediate/root_processor.rs` (elk-rs): marks every node without incoming edges as a
`ROOT`. Without any root a `DUMMY_ROOT` node (id 0, `ROOT` and `DUMMY`) is added; with several roots a
`SUPER_ROOT` node (id 0, `ROOT` and `DUMMY`) is added and connected to each former root by a `DUMMY`
edge (`TNode::add_child`), whose `ROOT` flag is cleared. The new node is appended to the graph's node
list, the new edges to its edge list.
-/
namespace Elk.Alg.MrTree.Intermediate

open Elk.Core.Util Elk.Alg.MrTree.Graph

namespace RootProcessor

/-- `RootProcessor::process`. -/
def process (graph : TGraphId) (monitor : ProgressMonitor) : MrTreeM Unit := do
  discard <| monitor.begin "Find roots" 1.0
  let nodes := (← MrTreeM.getGraph graph).nodes
  let mut roots : Array TNodeId := #[]
  for node in nodes do
    if (← MrTreeM.getNode node).incomingEdges.isEmpty then
      MrTreeM.modifyNode node fun n => { n with internal.root := true }
      roots := roots.push node
  if roots.size == 0 then
    -- empty graph; create a dummy root
    let root ← MrTreeM.createNode 0 (some graph) (some "DUMMY_ROOT")
    MrTreeM.modifyNode root fun n => { n with internal.root := true, internal.dummy := true }
  else if roots.size > 1 then
    let superRoot ← MrTreeM.createNode 0 (some graph) (some "SUPER_ROOT")
    for root in roots do
      discard <| MrTreeM.addChild superRoot root
      MrTreeM.modifyNode root fun n => { n with internal.root := false }
    MrTreeM.modifyNode superRoot fun n => { n with internal.root := true, internal.dummy := true }
  monitor.done

/-- The `RootProcessor` (`IntermediateProcessorStrategy.ROOT_PROC`). -/
def processor : TreeProcessor := { name := "RootProcessor", process }

end RootProcessor

end Elk.Alg.MrTree.Intermediate
