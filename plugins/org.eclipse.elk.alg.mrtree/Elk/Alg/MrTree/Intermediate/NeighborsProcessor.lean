import Elk.Alg.MrTree.Graph.TArena
/-!
# `org.eclipse.elk.alg.mrtree.intermediate.NeighborsProcessor`

Port of `intermediate/neighbors_processor.rs` (elk-rs): level by level, starting with the children
of the first `ROOT` node, consecutive nodes of a level become `LEFTNEIGHBOR`/`RIGHTNEIGHBOR` of each
other, and `LEFTSIBLING`/`RIGHTSIBLING` if their parents (`TNode::parent`) coincide. The next level
is the concatenation of the children of the level's nodes. The recursion of Rust is a loop here.
-/
namespace Elk.Alg.MrTree.Intermediate

open Elk.Core.Util Elk.Alg.MrTree.Graph

namespace NeighborsProcessor

/-- `set_neighbors(current_level)` for one level; returns the next level. -/
private def setNeighborsLevel (currentLevel : Array TNodeId) (numberOfNodes : Nat)
    (monitor : ProgressMonitor) : MrTreeM (Array TNodeId) := do
  let subTask ← monitor.subTask ((Float.ofNat currentLevel.size).toF32 / (Float.ofNat numberOfNodes).toF32).toF32
  discard <| subTask.begin "Set neighbors in level" 1.0
  let mut nextLevel : Array TNodeId := #[]
  let mut leftNeighbor : Option TNodeId := none
  for node in currentLevel do
    nextLevel := nextLevel ++ (← MrTreeM.children node)
    if let some left := leftNeighbor then
      MrTreeM.modifyNode left fun n => { n with internal.rightNeighbor := some node }
      MrTreeM.modifyNode node fun n => { n with internal.leftNeighbor := some left }
      let leftParent ← MrTreeM.parent left
      let nodeParent ← MrTreeM.parent node
      let sameParent : Bool := match leftParent, nodeParent with
        | some a, some b => a == b
        | _, _ => false
      if sameParent then
        MrTreeM.modifyNode left fun n => { n with internal.rightSibling := some node }
        MrTreeM.modifyNode node fun n => { n with internal.leftSibling := some left }
    leftNeighbor := some node
  subTask.done
  return nextLevel

/-- `NeighborsProcessor::process`. -/
def process (graph : TGraphId) (monitor : ProgressMonitor) : MrTreeM Unit := do
  discard <| monitor.begin "Processor set neighbors" 1.0
  let nodes := (← MrTreeM.getGraph graph).nodes
  let a ← get
  let root := nodes.find? fun n => (a.node n).internal.root
  let numberOfNodes := if nodes.isEmpty then 1 else nodes.size
  if let some root := root then
    let mut currentLevel ← MrTreeM.children root
    while !currentLevel.isEmpty do
      currentLevel ← setNeighborsLevel currentLevel numberOfNodes monitor
  monitor.done

/-- The `NeighborsProcessor` (`IntermediateProcessorStrategy.NEIGHBORS_PROC`). -/
def processor : TreeProcessor := { name := "NeighborsProcessor", process }

end NeighborsProcessor

end Elk.Alg.MrTree.Intermediate
