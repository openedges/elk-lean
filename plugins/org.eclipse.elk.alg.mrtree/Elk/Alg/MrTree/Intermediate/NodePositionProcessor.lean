import Elk.Alg.MrTree.Graph.TArena
/-!
# `org.eclipse.elk.alg.mrtree.intermediate.NodePositionProcessor`

Port of `intermediate/node_position_processor.rs` (elk-rs): level by level from the first `ROOT`
node, the position of every reached node becomes `(XCOOR, YCOOR)` (the integer coordinates computed
by the node placer); afterwards every node of the graph is moved by minus half its size (centre to
top-left corner).
-/
namespace Elk.Alg.MrTree.Intermediate

open Elk.Core.Util Elk.Core.Math Elk.Alg.MrTree.Graph

namespace NodePositionProcessor

/-- `(XCOOR, YCOOR)` as a position (`i32 as f64`). -/
@[inline] private def coordinates (n : TNode) : KVector :=
  ⟨Float.ofInt n.internal.xcoor, Float.ofInt n.internal.ycoor⟩

/-- `set_coordinates(current_level, monitor)`: positions the level; returns the next level. -/
private def setCoordinates (currentLevel : Array TNodeId) (monitor : ProgressMonitor) :
    MrTreeM (Array TNodeId) := do
  if currentLevel.isEmpty then return #[]
  discard <| monitor.begin "Set coordinates" 1.0
  let mut nextLevel : Array TNodeId := #[]
  for node in currentLevel do
    nextLevel := nextLevel ++ (← MrTreeM.children node)
    MrTreeM.modifyNode node fun n => { n with position := coordinates n }
  monitor.done
  return nextLevel

/-- `NodePositionProcessor::process`. -/
def process (graph : TGraphId) (monitor : ProgressMonitor) : MrTreeM Unit := do
  discard <| monitor.begin "Processor set coordinates" 1.0
  let nodes := (← MrTreeM.getGraph graph).nodes
  let a ← get
  let root := nodes.find? fun n => (a.node n).internal.root
  let numberOfNodes := if nodes.isEmpty then 1 else nodes.size
  if let some root := root then
    MrTreeM.modifyNode root fun n => { n with position := coordinates n }
    let mut nextLevel ← MrTreeM.children root
    let mut subTasks : Float := 1.0
    while !nextLevel.isEmpty do
      nextLevel ← setCoordinates nextLevel (← monitor.subTask subTasks)
      subTasks := ((Float.ofNat nextLevel.size).toF32 / (Float.ofNat numberOfNodes).toF32).toF32
  for node in (← MrTreeM.getGraph graph).nodes do
    MrTreeM.modifyNode node fun n =>
      { n with position := n.position - ⟨n.size.x / 2.0, n.size.y / 2.0⟩ }
  monitor.done

/-- The `NodePositionProcessor` (`IntermediateProcessorStrategy.NODE_POSITION_PROC`). -/
def processor : TreeProcessor := { name := "NodePositionProcessor", process }

end NodePositionProcessor

end Elk.Alg.MrTree.Intermediate
