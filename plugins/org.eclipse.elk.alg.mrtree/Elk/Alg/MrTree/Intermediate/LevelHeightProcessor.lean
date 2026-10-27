import Elk.Core.Util.Java
import Elk.Alg.MrTree.Graph.TArena
import Elk.Alg.MrTree.Options.MrTreeOptions
/-!
# `org.eclipse.elk.alg.mrtree.intermediate.LevelHeightProcessor`

Port of `intermediate/level_height_processor.rs` (elk-rs): level by level from the first `ROOT`
node, every node of a level gets `LEVELHEIGHT` = the maximal node width (horizontal layout
direction) or height (otherwise) of the level (`f64::max`). The direction is the graph's `DIRECTION`
(`unwrap_or(Undefined)`). The recursion of Rust is a loop here.
-/
namespace Elk.Alg.MrTree.Intermediate

open Elk.Core.Util Elk.Core.Options Elk.Alg.MrTree.Graph Elk.Alg.MrTree.Options

namespace LevelHeightProcessor

/-- `set_level_height(current_level)` for one level; returns the next level. -/
private def setLevelHeightLevel (currentLevel : Array TNodeId) (numberOfNodes : Nat)
    (monitor : ProgressMonitor) (direction : Direction) : MrTreeM (Array TNodeId) := do
  let subTask ← monitor.subTask ((Float.ofNat currentLevel.size).toF32 / (Float.ofNat numberOfNodes).toF32).toF32
  discard <| subTask.begin "Set neighbors in level" 1.0
  let mut nextLevel : Array TNodeId := #[]
  let mut height : Float := 0.0
  for node in currentLevel do
    let n ← MrTreeM.getNode node
    nextLevel := nextLevel ++ n.children
    height := if direction.isHorizontal then fmax height n.size.x else fmax height n.size.y
  for node in currentLevel do
    MrTreeM.modifyNode node fun n => { n with internal.levelHeight := height }
  subTask.done
  return nextLevel

/-- `LevelHeightProcessor::process`. -/
def process (graph : TGraphId) (monitor : ProgressMonitor) : MrTreeM Unit := do
  discard <| monitor.begin "Processor determine the height for each level" 1.0
  let g ← MrTreeM.getGraph graph
  let nodes := g.nodes
  let direction := (g.props.get MrTreeOptions.DIRECTION).getD .undefined
  let a ← get
  let root := nodes.find? fun n => (a.node n).internal.root
  let numberOfNodes := if nodes.isEmpty then 1 else nodes.size
  if let some root := root then
    let mut currentLevel := #[root]
    while !currentLevel.isEmpty do
      currentLevel ← setLevelHeightLevel currentLevel numberOfNodes monitor direction
  monitor.done

/-- The `LevelHeightProcessor` (`IntermediateProcessorStrategy.LEVEL_HEIGHT`). -/
def processor : TreeProcessor := { name := "LevelHeightProcessor", process }

end LevelHeightProcessor

end Elk.Alg.MrTree.Intermediate
