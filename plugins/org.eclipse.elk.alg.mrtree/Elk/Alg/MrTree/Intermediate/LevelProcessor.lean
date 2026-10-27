import Std.Data.HashMap
import Elk.Alg.MrTree.Graph.TArena
import Elk.Alg.MrTree.Options.MrTreeOptions
/-!
# `org.eclipse.elk.alg.mrtree.intermediate.LevelProcessor`

Port of `intermediate/level_processor.rs` (elk-rs): breadth-first from *all* `ROOT` nodes, records
the level of every reached node in a map keyed by the node's integer `id`, then stores
`TREE_LEVEL := level(id)` (0 if absent) on every node of the graph. Like Rust the map is keyed by
`id`, so nodes sharing an id (a `SUPER_ROOT`/`DUMMY_ROOT` has id 0) share the level written last.
The recursion of Rust is a loop here.
-/
namespace Elk.Alg.MrTree.Intermediate

open Elk.Core.Util Elk.Alg.MrTree.Graph Elk.Alg.MrTree.Options

namespace LevelProcessor

/-- `LevelProcessor::process`. -/
def process (graph : TGraphId) (monitor : ProgressMonitor) : MrTreeM Unit := do
  discard <| monitor.begin "Processor compute level" 1.0
  let nodes := (← MrTreeM.getGraph graph).nodes
  let a ← get
  let roots := nodes.filter fun n => (a.node n).internal.root
  let mut levelMap : Std.HashMap Int Int := {}
  let mut currentLevel := roots
  let mut level : Int := 0
  while !currentLevel.isEmpty do
    let mut nextLevel : Array TNodeId := #[]
    for node in currentLevel do
      let n ← MrTreeM.getNode node
      levelMap := levelMap.insert n.id level
      nextLevel := nextLevel ++ n.children
    currentLevel := nextLevel
    level := level + 1
  for node in (← MrTreeM.getGraph graph).nodes do
    MrTreeM.modifyNode node fun n =>
      { n with props := n.props.set MrTreeOptions.TREE_LEVEL (levelMap.getD n.id 0) }
  monitor.done

/-- The `LevelProcessor` (`IntermediateProcessorStrategy.LEVEL_PROC`). -/
def processor : TreeProcessor := { name := "LevelProcessor", process }

end LevelProcessor

end Elk.Alg.MrTree.Intermediate
