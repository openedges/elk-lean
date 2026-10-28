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

The map is an array indexed by `id` (`DFSTreeifyer.init` numbers the nodes `0 ..< size`) holding
`1 +` the level (0 = absent), with the same last-write-wins updates; a graph with an `id` outside
`0 ..< size` (on a node of the graph or a reached one) uses the hash map.
-/
namespace Elk.Alg.MrTree.Intermediate

open Elk.Core.Util Elk.Alg.MrTree.Graph Elk.Alg.MrTree.Options

namespace LevelProcessor

/-- The breadth-first levels from the roots, concatenated, with the level of every entry. -/
private def walk (a : TArena) (roots : Array TNodeId) : Array TNodeId × Array Int := Id.run do
  let mut entries : Array TNodeId := #[]
  let mut levels : Array Int := #[]
  let mut currentLevel := roots
  let mut level : Int := 0
  while !currentLevel.isEmpty do
    let mut nextLevel : Array TNodeId := #[]
    for node in currentLevel do
      entries := entries.push node
      levels := levels.push level
      nextLevel := nextLevel ++ (a.node node).children
    currentLevel := nextLevel
    level := level + 1
  return (entries, levels)

/-- `TREE_LEVEL` of every node of the graph (`levelMap.getD id 0`). -/
private def treeLevels (a : TArena) (nodes : Array TNodeId) : Array Int := Id.run do
  let roots := nodes.filter fun n => (a.node n).internal.root
  let (entries, levels) := walk a roots
  let size := nodes.size
  let inRange (n : TNodeId) : Bool := let id := (a.node n).id; id >= 0 && id < size
  if entries.all inRange && nodes.all inRange then
    let mut byId : Array Int := Array.replicate size 0
    for h : i in [0:entries.size] do
      byId := byId.set! (a.node entries[i]).id.toNat (levels[i]! + 1)
    return nodes.map fun n => match byId[(a.node n).id.toNat]! with
      | 0 => 0
      | l => l - 1
  else
    let mut levelMap : Std.HashMap Int Int := {}
    for h : i in [0:entries.size] do
      levelMap := levelMap.insert (a.node entries[i]).id levels[i]!
    return nodes.map fun n => levelMap.getD (a.node n).id 0

/-- `LevelProcessor::process`. -/
def process (graph : TGraphId) (monitor : ProgressMonitor) : MrTreeM Unit := do
  discard <| monitor.begin "Processor compute level" 1.0
  let nodes := (← MrTreeM.getGraph graph).nodes
  let levels := treeLevels (← get) nodes
  for h : i in [0:nodes.size] do
    MrTreeM.modifyNode nodes[i] fun n =>
      { n with props := n.props.set MrTreeOptions.TREE_LEVEL (levels[i]?.getD 0) }
  monitor.done

/-- The `LevelProcessor` (`IntermediateProcessorStrategy.LEVEL_PROC`). -/
def processor : TreeProcessor := { name := "LevelProcessor", process }

end LevelProcessor

end Elk.Alg.MrTree.Intermediate
