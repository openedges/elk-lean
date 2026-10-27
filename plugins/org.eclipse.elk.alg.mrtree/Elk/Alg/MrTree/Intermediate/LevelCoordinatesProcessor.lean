import Elk.Core.Util.Java
import Elk.Alg.MrTree.Graph.TArena
import Elk.Alg.MrTree.Options.MrTreeOptions
/-!
# `org.eclipse.elk.alg.mrtree.intermediate.LevelCoordinatesProcessor`

Port of `intermediate/level_coordinates_processor.rs` (elk-rs): per tree level (`TREE_LEVEL`) the
extent of the node boxes along the layout axis (x for a horizontal `DIRECTION`, y otherwise) is
computed (`f64::min`/`f64::max` starting at `(f64::MAX, -f64::MAX)`) and stored on every node of the
level as `LEVELMIN`/`LEVELMAX`.

Deviation: Rust converts the level with `as usize`; a negative `TREE_LEVEL` would wrap to a huge
index (and exhaust memory growing the level list). The Lean port clamps it to 0 (`Int.toNat`).
-/
namespace Elk.Alg.MrTree.Intermediate

open Elk.Core.Util Elk.Core.Options Elk.Alg.MrTree.Graph Elk.Alg.MrTree.Options

namespace LevelCoordinatesProcessor

/-- `LevelCoordinatesProcessor::process`. -/
def process (graph : TGraphId) (monitor : ProgressMonitor) : MrTreeM Unit := do
  discard <| monitor.begin "Processor determine the coords for each level" 1.0
  let g ← MrTreeM.getGraph graph
  let direction := (g.props.get MrTreeOptions.DIRECTION).getD .down
  let mut levels : Array (Float × Float) := #[]
  let mut nodeLevels : Array Nat := #[]
  -- pass 1: extract the level and the bounds
  for node in g.nodes do
    let n ← MrTreeM.getNode node
    let level := ((n.props.get MrTreeOptions.TREE_LEVEL).getD 0).toNat
    nodeLevels := nodeLevels.push level
    while level >= levels.size do
      levels := levels.push (Float.maxValue, -Float.maxValue)
    let (start, «end») := if direction.isHorizontal then (n.position.x, n.position.x + n.size.x)
      else (n.position.y, n.position.y + n.size.y)
    let (minVal, maxVal) := levels[level]!
    levels := levels.set! level (fmin minVal start, fmax maxVal «end»)
  -- pass 2: write back
  for i in [0:g.nodes.size] do
    let level := nodeLevels[i]!
    if level < levels.size then
      let (minVal, maxVal) := levels[level]!
      MrTreeM.modifyNode g.nodes[i]! fun n => { n with internal.levelMin := minVal, internal.levelMax := maxVal }
  monitor.done

/-- The `LevelCoordinatesProcessor` (`IntermediateProcessorStrategy.LEVEL_COORDS`). -/
def processor : TreeProcessor := { name := "LevelCoordinatesProcessor", process }

end LevelCoordinatesProcessor

end Elk.Alg.MrTree.Intermediate
