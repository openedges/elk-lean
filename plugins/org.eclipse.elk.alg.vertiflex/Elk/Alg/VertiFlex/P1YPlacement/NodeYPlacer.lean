import Elk.Core.Alg
import Elk.Core.Options
import Elk.Core.Util.Java
import Elk.Core.Util.ProgressMonitor
import Elk.Alg.VertiFlex.VertiFlexLayoutPhases
import Elk.Alg.VertiFlex.VertiFlexUtil
import Elk.Alg.VertiFlex.Options.VertiFlexOptions
/-!
# `org.eclipse.elk.alg.vertiflex.p1yplacement.NodeYPlacer`

Port of `node_y_placer.rs` (elk-rs): phase 1 of VertiFlex. Walks the tree from the root and sets
the y coordinate of every node to its fixed vertical constraint, or else to the bottom of its
parent plus the layer distance.
-/
namespace Elk.Alg.VertiFlex.P1YPlacement

open Elk.Graph Elk.Core.Alg Elk.Core.Util Elk.Core.Options Elk.Alg.VertiFlex.Options

namespace NodeYPlacer

/-- `set_y_levels(node, min_height)`: `layer_distance` and `node_node_spacing` are the fields of
the Rust placer. -/
partial def setYLevels (layerDistance nodeNodeSpacing : Float) (node : NodeId) (minHeight : Float) :
    VertiFlexM Unit := do
  let n ← ElkM.getNode node
  -- `has_property(VERTICAL_CONSTRAINT)` and its value
  let minHeight := match n.props.get VertiFlexOptions.VERTICAL_CONSTRAINT with
    | some value => value
    | none => minHeight
  ElkM.modifyNode node fun nd => { nd with y := minHeight }
  let marginsBottom := (n.props.getD CoreOptions.MARGINS {}).bottom
  let newMinHeight := minHeight + layerDistance + n.height + javaMax marginsBottom nodeNodeSpacing
  for child in ← VertiFlexUtil.outgoingChildren node do
    setYLevels layerDistance nodeNodeSpacing child newMinHeight

/-- `process(graph, progress_monitor)`. -/
def process (graph : NodeId) (monitor : ProgressMonitor) : VertiFlexM Unit := do
  let _ ← monitor.begin "YPlacer" 1.0
  let props := (← ElkM.getNode graph).props
  let layerDistance := props.getD VertiFlexOptions.LAYER_DISTANCE 0.0
  let nodeNodeSpacing := props.getD CoreOptions.SPACING_NODE_NODE 0.0
  let hasChildren := !(← ElkM.getNode graph).children.isEmpty
  if hasChildren then
    if let some parent ← VertiFlexUtil.findRoot graph then
      setYLevels layerDistance nodeNodeSpacing parent 0.0
  monitor.done

/-- The phase (`ILayoutPhase`) without a processor configuration. -/
def phase : VertiFlexPhase :=
  { name := "NodeYPlacer"
    process := process
    getLayoutProcessorConfiguration := fun _ => pure none }

end NodeYPlacer

end Elk.Alg.VertiFlex.P1YPlacement
