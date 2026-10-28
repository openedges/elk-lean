import Elk.Graph
import Elk.Core.Alg
import Elk.Core.Math
import Elk.Core.Options
import Elk.Core.Util.Java
import Elk.Core.Util.ProgressMonitor
import Elk.Alg.Radial.InternalProperties
import Elk.Alg.Radial.RadialUtil
import Elk.Alg.Radial.Options.RadialOptions
/-!
# `org.eclipse.elk.alg.radial.intermediate.CalculateGraphSize`

ELK Java's `CalculateGraphSize` (elk-rs `calculate_graph_size.rs` was the code reference): computes the
bounding box of all children (including margins; Java starts the maxima at `Double.MIN_VALUE` and uses
`Math.min`/`Math.max`, elk-rs `-f64::MAX` and `f64::min`/`max`), moves the children so that the box starts at the padding, sets the size of the graph
(unless `NODE_SIZE_FIXED_GRAPH_SIZE`) and the child area. With `CENTER_ON_ROOT` the box is
extended on one side so that the root is exactly in the middle of the graph.
-/
namespace Elk.Alg.Radial.Intermediate

open Elk.Graph Elk.Core.Alg Elk.Core.Math Elk.Core.Options Elk.Core.Util Elk.Alg.Radial.Options

namespace CalculateGraphSize

/-- `process(graph, progress_monitor)`. -/
def process (graph : NodeId) (monitor : ProgressMonitor) : RadialM Unit := do
  let _ ← monitor.begin "Calculate Graph Size" 1.0
  if ← monitor.isLoggingEnabled then monitor.logGraph "Before"
  let graphNode ← ElkM.getNode graph
  let children := graphNode.children
  let padding := graphNode.props.getD CoreOptions.PADDING {}
  let centerOnRoot := graphNode.props.getD RadialOptions.CENTER_ON_ROOT false
  -- Java: `Double.MAX_VALUE` / `Double.MIN_VALUE` (the smallest positive double, not `-MAX_VALUE`)
  -- and `Math.min`/`Math.max` (a NaN coordinate makes the whole box NaN)
  let mut minXPos := Float.maxValue
  let mut minYPos := Float.maxValue
  let mut maxXPos := Float.minPositive
  let mut maxYPos := Float.minPositive
  for node in children do
    let n ← ElkM.getNode node
    let margins := n.props.getD CoreOptions.MARGINS {}
    minXPos := javaMin minXPos (n.x - margins.left)
    minYPos := javaMin minYPos (n.y - margins.top)
    maxXPos := javaMax maxXPos (n.x + n.width + margins.right)
    maxYPos := javaMax maxYPos (n.y + n.height + margins.bottom)
  let mut offsetX := minXPos - padding.left
  let mut offsetY := minYPos - padding.top
  let mut width := maxXPos - minXPos + padding.left + padding.right
  let mut height := maxYPos - minYPos + padding.top + padding.bottom
  if centerOnRoot then
    if let some root ← RadialUtil.rootFromGraph graph then
      let r ← ElkM.getNode root
      let margins := r.props.getD CoreOptions.MARGINS {}
      let rootX := r.x + r.width / 2.0 + (margins.left + margins.right) / 2.0 - offsetX
      let rootY := r.y + r.height / 2.0 + (margins.top + margins.bottom) / 2.0 - offsetY
      let dx := width - rootX
      let dy := height - rootY
      if dx < width / 2.0 then
        let additionalX := dx - rootX
        width := width + additionalX
        offsetX := offsetX - additionalX
      else
        let additionalX := rootX - dx
        width := width + additionalX
      if dy < height / 2.0 then
        let additionalY := dy - rootY
        height := height + additionalY
        offsetY := offsetY - additionalY
      else
        let additionalY := rootY - dy
        height := height + additionalY
  for node in children do
    ElkM.modifyNode node fun n => { n with x := n.x - offsetX, y := n.y - offsetY }
  let fixedGraphSize := graphNode.props.getD CoreOptions.NODE_SIZE_FIXED_GRAPH_SIZE false
  if !fixedGraphSize then
    ElkM.modifyNode graph fun n => { n with width := width, height := height }
  ElkM.setNodeProp graph CoreOptions.CHILD_AREA_WIDTH (width - padding.left - padding.right)
  ElkM.setNodeProp graph CoreOptions.CHILD_AREA_HEIGHT (height - padding.top - padding.bottom)
  if ← monitor.isLoggingEnabled then monitor.logGraph "After"

/-- The processor (`ILayoutProcessor`). -/
def processor : LayoutProcessor RadialM NodeId :=
  { name := "CalculateGraphSize", process := process }

end CalculateGraphSize

end Elk.Alg.Radial.Intermediate
