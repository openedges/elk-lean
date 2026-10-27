import Elk.Alg.RectPacking.Util.RectPackingArena
/-!
# `org.eclipse.elk.alg.rectpacking.util.DrawingUtil`

Port of `util/drawing_util.rs` (elk-rs): scale measure and drawing dimensions.
-/
namespace Elk.Alg.RectPacking.Util

open Elk.Graph Elk.Core.Util Elk.Core.Math
open RectPackingM

namespace DrawingUtil

/-- `compute_scale_measure(width, height, desired_aspect_ratio)`:
`min(desired_aspect_ratio / width, 1 / height)` (Rust `f64::min`). -/
@[inline] def computeScaleMeasure (width height desiredAspectRatio : Float) : Float :=
  fmin (desiredAspectRatio / width) (1.0 / height)

/-- `reset_coordinates(nodes)`: moves every node to `(0, 0)`. -/
def resetCoordinates (nodes : Array NodeId) : ElkM Unit := do
  for n in nodes do
    ElkM.modifyNode n fun x => { x with x := 0.0, y := 0.0 }

/-- `calculate_dimensions(rows, node_node_spacing)`: maximum row width and the summed row heights
plus spacing between the rows. -/
def calculateDimensions (rows : Array RectRowId) (nodeNodeSpacing : Float) : RectPackingM KVector := do
  let mut maxWidth : Float := 0.0
  let mut newHeight : Float := 0.0
  let mut index := 0
  for row in rows do
    let r ← getRow row
    maxWidth := fmax maxWidth r.width
    newHeight := newHeight + (r.height + (if index > 0 then nodeNodeSpacing else 0.0))
    index := index + 1
  return ⟨maxWidth, newHeight⟩

/-- `calculate_dimensions_from_nodes(nodes)`: the maximum right (`width + x`) and bottom
(`height + y`) borders of the nodes. -/
def calculateDimensionsFromNodes (nodes : Array NodeId) : ElkM KVector := do
  let mut maxWidth : Float := 0.0
  let mut maxHeight : Float := 0.0
  for n in nodes do
    let node ← ElkM.getNode n
    maxWidth := fmax maxWidth (node.width + node.x)
    maxHeight := fmax maxHeight (node.height + node.y)
  return ⟨maxWidth, maxHeight⟩

end DrawingUtil

end Elk.Alg.RectPacking.Util
