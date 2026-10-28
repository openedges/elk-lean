import Elk.Alg.Common.NodeSpacing.Internal.Algorithm.NodeLabelAndSizeUtilities
/-!
# `org.eclipse.elk.alg.common.nodespacing.internal.algorithm.NodeSizeCalculator`

Determines the node width and height from the size constraints and the cell system, sets them on
the node container and lets the cell system compute its horizontal / vertical layout (elk-rs
`internal::algorithm::NodeSizeCalculator`).

Deviations from Java (following elk-rs): `Math.max` is `f64::max` (`fmax`); missing outside
containers / inside port label cells are skipped instead of failing; `NODE_SIZE_FIXED_GRAPH_SIZE`
of the parent graph is read once by `NodeContext.new` (`nodeSizeFixedGraphSize`). The elk-rs call
to `sync_inside_port_label_cell_rectangles` is kept as the documented no-op of `NodeContext`.
-/
namespace Elk.Alg.Common.NodeSpacing.Internal.Algorithm

open Elk Elk.Core.Math Elk.Core.Util Elk.Core.Options
open Elk.Alg.Common.NodeSpacing.CellSystem Elk.Alg.Common.NodeSpacing.Internal

namespace NodeSizeCalculator

variable {N P L : Type}

/-- The width the size constraints ask for (the first part of `setNodeWidth`): the current width
for effectively fixed constraints, else the node container's minimum width (at least the current
width in top-down layout), widened to the NORTH/SOUTH outside containers if `NODE_LABELS` is set
and outside labels may not overhang, and to the minimum node width if any. -/
def computeNodeWidth (ctx : NodeContext N P L) : Float := Id.run do
  if NodeLabelAndSizeUtilities.areSizeConstraintsFixed ctx then
    -- Simply use the node's current width
    return ctx.nodeSize.x
  -- Ask the cell system how wide it would like to be
  let mut w :=
    if ctx.topdownLayout then fmax ctx.nodeSize.x (ctx.cells.minimumWidth ctx.nodeContainer)
    else ctx.cells.minimumWidth ctx.nodeContainer
  -- If we include node labels and outside node labels are not to overhang
  if ctx.sizeConstraints.contains .nodeLabels && !ctx.sizeOptions.contains .outsideNodeLabelsOverhang then
    if let some northContainer := ctx.outsideNodeLabelContainer .north then
      w := fmax w (ctx.cells.minimumWidth northContainer)
    if let some southContainer := ctx.outsideNodeLabelContainer .south then
      w := fmax w (ctx.cells.minimumWidth southContainer)
  -- The node might have a minimum size set
  if let some minNodeSize := NodeLabelAndSizeUtilities.getMinimumNodeSize ctx then
    w := fmax w minNodeSize.x
  return w

/-- The node size with the width the size constraints ask for (never shrinking it if
`NODE_SIZE_FIXED_GRAPH_SIZE` is set on the parent graph). Not inlined: its branches would
otherwise precede the context update of `setNodeWidth`, which then could not reuse the context
object (PLAN §7.1 item 13). -/
@[noinline] def nodeSizeWithWidth (ctx : NodeContext N P L) (width : Float) : KVector :=
  let nodeSize := ctx.nodeSize
  { nodeSize with x := if ctx.nodeSizeFixedGraphSize then fmax nodeSize.x width else width }

/-- The node size with the height the size constraints ask for (see `nodeSizeWithWidth`). -/
@[noinline] def nodeSizeWithHeight (ctx : NodeContext N P L) (height : Float) : KVector :=
  let nodeSize := ctx.nodeSize
  { nodeSize with y := if ctx.nodeSizeFixedGraphSize then fmax nodeSize.y height else height }

/-- `NodeSizeCalculator.setNodeWidth(nodeContext)` (elk-rs `set_node_width`): sets the node width
to `computeNodeWidth` (never shrinking it if `NODE_SIZE_FIXED_GRAPH_SIZE` is set on the parent
graph), gives the node container `x = 0` and that width and lays out the cell system
horizontally. -/
def setNodeWidth (ctx : NodeContext N P L) : NodeContext N P L :=
  let width := computeNodeWidth ctx
  -- Set the node's width
  let nodeSize := nodeSizeWithWidth ctx width
  let nodeContainer := ctx.nodeContainer
  -- Set the cell system's width and tell it to compute horizontal coordinates and widths (the
  -- arena is taken out of the context first, so both are updated in place)
  let ctx := ctx.modifyCells fun cells =>
    let cells := cells.modifyCellRectangle nodeContainer fun r => { r with x := cellZero, width := width }
    cells.layoutChildrenHorizontally nodeContainer
  NodeContext.syncInsidePortLabelCellRectangles { ctx with nodeSize }

/-- The height the size constraints ask for (the first part of `setNodeHeight`): the current
height for effectively fixed constraints, else the node container's minimum height (at least the
current height in top-down layout), raised to the EAST/WEST outside containers if `NODE_LABELS`
is set and outside labels may not overhang, to the minimum node height if any, and — with `PORTS`
and `FIXED_RATIO`/`FIXED_POS` port constraints — to the EAST/WEST inside port label cells (their
height does not come out of the cell system in that case). -/
def computeNodeHeight (ctx : NodeContext N P L) : Float := Id.run do
  if NodeLabelAndSizeUtilities.areSizeConstraintsFixed ctx then
    -- Simply use the node's current height
    return ctx.nodeSize.y
  -- Ask the cell system how high it would like to be
  let mut h :=
    if ctx.topdownLayout then fmax ctx.nodeSize.y (ctx.cells.minimumHeight ctx.nodeContainer)
    else ctx.cells.minimumHeight ctx.nodeContainer
  -- If we include node labels and outside node labels are not to overhang
  if ctx.sizeConstraints.contains .nodeLabels && !ctx.sizeOptions.contains .outsideNodeLabelsOverhang then
    if let some eastContainer := ctx.outsideNodeLabelContainer .east then
      h := fmax h (ctx.cells.minimumHeight eastContainer)
    if let some westContainer := ctx.outsideNodeLabelContainer .west then
      h := fmax h (ctx.cells.minimumHeight westContainer)
  -- The node might have a minimum size set
  if let some minNodeSize := NodeLabelAndSizeUtilities.getMinimumNodeSize ctx then
    h := fmax h minNodeSize.y
  -- With fixed port positions, the heights required by eastern and western ports don't come out
  -- of the cell system
  if ctx.sizeConstraints.contains .ports
      && (ctx.portConstraints == .fixedRatio || ctx.portConstraints == .fixedPos) then
    if let some eastCell := ctx.insidePortLabelCell .east then
      h := fmax h (ctx.cells.minimumHeight eastCell)
    if let some westCell := ctx.insidePortLabelCell .west then
      h := fmax h (ctx.cells.minimumHeight westCell)
  return h

/-- `NodeSizeCalculator.setNodeHeight(nodeContext)` (elk-rs `set_node_height`): sets the node
height to `computeNodeHeight` (never shrinking it if `NODE_SIZE_FIXED_GRAPH_SIZE` is set on the
parent graph), gives the node container `y = 0` and that height and lays out the cell system
vertically. -/
def setNodeHeight (ctx : NodeContext N P L) : NodeContext N P L :=
  let height := computeNodeHeight ctx
  -- Set the node's height
  let nodeSize := nodeSizeWithHeight ctx height
  let nodeContainer := ctx.nodeContainer
  -- Set the cell system's height and tell it to compute vertical coordinates and heights (the
  -- arena is taken out of the context first, so both are updated in place)
  let ctx := ctx.modifyCells fun cells =>
    let cells := cells.modifyCellRectangle nodeContainer fun r => { r with y := cellZero, height := height }
    cells.layoutChildrenVertically nodeContainer
  NodeContext.syncInsidePortLabelCellRectangles { ctx with nodeSize }

end NodeSizeCalculator

end Elk.Alg.Common.NodeSpacing.Internal.Algorithm
