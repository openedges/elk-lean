import Elk.Alg.Common.NodeSpacing.Internal.NodeContext
import Elk.Core.Util.FloatConst
open Elk.Core.Util.FloatConst
/-!
# `org.eclipse.elk.alg.common.nodespacing.internal.algorithm.LabelPlacer`

Sizes and positions the outer node label containers and places the node and port labels (elk-rs
`internal::algorithm::LabelPlacer`).

The cell system is pure, so label positions are not written by the cells themselves:
* `placeLabels` is the Java/elk-rs method: it lays out the containers and writes every label
  position through the adapters (`label.setPosition`), re-reading the label sizes like
  `LabelCell.applyLabelLayout()` does;
* `placeLabelsPure` returns the positions (computed from the label sizes recorded by `addLabel`)
  instead of writing them.

Label cell order (elk-rs `place_labels`; each label belongs to exactly one cell, so the order does
not change the result): inside node label cells in row-major grid order, outside node label cells
of the NORTH, SOUTH, EAST and WEST containers in area order, then the port label cells in
`portContexts.values()` order. Java visits `nodeLabelCells.values()` (location order) instead.

Deviation from Java (following elk-rs): a missing outside container is skipped instead of failing.
-/

namespace Elk.Alg.Common.NodeSpacing.Internal.Algorithm

open Elk Elk.Core.Math Elk.Core.Util Elk.Core.Options Elk.Core.Util.Adapters
open Elk.Alg.Common.NodeSpacing.CellSystem Elk.Alg.Common.NodeSpacing.Internal

namespace LabelPlacer

variable {N P L : Type}

/-- Sets the container's cell rectangle and lays out its children horizontally, then vertically. -/
private def layoutContainer (ctx : NodeContext N P L) (container : CellId) (rect : ElkRectangle) :
    NodeContext N P L :=
  let cells := ctx.cells.setCellRectangle container rect
  let cells := cells.layoutChildrenHorizontally container
  { ctx with cells := cells.layoutChildrenVertically container }

/-- `LabelPlacer.placeHorizontalOuterNodeLabelContainer(nodeContext, overhang, side)`: the NORTH or
SOUTH container gets its minimum size, but at least the node width (exactly the node width unless
outside labels may overhang); it is centered horizontally on the node and placed above (NORTH) or
below (SOUTH) it; then its children are laid out. -/
def placeHorizontalOuterNodeLabelContainer (ctx : NodeContext N P L) (outerNodeLabelsOverhang : Bool)
    (portSide : PortSide) : NodeContext N P L :=
  match ctx.outsideNodeLabelContainer portSide with
  | none => ctx
  | some container =>
    let nodeSize := ctx.nodeSize
    let rect := ctx.cells.cellRectangle container
    -- Set the container's width and height to its minimum width and height
    let rect := { rect with width := ctx.cells.minimumWidth container, height := ctx.cells.minimumHeight container }
    -- The container must be at least as wide as the node is
    let rect := { rect with width := fmax rect.width nodeSize.x }
    -- If node labels are not allowed to overhang and would do so right now, make the container smaller
    let rect := if rect.width > nodeSize.x && !outerNodeLabelsOverhang then { rect with width := nodeSize.x } else rect
    -- Container's x coordinate
    let rect := { rect with x := -(rect.width - nodeSize.x) / fl2p0 }
    -- Container's y coordinate depends on the side
    let rect := match portSide with
      | .north => { rect with y := -rect.height }
      | .south => { rect with y := nodeSize.y }
      | _ => rect
    layoutContainer ctx container rect

/-- `LabelPlacer.placeVerticalOuterNodeLabelContainer(nodeContext, overhang, side)`: the EAST or
WEST container gets its minimum size, but at least the node height (exactly the node height unless
outside labels may overhang); it is centered vertically on the node and placed left of (WEST) or
right of (EAST) it; then its children are laid out. -/
def placeVerticalOuterNodeLabelContainer (ctx : NodeContext N P L) (outerNodeLabelsOverhang : Bool)
    (portSide : PortSide) : NodeContext N P L :=
  match ctx.outsideNodeLabelContainer portSide with
  | none => ctx
  | some container =>
    let nodeSize := ctx.nodeSize
    let rect := ctx.cells.cellRectangle container
    -- Set the container's width and height to its minimum width and height
    let rect := { rect with width := ctx.cells.minimumWidth container, height := ctx.cells.minimumHeight container }
    -- The container must be at least as high as the node is
    let rect := { rect with height := fmax rect.height nodeSize.y }
    -- If node labels are not allowed to overhang and would do so right now, make the container smaller
    let rect := if rect.height > nodeSize.y && !outerNodeLabelsOverhang then { rect with height := nodeSize.y } else rect
    -- Container's y coordinate
    let rect := { rect with y := -(rect.height - nodeSize.y) / fl2p0 }
    -- Container's x coordinate depends on the side
    let rect := match portSide with
      | .west => { rect with x := -rect.width }
      | .east => { rect with x := nodeSize.x }
      | _ => rect
    layoutContainer ctx container rect

/-- `LabelPlacer.placeOuterNodeLabelContainers(nodeContext)`: NORTH, SOUTH, EAST, WEST. -/
def placeOuterNodeLabelContainers (ctx : NodeContext N P L) : NodeContext N P L :=
  let overhang := ctx.sizeOptions.contains .outsideNodeLabelsOverhang
  let ctx := placeHorizontalOuterNodeLabelContainer ctx overhang .north
  let ctx := placeHorizontalOuterNodeLabelContainer ctx overhang .south
  let ctx := placeVerticalOuterNodeLabelContainer ctx overhang .east
  placeVerticalOuterNodeLabelContainer ctx overhang .west

/-- All label cells whose labels `placeLabels` places, in elk-rs order (see the module doc). -/
def labelCellsToPlace (ctx : NodeContext N P L) : Array CellId := Id.run do
  let cells := ctx.cells
  let mut result : Array CellId := #[]
  -- Inside node labels
  if let some grid := ctx.insideNodeLabelContainer then
    for row in ContainerArea.values do
      for col in ContainerArea.values do
        if let some c := cells.getGridCell grid row col then
          if cells.isLabel c then result := result.push c
  -- Outside node labels
  for side in #[PortSide.north, .south, .east, .west] do
    if let some container := ctx.outsideNodeLabelContainer side then
      for area in ContainerArea.values do
        if let some c := cells.getCell container area then
          if cells.isLabel c then result := result.push c
  -- Port labels
  for pc in ctx.allPortContexts do
    if let some c := pc.portLabelCell then result := result.push c
  return result

/-- Whether one of the `labelCellsToPlace` may hold a label: some registered node label cell
(`NodeContext.nodeLabelCells`; every node label cell in the inside grid or an outside container
is created and registered by `NodeLabelCellCreator.retrieveNodeLabelCell`) or some port label
cell has labels. When none does, `placeLabels` only lays out the outer node label containers and
writes no label position (no Java counterpart; `NodeLabelAndSizeCalculator.processWithOptions`
then skips it, since nothing reads those container rectangles afterwards). -/
def hasLabelsToPlace (ctx : NodeContext N P L) : Bool := Id.run do
  let cells := ctx.cells
  -- Node labels (inside and outside)
  for cell in ctx.nodeLabelCells do
    if let some c := cell then
      if cells.hasLabels c then return true
  -- Port labels
  for pcs in ctx.portContexts do
    for pc in pcs do
      if let some c := pc.portLabelCell then
        if cells.hasLabels c then return true
  return false

/-- `LabelPlacer.placeLabels(nodeContext)` without side effects: places the outer node label
containers and returns every label with its new position (`LabelCell.applyLabelLayout()` with the
label sizes recorded when the labels were added), in `labelCellsToPlace` order. -/
def placeLabelsPure (ctx : NodeContext N P L) : NodeContext N P L × Array (L × KVector) :=
  let ctx := placeOuterNodeLabelContainers ctx
  let positions := (labelCellsToPlace ctx).foldl (init := #[]) fun acc c => acc ++ ctx.cells.applyLabelLayout c
  (ctx, positions)

variable {m : Type → Type} [Monad m] {G E : Type}

/-- `LabelPlacer.placeLabels(nodeContext)` (elk-rs `place_labels`): places the outer node label
containers, then tells every node and port label cell to place its labels, which writes the label
positions through the adapters (sizes are re-read with `label.getSize()` like elk-rs). -/
def placeLabels (a : GraphAdapters m G N P L E) (ctx : NodeContext N P L) : m (NodeContext N P L) := do
  -- Properly place all label cells for outer node labels
  let ctx := placeOuterNodeLabelContainers ctx
  -- Tell all node and port label cells to place their labels
  for c in labelCellsToPlace ctx do
    let positions ← ctx.cells.applyLabelLayoutM c a.label.getSize
    for (label, pos) in positions do
      a.label.setPosition label pos
  return ctx

end LabelPlacer

end Elk.Alg.Common.NodeSpacing.Internal.Algorithm
