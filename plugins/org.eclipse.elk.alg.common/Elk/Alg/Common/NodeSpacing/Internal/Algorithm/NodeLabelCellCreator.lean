import Elk.Alg.Common.NodeSpacing.Internal.NodeContext
/-!
# `org.eclipse.elk.alg.common.nodespacing.internal.algorithm.NodeLabelCellCreator`

Takes all of a node's labels and creates the node label containers and label cells (elk-rs
`internal::algorithm::NodeLabelCellCreator`):
* the inside node label container, a grid (`FORCE_TABULAR_NODE_LABELS` → tabular,
  symmetrical unless `ASYMMETRICAL`, gap `labelCellSpacing`, padding `NODE_LABELS_PADDING`) placed
  in the center of `nodeContainerMiddleRow`;
* unless `onlyInside`, one outside container per side (horizontal strips for NORTH/SOUTH, vertical
  strips for WEST/EAST) whose padding towards the node is `nodeLabelSpacing`, registered in
  `NodeContext.outsideNodeLabelContainers`;
* one label cell per used `NodeLabelLocation`, created lazily when its first label arrives and
  shared by all later labels of the same location (the elk-rs fix against overwriting a
  multi-label cell: elk-rs looks the cell up in its container slot before creating one). Inside
  cells go to the grid at (row, column) of the location, outside cells to their side container (at
  the location's column on NORTH/SOUTH, contributing to the minimum height; at its row on
  WEST/EAST, contributing to the minimum width). New cells are also registered in
  `NodeContext.nodeLabelCells` (Java `nodeLabelCells.put`).

Deviation from Java (following elk-rs): Java finds an existing cell through
`nodeContext.nodeLabelCells`, elk-rs (and this port) through the container slot of the location.
Both agree because every location has its own slot and the containers are created right before.
-/
namespace Elk.Alg.Common.NodeSpacing.Internal.Algorithm

open Elk Elk.Core.Math Elk.Core.Util Elk.Core.Options Elk.Core.Util.Adapters
open Elk.Alg.Common.NodeSpacing.CellSystem Elk.Alg.Common.NodeSpacing.Internal

namespace NodeLabelCellCreator

variable {N P L : Type}

/-! ### Cell creation and retrieval -/

/-- Creates an outside node label container (a strip with gap `labelCellSpacing`) for the given
side and registers it in `outsideNodeLabelContainers`. -/
@[inline] private def createOutsideContainer (ctx : NodeContext N P L) (side : PortSide) (mode : Strip)
    (symmetry : Bool) (f : ElkPadding → ElkPadding) : NodeContext N P L :=
  let gap := ctx.labelCellSpacing
  let (ctx, container) := ctx.modifyCellsGet fun cells =>
    let (cells, container) := cells.createStrip mode symmetry gap
    (cells.modifyPadding container f, container)
  NodeContext.setOutsideNodeLabelContainer ctx side (some container)

/-- `NodeLabelCellCreator.createNodeLabelCellContainers(nodeContext, onlyInside)` (elk-rs
`create_node_label_cell_containers`): creates the inside node label container (grid in the center
of the middle row) and, unless `onlyInside`, the NORTH, SOUTH, WEST and EAST outside containers
(in that order). -/
def createNodeLabelCellContainers (ctx : NodeContext N P L) (onlyInside : Bool) : NodeContext N P L := Id.run do
  let symmetry := !ctx.sizeOptions.contains .asymmetrical
  let tabularNodeLabels := ctx.sizeOptions.contains .forceTabularNodeLabels
  -- Inside container
  let gap := ctx.labelCellSpacing
  let nlp := ctx.nodeLabelsPadding
  let middleRow := ctx.nodeContainerMiddleRow
  let mut ctx := ctx.modifyCells fun cells =>
    let (cells, insideContainer) := cells.createGrid tabularNodeLabels symmetry gap
    -- Apply node labels padding
    let cells := cells.modifyPadding insideContainer fun p =>
      { p with top := nlp.top, right := nlp.right, bottom := nlp.bottom, left := nlp.left }
    cells.setCell middleRow .center (some insideContainer)
  -- Outside containers, if requested
  if !onlyInside then
    let spacing := ctx.nodeLabelSpacing
    ctx := createOutsideContainer ctx .north .horizontal symmetry fun p => { p with bottom := spacing }
    ctx := createOutsideContainer ctx .south .horizontal symmetry fun p => { p with top := spacing }
    ctx := createOutsideContainer ctx .west .vertical symmetry fun p => { p with right := spacing }
    ctx := createOutsideContainer ctx .east .vertical symmetry fun p => { p with left := spacing }
  return ctx

/-- The slot of an outside location in its side container: the location's column on NORTH and
SOUTH, its row otherwise (elk-rs `retrieve_node_label_cell`). -/
def outsideContainerArea (location : NodeLabelLocation) : Option ContainerArea :=
  match location.outsideSide with
  | .north | .south => location.containerColumn
  | _ => location.containerRow

/-- The label cell currently stored in the container slot of the location, if any (elk-rs
`cell_exists` check of `retrieve_node_label_cell`). -/
def existingNodeLabelCell (ctx : NodeContext N P L) (location : NodeLabelLocation) : Option CellId :=
  let slot : Option CellId :=
    if location.isInsideLocation then
      match ctx.insideNodeLabelContainer, location.containerRow, location.containerColumn with
      | some grid, some row, some col => ctx.cells.getGridCell grid row col
      | _, _, _ => none
    else
      match ctx.outsideNodeLabelContainer location.outsideSide, outsideContainerArea location with
      | some container, some area => ctx.cells.getCell container area
      | _, _ => none
  match slot with
  | some c => if ctx.cells.isLabel c then some c else none
  | none => none

/-- `NodeLabelCellCreator.retrieveNodeLabelCell(nodeContext, location, horizontalLayoutMode)`
(elk-rs `retrieve_node_label_cell`): the label cell of the location, created (gap
`labelLabelSpacing`, alignments of the location) and put into its container if it does not exist
yet. `none` only if the location's container is missing, which cannot happen after
`createNodeLabelCellContainers` (elk-rs `expect`s it). -/
def retrieveNodeLabelCell (ctx : NodeContext N P L) (location : NodeLabelLocation)
    (horizontalLayoutMode : Bool) : NodeContext N P L × Option CellId :=
  match existingNodeLabelCell ctx location with
  | some c => (ctx, some c)
  | none =>
    -- The node label cell doesn't exist yet, so create one and add it to the relevant container
    let (cells, cell) := ctx.cells.createLabel ctx.labelLabelSpacing horizontalLayoutMode
    -- Set alignment based on location
    let cells := match location.horizontalAlignment with
      | some h => cells.setHorizontalAlignment cell h
      | none => cells
    let cells := match location.verticalAlignment with
      | some v => cells.setVerticalAlignment cell v
      | none => cells
    let register (cells : CellArena L) : NodeContext N P L × Option CellId :=
      (NodeContext.setNodeLabelCell { ctx with cells } location (some cell), some cell)
    -- Find the correct container and add the cell to it
    if location.isInsideLocation then
      match ctx.insideNodeLabelContainer, location.containerRow, location.containerColumn with
      | some grid, some row, some col => register (cells.setGridCell grid row col (some cell))
      | _, _, _ => (ctx, none) -- unreachable: the inside container always exists
    else
      let side := location.outsideSide
      match ctx.outsideNodeLabelContainer side with
      | none => (ctx, none) -- unreachable: outside locations are skipped without containers
      | some container =>
        match side with
        | .north | .south =>
          match location.containerColumn with
          | some area =>
            let cells := cells.setContributesToMinimumHeight cell true
            register (cells.setCell container area (some cell))
          | none => (ctx, none) -- unreachable
        | .west | .east =>
          match location.containerRow with
          | some area =>
            let cells := cells.setContributesToMinimumWidth cell true
            register (cells.setCell container area (some cell))
          | none => (ctx, none) -- unreachable
        | .undefined => (ctx, none) -- unreachable: outside locations have a side

/-! ### Label handling -/

variable {m : Type → Type} [Monad m] {G E : Type}

/-- `NodeLabelCellCreator.handleNodeLabel(nodeContext, label, onlyInside, horizontalLayoutMode)`
(elk-rs `handle_node_label`): the label's own `NODE_LABELS_PLACEMENT` if set (else the node's)
determines its location; labels with an undefined (fixed) location, and outside labels if
`onlyInside`, are ignored; all others are added to the location's label cell with their current
size. -/
def handleNodeLabel (a : GraphAdapters m G N P L E) (ctx : NodeContext N P L) (label : L)
    (onlyInside horizontalLayoutMode : Bool) : m (NodeContext N P L) := do
  -- Find the effective label location
  let labelPlacement ←
    if ← a.label.hasProp label CoreOptions.NODE_LABELS_PLACEMENT then
      a.label.getPropertyD label CoreOptions.NODE_LABELS_PLACEMENT EnumSet.empty
    else
      pure ctx.nodeLabelPlacement
  let labelLocation := NodeLabelLocation.fromNodeLabelPlacement labelPlacement
  -- If the label has its location fixed, we will ignore it
  if labelLocation == .undefined then return ctx
  -- If the label's location is on the node's outside but we only want inside node labels, ignore it
  if onlyInside && !labelLocation.isInsideLocation then return ctx
  let (ctx, cell) := retrieveNodeLabelCell ctx labelLocation horizontalLayoutMode
  match cell with
  | some c =>
    let size ← a.label.getSize label
    return ctx.modifyCells (·.addLabel c label size)
  | none => return ctx

/-- `NodeLabelCellCreator.createNodeLabelCells(nodeContext, onlyInside, horizontalLayoutMode)`
(elk-rs `create_node_label_cells`): creates the node label containers, then handles the node's
labels in label order. `horizontalLayoutMode` is the layout mode of new label cells.

A node without labels and without `NODE_LABELS` size constraints gets no outside containers (no
Java counterpart): they would stay empty, and empty outside containers are only read for label
placement (skipped without labels), for the `NODE_LABELS` size contributions (no slot cells) and
for the `NODE_LABELS` node size (excluded); everything else already treats a missing outside
container like an empty one. -/
def createNodeLabelCells (a : GraphAdapters m G N P L E) (ctx : NodeContext N P L)
    (onlyInside horizontalLayoutMode : Bool) : m (NodeContext N P L) := do
  let labels ← a.nodeLabels ctx.node
  let noOutsideContainers := labels.isEmpty && !ctx.sizeConstraints.contains .nodeLabels
  -- Make sure all the relevant containers exist
  let mut ctx := createNodeLabelCellContainers ctx (onlyInside || noOutsideContainers)
  -- Handle each of the node's labels
  for label in labels do
    ctx ← handleNodeLabel a ctx label onlyInside horizontalLayoutMode
  return ctx

end NodeLabelCellCreator

end Elk.Alg.Common.NodeSpacing.Internal.Algorithm
