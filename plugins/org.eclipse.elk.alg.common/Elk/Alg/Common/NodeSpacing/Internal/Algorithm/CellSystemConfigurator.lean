import Elk.Alg.Common.NodeSpacing.Internal.NodeContext
import Elk.Core.Util.FloatConst
open Elk.Core.Util.FloatConst
/-!
# `org.eclipse.elk.alg.common.nodespacing.internal.algorithm.CellSystemConfigurator`

Configures the size contributions of the cell system so that the cells contribute properly to the
node size calculation, and updates the padding of the east/west inside port label cells (elk-rs
`internal::algorithm::CellSystemConfigurator`).

elk-rs sets every flag both on its `inside_port_label_cells` copies and on the corresponding cells
of the cell tree; both are the same arena cell here, so each flag is set once.

Like Java, `MINIMUM_SIZE` with `MINIMUM_SIZE_ACCOUNTS_FOR_PADDING` sets the middle row's
`contributesToMinimumHeight` twice and never its `contributesToMinimumWidth` (elk-rs sets both, so a
node without other width contributions got the minimum width; Java keeps the width of the other
constraints, e.g. `0`).

Deviations from Java (following elk-rs):
* `NODE_LABELS`: Java iterates `nodeContext.nodeLabelCells`; elk-rs visits the container slot of
  every defined `NodeLabelLocation` (inside: grid cell at row/column; outside: the side container's
  slot). Both find the same label cells (see `NodeLabelCellCreator`).
* `updateVerticalInsidePortLabelCellPadding` uses `f64::max` (`fmax`) instead of `Math.max`, and
  missing cells count as zero height/padding.
-/

namespace Elk.Alg.Common.NodeSpacing.Internal.Algorithm

open Elk Elk.Core.Math Elk.Core.Util Elk.Core.Options
open Elk.Alg.Common.NodeSpacing.CellSystem Elk.Alg.Common.NodeSpacing.Internal

namespace CellSystemConfigurator

variable {N P L : Type}

/-- Sets both size contribution flags of an optional cell. -/
private def setContributions (cells : CellArena L) (cell : Option CellId) (b : Bool) : CellArena L :=
  (cells.setContributesToMinimumHeightOpt cell b).setContributesToMinimumWidthOpt cell b

/-- The slot of an outside node label location in its side container (column on NORTH/SOUTH,
row otherwise). -/
private def outsideArea (location : NodeLabelLocation) : Option ContainerArea :=
  match location.outsideSide with
  | .north | .south => location.containerColumn
  | _ => location.containerRow

/-- `CellSystemConfigurator.configureCellSystemSizeContributions(nodeContext)` (elk-rs
`configure_cell_system_size_contributions`): nothing for fixed-size nodes (empty constraints);
* `PORTS`: NORTH/SOUTH inside port label cells contribute their width; EAST/WEST cells and the
  middle row contribute their height only for free port placement (not `FIXED_RATIO`/`FIXED_POS`);
  with `PORT_LABELS` also NORTH/SOUTH heights, EAST/WEST widths and the middle row's width;
* `NODE_LABELS`: the inside node label container and the middle row contribute both; inside label
  cells contribute both, outside label cells both unless `OUTSIDE_NODE_LABELS_OVERHANG`;
* `MINIMUM_SIZE` + `MINIMUM_SIZE_ACCOUNTS_FOR_PADDING`: the middle row contributes its height (Java
  never sets its width flag here); if the
  inside node label container does not contribute its height yet, it contributes both but only
  through its center cell. -/
def configureCellSystemSizeContributions (ctx : NodeContext N P L) : NodeContext N P L := Id.run do
  -- If the node has a fixed size, the cell system won't be used to calculate the node's size
  if ctx.sizeConstraints.isEmpty then return ctx
  let middleRow := ctx.nodeContainerMiddleRow
  let insideContainer := ctx.insideNodeLabelContainer
  let north := ctx.insidePortLabelCell .north
  let south := ctx.insidePortLabelCell .south
  let east := ctx.insidePortLabelCell .east
  let west := ctx.insidePortLabelCell .west
  -- the arena is taken out of the context first so that it is updated in place (`ctx.cells` is
  -- not read below)
  let mut cells := ctx.cells
  let ctx : NodeContext N P L := { ctx with cells := {} }
  -- Go through the different size constraint components
  if ctx.sizeConstraints.contains .ports then
    -- The northern and southern inside port label cells have the correct width for the node
    cells := cells.setContributesToMinimumWidthOpt north true
    cells := cells.setContributesToMinimumWidthOpt south true
    -- The eastern and western cells only give a correct height if port placement is free
    let freePortPlacement := ctx.portConstraints != .fixedRatio && ctx.portConstraints != .fixedPos
    cells := cells.setContributesToMinimumHeightOpt east freePortPlacement
    cells := cells.setContributesToMinimumHeightOpt west freePortPlacement
    -- The main row needs to contribute height for the east and west cells to contribute theirs
    cells := cells.setContributesToMinimumHeight middleRow freePortPlacement
    -- Port labels only contribute their size if ports are accounted for as well
    if ctx.sizeConstraints.contains .portLabels then
      cells := cells.setContributesToMinimumHeightOpt north true
      cells := cells.setContributesToMinimumHeightOpt south true
      cells := cells.setContributesToMinimumWidthOpt east true
      cells := cells.setContributesToMinimumWidthOpt west true
      -- The main row needs to contribute width for the east and west cells to contribute theirs
      cells := cells.setContributesToMinimumWidth middleRow true
  if ctx.sizeConstraints.contains .nodeLabels then
    -- The inside node label container needs to contribute both width and height, as does the middle row
    cells := setContributions cells insideContainer true
    cells := setContributions cells (some middleRow) true
    -- Outside node labels only contribute unless they are configured to overhang
    let overhang := ctx.sizeOptions.contains .outsideNodeLabelsOverhang
    for location in NodeLabelLocation.allDefined do
      if location.isInsideLocation then
        match insideContainer, location.containerRow, location.containerColumn with
        | some grid, some row, some col => cells := setContributions cells (cells.getGridCell grid row col) true
        | _, _, _ => pure ()
      else
        match ctx.outsideNodeLabelContainer location.outsideSide, outsideArea location with
        | some container, some area => cells := setContributions cells (cells.getCell container area) !overhang
        | _, _ => pure ()
  -- If the middle cell contributes to the node size, we need to set that up as well
  if ctx.sizeConstraints.contains .minimumSize && ctx.sizeOptions.contains .minimumSizeAccountsForPadding then
    -- "The middle row now needs to contribute width and height": Java sets the height flag twice
    -- and never the width flag (elk-rs sets both); the width only comes from other constraints
    cells := cells.setContributesToMinimumHeight middleRow true
    -- If the inside node label container is not contributing yet, node labels are not to be
    -- regarded: only its center cell contributes
    let alreadyContributing := match insideContainer with
      | some c => cells.isContributingToMinimumHeight c
      | none => false
    if !alreadyContributing then
      if let some c := insideContainer then
        cells := setContributions cells (some c) true
        cells := cells.setOnlyCenterCellContributesToMinimumSize c true
  return { ctx with cells }

/-- `CellSystemConfigurator.updateVerticalInsidePortLabelCellPadding(nodeContext)` (elk-rs
`update_vertical_inside_port_label_cell_padding`): for free port placement only, the top/bottom
paddings of the EAST and WEST inside port label cells shrink by the space already reserved above
(node container top padding + NORTH cell minimum height + `labelCellSpacing`) and below (same with
the bottom padding and the SOUTH cell); both cells get the larger requirement, at least `0`. -/
def updateVerticalInsidePortLabelCellPadding (ctx : NodeContext N P L) : NodeContext N P L :=
  -- We only care for the free port placement case
  if ctx.portConstraints == .fixedRatio || ctx.portConstraints == .fixedPos then ctx
  else
    let cells := ctx.cells
    -- Calculate where the east and west port cells will end up
    let northCellHeight := cells.minimumHeightOpt (ctx.insidePortLabelCell .north)
    let southCellHeight := cells.minimumHeightOpt (ctx.insidePortLabelCell .south)
    let containerPadding := cells.padding ctx.nodeContainer
    let topBorderOffset := containerPadding.top + northCellHeight + ctx.labelCellSpacing
    let bottomBorderOffset := containerPadding.bottom + southCellHeight + ctx.labelCellSpacing
    let east := ctx.insidePortLabelCell .east
    let west := ctx.insidePortLabelCell .west
    let eastPadding := cells.paddingOpt east
    let westPadding := cells.paddingOpt west
    -- Calculate how much top/bottom padding we actually need
    let topPadding := fmax (fmax fl0p0 (eastPadding.top - topBorderOffset)) (westPadding.top - topBorderOffset)
    let bottomPadding :=
      fmax (fmax fl0p0 (eastPadding.bottom - bottomBorderOffset)) (westPadding.bottom - bottomBorderOffset)
    -- Update paddings
    let update (cells : CellArena L) (cell : Option CellId) : CellArena L :=
      match cell with
      | some c => cells.modifyPadding c fun p => { p with top := topPadding, bottom := bottomPadding }
      | none => cells
    -- the arena is taken out of the context first so that it is updated in place
    ctx.modifyCells fun cells => update (update cells east) west

end CellSystemConfigurator

end Elk.Alg.Common.NodeSpacing.Internal.Algorithm
