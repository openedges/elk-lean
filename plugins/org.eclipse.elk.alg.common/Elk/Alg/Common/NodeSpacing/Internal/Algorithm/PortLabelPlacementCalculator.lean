import Elk.Core.Util.Java
import Elk.Alg.Common.Overlaps.RectangleStripOverlapRemover
import Elk.Alg.Common.NodeSpacing.Internal.Algorithm.NodeLabelAndSizeUtilities
/-!
# `org.eclipse.elk.alg.common.nodespacing.internal.algorithm.PortLabelPlacementCalculator`

Knows how to place port labels (elk-rs `internal::algorithm::PortLabelPlacementCalculator`).
Northern and southern port labels are placed by `placeHorizontalPortLabels` (PHASE 5, after the
horizontal ports), eastern and western ones by `placeVerticalPortLabels` (PHASE 6).

Like Java/elk-rs, the placement only sets up the port label cells (arena cells referenced by
`PortContext.portLabelCell`): their cell rectangle, relative to the port position, and their
label alignments. The label positions are computed from that later
(`CellArena.applyLabelLayout`, applied by `LabelPlacer`). For inside labels of northern and
southern ports, the height needed by the labels becomes the content height of the side's inside
port label cell.

Ports without a label cell or without labels are skipped. The constrained placements (port
labels not part of the size constraints, or `FIXED_POS` ports) remove overlaps between the label
cells of northern/southern ports with a `RectangleStripOverlapRemover`; elk-rs lets the remover
write the new coordinate through raw pointers into the cell rectangles, the Lean remover returns
the updated rectangles, which are written back to the label cells (the cells are not touched in
between, so this is the same).

Inside port label cells are shared by `NodeContext.insidePortLabelCells` and the node container
(see `HorizontalPortPlacementSizeCalculator`); elk-rs updates both of its copies, the Lean arena
updates the shared cell once.

Deviations from Java (following elk-rs): `ElkMath.maxd` / `Math.max` / `Math.min` are
`f64::max` / `f64::min` (`fmax` / `fmin`); the first label's height is the size recorded in the
label cell. A northern/southern side without an inside port label cell skips the constrained
inside placement (Java would throw a `NullPointerException`).
-/
namespace Elk.Alg.Common.NodeSpacing.Internal.Algorithm

open Elk Elk.Core.Math Elk.Core.Util Elk.Core.Options
open Elk.Alg.Common.NodeSpacing.CellSystem Elk.Alg.Common.NodeSpacing.Internal Elk.Alg.Common.Overlaps

namespace PortLabelPlacementCalculator

variable {N P L : Type}

/-- elk-rs `set_inside_north_south_label_cell_height(nodeContext, portSide, height)` (Java
`insidePortLabelCells.get(portSide).getMinimumContentAreaSize().y = height`): sets the content
height of the northern/southern inside port label cell (and of the node container's atomic
`BEGIN`/`END` cell, which is the same arena cell). Other sides are ignored. -/
private def setInsideNorthSouthLabelCellHeight (ctx : NodeContext N P L) (portSide : PortSide) (height : Float) :
    NodeContext N P L :=
  if !(portSide == .north || portSide == .south) then ctx
  else
    let setHeight (cs : CellArena L) (c : CellId) : CellArena L :=
      cs.modifyMinimumContentAreaSize c fun s => { s with y := height }
    let insideCell := ctx.insidePortLabelCell portSide
    let cells := match insideCell with
      | some c => setHeight ctx.cells c
      | none => ctx.cells
    let containerArea : ContainerArea := if portSide == .north then .begin else .«end»
    let containerCell := (cells.getCell ctx.nodeContainer containerArea).filter cells.isAtomic
    let cells := match containerCell with
      | some c => if insideCell == some c then cells else setHeight cells c
      | none => cells
    { ctx with cells }

/-- The port's label cell if it exists and has labels (Java `portLabelCell != null &&
portLabelCell.hasLabels()`). -/
private def labelCellWithLabels? (cells : CellArena L) (pc : PortContext P L) : Option CellId :=
  match pc.portLabelCell with
  | some c => if cells.hasLabels c then some c else none
  | none => none

/-- Sets the label cell's rectangle size to its minimum size and returns `(minWidth, minHeight)`. -/
private def sizeLabelCell (cells : CellArena L) (lc : CellId) : CellArena L × Float × Float :=
  let minWidth := cells.minimumWidth lc
  let minHeight := cells.minimumHeight lc
  (cells.modifyCellRectangle lc fun r => { r with width := minWidth, height := minHeight }, minWidth, minHeight)

/-- Height of the first label of a label cell (`0` without labels). -/
private def firstLabelHeight (cells : CellArena L) (lc : CellId) : Float :=
  ((cells.labels lc)[0]?.map (·.2.y)).getD 0.0

/-- Makes the label cell rectangles of the side's ports (with labels) relative to their port
positions (the second pass of the constrained placements). -/
private def makeLabelCellsRelative (ctx : NodeContext N P L) (portSide : PortSide) : NodeContext N P L := Id.run do
  let mut cells := ctx.cells
  for pc in ctx.portContextsOf portSide do
    let some lc := labelCellWithLabels? cells pc | continue
    let portPosition := pc.portPosition
    cells := cells.modifyCellRectangle lc fun r => { r with x := r.x - portPosition.x, y := r.y - portPosition.y }
  return { ctx with cells }

/-! ### Simple inside port labels -/

/-- `portLabelBorderOffsetForPortSide(nodeContext, portSide)`: the node container's padding on
the side plus the port-label spacing (vertical for NORTH/SOUTH, horizontal for EAST/WEST). -/
private def portLabelBorderOffsetForPortSide (ctx : NodeContext N P L) (portSide : PortSide) : Float :=
  let containerPadding := ctx.cells.padding ctx.nodeContainer
  match portSide with
  | .north => containerPadding.top + ctx.portLabelSpacingVertical
  | .south => containerPadding.bottom + ctx.portLabelSpacingVertical
  | .east => containerPadding.right + ctx.portLabelSpacingHorizontal
  | .west => containerPadding.left + ctx.portLabelSpacingHorizontal
  | .undefined => 0.0

/-- `simpleInsidePortLabelPlacement(nodeContext, portSide)`: places the label cells inside the
node, next to (centered on) the port or beside it, offset from the node border by the border
offset; northern/southern label heights set the inside port label cell's content height. -/
private def simpleInsidePortLabelPlacement (ctx : NodeContext N P L) (portSide : PortSide) : NodeContext N P L := Id.run do
  let mut insideNorthOrSouthPortLabelAreaHeight := 0.0
  let labelBorderOffset := portLabelBorderOffsetForPortSide ctx portSide
  let portLabelSpacingHorizontal := ctx.portLabelSpacingHorizontal
  let portLabelSpacingVertical := ctx.portLabelSpacingVertical
  let portLabelsTreatAsGroup := ctx.portLabelsTreatAsGroup
  let mut cells := ctx.cells
  for pc in ctx.portContextsOf portSide do
    let some lc := labelCellWithLabels? cells pc | continue
    let portSize := pc.portSize
    let portBorderOffset := pc.portBorderOffset
    let labelsNextToPort := pc.labelsNextToPort
    let (cells', minWidth, minHeight) := sizeLabelCell cells lc
    cells := cells'
    match portSide with
    | .north =>
      cells := cells.modifyCellRectangle lc fun r => { r with
        x := if labelsNextToPort then (portSize.x - minWidth) / 2.0 else portSize.x + portLabelSpacingHorizontal
        y := portSize.y + portBorderOffset + labelBorderOffset }
      cells := (cells.setHorizontalAlignment lc .center).setVerticalAlignment lc .top
    | .south =>
      cells := cells.modifyCellRectangle lc fun r => { r with
        x := if labelsNextToPort then (portSize.x - minWidth) / 2.0 else portSize.x + portLabelSpacingHorizontal
        y := -portBorderOffset - labelBorderOffset - minHeight }
      cells := (cells.setHorizontalAlignment lc .center).setVerticalAlignment lc .bottom
    | .east =>
      let firstHeight := if !portLabelsTreatAsGroup then firstLabelHeight cells lc else 0.0
      cells := cells.modifyCellRectangle lc fun r => { r with
        x := -portBorderOffset - labelBorderOffset - minWidth
        y := if labelsNextToPort then
            (portSize.y - (if portLabelsTreatAsGroup then minHeight else firstHeight)) / 2.0
          else portSize.y + portLabelSpacingVertical }
      cells := (cells.setHorizontalAlignment lc .right).setVerticalAlignment lc .center
    | .west =>
      let firstHeight := if !portLabelsTreatAsGroup then firstLabelHeight cells lc else 0.0
      cells := cells.modifyCellRectangle lc fun r => { r with
        x := portSize.x + portBorderOffset + labelBorderOffset
        y := if labelsNextToPort then
            (portSize.y - (if portLabelsTreatAsGroup then minHeight else firstHeight)) / 2.0
          else portSize.y + portLabelSpacingVertical }
      cells := (cells.setHorizontalAlignment lc .left).setVerticalAlignment lc .center
    | .undefined => pure ()
    -- Update the port label area height for N/S
    if portSide == .north || portSide == .south then
      insideNorthOrSouthPortLabelAreaHeight := fmax insideNorthOrSouthPortLabelAreaHeight minHeight
  let ctx := { ctx with cells }
  -- Apply the N/S port label area height
  if insideNorthOrSouthPortLabelAreaHeight > 0.0 then
    return setInsideNorthSouthLabelCellHeight ctx portSide insideNorthOrSouthPortLabelAreaHeight
  return ctx

/-! ### Constrained inside port labels -/

/-- `centerPortLabel(portLabelCellRect, portPosition, portSize, minX, maxX)`: centers the label
cell (absolute coordinates) on the port, keeping it within `[minX, maxX]` unless that would make
it slide past the port (corrected in one direction only). -/
private def centerPortLabel (r : ElkRectangle) (portPosition portSize : KVector) (minX maxX : Float) : ElkRectangle :=
  -- Center the label
  let r := { r with x := portPosition.x - (r.width - portSize.x) / 2.0 }
  -- Make sure it doesn't slide past the port
  let actualMinX := fmin minX portPosition.x
  let actualMaxX := fmax maxX (portPosition.x + portSize.x)
  -- Keep inside the boundaries
  if r.x < actualMinX then { r with x := actualMinX }
  else if r.x + r.width > actualMaxX then { r with x := actualMaxX - r.width }
  else r

/-- `constrainedInsidePortLabelPlacement(nodeContext, portSide)`: EAST/WEST revert to the simple
placement; NORTH/SOUTH label cells are centered below/above their ports within the inside port
label cell's content area and stacked by a `DOWN`/`UP` overlap removal starting next to the
ports; the strip height becomes the inside port label cell's content height. -/
private def constrainedInsidePortLabelPlacement (ctx : NodeContext N P L) (portSide : PortSide) :
    NodeContext N P L := Id.run do
  -- For East/West, simply revert to the simple placement
  if portSide == .east || portSide == .west then
    return simpleInsidePortLabelPlacement ctx portSide
  let overlapRemovalDirection : OverlapRemovalDirection := if portSide == .north then .down else .up
  let verticalLabelAlignment : VerticalLabelAlignment := if portSide == .north then .top else .bottom
  -- Cell boundaries
  let some insideCell := ctx.insidePortLabelCell portSide | return ctx
  let labelContainerRect := ctx.cells.cellRectangle insideCell
  let cellPadding := ctx.cells.padding insideCell
  let leftBorder := labelContainerRect.x +
    fmax (fmax cellPadding.left ctx.surroundingPortMargins.left) ctx.nodeLabelSpacing
  let rightBorder := labelContainerRect.x + labelContainerRect.width -
    fmax (fmax cellPadding.right ctx.surroundingPortMargins.right) ctx.nodeLabelSpacing
  let portLabelSpacingH := ctx.portLabelSpacingHorizontal
  let portLabelSpacingV := ctx.portLabelSpacingVertical
  -- Prepare the overlap remover
  let mut overlapRemover := (RectangleStripOverlapRemover.createForDirection overlapRemovalDirection).withGap
    portLabelSpacingH portLabelSpacingV
  -- First pass: set up the rectangles and add them to the overlap remover
  let mut startCoordinate := if portSide == .north then Float.negInf else Float.posInf
  let mut cells := ctx.cells
  let mut added : Array CellId := #[]
  for pc in ctx.portContextsOf portSide do
    let some lc := labelCellWithLabels? cells pc | continue
    let portSize := pc.portSize
    let portPosition := pc.portPosition
    let (cells', _, _) := sizeLabelCell cells lc
    cells := (cells'.setVerticalAlignment lc verticalLabelAlignment).setHorizontalAlignment lc .right
    -- Center the label, keeping it within the boundaries
    cells := cells.modifyCellRectangle lc fun r => centerPortLabel r portPosition portSize leftBorder rightBorder
    -- Add it to the overlap remover
    overlapRemover := overlapRemover.addRectangle (cells.cellRectangle lc)
    added := added.push lc
    -- Update the start coordinate
    if portSide == .north then
      startCoordinate := fmax startCoordinate (portPosition.y + portSize.y)
    else
      startCoordinate := fmin startCoordinate portPosition.y
  -- Offset the start coordinate by the port-label spacing
  startCoordinate := startCoordinate + (if portSide == .north then portLabelSpacingV else -portLabelSpacingV)
  -- Invoke the overlap removal and write the new coordinates back
  let (rects, stripHeight) := (overlapRemover.withStartCoordinate startCoordinate).removeOverlaps
  for (lc, r) in added.zip rects do
    cells := cells.setCellRectangle lc r
  let mut ctx := { ctx with cells }
  if stripHeight > 0.0 then
    ctx := setInsideNorthSouthLabelCellHeight ctx portSide stripHeight
  -- Second pass: make the label cell coordinates relative to the port positions
  return makeLabelCellsRelative ctx portSide

/-! ### Simple outside port labels -/

/-- `simpleOutsidePortLabelPlacement(nodeContext, portSide)`: places the label cells outside the
node: next to (centered on) the port, or beside it (on the far side for the first port if
`isFirstOutsidePortLabelPlacedDifferently`, or for every port with `ALWAYS_OTHER_SAME_SIDE`). -/
private def simpleOutsidePortLabelPlacement (ctx : NodeContext N P L) (portSide : PortSide) : NodeContext N P L := Id.run do
  let placeFirstPortDifferently := NodeLabelAndSizeUtilities.isFirstOutsidePortLabelPlacedDifferently ctx portSide
  let alwaysAbove := ctx.portLabelsPlacement.contains .alwaysOtherSameSide
  let portLabelSpacingH := ctx.portLabelSpacingHorizontal
  let portLabelSpacingV := ctx.portLabelSpacingVertical
  let portLabelsTreatAsGroup := ctx.portLabelsTreatAsGroup
  let mut firstSpecial := placeFirstPortDifferently
  let mut cells := ctx.cells
  for pc in ctx.portContextsOf portSide do
    let some lc := labelCellWithLabels? cells pc | continue
    let portSize := pc.portSize
    let labelsNextToPort := pc.labelsNextToPort
    let (cells', minWidth, minHeight) := sizeLabelCell cells lc
    cells := cells'
    match portSide with
    | .north | .south =>
      if labelsNextToPort then
        cells := cells.modifyCellRectangle lc fun r => { r with x := (portSize.x - minWidth) / 2.0 }
        cells := cells.setHorizontalAlignment lc .center
      else if firstSpecial || alwaysAbove then
        cells := cells.modifyCellRectangle lc fun r => { r with x := -minWidth - portLabelSpacingH }
        cells := cells.setHorizontalAlignment lc .right
      else
        cells := cells.modifyCellRectangle lc fun r => { r with x := portSize.x + portLabelSpacingH }
        cells := cells.setHorizontalAlignment lc .left
      if portSide == .north then
        cells := cells.modifyCellRectangle lc fun r => { r with y := -minHeight - portLabelSpacingV }
        cells := cells.setVerticalAlignment lc .bottom
      else
        cells := cells.modifyCellRectangle lc fun r => { r with y := portSize.y + portLabelSpacingV }
        cells := cells.setVerticalAlignment lc .top
    | .east | .west =>
      let firstHeight := if !portLabelsTreatAsGroup then firstLabelHeight cells lc else 0.0
      if labelsNextToPort then
        let labelHeight := if portLabelsTreatAsGroup then minHeight else firstHeight
        cells := cells.modifyCellRectangle lc fun r => { r with y := (portSize.y - labelHeight) / 2.0 }
        cells := cells.setVerticalAlignment lc .center
      else if firstSpecial || alwaysAbove then
        cells := cells.modifyCellRectangle lc fun r => { r with y := -minHeight - portLabelSpacingV }
        cells := cells.setVerticalAlignment lc .bottom
      else
        cells := cells.modifyCellRectangle lc fun r => { r with y := portSize.y + portLabelSpacingV }
        cells := cells.setVerticalAlignment lc .top
      if portSide == .east then
        cells := cells.modifyCellRectangle lc fun r => { r with x := portSize.x + portLabelSpacingH }
        cells := cells.setHorizontalAlignment lc .left
      else
        cells := cells.modifyCellRectangle lc fun r => { r with x := -minWidth - portLabelSpacingH }
        cells := cells.setHorizontalAlignment lc .right
    | .undefined => pure ()
    -- The next port doesn't have special needs
    firstSpecial := false
  return { ctx with cells }

/-! ### Constrained outside port labels -/

/-- `constrainedOutsidePortLabelPlacement(nodeContext, portSide)`: with at most two ports or on
EAST/WEST, reverts to the simple placement; otherwise the NORTH/SOUTH label cells are placed
right of their ports (the first one left of it with `SPACE_EFFICIENT`) and stacked by an
`UP`/`DOWN` overlap removal starting next to the ports. -/
private def constrainedOutsidePortLabelPlacement (ctx : NodeContext N P L) (portSide : PortSide) :
    NodeContext N P L := Id.run do
  let portCount := (ctx.portContextsOf portSide).size
  -- If at most 2 ports or E/W, revert to the simple placement
  if portCount <= 2 || portSide == .east || portSide == .west then
    return simpleOutsidePortLabelPlacement ctx portSide
  let mut portWithSpecialNeeds := ctx.portLabelsPlacement.contains .spaceEfficient
  let overlapRemovalDirection : OverlapRemovalDirection := if portSide == .north then .up else .down
  let verticalLabelAlignment : VerticalLabelAlignment := if portSide == .north then .bottom else .top
  let portLabelSpacingH := ctx.portLabelSpacingHorizontal
  let portLabelSpacingV := ctx.portLabelSpacingVertical
  -- Prepare the overlap remover (Java/elk-rs pass the vertical spacing as the horizontal gap)
  let mut overlapRemover := (RectangleStripOverlapRemover.createForDirection overlapRemovalDirection).withGap
    portLabelSpacingV portLabelSpacingH
  let mut startCoordinate := if portSide == .north then Float.posInf else Float.negInf
  let mut cells := ctx.cells
  let mut added : Array CellId := #[]
  for pc in ctx.portContextsOf portSide do
    let some lc := labelCellWithLabels? cells pc | continue
    let portSize := pc.portSize
    let portPosition := pc.portPosition
    let (cells', minWidth, _) := sizeLabelCell cells lc
    cells := cells'
    if portWithSpecialNeeds then
      cells := cells.modifyCellRectangle lc fun r => { r with x := portPosition.x - minWidth - portLabelSpacingH }
      portWithSpecialNeeds := false
    else
      cells := cells.modifyCellRectangle lc fun r => { r with x := portPosition.x + portSize.x + portLabelSpacingH }
    cells := (cells.setVerticalAlignment lc verticalLabelAlignment).setHorizontalAlignment lc .right
    -- Add it to the overlap remover
    overlapRemover := overlapRemover.addRectangle (cells.cellRectangle lc)
    added := added.push lc
    -- Update the start coordinate
    if portSide == .north then
      startCoordinate := fmin startCoordinate portPosition.y
    else
      startCoordinate := fmax startCoordinate (portPosition.y + portSize.y)
  -- Offset the start coordinate
  startCoordinate := startCoordinate + (if portSide == .north then -portLabelSpacingV else portLabelSpacingV)
  -- Invoke the overlap removal (the strip size is not needed) and write the new coordinates back
  let (rects, _) := (overlapRemover.withStartCoordinate startCoordinate).removeOverlaps
  for (lc, r) in added.zip rects do
    cells := cells.setCellRectangle lc r
  -- Make the coordinates relative to the port positions
  return makeLabelCellsRelative { ctx with cells } portSide

/-! ### Entry points -/

/-- `placePortLabels(nodeContext, portSide)`: inside or outside placement, constrained if port
labels were not part of the size constraints or the ports have fixed positions. Fixed port
labels are left alone. -/
private def placePortLabels (ctx : NodeContext N P L) (portSide : PortSide) : NodeContext N P L :=
  let constrainedPlacement := !ctx.sizeConstraints.contains .portLabels || ctx.portConstraints == .fixedPos
  if ctx.portLabelsPlacement.contains .inside then
    if constrainedPlacement then constrainedInsidePortLabelPlacement ctx portSide
    else simpleInsidePortLabelPlacement ctx portSide
  else if ctx.portLabelsPlacement.contains .outside then
    if constrainedPlacement then constrainedOutsidePortLabelPlacement ctx portSide
    else simpleOutsidePortLabelPlacement ctx portSide
  else ctx

/-- `placeHorizontalPortLabels(nodeContext)`: places the labels of northern, then southern ports.
For inside labels, the height they need becomes the content height of the northern/southern
inside port label cells. -/
def placeHorizontalPortLabels (ctx : NodeContext N P L) : NodeContext N P L :=
  placePortLabels (placePortLabels ctx .north) .south

/-- `placeVerticalPortLabels(nodeContext)`: places the labels of eastern, then western ports. -/
def placeVerticalPortLabels (ctx : NodeContext N P L) : NodeContext N P L :=
  placePortLabels (placePortLabels ctx .east) .west

end PortLabelPlacementCalculator

end Elk.Alg.Common.NodeSpacing.Internal.Algorithm
