import Elk.Core.Util.Sort
import Elk.Core.Util.ElkUtil
import Elk.Alg.Common.NodeSpacing.Internal
import Elk.Alg.Common.NodeSpacing.Internal.AlgorithmCells
import Elk.Alg.Common.NodeSpacing.Internal.AlgorithmPorts
/-!
# `org.eclipse.elk.alg.common.nodespacing.NodeLabelAndSizeCalculator`

Calculates node sizes, places ports and places node and port labels (elk-rs
`nodespacing::node_label_and_size_calculator`). Java puts the class directly into `nodespacing`;
the `Calculators` directory is only a file grouping. Every entry point is generic over the
`GraphAdapters` record.

Two independent paths, both ported from elk-rs (the oracle):
* `processWithOptions` (`process` = `applyStuff := true, ignoreInsidePortLabels := false`): Java's
  7-phase cell-system pipeline on the `internal.algorithm` modules.
* `processNode`: the simplified elk-rs path with its own label layout structures
  (`LabelCellLayout`, `StripContainerLayout`, `InsideLabelLayoutGrid`, `layoutAxisThree`). It has no
  Java counterpart; elk-rs' `NodeDimensionCalculation` uses it for most nodes.
`computeInsideNodeLabelPadding` / `computeInsideNodeLabelContainerMinimumSize` use the elk-rs
`InsideNodeLabelGrid` (label sizes only, no label handles).

Oracle facts reproduced on purpose:
* `processWithOptions` computes the node padding (`NodeLabelAndSizeUtilities.computeNodePadding`,
  elk-rs `set_node_padding`) but discards it, so `COMPUTE_PADDING` never changes the node there;
  `processNode` does apply its own computed padding.
* `processWithOptions` applies the node size and then the port positions, port contexts sorted by
  volatile id and zipped with `NodeAdapter.getPorts()` (the volatile id is the port index).
* `PortContext.portRatioOrPosition` stays `0.0` (see `PortContextCreator`).
* The horizontal layout mode of label cells is `!layoutDirection.isVertical` (Java reads the
  parent graph's `DIRECTION` instead).
* `computeInsideNodeLabelPadding` inherits spacings from the node's parent graph (Java creates its
  `NodeContext` without a parent graph).

Deviations from elk-rs:
* The `ElkTrace` (`sizing`, `sizingLabels`) and `DEBUG_NODE_LABEL_PADDING` diagnostics only print
  to stderr and are not ported (the functions are generic over the monad).
* elk-rs' `DynLabel` type erasure is unnecessary: the layout structures hold the label handles
  `L` and write positions through `ElementOps.setPosition`. The private `Rect` is `ElkRectangle`,
  `[f64; 3]` area arrays are `Array Float` of size 3 indexed by `ContainerArea.index`, and the
  reused `ContainerArea`/`HorizontalLabelAlignment`/`VerticalLabelAlignment` are the cell system
  enums (identical to the elk-rs file-private copies).
-/
namespace Elk.Alg.Common.NodeSpacing

open Elk Elk.Core.Math Elk.Core.Util Elk.Core.Options Elk.Core.Util.Adapters
open Elk.Alg.Common.NodeSpacing.CellSystem Elk.Alg.Common.NodeSpacing.Internal
open Elk.Alg.Common.NodeSpacing.Internal.Algorithm

namespace NodeLabelAndSizeCalculator

variable {m : Type → Type} [Monad m] {G N P L E : Type}

/-! ### Small helpers -/

/-- elk-rs file-private `OutsideSide`: the node side of an outside node label strip. -/
elk_enum OutsideSide := north south east west

/-- `values[area.index()]` of an elk-rs `[f64; 3]` (`0.0` if out of range, which cannot happen). -/
@[inline] def at3 (values : Array Float) (area : ContainerArea) : Float :=
  values.getD area.index 0.0

/-- Gives BEGIN and END the larger of their two values (the `symmetrical` step of elk-rs'
`min_column_widths` / `min_row_heights` / `min_cell_widths` / `min_cell_heights`). -/
def symmetrize (values : Array Float) : Array Float :=
  let side := fmax (at3 values .begin) (at3 values .«end»)
  (values.setIfInBounds ContainerArea.begin.index side).setIfInBounds ContainerArea.«end».index side

/-- elk-rs `sum_with_gaps_with_gap(values, gap)`: the sum of the positive values plus one gap
between each two of them. -/
def sumWithGapsWithGap (values : Array Float) (gap : Float) : Float := Id.run do
  let mut sum := 0.0
  let mut activeCount : Nat := 0
  for value in values do
    if value > 0.0 then
      sum := sum + value
      activeCount := activeCount + 1
  if activeCount > 1 then
    sum := sum + gap * (activeCount - 1).toFloat
  return sum

/-- `values.into_iter().fold(0.0, f64::max)`. -/
@[inline] def maxOf (values : Array Float) : Float := values.foldl fmax 0.0

/-! ### `CellMinSize` -/

/-- elk-rs file-private `CellMinSize`: the minimum content size of a label cell and the number of
labels added so far. -/
structure CellMinSize where
  /-- Minimum width. -/
  width : Float := 0.0
  /-- Minimum height. -/
  height : Float := 0.0
  /-- Number of labels added. -/
  labelCount : Nat := 0
  deriving Inhabited, Repr

namespace CellMinSize

/-- elk-rs `CellMinSize::add_label(label_size, gap, horizontal_layout_mode)`: in horizontal layout
mode labels are stacked vertically (width = max, height = sum plus gaps), otherwise side by side. -/
def addLabel (s : CellMinSize) (labelSize : KVector) (gap : Float) (horizontalLayoutMode : Bool) : CellMinSize :=
  if horizontalLayoutMode then
    let height := s.height + labelSize.y
    let height := if s.labelCount > 0 then height + gap else height
    { width := fmax s.width labelSize.x, height, labelCount := s.labelCount + 1 }
  else
    let width := s.width + labelSize.x
    let width := if s.labelCount > 0 then width + gap else width
    { width, height := fmax s.height labelSize.y, labelCount := s.labelCount + 1 }

end CellMinSize

/-! ### `LabelCellLayout` -/

/-- elk-rs file-private `LabelCellLayout`: the labels of one cell of the simplified `processNode`
path, their minimum content size and their alignment. -/
structure LabelCellLayout (L : Type) where
  /-- The labels, in insertion order. -/
  labels : Array L := #[]
  /-- `minimum_content_area_size`. -/
  minimumContentAreaSize : CellMinSize := {}
  /-- Horizontal alignment of the labels inside the cell. -/
  horizontalAlignment : HorizontalLabelAlignment
  /-- Vertical alignment of the labels inside the cell. -/
  verticalAlignment : VerticalLabelAlignment
  /-- Labels are stacked vertically if `true`, placed side by side otherwise. -/
  horizontalLayoutMode : Bool
  /-- Gap between two labels. -/
  labelGap : Float
  deriving Inhabited

namespace LabelCellLayout

/-- elk-rs `LabelCellLayout::new(horizontal_alignment, vertical_alignment, horizontal_layout_mode,
label_gap)`: an empty cell. -/
def new (horizontalAlignment : HorizontalLabelAlignment) (verticalAlignment : VerticalLabelAlignment)
    (horizontalLayoutMode : Bool) (labelGap : Float) : LabelCellLayout L :=
  { horizontalAlignment, verticalAlignment, horizontalLayoutMode, labelGap }

/-- elk-rs `LabelCellLayout::add_label(label)`: grows the minimum content size by the label's
size (read by the caller with `label.getSize()`, like elk-rs' `DynLabel::get_size`) and appends the
label. -/
def addLabel (c : LabelCellLayout L) (label : L) (size : KVector) : LabelCellLayout L :=
  { c with
    minimumContentAreaSize := c.minimumContentAreaSize.addLabel size c.labelGap c.horizontalLayoutMode
    labels := c.labels.push label }

/-- elk-rs `LabelCellLayout::min_width()`. -/
@[inline] def minWidth (c : LabelCellLayout L) : Float := c.minimumContentAreaSize.width

/-- elk-rs `LabelCellLayout::min_height()`. -/
@[inline] def minHeight (c : LabelCellLayout L) : Float := c.minimumContentAreaSize.height

/-- elk-rs `LabelCellLayout::apply_horizontal_layout(rect)`: stacks the labels from the top of the
rectangle (shifted by the free height for CENTER/BOTTOM alignment), each one aligned horizontally
in the rectangle. Label sizes are re-read through `ops.getSize`. -/
def applyHorizontalLayout (ops : ElementOps m L) (c : LabelCellLayout L) (rect : ElkRectangle) : m Unit := do
  let mut yPos := rect.y
  if c.verticalAlignment == .center then
    yPos := yPos + (rect.height - c.minimumContentAreaSize.height) / 2.0
  else if c.verticalAlignment == .bottom then
    yPos := yPos + (rect.height - c.minimumContentAreaSize.height)
  for label in c.labels do
    let size ← ops.getSize label
    let posY := yPos
    yPos := yPos + (size.y + c.labelGap)
    let posX := match c.horizontalAlignment with
      | .left => rect.x
      | .center => rect.x + (rect.width - size.x) / 2.0
      | .right => rect.x + rect.width - size.x
    ops.setPosition label ⟨posX, posY⟩

/-- elk-rs `LabelCellLayout::apply_vertical_layout(rect)`: places the labels side by side from the
left of the rectangle (shifted by the free width for CENTER/RIGHT alignment), each one aligned
vertically in the rectangle. Label sizes are re-read through `ops.getSize`. -/
def applyVerticalLayout (ops : ElementOps m L) (c : LabelCellLayout L) (rect : ElkRectangle) : m Unit := do
  let mut xPos := rect.x
  if c.horizontalAlignment == .center then
    xPos := xPos + (rect.width - c.minimumContentAreaSize.width) / 2.0
  else if c.horizontalAlignment == .right then
    xPos := xPos + (rect.width - c.minimumContentAreaSize.width)
  for label in c.labels do
    let size ← ops.getSize label
    let posX := xPos
    xPos := xPos + (size.x + c.labelGap)
    let posY := match c.verticalAlignment with
      | .top => rect.y
      | .center => rect.y + (rect.height - size.y) / 2.0
      | .bottom => rect.y + rect.height - size.y
    ops.setPosition label ⟨posX, posY⟩

/-- elk-rs `LabelCellLayout::apply_layout(rect)`: nothing without labels, else the horizontal or
vertical layout depending on the layout mode. -/
def applyLayout (ops : ElementOps m L) (c : LabelCellLayout L) (rect : ElkRectangle) : m Unit := do
  if c.labels.isEmpty then return
  if c.horizontalLayoutMode then
    applyHorizontalLayout ops c rect
  else
    applyVerticalLayout ops c rect

end LabelCellLayout

/-! ### Placement helpers -/

/-- elk-rs `inside_cell_for_placement(placement)`: the (row, column) of an inside placement
(`INSIDE` without `OUTSIDE`, one vertical and one horizontal flag; the first of TOP/CENTER/BOTTOM
and LEFT/CENTER/RIGHT wins), else `none`. -/
def insideCellForPlacement (placement : EnumSet NodeLabelPlacement) : Option (ContainerArea × ContainerArea) :=
  if !placement.contains .inside || placement.contains .outside then none
  else
    let row : Option ContainerArea :=
      if placement.contains .vTop then some .begin
      else if placement.contains .vCenter then some .center
      else if placement.contains .vBottom then some .«end»
      else none
    let col : Option ContainerArea :=
      if placement.contains .hLeft then some .begin
      else if placement.contains .hCenter then some .center
      else if placement.contains .hRight then some .«end»
      else none
    match row, col with
    | some r, some c => some (r, c)
    | _, _ => none

/-- elk-rs `horizontal_alignment_for_area_index(index)`: 0 → LEFT, 1 → CENTER, otherwise RIGHT. -/
def horizontalAlignmentForAreaIndex (index : Nat) : HorizontalLabelAlignment :=
  match index with
  | 0 => .left
  | 1 => .center
  | _ => .right

/-- elk-rs `vertical_alignment_for_area_index(index)`: 0 → TOP, 1 → CENTER, otherwise BOTTOM. -/
def verticalAlignmentForAreaIndex (index : Nat) : VerticalLabelAlignment :=
  match index with
  | 0 => .top
  | 1 => .center
  | _ => .bottom

/-- elk-rs `horizontal_alignment_for_placement(placement)`: H_LEFT, H_CENTER, H_RIGHT in that
priority, else `none`. -/
def horizontalAlignmentForPlacement (placement : EnumSet NodeLabelPlacement) : Option HorizontalLabelAlignment :=
  if placement.contains .hLeft then some .left
  else if placement.contains .hCenter then some .center
  else if placement.contains .hRight then some .right
  else none

/-- elk-rs `vertical_alignment_for_placement(placement)`: V_TOP, V_CENTER, V_BOTTOM in that
priority, else `none`. -/
def verticalAlignmentForPlacement (placement : EnumSet NodeLabelPlacement) : Option VerticalLabelAlignment :=
  if placement.contains .vTop then some .top
  else if placement.contains .vCenter then some .center
  else if placement.contains .vBottom then some .bottom
  else none

/-- elk-rs `area_for_horizontal_alignment`: LEFT → BEGIN, CENTER → CENTER, RIGHT → END. -/
def areaForHorizontalAlignment : HorizontalLabelAlignment → ContainerArea
  | .left => .begin
  | .center => .center
  | .right => .«end»

/-- elk-rs `area_for_vertical_alignment`: TOP → BEGIN, CENTER → CENTER, BOTTOM → END. -/
def areaForVerticalAlignment : VerticalLabelAlignment → ContainerArea
  | .top => .begin
  | .center => .center
  | .bottom => .«end»

/-- elk-rs file-private `NodeLabelLocationInfo`: where a node label of the `processNode` path
goes (inside grid cell, or outside strip `outsideSide` at `row`/`col`). -/
structure NodeLabelLocationInfo where
  /-- Inside the node. -/
  inside : Bool
  /-- Row (BEGIN = top). -/
  row : ContainerArea
  /-- Column (BEGIN = left). -/
  col : ContainerArea
  /-- The outside strip (`none` for inside labels). -/
  outsideSide : Option OutsideSide
  deriving Inhabited, Repr, BEq

/-- elk-rs `node_label_location_info_for_placement(placement)`: `none` unless exactly one of
INSIDE/OUTSIDE is set and both alignments are given. Inside labels go to the grid cell of their
alignments. Outside labels with H_PRIORITY go to the WEST/EAST strip for LEFT/RIGHT alignment and to
NORTH/SOUTH for CENTER (TOP/BOTTOM; CENTER/CENTER is `none`); without H_PRIORITY they go to
NORTH/SOUTH for TOP/BOTTOM and to WEST/EAST for CENTER (LEFT/RIGHT; CENTER/CENTER is `none`). -/
def nodeLabelLocationInfoForPlacement (placement : EnumSet NodeLabelPlacement) : Option NodeLabelLocationInfo :=
  let inside := placement.contains .inside
  let outside := placement.contains .outside
  if inside == outside then none
  else
    match horizontalAlignmentForPlacement placement, verticalAlignmentForPlacement placement with
    | some horizontalAlignment, some verticalAlignment =>
      let row := areaForVerticalAlignment verticalAlignment
      let col := areaForHorizontalAlignment horizontalAlignment
      if inside then
        some { inside := true, row, col, outsideSide := none }
      else if placement.contains .hPriority then
        match horizontalAlignment, verticalAlignment with
        | .left, _ => some { inside := false, row, col := .begin, outsideSide := some .west }
        | .right, _ => some { inside := false, row, col := .«end», outsideSide := some .east }
        | .center, .top => some { inside := false, row := .begin, col := .center, outsideSide := some .north }
        | .center, .bottom => some { inside := false, row := .«end», col := .center, outsideSide := some .south }
        | .center, .center => none
      else
        match verticalAlignment, horizontalAlignment with
        | .top, _ => some { inside := false, row := .begin, col, outsideSide := some .north }
        | .bottom, _ => some { inside := false, row := .«end», col, outsideSide := some .south }
        | .center, .left => some { inside := false, row := .center, col := .begin, outsideSide := some .west }
        | .center, .right => some { inside := false, row := .center, col := .«end», outsideSide := some .east }
        | .center, .center => none
    | _, _ => none

/-- elk-rs `has_effectively_fixed_size_constraints(size_constraints)`: empty or exactly
`{PORT_LABELS}`. -/
def hasEffectivelyFixedSizeConstraints (sizeConstraints : EnumSet SizeConstraint) : Bool :=
  sizeConstraints.isEmpty || (sizeConstraints.size == 1 && sizeConstraints.contains .portLabels)

/-- elk-rs `configured_minimum_size(node, size_options)`: `NODE_SIZE_MINIMUM`, non-positive
components replaced by `ElkUtil.DEFAULT_MIN_WIDTH/HEIGHT` if `DEFAULT_MINIMUM_SIZE` is set. -/
def configuredMinimumSize (a : GraphAdapters m G N P L E) (node : N) (sizeOptions : EnumSet SizeOptions) :
    m KVector := do
  let mut minimumSize ← a.node.getPropertyD node CoreOptions.NODE_SIZE_MINIMUM KVector.zero
  if sizeOptions.contains .defaultMinimumSize then
    if minimumSize.x <= 0.0 then
      minimumSize := { minimumSize with x := ElkUtil.DEFAULT_MIN_WIDTH }
    if minimumSize.y <= 0.0 then
      minimumSize := { minimumSize with y := ElkUtil.DEFAULT_MIN_HEIGHT }
  return minimumSize

/-- The effective `NODE_LABELS_PLACEMENT` of a node label: its own value if set (elk-rs
`label.has_property` then `get_property(..).unwrap_or_else(default)`), else the node's default. -/
def effectiveNodeLabelPlacement (a : GraphAdapters m G N P L E) (label : L)
    (defaultPlacement : EnumSet NodeLabelPlacement) : m (EnumSet NodeLabelPlacement) := do
  if ← a.label.hasProp label CoreOptions.NODE_LABELS_PLACEMENT then
    return (← a.label.getProperty label CoreOptions.NODE_LABELS_PLACEMENT).getD defaultPlacement
  else
    return defaultPlacement

/-! ### `InsideNodeLabelGrid` (padding / container minimum size) -/

/-- elk-rs file-private `InsideNodeLabelGrid`: the minimum sizes of the 3×3 inside node label
cells (`cells[row][col]`) with the grid settings, for `computeInsideNodeLabelPadding` and
`computeInsideNodeLabelContainerMinimumSize`. -/
structure InsideNodeLabelGrid where
  /-- Minimum cell sizes, `cells[row.index][col.index]`. -/
  cells : Array (Array CellMinSize)
  /-- Gap between two cells (`2 * labelGap`). -/
  containerGap : Float
  /-- Gap between two labels (`SPACING_LABEL_LABEL`). -/
  labelGap : Float
  /-- `NODE_LABELS_PADDING`. -/
  padding : ElkPadding
  /-- `FORCE_TABULAR_NODE_LABELS`. -/
  tabular : Bool
  /-- Not `ASYMMETRICAL`. -/
  symmetrical : Bool
  /-- The client area minimum size (`MINIMUM_SIZE` + `MINIMUM_SIZE_ACCOUNTS_FOR_PADDING`). -/
  centerCellMinSize : Option KVector
  deriving Inhabited

namespace InsideNodeLabelGrid

/-- `cells[row][col]`. -/
def cell (g : InsideNodeLabelGrid) (row col : ContainerArea) : CellMinSize :=
  (g.cells.getD row.index #[]).getD col.index {}

/-- Updates `cells[row][col]`. -/
def modifyCell (g : InsideNodeLabelGrid) (row col : ContainerArea) (f : CellMinSize → CellMinSize) :
    InsideNodeLabelGrid :=
  { g with cells := g.cells.modify row.index (·.modify col.index f) }

/-- elk-rs `InsideNodeLabelGrid::new(node, layout_direction)`: reads the grid settings (spacings
individual or inherited) and adds the size of every node label with an inside placement
(`insideCellForPlacement`) to its cell, in label order; the center cell minimum size is the
configured minimum size if `MINIMUM_SIZE` and `MINIMUM_SIZE_ACCOUNTS_FOR_PADDING` are set. -/
def new (a : GraphAdapters m G N P L E) (node : N) (layoutDirection : Direction) : m InsideNodeLabelGrid := do
  let sizeOptions ← a.node.getPropertyD node CoreOptions.NODE_SIZE_OPTIONS EnumSet.empty
  let labelGap := (← a.getIndividualOrInherited node CoreOptions.SPACING_LABEL_LABEL).getD 0.0
  let containerGap := 2.0 * labelGap
  let padding := (← a.getIndividualOrInherited node CoreOptions.NODE_LABELS_PADDING).getD {}
  let mut grid : InsideNodeLabelGrid := {
    cells := Array.replicate 3 (Array.replicate 3 {})
    containerGap, labelGap, padding
    tabular := sizeOptions.contains .forceTabularNodeLabels
    symmetrical := !sizeOptions.contains .asymmetrical
    centerCellMinSize := none }
  let defaultNodeLabelPlacement ← a.node.getPropertyD node CoreOptions.NODE_LABELS_PLACEMENT EnumSet.empty
  let horizontalLayoutMode := !layoutDirection.isVertical
  for label in ← a.nodeLabels node do
    let effectivePlacement ← effectiveNodeLabelPlacement a label defaultNodeLabelPlacement
    if let some (row, col) := insideCellForPlacement effectivePlacement then
      let size ← a.label.getSize label
      let gap := grid.labelGap
      grid := grid.modifyCell row col (·.addLabel size gap horizontalLayoutMode)
  let sizeConstraints ← a.node.getPropertyD node CoreOptions.NODE_SIZE_CONSTRAINTS EnumSet.empty
  if sizeConstraints.contains .minimumSize && sizeOptions.contains .minimumSizeAccountsForPadding then
    grid := { grid with centerCellMinSize := some (← configuredMinimumSize a node sizeOptions) }
  return grid

/-- elk-rs `InsideNodeLabelGrid::compute_inside_padding()`: top/bottom = highest cell of the top /
bottom row, left/right = widest cell of the left / right column; each positive side additionally
gets the node labels padding of that side and the container gap. -/
def computeInsidePadding (g : InsideNodeLabelGrid) : ElkPadding := Id.run do
  let mut padding : ElkPadding := {}
  for col in ContainerArea.values do
    padding := { padding with top := fmax padding.top (g.cell .begin col).height }
  for col in ContainerArea.values do
    padding := { padding with bottom := fmax padding.bottom (g.cell .«end» col).height }
  for row in ContainerArea.values do
    padding := { padding with left := fmax padding.left (g.cell row .begin).width }
  for row in ContainerArea.values do
    padding := { padding with right := fmax padding.right (g.cell row .«end»).width }
  if padding.top > 0.0 then
    padding := { padding with top := padding.top + (g.padding.top + g.containerGap) }
  if padding.bottom > 0.0 then
    padding := { padding with bottom := padding.bottom + (g.padding.bottom + g.containerGap) }
  if padding.left > 0.0 then
    padding := { padding with left := padding.left + (g.padding.left + g.containerGap) }
  if padding.right > 0.0 then
    padding := { padding with right := padding.right + (g.padding.right + g.containerGap) }
  return padding

/-- elk-rs `InsideNodeLabelGrid::min_column_widths(row)`: per column the cell width in `row`, or
the widest cell of the column (`none`); the center column is at least the center cell minimum
width; BEGIN/END get the same width if symmetrical. -/
def minColumnWidths (g : InsideNodeLabelGrid) (row : Option ContainerArea) : Array Float := Id.run do
  let mut colWidths : Array Float := #[0.0, 0.0, 0.0]
  for col in ContainerArea.values do
    let maxWidth := match row with
      | some r => (g.cell r col).width
      | none => ContainerArea.values.foldl (fun acc iterRow => fmax acc (g.cell iterRow col).width) 0.0
    colWidths := colWidths.setIfInBounds col.index maxWidth
  if let some centerMinSize := g.centerCellMinSize then
    colWidths := colWidths.setIfInBounds ContainerArea.center.index (fmax (at3 colWidths .center) centerMinSize.x)
  if g.symmetrical then
    colWidths := symmetrize colWidths
  return colWidths

/-- elk-rs `InsideNodeLabelGrid::min_row_heights()`: per row the highest cell; the center row is
at least the center cell minimum height; BEGIN/END get the same height if symmetrical. -/
def minRowHeights (g : InsideNodeLabelGrid) : Array Float := Id.run do
  let mut rowHeights : Array Float := #[0.0, 0.0, 0.0]
  for row in ContainerArea.values do
    let maxHeight := ContainerArea.values.foldl (fun acc col => fmax acc (g.cell row col).height) 0.0
    rowHeights := rowHeights.setIfInBounds row.index maxHeight
  if let some centerMinSize := g.centerCellMinSize then
    rowHeights := rowHeights.setIfInBounds ContainerArea.center.index (fmax (at3 rowHeights .center) centerMinSize.y)
  if g.symmetrical then
    rowHeights := symmetrize rowHeights
  return rowHeights

/-- The grid width without padding: tabular → one sum over the column maxima, else the widest
row (elk-rs inline loop of `compute_minimum_size`). -/
def contentWidth (g : InsideNodeLabelGrid) : Float :=
  if g.tabular then sumWithGapsWithGap (g.minColumnWidths none) g.containerGap
  else ContainerArea.values.foldl
    (fun width row => fmax width (sumWithGapsWithGap (g.minColumnWidths (some row)) g.containerGap)) 0.0

/-- elk-rs `InsideNodeLabelGrid::compute_minimum_size(only_center_cell_contributes)`: the center
cell (or its configured minimum size) alone, or the grid content; positive components get the
node labels padding. -/
def computeMinimumSize (g : InsideNodeLabelGrid) (onlyCenterCellContributes : Bool) : KVector :=
  let (minWidth, minHeight) : Float × Float :=
    if onlyCenterCellContributes then
      match g.centerCellMinSize with
      | some centerMinSize => (centerMinSize.x, centerMinSize.y)
      | none =>
        let center := g.cell .center .center
        (center.width, center.height)
    else
      (g.contentWidth, sumWithGapsWithGap g.minRowHeights g.containerGap)
  let minWidth := if minWidth > 0.0 then minWidth + (g.padding.left + g.padding.right) else minWidth
  let minHeight := if minHeight > 0.0 then minHeight + (g.padding.top + g.padding.bottom) else minHeight
  ⟨minWidth, minHeight⟩

end InsideNodeLabelGrid

/-! ### Axis layout -/

/-- elk-rs file-private `AxisLayout`: start and span of the three areas along one axis and the
free (center) area. -/
structure AxisLayout where
  /-- Start coordinate of BEGIN, CENTER, END. -/
  starts : Array Float
  /-- Span of BEGIN, CENTER, END. -/
  spans : Array Float
  /-- Start of the free content area. -/
  centerAreaStart : Float
  /-- Span of the free content area (at least `0`). -/
  centerAreaSpan : Float
  deriving Inhabited, Repr

/-- elk-rs `layout_axis_three(start, span, padding_start, padding_end, min_spans, gap)`: BEGIN at
the padded start, END flush with the padded end, CENTER gets the free span (at least its minimum,
centered on the free span if larger); the free area is the free span clamped at `0`. -/
def layoutAxisThree (start span paddingStart paddingEnd : Float) (minSpans : Array Float) (gap : Float) :
    AxisLayout :=
  let minBegin := at3 minSpans .begin
  let minCenter := at3 minSpans .center
  let minEnd := at3 minSpans .«end»
  let freeContentSpan := span - paddingStart - paddingEnd
  let (startSpanWithGap, freeContentSpan) :=
    if minBegin > 0.0 then
      let s := minBegin + gap
      (s, freeContentSpan - s)
    else (minBegin, freeContentSpan)
  let freeContentSpan := if minEnd > 0.0 then freeContentSpan - (minEnd + gap) else freeContentSpan
  let centerSpan := fmax minCenter freeContentSpan
  let startPos := start + paddingStart
  let centerPos := start + paddingStart + startSpanWithGap - (centerSpan - freeContentSpan) / 2.0
  let endPos := start + span - paddingEnd - minEnd
  let clampedCenterSpan := fmax freeContentSpan 0.0
  let centerAreaStart := start + paddingStart + (clampedCenterSpan - freeContentSpan) / 2.0
  { starts := #[startPos, centerPos, endPos]
    spans := #[minBegin, centerSpan, minEnd]
    centerAreaStart
    centerAreaSpan := clampedCenterSpan }

/-! ### `StripContainerLayout` -/

/-- elk-rs file-private `StripContainerLayout`: an outside node label strip of three label cells
(horizontal for NORTH/SOUTH, vertical for WEST/EAST). -/
structure StripContainerLayout (L : Type) where
  /-- BEGIN, CENTER, END cells. -/
  cells : Array (LabelCellLayout L)
  /-- `true` for WEST/EAST strips (cells stacked vertically). -/
  verticalStrip : Bool
  /-- BEGIN and END get the same size. -/
  symmetrical : Bool
  /-- Gap between two cells. -/
  gap : Float
  /-- Padding (the label-node spacing towards the node). -/
  padding : ElkPadding
  deriving Inhabited

namespace StripContainerLayout

/-- elk-rs `StripContainerLayout::new_horizontal(...)`: LEFT/CENTER/RIGHT aligned cells with the
given vertical alignment. -/
def newHorizontal (symmetrical : Bool) (gap : Float) (padding : ElkPadding) (labelGap : Float)
    (horizontalLayoutMode : Bool) (verticalAlignment : VerticalLabelAlignment) : StripContainerLayout L :=
  { cells := #[LabelCellLayout.new .left verticalAlignment horizontalLayoutMode labelGap,
      LabelCellLayout.new .center verticalAlignment horizontalLayoutMode labelGap,
      LabelCellLayout.new .right verticalAlignment horizontalLayoutMode labelGap]
    verticalStrip := false, symmetrical, gap, padding }

/-- elk-rs `StripContainerLayout::new_vertical(...)`: TOP/CENTER/BOTTOM aligned cells with the
given horizontal alignment. -/
def newVertical (symmetrical : Bool) (gap : Float) (padding : ElkPadding) (labelGap : Float)
    (horizontalLayoutMode : Bool) (horizontalAlignment : HorizontalLabelAlignment) : StripContainerLayout L :=
  { cells := #[LabelCellLayout.new horizontalAlignment .top horizontalLayoutMode labelGap,
      LabelCellLayout.new horizontalAlignment .center horizontalLayoutMode labelGap,
      LabelCellLayout.new horizontalAlignment .bottom horizontalLayoutMode labelGap]
    verticalStrip := true, symmetrical, gap, padding }

/-- elk-rs `StripContainerLayout::add_label(area_index, label)`. -/
def addLabel (s : StripContainerLayout L) (area : ContainerArea) (label : L) (size : KVector) :
    StripContainerLayout L :=
  { s with cells := s.cells.modify area.index (·.addLabel label size) }

/-- elk-rs `StripContainerLayout::has_labels()`. -/
def hasLabels (s : StripContainerLayout L) : Bool := s.cells.any (!·.labels.isEmpty)

/-- Minimum width of one cell (`0` if missing). -/
private def cellMinWidth (s : StripContainerLayout L) (area : ContainerArea) : Float :=
  match s.cells[area.index]? with
  | some c => c.minWidth
  | none => 0.0

/-- Minimum height of one cell (`0` if missing). -/
private def cellMinHeight (s : StripContainerLayout L) (area : ContainerArea) : Float :=
  match s.cells[area.index]? with
  | some c => c.minHeight
  | none => 0.0

/-- elk-rs `StripContainerLayout::min_cell_widths()`. -/
def minCellWidths (s : StripContainerLayout L) : Array Float :=
  let widths := #[s.cellMinWidth .begin, s.cellMinWidth .center, s.cellMinWidth .«end»]
  if s.symmetrical then symmetrize widths else widths

/-- elk-rs `StripContainerLayout::min_cell_heights()`. -/
def minCellHeights (s : StripContainerLayout L) : Array Float :=
  let heights := #[s.cellMinHeight .begin, s.cellMinHeight .center, s.cellMinHeight .«end»]
  if s.symmetrical then symmetrize heights else heights

/-- elk-rs `StripContainerLayout::min_width()`: widest cell (vertical strip) or sum with gaps
(horizontal strip), plus left and right padding; `0` without labels. -/
def minWidth (s : StripContainerLayout L) : Float :=
  let width := if s.verticalStrip then maxOf s.minCellWidths else sumWithGapsWithGap s.minCellWidths s.gap
  if s.hasLabels then width + s.padding.left + s.padding.right else 0.0

/-- elk-rs `StripContainerLayout::min_height()`: sum with gaps (vertical strip) or highest cell
(horizontal strip), plus top and bottom padding; `0` without labels. -/
def minHeight (s : StripContainerLayout L) : Float :=
  let height := if s.verticalStrip then sumWithGapsWithGap s.minCellHeights s.gap else maxOf s.minCellHeights
  if s.hasLabels then height + s.padding.top + s.padding.bottom else 0.0

/-- elk-rs `apply_horizontal_strip_layout(rect)`: cells laid out along x by `layoutAxisThree`,
each spanning the padded height. -/
def applyHorizontalStripLayout (ops : ElementOps m L) (s : StripContainerLayout L) (rect : ElkRectangle) : m Unit := do
  let horizontalAxis := layoutAxisThree rect.x rect.width s.padding.left s.padding.right s.minCellWidths s.gap
  let y := rect.y + s.padding.top
  let height := fmax (rect.height - s.padding.top - s.padding.bottom) 0.0
  for area in ContainerArea.values do
    if let some cell := s.cells[area.index]? then
      cell.applyLayout ops
        { x := at3 horizontalAxis.starts area, y, width := at3 horizontalAxis.spans area, height }

/-- elk-rs `apply_vertical_strip_layout(rect)`: cells laid out along y by `layoutAxisThree`, each
spanning the padded width. -/
def applyVerticalStripLayout (ops : ElementOps m L) (s : StripContainerLayout L) (rect : ElkRectangle) : m Unit := do
  let x := rect.x + s.padding.left
  let width := fmax (rect.width - s.padding.left - s.padding.right) 0.0
  let verticalAxis := layoutAxisThree rect.y rect.height s.padding.top s.padding.bottom s.minCellHeights s.gap
  for area in ContainerArea.values do
    if let some cell := s.cells[area.index]? then
      cell.applyLayout ops
        { x, y := at3 verticalAxis.starts area, width, height := at3 verticalAxis.spans area }

/-- elk-rs `StripContainerLayout::apply_layout(rect)`. -/
def applyLayout (ops : ElementOps m L) (s : StripContainerLayout L) (rect : ElkRectangle) : m Unit :=
  if s.verticalStrip then applyVerticalStripLayout ops s rect else applyHorizontalStripLayout ops s rect

end StripContainerLayout

/-! ### `InsideLabelLayoutGrid` -/

/-- elk-rs file-private `InsideLabelLayoutGrid`: the 3×3 inside node label cells of the
`processNode` path (`cells[row][col]`, LEFT/CENTER/RIGHT by column and TOP/CENTER/BOTTOM by row),
the node labels padding and the node (cell) padding reserved for ports. -/
structure InsideLabelLayoutGrid (L : Type) where
  /-- The cells, `cells[row.index][col.index]`. -/
  cells : Array (Array (LabelCellLayout L))
  /-- Gap between two cells. -/
  containerGap : Float
  /-- `NODE_LABELS_PADDING` (individual or inherited). -/
  nodeLabelPadding : ElkPadding
  /-- Space reserved for ports (`setupNodePaddingForPortsWithOffset`), initially zero. -/
  nodePadding : ElkPadding
  /-- `FORCE_TABULAR_NODE_LABELS`. -/
  tabular : Bool
  /-- Not `ASYMMETRICAL`. -/
  symmetrical : Bool
  /-- The client area minimum size (`MINIMUM_SIZE` + `MINIMUM_SIZE_ACCOUNTS_FOR_PADDING`). -/
  centerCellMinSize : Option KVector
  deriving Inhabited

namespace InsideLabelLayoutGrid

/-- `cells[row][col]`. -/
def getCell (g : InsideLabelLayoutGrid L) (row col : ContainerArea) : Option (LabelCellLayout L) :=
  (g.cells[row.index]?).bind (·[col.index]?)

/-- Minimum width of `cells[row][col]` (`0` if missing). -/
def cellMinWidth (g : InsideLabelLayoutGrid L) (row col : ContainerArea) : Float :=
  match g.getCell row col with
  | some c => c.minWidth
  | none => 0.0

/-- Minimum height of `cells[row][col]` (`0` if missing). -/
def cellMinHeight (g : InsideLabelLayoutGrid L) (row col : ContainerArea) : Float :=
  match g.getCell row col with
  | some c => c.minHeight
  | none => 0.0

/-- Updates `cells[row][col]`. -/
def modifyCell (g : InsideLabelLayoutGrid L) (row col : ContainerArea)
    (f : LabelCellLayout L → LabelCellLayout L) : InsideLabelLayoutGrid L :=
  { g with cells := g.cells.modify row.index (·.modify col.index f) }

/-- elk-rs `InsideLabelLayoutGrid::add_label(row, col, label)`. -/
def addLabel (g : InsideLabelLayoutGrid L) (row col : ContainerArea) (label : L) (size : KVector) :
    InsideLabelLayoutGrid L :=
  g.modifyCell row col (·.addLabel label size)

/-- elk-rs `InsideLabelLayoutGrid::ensure_cell_min_width(row, col, width)`: the cell's minimum
content width becomes at least `width`. -/
def ensureCellMinWidth (g : InsideLabelLayoutGrid L) (row col : ContainerArea) (width : Float) :
    InsideLabelLayoutGrid L :=
  g.modifyCell row col fun c =>
    { c with minimumContentAreaSize := { c.minimumContentAreaSize with
        width := fmax c.minimumContentAreaSize.width width } }

/-- elk-rs `InsideLabelLayoutGrid::min_column_widths(row)` (see `InsideNodeLabelGrid.minColumnWidths`). -/
def minColumnWidths (g : InsideLabelLayoutGrid L) (row : Option ContainerArea) : Array Float := Id.run do
  let mut colWidths : Array Float := #[0.0, 0.0, 0.0]
  for col in ContainerArea.values do
    let maxWidth := match row with
      | some r => g.cellMinWidth r col
      | none => ContainerArea.values.foldl (fun acc iterRow => fmax acc (g.cellMinWidth iterRow col)) 0.0
    colWidths := colWidths.setIfInBounds col.index maxWidth
  if let some centerMinSize := g.centerCellMinSize then
    colWidths := colWidths.setIfInBounds ContainerArea.center.index (fmax (at3 colWidths .center) centerMinSize.x)
  if g.symmetrical then
    colWidths := symmetrize colWidths
  return colWidths

/-- elk-rs `InsideLabelLayoutGrid::min_row_heights()` (see `InsideNodeLabelGrid.minRowHeights`). -/
def minRowHeights (g : InsideLabelLayoutGrid L) : Array Float := Id.run do
  let mut rowHeights : Array Float := #[0.0, 0.0, 0.0]
  for row in ContainerArea.values do
    let maxHeight := ContainerArea.values.foldl (fun acc col => fmax acc (g.cellMinHeight row col)) 0.0
    rowHeights := rowHeights.setIfInBounds row.index maxHeight
  if let some centerMinSize := g.centerCellMinSize then
    rowHeights := rowHeights.setIfInBounds ContainerArea.center.index (fmax (at3 rowHeights .center) centerMinSize.y)
  if g.symmetrical then
    rowHeights := symmetrize rowHeights
  return rowHeights

/-- The grid width without padding (tabular: one sum over the column maxima, else the widest row). -/
def contentWidth (g : InsideLabelLayoutGrid L) : Float :=
  if g.tabular then sumWithGapsWithGap (g.minColumnWidths none) g.containerGap
  else ContainerArea.values.foldl
    (fun width row => fmax width (sumWithGapsWithGap (g.minColumnWidths (some row)) g.containerGap)) 0.0

/-- elk-rs `InsideLabelLayoutGrid::compute_minimum_size(only_center_cell_contributes)`: like
`InsideNodeLabelGrid.computeMinimumSize`, positive components get the node (port) padding and the
node labels padding. -/
def computeMinimumSize (g : InsideLabelLayoutGrid L) (onlyCenterCellContributes : Bool) : KVector :=
  let (minWidth, minHeight) : Float × Float :=
    if onlyCenterCellContributes then
      match g.centerCellMinSize with
      | some centerMinSize => (centerMinSize.x, centerMinSize.y)
      | none => (g.cellMinWidth .center .center, g.cellMinHeight .center .center)
    else
      (g.contentWidth, sumWithGapsWithGap g.minRowHeights g.containerGap)
  let np := g.nodePadding
  let nlp := g.nodeLabelPadding
  let minWidth := if minWidth > 0.0 then minWidth + (np.left + np.right + nlp.left + nlp.right) else minWidth
  let minHeight := if minHeight > 0.0 then minHeight + (np.top + np.bottom + nlp.top + nlp.bottom) else minHeight
  ⟨minWidth, minHeight⟩

/-- elk-rs `InsideLabelLayoutGrid::new(node, horizontal_layout_mode, size_constraints, size_options,
label_gap, container_gap)`. -/
def new (a : GraphAdapters m G N P L E) (node : N) (horizontalLayoutMode : Bool)
    (sizeConstraints : EnumSet SizeConstraint) (sizeOptions : EnumSet SizeOptions) (labelGap containerGap : Float) :
    m (InsideLabelLayoutGrid L) := do
  let padding := (← a.getIndividualOrInherited node CoreOptions.NODE_LABELS_PADDING).getD {}
  let centerCellMinSize ←
    if sizeConstraints.contains .minimumSize && sizeOptions.contains .minimumSizeAccountsForPadding then
      some <$> configuredMinimumSize a node sizeOptions
    else pure none
  let cells := ContainerArea.values.map fun row => ContainerArea.values.map fun col =>
    LabelCellLayout.new (horizontalAlignmentForAreaIndex col.index) (verticalAlignmentForAreaIndex row.index)
      horizontalLayoutMode labelGap
  return {
    cells, containerGap
    nodeLabelPadding := padding
    nodePadding := {}
    tabular := sizeOptions.contains .forceTabularNodeLabels
    symmetrical := !sizeOptions.contains .asymmetrical
    centerCellMinSize }

/-- Lays out the cells of one grid row (the loop body of elk-rs `apply_layout`). -/
private def applyRowLayout (ops : ElementOps m L) (g : InsideLabelLayoutGrid L) (gridRect : ElkRectangle)
    (verticalAxis : AxisLayout) (tabularWidths : Option (Array Float)) (row : ContainerArea) : m Unit := do
  let colWidths := tabularWidths.getD (g.minColumnWidths (some row))
  let horizontalAxis := layoutAxisThree gridRect.x gridRect.width g.nodeLabelPadding.left
    g.nodeLabelPadding.right colWidths g.containerGap
  for col in ContainerArea.values do
    if let some cell := g.getCell row col then
      cell.applyLayout ops
        { x := at3 horizontalAxis.starts col, y := at3 verticalAxis.starts row
          width := at3 horizontalAxis.spans col, height := at3 verticalAxis.spans row }

/-- elk-rs `InsideLabelLayoutGrid::apply_layout(node_size)`: lays out the grid inside the node minus
the node (port) padding — rows by `layoutAxisThree` over the row heights, each row's columns over
its column widths (or the tabular widths) — and returns the free center area (the client area). -/
def applyLayout (ops : ElementOps m L) (g : InsideLabelLayoutGrid L) (nodeSize : KVector) : m ElkRectangle := do
  let np := g.nodePadding
  let gridRect : ElkRectangle := {
    x := np.left, y := np.top
    width := fmax (nodeSize.x - np.left - np.right) 0.0
    height := fmax (nodeSize.y - np.top - np.bottom) 0.0 }
  let rowHeights := g.minRowHeights
  let verticalAxis := layoutAxisThree gridRect.y gridRect.height g.nodeLabelPadding.top
    g.nodeLabelPadding.bottom rowHeights g.containerGap
  let tabularWidths := if g.tabular then some (g.minColumnWidths none) else none
  for row in ContainerArea.values do
    applyRowLayout ops g gridRect verticalAxis tabularWidths row
  let centerWidths := tabularWidths.getD (g.minColumnWidths (some .center))
  let centerHorizontalAxis := layoutAxisThree gridRect.x gridRect.width g.nodeLabelPadding.left
    g.nodeLabelPadding.right centerWidths g.containerGap
  return {
    x := centerHorizontalAxis.centerAreaStart, y := verticalAxis.centerAreaStart
    width := centerHorizontalAxis.centerAreaSpan, height := verticalAxis.centerAreaSpan }

end InsideLabelLayoutGrid

/-! ### Outside strips -/

/-- The four outside node label strips of `processNode` (elk-rs keeps them in four local
variables `north_labels`, `south_labels`, `west_labels`, `east_labels`). -/
structure OutsideLabelStrips (L : Type) where
  /-- NORTH strip (horizontal, BOTTOM aligned, bottom padding = label-node spacing). -/
  north : StripContainerLayout L
  /-- SOUTH strip (horizontal, TOP aligned, top padding = label-node spacing). -/
  south : StripContainerLayout L
  /-- WEST strip (vertical, RIGHT aligned, right padding = label-node spacing). -/
  west : StripContainerLayout L
  /-- EAST strip (vertical, LEFT aligned, left padding = label-node spacing). -/
  east : StripContainerLayout L
  deriving Inhabited

/-- elk-rs `place_outside_container(container, side, node_size, outside_overhang)`: nothing without
labels; NORTH/SOUTH strips are at least as wide as the node (exactly as wide unless outside labels
may overhang), centered horizontally, above / below the node; WEST/EAST strips likewise with the
height, left / right of the node. -/
def placeOutsideContainer (ops : ElementOps m L) (container : StripContainerLayout L) (side : OutsideSide)
    (nodeSize : KVector) (outsideOverhang : Bool) : m Unit := do
  if !container.hasLabels then return
  let mut containerRect : ElkRectangle := { width := container.minWidth, height := container.minHeight }
  match side with
  | .north | .south =>
    containerRect := { containerRect with width := fmax containerRect.width nodeSize.x }
    if containerRect.width > nodeSize.x && !outsideOverhang then
      containerRect := { containerRect with width := nodeSize.x }
    containerRect := { containerRect with x := -(containerRect.width - nodeSize.x) / 2.0 }
    containerRect := { containerRect with
      y := if side == .north then -containerRect.height else nodeSize.y }
  | .west | .east =>
    containerRect := { containerRect with height := fmax containerRect.height nodeSize.y }
    if containerRect.height > nodeSize.y && !outsideOverhang then
      containerRect := { containerRect with height := nodeSize.y }
    containerRect := { containerRect with y := -(containerRect.height - nodeSize.y) / 2.0 }
    containerRect := { containerRect with
      x := if side == .west then -containerRect.width else nodeSize.x }
  container.applyLayout ops containerRect

/-! ### `process` / `processWithOptions` (Java pipeline) -/

/-- Applies the port positions like elk-rs `process_with_options`: all port contexts sorted by
volatile id (stable), zipped with `NodeAdapter.getPorts()`. -/
def applyPortPositions (a : GraphAdapters m G N P L E) (ctx : NodeContext N P L) : m Unit := do
  let allPortContexts := ctx.allPortContexts
  let volatileIdAt (i : Nat) : Int := (allPortContexts[i]?.map (·.volatileId)).getD 0
  -- Sort the context indices (`PortContext P L` has no `Inhabited` instance for arbitrary `P`)
  let order := stableSort (Array.range allPortContexts.size) fun i j => Ord.compare (volatileIdAt i) (volatileIdAt j)
  let ports ← a.nodePorts ctx.node
  for (port, i) in ports.zip order do
    if let some pc := allPortContexts[i]? then
      a.port.setPosition port pc.portPosition

/-- Java `NodeLabelAndSizeCalculator.process(graph, node, applyStuff, ignoreInsidePortLabels)`
(elk-rs `process_with_options(node, layout_direction, apply_stuff, ignore_inside_port_labels)`):
the full 7-phase cell system pipeline. Returns the node size that was (`applyStuff`) or would be
applied. With `applyStuff`, the node size, the port positions and the node and port label
positions are written through the adapters; the computed node padding is discarded (elk-rs).
`applyStuff := false, ignoreInsidePortLabels := true` is the importer path that computes a lower
bound for a hierarchical node's size. Throws `IllegalArgumentException` for ports without side. -/
def processWithOptions [MonadExcept IO.Error m] (a : GraphAdapters m G N P L E) (node : N)
    (layoutDirection : Direction) (applyStuff ignoreInsidePortLabels : Bool) : m KVector := do
  -- PREPARATORY PREPARATIONS: Create context objects
  let ctx ← NodeContext.new a node
  let ctx ← PortContextCreator.createPortContexts a ctx ignoreInsidePortLabels
  -- PHASE 1 (WONDEROUS WATERFOWL): Setup All Cells
  let horizontalLayoutMode := !layoutDirection.isVertical
  let ctx ← NodeLabelCellCreator.createNodeLabelCells a ctx false horizontalLayoutMode
  let ctx := InsidePortLabelCellCreator.createInsidePortLabelCells ctx
  -- PHASE 2 (DEFECTIVE DUCK): Setup Client Area Space and Node Cell Padding
  let ctx := NodeLabelAndSizeUtilities.setupMinimumClientAreaSize ctx
  let ctx := NodeLabelAndSizeUtilities.setupNodePaddingForPortsWithOffset ctx
  -- PHASE 3 (SALVAGEABLE SWAN): Minimum Space Required to Place Ports
  let ctx := HorizontalPortPlacementSizeCalculator.calculateHorizontalPortPlacementSize ctx
  let ctx := VerticalPortPlacementSizeCalculator.calculateVerticalPortPlacementSize ctx
  -- PHASE 4 (DAMNABLE DUCKLING): Setup Cell System Size Contribution Flags
  let ctx := CellSystemConfigurator.configureCellSystemSizeContributions ctx
  -- PHASE 5 (DUCK AND COVER): Set Node Width and Place Horizontal Ports
  let ctx := NodeSizeCalculator.setNodeWidth ctx
  let ctx := PortPlacementCalculator.placeHorizontalPorts ctx
  let ctx := PortLabelPlacementCalculator.placeHorizontalPortLabels ctx
  -- PHASE 6 (GIGANTIC GOOSE): Set Node Height and Place Vertical Ports
  let ctx := CellSystemConfigurator.updateVerticalInsidePortLabelCellPadding ctx
  let ctx := NodeSizeCalculator.setNodeHeight ctx
  if !applyStuff then
    return ctx.nodeSize
  let ctx := NodeLabelAndSizeUtilities.offsetSouthernPortsByNodeSize ctx
  let ctx := PortPlacementCalculator.placeVerticalPorts ctx
  let ctx := PortLabelPlacementCalculator.placeVerticalPortLabels ctx
  -- PHASE 7 (THANKSGIVING): Place Labels and Apply Stuff
  let ctx ← LabelPlacer.placeLabels a ctx
  -- elk-rs `set_node_padding` only returns the padding, which `process_with_options` discards
  let _discardedNodePadding := NodeLabelAndSizeUtilities.computeNodePadding ctx
  -- applyStuff: write computed sizes/positions back to the adapter
  a.node.setSize node ctx.nodeSize
  applyPortPositions a ctx
  return ctx.nodeSize

/-- Java `NodeLabelAndSizeCalculator.process(graph, node, true, false)` (elk-rs
`process(node, layout_direction)`): resizes the node and places its ports and labels. -/
def process [MonadExcept IO.Error m] (a : GraphAdapters m G N P L E) (node : N) (layoutDirection : Direction) :
    m KVector :=
  processWithOptions a node layoutDirection true false

/-! ### `processNode` (elk-rs simplified path) -/

/-- Grows `p` on the port's side to `extension` (WEST for UNDEFINED, like elk-rs). -/
private def growPaddingForExtension (p : ElkPadding) (side : PortSide) (extension : Float) : ElkPadding :=
  match side with
  | .north => { p with top := fmax p.top extension }
  | .south => { p with bottom := fmax p.bottom extension }
  | .east => { p with right := fmax p.right extension }
  | .west | .undefined => { p with left := fmax p.left extension }

/-- Grows `p` on the port's side to the inside part of its fixed labels and, if symmetrical and
the inside part was bigger, mirrors the result to the opposite side plus the border offset (the
`match port.get_side()` block of elk-rs `setup_node_padding_for_ports_with_offset`). -/
private def growPaddingForInsidePart (p : ElkPadding) (side : PortSide) (insidePart portBorderOffset : Float)
    (symmetrical : Bool) : ElkPadding :=
  match side with
  | .north =>
    let insidePartIsBigger := insidePart > p.top
    let p := { p with top := fmax p.top insidePart }
    if symmetrical && insidePartIsBigger then
      let p := { p with top := fmax p.top p.bottom }
      { p with bottom := p.top + portBorderOffset }
    else p
  | .south =>
    let insidePartIsBigger := insidePart > p.bottom
    let p := { p with bottom := fmax p.bottom insidePart }
    if symmetrical && insidePartIsBigger then
      let p := { p with bottom := fmax p.bottom p.top }
      { p with top := p.bottom + portBorderOffset }
    else p
  | .east =>
    let insidePartIsBigger := insidePart > p.right
    let p := { p with right := fmax p.right insidePart }
    if symmetrical && insidePartIsBigger then
      let p := { p with right := fmax p.right p.left }
      { p with left := p.right + portBorderOffset }
    else p
  | .west | .undefined =>
    let insidePartIsBigger := insidePart > p.left
    let p := { p with left := fmax p.left insidePart }
    if symmetrical && insidePartIsBigger then
      let p := { p with left := fmax p.left p.right }
      { p with right := p.left + portBorderOffset }
    else p

/-- Bounding box `(min, size)` of the given labels' bounds (elk-rs inline loop: the first label
initializes the box), `none` without labels. -/
private def labelsBoundingBox (a : GraphAdapters m G N P L E) (labels : Array L) : m (Option (KVector × KVector)) := do
  let mut minX := 0.0
  let mut minY := 0.0
  let mut maxX := 0.0
  let mut maxY := 0.0
  let mut hasLabel := false
  for label in labels do
    let pos ← a.label.getPosition label
    let size ← a.label.getSize label
    let x1 := pos.x
    let y1 := pos.y
    let x2 := pos.x + size.x
    let y2 := pos.y + size.y
    if !hasLabel then
      minX := x1
      minY := y1
      maxX := x2
      maxY := y2
      hasLabel := true
    else
      minX := fmin minX x1
      minY := fmin minY y1
      maxX := fmax maxX x2
      maxY := fmax maxY y2
  if !hasLabel then return none
  return some (⟨minX, minY⟩, ⟨maxX - minX, maxY - minY⟩)

/-- elk-rs `NodeLabelAndSizeCalculator::setup_node_padding_for_ports_with_offset(inside_layout, node,
port_labels_placement, size_options)` (private, `processNode` path): for every port in port order,
a negative `PORT_BORDER_OFFSET` grows the node padding on its side to `-offset`; with fixed port
labels, the part of the port's label bounding box inside the node (`ElkUtil.computeInsidePart`)
grows it as well (mirrored to the opposite side if symmetrical). UNDEFINED counts as WEST. -/
def setupNodePaddingForPortsWithOffset (insideLayout : InsideLabelLayoutGrid L) (a : GraphAdapters m G N P L E)
    (node : N) (portLabelsPlacement : EnumSet PortLabelPlacement) (sizeOptions : EnumSet SizeOptions) :
    m (InsideLabelLayoutGrid L) := do
  let mut nodeCellPadding := insideLayout.nodePadding
  let symmetrical := !sizeOptions.contains .asymmetrical
  for port in ← a.nodePorts node do
    let portBorderOffset ← a.port.getPropertyD port CoreOptions.PORT_BORDER_OFFSET 0.0
    let side ← a.portSide port
    if portBorderOffset < 0.0 then
      nodeCellPadding := growPaddingForExtension nodeCellPadding side (-portBorderOffset)
    if !PortLabelPlacement.isFixed portLabelsPlacement then
      continue
    let some (bboxMin, bboxSize) ← labelsBoundingBox a (← a.portLabels port) | continue
    let portSize ← a.port.getSize port
    let insidePart := ElkUtil.computeInsidePart bboxMin bboxSize portSize portBorderOffset side
    nodeCellPadding := growPaddingForInsidePart nodeCellPadding side insidePart portBorderOffset symmetrical
  return { insideLayout with nodePadding := nodeCellPadding }

/-- Top/bottom margin of one port for `verticalPortSizeForFreeSide` (elk-rs local struct
`PortMargin`). -/
structure FreePortMargin where
  /-- Space above the port. -/
  top : Float := 0.0
  /-- Space below the port. -/
  bottom : Float := 0.0
  deriving Inhabited, Repr

/-- The label-induced margin of one port (the `for port in &ports` body of elk-rs
`vertical_port_size_for_free_side`): fixed labels → their overhang above / below the port;
otherwise the stacked label height (labels of zero size ignored) either centered next to the port
(as a group, or only the first label centered) or below the port after the vertical label
spacing. -/
private def freePortMargin (a : GraphAdapters m G N P L E) (port : P) (includePortLabels fixedPortLabels
    labelsNextToPort treatAsGroup : Bool) (labelLabelSpacing portLabelSpacingV : Float) : m FreePortMargin := do
  let mut margin : FreePortMargin := {}
  if !includePortLabels then return margin
  let labels ← (← a.portLabels port).filterM fun label => do
    let size ← a.label.getSize label
    return size.x > 0.0 || size.y > 0.0
  if fixedPortLabels then
    let mut minY := 0.0
    let mut maxY := 0.0
    let mut hasFixedLabel := false
    for label in labels do
      let pos ← a.label.getPosition label
      let size ← a.label.getSize label
      let y1 := pos.y
      let y2 := pos.y + size.y
      if !hasFixedLabel then
        minY := y1
        maxY := y2
        hasFixedLabel := true
      else
        minY := fmin minY y1
        maxY := fmax maxY y2
    if hasFixedLabel then
      let portHeight := (← a.port.getSize port).y
      margin := { top := fmax (-minY) 0.0, bottom := fmax (maxY - portHeight) 0.0 }
    return margin
  let labelHeight : Float ← if labels.isEmpty then pure 0.0 else do
    let mut sum := 0.0
    for label in labels do
      sum := sum + (← a.label.getSize label).y
    pure (sum + labelLabelSpacing * fmax (labels.size.toFloat - 1.0) 0.0)
  if labelHeight > 0.0 then
    if labelsNextToPort then
      let portHeight := (← a.port.getSize port).y
      if labelHeight > portHeight then
        if treatAsGroup || labels.size == 1 then
          let overhang := (labelHeight - portHeight) / 2.0
          margin := { top := overhang, bottom := overhang }
        else
          let firstLabelHeight ← match labels[0]? with
            | some first => (·.y) <$> a.label.getSize first
            | none => pure 0.0
          let firstLabelOverhang := (firstLabelHeight - portHeight) / 2.0
          margin := { top := fmax firstLabelOverhang 0.0, bottom := labelHeight - firstLabelOverhang - portHeight }
    else
      -- Label placed below the port
      margin := { margin with bottom := portLabelSpacingV + labelHeight }
  return margin

/-- elk-rs `vertical_port_size_for_free_side(node, side, size_constraints, port_labels_placement)`
(mirrors Java's `VerticalPortPlacementSizeCalculator.calculateVerticalNodeSizeRequiredByFreePorts`):
the height the EAST or WEST ports need with free placement — port heights, label margins
(`freePortMargin`; with OUTSIDE labels the outermost margins are dropped, and the first port's
bottom margin too for space-efficient labels not next to the port), port-port spacings, the
surrounding port margins and two more spacings for DISTRIBUTED alignment. `0` without ports. -/
def verticalPortSizeForFreeSide (a : GraphAdapters m G N P L E) (node : N) (side : PortSide)
    (sizeConstraints : EnumSet SizeConstraint) (portLabelsPlacement : EnumSet PortLabelPlacement) : m Float := do
  let ports ← (← a.nodePorts node).filterM fun p => return (← a.portSide p) == side
  if ports.isEmpty then return 0.0
  let portPortSpacing := fmax ((← a.getIndividualOrInherited node CoreOptions.SPACING_PORT_PORT).getD 10.0) 0.0
  let surrounding : ElkMargin := (← a.getIndividualOrInherited node CoreOptions.SPACING_PORTS_SURROUNDING).getD {}
  let portLabelSpacingV := (← a.getIndividualOrInherited node CoreOptions.SPACING_LABEL_PORT_VERTICAL).getD 1.0
  let labelLabelSpacing := fmax ((← a.getIndividualOrInherited node CoreOptions.SPACING_LABEL_LABEL).getD 0.0) 0.0
  let treatAsGroup ← a.node.getPropertyD node CoreOptions.PORT_LABELS_TREAT_AS_GROUP true
  let portLabelsOutside := portLabelsPlacement.contains .outside
  let nextToPortIfPossible := portLabelsPlacement.contains .nextToPortIfPossible
  let alwaysSameSide := portLabelsPlacement.contains .alwaysSameSide
  let alwaysOtherSameSide := portLabelsPlacement.contains .alwaysOtherSameSide
  let spaceEfficient := portLabelsPlacement.contains .spaceEfficient
  let spaceEfficientPortLabels := !alwaysSameSide && !alwaysOtherSameSide && (spaceEfficient || ports.size == 2)
  let fixedPortLabels := PortLabelPlacement.isFixed portLabelsPlacement
  let includePortLabels := sizeConstraints.contains .portLabels
  let eastOrWest := side == .east || side == .west
  -- Labels placed "next to port" (beside it vertically)
  let labelsNextToPort :=
    if portLabelsOutside then nextToPortIfPossible && eastOrWest
    else portLabelsPlacement.contains .inside && eastOrWest
  -- Compute per-port top/bottom margins from labels
  let mut margins : Array FreePortMargin := #[]
  for port in ports do
    margins := margins.push (← freePortMargin a port includePortLabels fixedPortLabels labelsNextToPort
      treatAsGroup labelLabelSpacing portLabelSpacingV)
  -- For outside placement: topmost port margin.top = 0, bottommost port margin.bottom = 0
  if portLabelsOutside && !margins.isEmpty then
    margins := margins.modify 0 fun mg => { mg with top := 0.0 }
    margins := margins.modify (margins.size - 1) fun mg => { mg with bottom := 0.0 }
    -- Space-efficient: if topmost port's labels are NOT next to port, clear its bottom margin
    if spaceEfficientPortLabels && !labelsNextToPort then
      margins := margins.modify 0 fun mg => { mg with bottom := 0.0 }
  -- Sum port heights + margins + inter-port spacing
  let mut height := 0.0
  for i in [0:ports.size] do
    let some port := ports[i]? | continue
    let mg := margins.getD i {}
    height := height + (mg.top + (← a.port.getSize port).y + mg.bottom)
    if i + 1 < ports.size then
      height := height + portPortSpacing
  -- Add surrounding port margins (top/bottom for EAST/WEST)
  let (surrTop, surrBottom) := if eastOrWest then (surrounding.top, surrounding.bottom) else (0.0, 0.0)
  height := height + (surrTop + surrBottom)
  -- For DISTRIBUTED alignment, add 2 * port_port_spacing
  let sideAlignment ← match side with
    | .east => a.node.getProperty node CoreOptions.PORT_ALIGNMENT_EAST
    | .west => a.node.getProperty node CoreOptions.PORT_ALIGNMENT_WEST
    | _ => pure none
  let portAlignment ← match sideAlignment with
    | some alignment => pure alignment
    | none => a.node.getPropertyD node CoreOptions.PORT_ALIGNMENT_DEFAULT PortAlignment.justified
  if portAlignment == .distributed then
    height := height + 2.0 * portPortSpacing
  return height

/-- Widest label of a port (`0` without labels). -/
private def maxLabelWidth (a : GraphAdapters m G N P L E) (port : P) : m Float := do
  let mut w := 0.0
  for label in ← a.portLabels port do
    w := fmax w (← a.label.getSize label).x
  return w

/-- elk-rs `setup_inside_port_label_cell_minimums(inside_layout, node, port_labels_placement)`
(`processNode` path, INSIDE port labels only): the widest port label per side (plus spacing
compensation unless `MINIMUM_SIZE` is set) becomes the minimum width of the inside cell next to
that side (CENTER/END for EAST, CENTER/BEGIN for WEST and UNDEFINED, BEGIN/CENTER for NORTH,
END/CENTER for SOUTH), plus the horizontal port label spacing. -/
def setupInsidePortLabelCellMinimums (insideLayout : InsideLabelLayoutGrid L) (a : GraphAdapters m G N P L E)
    (node : N) (portLabelsPlacement : EnumSet PortLabelPlacement) : m (InsideLabelLayoutGrid L) := do
  if !portLabelsPlacement.contains .inside then return insideLayout
  let labelSpacing ← a.node.getPropertyD node CoreOptions.SPACING_LABEL_PORT_HORIZONTAL 0.0
  let sizeConstraints ← a.node.getPropertyD node CoreOptions.NODE_SIZE_CONSTRAINTS EnumSet.empty
  let allowInsideSpacingCompensation := !sizeConstraints.contains .minimumSize
  let portSpacing := fmax (← a.node.getPropertyD node CoreOptions.SPACING_PORT_PORT 0.0) 0.0
  let nodeLabelSpacing := fmax (← a.node.getPropertyD node CoreOptions.SPACING_LABEL_NODE 0.0) 0.0
  let mut eastWidth := 0.0
  let mut westWidth := 0.0
  let mut northWidth := 0.0
  let mut southWidth := 0.0
  let mut eastBorderExtension := 0.0
  let mut westBorderExtension := 0.0
  for port in ← a.nodePorts node do
    let maxWidth ← maxLabelWidth a port
    if maxWidth <= 0.0 then continue
    let borderExtension := fmax (-(← a.port.getPropertyD port CoreOptions.PORT_BORDER_OFFSET 0.0)) 0.0
    match ← a.portSide port with
    | .east =>
      eastWidth := fmax eastWidth maxWidth
      eastBorderExtension := fmax eastBorderExtension borderExtension
    | .north => northWidth := fmax northWidth maxWidth
    | .south => southWidth := fmax southWidth maxWidth
    | .west | .undefined =>
      westWidth := fmax westWidth maxWidth
      westBorderExtension := fmax westBorderExtension borderExtension
  if allowInsideSpacingCompensation then
    if northWidth > 0.0 then
      northWidth := northWidth + (portSpacing + 2.0 * labelSpacing + 3.0)
    if southWidth > 0.0 then
      southWidth := southWidth + (portSpacing + 2.0 * labelSpacing + 3.0)
    if eastWidth > 0.0 then
      eastWidth := eastWidth + (portSpacing + nodeLabelSpacing + eastBorderExtension + 2.0)
    if westWidth > 0.0 then
      westWidth := westWidth + (portSpacing + nodeLabelSpacing + westBorderExtension + 2.0)
  let mut insideLayout := insideLayout
  if eastWidth > 0.0 then
    insideLayout := insideLayout.ensureCellMinWidth .center .«end» (eastWidth + labelSpacing)
  if westWidth > 0.0 then
    insideLayout := insideLayout.ensureCellMinWidth .center .begin (westWidth + labelSpacing)
  if northWidth > 0.0 then
    insideLayout := insideLayout.ensureCellMinWidth .begin .center (northWidth + labelSpacing)
  if southWidth > 0.0 then
    insideLayout := insideLayout.ensureCellMinWidth .«end» .center (southWidth + labelSpacing)
  return insideLayout

/-- Sorts the node's labels into the inside grid and the outside strips (the label loop of elk-rs
`process_node`): labels without a location (`nodeLabelLocationInfoForPlacement` = `none`) are
ignored; outside labels go to their side's strip at the location's column (NORTH/SOUTH) or row
(WEST/EAST). -/
private def distributeNodeLabels (a : GraphAdapters m G N P L E) (node : N)
    (defaultLabelPlacement : EnumSet NodeLabelPlacement) (insideLayout : InsideLabelLayoutGrid L)
    (strips : OutsideLabelStrips L) : m (InsideLabelLayoutGrid L × OutsideLabelStrips L) := do
  let mut insideLayout := insideLayout
  let mut strips := strips
  for label in ← a.nodeLabels node do
    let effectivePlacement ← effectiveNodeLabelPlacement a label defaultLabelPlacement
    let some labelLocation := nodeLabelLocationInfoForPlacement effectivePlacement | continue
    if labelLocation.inside then
      insideLayout := insideLayout.addLabel labelLocation.row labelLocation.col label (← a.label.getSize label)
    else if let some side := labelLocation.outsideSide then
      let size ← a.label.getSize label
      match side with
      | .north => strips := { strips with north := strips.north.addLabel labelLocation.col label size }
      | .south => strips := { strips with south := strips.south.addLabel labelLocation.col label size }
      | .east => strips := { strips with east := strips.east.addLabel labelLocation.row label size }
      | .west => strips := { strips with west := strips.west.addLabel labelLocation.row label size }
  return (insideLayout, strips)

/-- The node size `processNode` asks for when the size constraints are not effectively fixed (the
`if !fixed_size_constraints` block of elk-rs `process_node`): the inside grid minimum (with
`NODE_LABELS`, or only the center cell for a padded minimum size), the NORTH/SOUTH widths and
EAST/WEST heights of the outside strips (`NODE_LABELS` without overhang), the configured minimum
size (`MINIMUM_SIZE` without `MINIMUM_SIZE_ACCOUNTS_FOR_PADDING`), the EAST/WEST free port heights
(`PORTS`, not `FIXED_RATIO`/`FIXED_POS`, only if a height was requested already); components that
were not requested keep the initial size; top-down layout never shrinks; with the parent graph's
`NODE_SIZE_FIXED_GRAPH_SIZE` the node never shrinks either. -/
private def requiredNodeSize (a : GraphAdapters m G N P L E) (node : N) (insideLayout : InsideLabelLayoutGrid L)
    (strips : OutsideLabelStrips L) (sizeConstraints : EnumSet SizeConstraint) (sizeOptions : EnumSet SizeOptions)
    (portLabelsPlacement : EnumSet PortLabelPlacement) (initialNodeSize : KVector) (topdownLayout : Bool) :
    m KVector := do
  let minimumSizeAccountsForPadding :=
    sizeConstraints.contains .minimumSize && sizeOptions.contains .minimumSizeAccountsForPadding
  let includeNodeLabels := sizeConstraints.contains .nodeLabels
  let outsideOverhang := sizeOptions.contains .outsideNodeLabelsOverhang
  let mut requiredWidth := 0.0
  let mut requiredHeight := 0.0
  let mut widthRequested := false
  let mut heightRequested := false
  if includeNodeLabels || minimumSizeAccountsForPadding then
    let onlyCenter := minimumSizeAccountsForPadding && !includeNodeLabels
    let insideMinSize := insideLayout.computeMinimumSize onlyCenter
    requiredWidth := fmax requiredWidth insideMinSize.x
    requiredHeight := fmax requiredHeight insideMinSize.y
    widthRequested := true
    heightRequested := true
  if includeNodeLabels && !outsideOverhang then
    requiredWidth := fmax (fmax requiredWidth strips.north.minWidth) strips.south.minWidth
    requiredHeight := fmax (fmax requiredHeight strips.east.minHeight) strips.west.minHeight
    widthRequested := true
    heightRequested := true
  if sizeConstraints.contains .minimumSize && !minimumSizeAccountsForPadding then
    let minimumSize ← configuredMinimumSize a node sizeOptions
    requiredWidth := fmax requiredWidth minimumSize.x
    requiredHeight := fmax requiredHeight minimumSize.y
    widthRequested := true
    heightRequested := true
  -- Port-driven minimum height for EAST/WEST ports (only if a height is requested already)
  if sizeConstraints.contains .ports && heightRequested then
    let portConstraints ← a.node.getPropertyD node CoreOptions.PORT_CONSTRAINTS PortConstraints.undefined
    if portConstraints != .fixedPos && portConstraints != .fixedRatio then
      let eastHeight ← verticalPortSizeForFreeSide a node .east sizeConstraints portLabelsPlacement
      let westHeight ← verticalPortSizeForFreeSide a node .west sizeConstraints portLabelsPlacement
      requiredHeight := fmax requiredHeight (fmax eastHeight westHeight)
  if !widthRequested then
    requiredWidth := initialNodeSize.x
  if !heightRequested then
    requiredHeight := initialNodeSize.y
  if topdownLayout then
    requiredWidth := fmax requiredWidth initialNodeSize.x
    requiredHeight := fmax requiredHeight initialNodeSize.y
  let nodeSizeFixedGraphSize ← match ← a.getGraph node with
    | some graph => a.graph.getPropertyD graph CoreOptions.NODE_SIZE_FIXED_GRAPH_SIZE false
    | none => pure false
  return {
    x := if nodeSizeFixedGraphSize then fmax initialNodeSize.x requiredWidth else requiredWidth
    y := if nodeSizeFixedGraphSize then fmax initialNodeSize.y requiredHeight else requiredHeight }

/-- elk-rs `NodeLabelAndSizeCalculator::process_node(node, layout_direction)`: the simplified
node sizing used by elk-rs' `NodeDimensionCalculation` (no Java counterpart). Node labels are
sorted into a 3×3 inside grid and four outside strips; ports with negative border offsets or fixed
inside label parts reserve node padding; INSIDE port labels widen the inside border cells. Unless
the size constraints are effectively fixed, the node is resized to `requiredNodeSize` (compound
nodes with fixed port labels only grow to the inside grid minimum). Then the inside grid and the
outside strips are laid out on the final node size, writing the label positions, and with
`COMPUTE_PADDING` the node padding becomes the distance to the free center area. Ports are not
moved. -/
def processNode (a : GraphAdapters m G N P L E) (node : N) (layoutDirection : Direction) : m Unit := do
  let sizeConstraints ← a.node.getPropertyD node CoreOptions.NODE_SIZE_CONSTRAINTS EnumSet.empty
  let sizeOptions ← a.node.getPropertyD node CoreOptions.NODE_SIZE_OPTIONS EnumSet.empty
  let defaultLabelPlacement ← a.node.getPropertyD node CoreOptions.NODE_LABELS_PLACEMENT EnumSet.empty
  let labelLabelSpacing := (← a.getIndividualOrInherited node CoreOptions.SPACING_LABEL_LABEL).getD 0.0
  let labelCellSpacing := 2.0 * labelLabelSpacing
  let nodeLabelSpacing := (← a.getIndividualOrInherited node CoreOptions.SPACING_LABEL_NODE).getD 0.0
  let horizontalLayoutMode := !layoutDirection.isVertical
  let insideLayout ← InsideLabelLayoutGrid.new a node horizontalLayoutMode sizeConstraints sizeOptions
    labelLabelSpacing labelCellSpacing
  let symmetrical := !sizeOptions.contains .asymmetrical
  let strips : OutsideLabelStrips L := {
    north := StripContainerLayout.newHorizontal symmetrical labelCellSpacing { bottom := nodeLabelSpacing }
      labelLabelSpacing horizontalLayoutMode .bottom
    south := StripContainerLayout.newHorizontal symmetrical labelCellSpacing { top := nodeLabelSpacing }
      labelLabelSpacing horizontalLayoutMode .top
    west := StripContainerLayout.newVertical symmetrical labelCellSpacing { right := nodeLabelSpacing }
      labelLabelSpacing horizontalLayoutMode .right
    east := StripContainerLayout.newVertical symmetrical labelCellSpacing { left := nodeLabelSpacing }
      labelLabelSpacing horizontalLayoutMode .left }
  let (insideLayout, strips) ← distributeNodeLabels a node defaultLabelPlacement insideLayout strips
  let portLabelsPlacement ← a.node.getPropertyD node CoreOptions.PORT_LABELS_PLACEMENT EnumSet.empty
  let insideLayout ← setupNodePaddingForPortsWithOffset insideLayout a node portLabelsPlacement sizeOptions
  let insideLayout ← setupInsidePortLabelCellMinimums insideLayout a node portLabelsPlacement
  let outsideOverhang := sizeOptions.contains .outsideNodeLabelsOverhang
  let topdownLayout ← a.node.getPropertyD node CoreOptions.TOPDOWN_LAYOUT false
  let initialNodeSize ← a.node.getSize node
  let fixedSizeConstraints := hasEffectivelyFixedSizeConstraints sizeConstraints
  let fixedPortLabels := PortLabelPlacement.isFixed portLabelsPlacement
  let compoundFixedPortLabels := (← a.isCompoundNode node) && fixedPortLabels
  if !fixedSizeConstraints then
    let targetNodeSize ← requiredNodeSize a node insideLayout strips sizeConstraints sizeOptions
      portLabelsPlacement initialNodeSize topdownLayout
    a.node.setSize node targetNodeSize
  else if compoundFixedPortLabels then
    let compoundMinSize := insideLayout.computeMinimumSize false
    a.node.setSize node ⟨fmax initialNodeSize.x compoundMinSize.x, fmax initialNodeSize.y compoundMinSize.y⟩
  let finalNodeSize ← a.node.getSize node
  let centerCellRect ← insideLayout.applyLayout a.label finalNodeSize
  placeOutsideContainer a.label strips.north .north finalNodeSize outsideOverhang
  placeOutsideContainer a.label strips.south .south finalNodeSize outsideOverhang
  placeOutsideContainer a.label strips.west .west finalNodeSize outsideOverhang
  placeOutsideContainer a.label strips.east .east finalNodeSize outsideOverhang
  if sizeOptions.contains .computePadding then
    a.setPadding node {
      left := fmax centerCellRect.x 0.0
      top := fmax centerCellRect.y 0.0
      right := fmax (finalNodeSize.x - (centerCellRect.x + centerCellRect.width)) 0.0
      bottom := fmax (finalNodeSize.y - (centerCellRect.y + centerCellRect.height)) 0.0 }

/-! ### Inside node label padding / minimum size -/

/-- Java `NodeLabelAndSizeCalculator.computeInsideNodeLabelPadding(graph, node, layoutDirection)`
(elk-rs `compute_inside_node_label_padding(node, layout_direction)`): the padding required to place
the inside non-center node labels (`InsideNodeLabelGrid.computeInsidePadding`). Spacings are
individual or inherited from the node's parent graph (elk-rs). -/
def computeInsideNodeLabelPadding (a : GraphAdapters m G N P L E) (node : N) (layoutDirection : Direction) :
    m ElkPadding := do
  let grid ← InsideNodeLabelGrid.new a node layoutDirection
  return grid.computeInsidePadding

/-- elk-rs `compute_inside_node_label_container_minimum_size(node, layout_direction)` (no Java
counterpart): the minimum size of the inside node label container. Only the center cell
contributes for a padded minimum size without `NODE_LABELS`; otherwise the width is the tabular
column sum or the widest row and the height the row sum (each with the node labels padding when
positive). -/
def computeInsideNodeLabelContainerMinimumSize (a : GraphAdapters m G N P L E) (node : N)
    (layoutDirection : Direction) : m KVector := do
  let grid ← InsideNodeLabelGrid.new a node layoutDirection
  let sizeConstraints ← a.node.getPropertyD node CoreOptions.NODE_SIZE_CONSTRAINTS EnumSet.empty
  let sizeOptions ← a.node.getPropertyD node CoreOptions.NODE_SIZE_OPTIONS EnumSet.empty
  let onlyCenterCellContributes := sizeConstraints.contains .minimumSize
    && sizeOptions.contains .minimumSizeAccountsForPadding && !sizeConstraints.contains .nodeLabels
  let mut minSize := grid.computeMinimumSize onlyCenterCellContributes
  if grid.tabular then
    -- Tabular mode keeps per-column widths consistent across rows
    let tabularWidth := sumWithGapsWithGap (grid.minColumnWidths none) grid.containerGap
    if tabularWidth > 0.0 then
      minSize := { minSize with x := tabularWidth + grid.padding.left + grid.padding.right }
  else if !onlyCenterCellContributes then
    let mut nonTabularWidth := 0.0
    for row in ContainerArea.values do
      nonTabularWidth := fmax nonTabularWidth (sumWithGapsWithGap (grid.minColumnWidths (some row)) grid.containerGap)
    if nonTabularWidth > 0.0 then
      minSize := { minSize with x := nonTabularWidth + grid.padding.left + grid.padding.right }
  if !onlyCenterCellContributes then
    let height := sumWithGapsWithGap grid.minRowHeights grid.containerGap
    if height > 0.0 then
      minSize := { minSize with y := height + grid.padding.top + grid.padding.bottom }
  return minSize

end NodeLabelAndSizeCalculator

end Elk.Alg.Common.NodeSpacing
