import Elk.Alg.Common.NodeSpacing.CellSystem.Cell
import Elk.Core.Util.FloatConst
open Elk.Core.Util.FloatConst
/-!
# `org.eclipse.elk.alg.common.nodespacing.cellsystem.LabelCell`

A cell that holds labels and knows how to place them (elk-rs `cellsystem::LabelCell` /
`DynLabelCell`). The cell system is pure: `applyLabelLayout` returns the label positions
instead of calling `label.setPosition(…)`; callers apply them through their adapters.

Deviations:
* Labels are stored with the size read at `addLabel` time. Java/Rust read `label.getSize()`
  again in `applyLabelLayout`; label sizes do not change during node size calculation, so the
  result is the same. `applyLabelLayoutM` re-reads the sizes through a callback for callers
  that need the exact Java/Rust behaviour.
* The Java constructors taking a `NodeLabelLocation` are not ported (elk-rs has no
  counterpart either); callers set the alignments with `setHorizontalAlignment` /
  `setVerticalAlignment` (see `NodeLabelLocation.horizontalAlignment`).
-/

namespace Elk.Alg.Common.NodeSpacing.CellSystem

open Elk Elk.Core.Math Elk.Core.Util

namespace LabelCell

variable {L : Type}

/-- `LabelCell.getMinimumWidth()`. -/
@[inline] def minimumWidth (d : LabelCellData L) (padding : ElkPadding) : Float :=
  d.minimumContentAreaSize.x + padding.left + padding.right

/-- `LabelCell.getMinimumHeight()`. -/
@[inline] def minimumHeight (d : LabelCellData L) (padding : ElkPadding) : Float :=
  d.minimumContentAreaSize.y + padding.top + padding.bottom

/-- `LabelCell.addLabel(label)`: appends the label and grows the minimum content area. -/
def addLabel (d : LabelCellData L) (label : L) (labelSize : KVector) : LabelCellData L :=
  let labels := d.labels.push (label, labelSize)
  let mc := d.minimumContentAreaSize
  let mc :=
    if d.horizontalLayoutMode then
      let mc := { mc with x := fmax mc.x labelSize.x }
      let mc := { mc with y := mc.y + labelSize.y }
      if labels.size > 1 then { mc with y := mc.y + d.gap } else mc
    else
      let mc := { mc with x := mc.x + labelSize.x }
      let mc := { mc with y := fmax mc.y labelSize.y }
      if labels.size > 1 then { mc with x := mc.x + d.gap } else mc
  { d with labels := labels, minimumContentAreaSize := mc }

/-- `LabelCell.applyHorizontalModeLabelLayout()`: positions for labels of the given sizes. -/
def horizontalModePositions (d : LabelCellData L) (cellRect : ElkRectangle) (padding : ElkPadding)
    (sizes : Array KVector) : Array KVector := Id.run do
  let mut yPos := cellRect.y
  if d.verticalAlignment == .center then
    yPos := yPos + (cellRect.height - d.minimumContentAreaSize.y) / fl2p0
  else if d.verticalAlignment == .bottom then
    yPos := yPos + (cellRect.height - d.minimumContentAreaSize.y)
  let mut result : Array KVector := Array.mkEmpty sizes.size
  for labelSize in sizes do
    let y := yPos
    yPos := yPos + (labelSize.y + d.gap)
    let x := match d.horizontalAlignment with
      | .left => cellRect.x + padding.left
      | .center => cellRect.x + padding.left + (cellRect.width - labelSize.x) / fl2p0
      | .right => cellRect.x + cellRect.width - padding.right - labelSize.x
    result := result.push ⟨x, y⟩
  return result

/-- `LabelCell.applyVerticalModeLabelLayout()`: positions for labels of the given sizes. -/
def verticalModePositions (d : LabelCellData L) (cellRect : ElkRectangle) (padding : ElkPadding)
    (sizes : Array KVector) : Array KVector := Id.run do
  let mut xPos := cellRect.x
  if d.horizontalAlignment == .center then
    xPos := xPos + (cellRect.width - d.minimumContentAreaSize.x) / fl2p0
  else if d.horizontalAlignment == .right then
    xPos := xPos + (cellRect.width - d.minimumContentAreaSize.x)
  let mut result : Array KVector := Array.mkEmpty sizes.size
  for labelSize in sizes do
    let x := xPos
    xPos := xPos + (labelSize.x + d.gap)
    let y := match d.verticalAlignment with
      | .top => cellRect.y + padding.top
      | .center => cellRect.y + padding.top + (cellRect.height - labelSize.y) / fl2p0
      | .bottom => cellRect.y + cellRect.height - padding.bottom - labelSize.y
    result := result.push ⟨x, y⟩
  return result

/-- `LabelCell.applyLabelLayout()` for the given label sizes (one per label, in label order). -/
def layoutPositions (d : LabelCellData L) (cellRect : ElkRectangle) (padding : ElkPadding)
    (sizes : Array KVector) : Array KVector :=
  if d.horizontalLayoutMode then horizontalModePositions d cellRect padding sizes
  else verticalModePositions d cellRect padding sizes

end LabelCell

namespace CellArena

variable {L : Type}

/-- `new LabelCell(gap)` / `new LabelCell(gap, horizontalLayoutMode)` (elk-rs
`DynLabelCell::new` / `new_with_layout_mode`): centered alignments, no labels. -/
def createLabel (a : CellArena L) (gap : Float) (horizontalLayoutMode : Bool := true) : CellArena L × CellId :=
  a.add { kind := .label { gap := gap, horizontalLayoutMode := horizontalLayoutMode } }

/-- The label data of a label cell (`none` for other kinds). -/
def labelData? (a : CellArena L) (id : CellId) : Option (LabelCellData L) :=
  match (a.get id).kind with
  | .label d => some d
  | _ => none

/-- Updates the label data of a label cell (ignored for other kinds). -/
def modifyLabelData (a : CellArena L) (id : CellId) (f : LabelCellData L → LabelCellData L) : CellArena L :=
  a.modify id fun c =>
    match c.kind with
    | .label d => { c with kind := .label (f d) }
    | _ => c

/-- `LabelCell.addLabel(label)`; `labelSize` is the label's current size (`label.getSize()`). -/
def addLabel (a : CellArena L) (id : CellId) (label : L) (labelSize : KVector) : CellArena L :=
  a.modifyLabelData id (LabelCell.addLabel · label labelSize)

/-- `LabelCell.getLabels()` with the sizes recorded by `addLabel` (empty for other kinds). -/
def labels (a : CellArena L) (id : CellId) : Array (L × KVector) :=
  match a.labelData? id with
  | some d => d.labels
  | none => #[]

/-- `LabelCell.hasLabels()`. -/
def hasLabels (a : CellArena L) (id : CellId) : Bool := !(a.labels id).isEmpty

/-- `LabelCell.getHorizontalAlignment()` (`CENTER` for non-label cells). -/
def horizontalAlignment (a : CellArena L) (id : CellId) : HorizontalLabelAlignment :=
  match a.labelData? id with
  | some d => d.horizontalAlignment
  | none => .center

/-- `LabelCell.setHorizontalAlignment(alignment)`. -/
def setHorizontalAlignment (a : CellArena L) (id : CellId) (al : HorizontalLabelAlignment) : CellArena L :=
  a.modifyLabelData id fun d => { d with horizontalAlignment := al }

/-- `LabelCell.getVerticalAlignment()` (`CENTER` for non-label cells). -/
def verticalAlignment (a : CellArena L) (id : CellId) : VerticalLabelAlignment :=
  match a.labelData? id with
  | some d => d.verticalAlignment
  | none => .center

/-- `LabelCell.setVerticalAlignment(alignment)`. -/
def setVerticalAlignment (a : CellArena L) (id : CellId) (al : VerticalLabelAlignment) : CellArena L :=
  a.modifyLabelData id fun d => { d with verticalAlignment := al }

/-- `LabelCell.applyLabelLayout()`: the position of every label of the cell (in label order),
computed from the cell rectangle, padding, alignments and the recorded label sizes. The caller
applies them (`label.setPosition(pos)`). Empty for non-label cells. -/
def applyLabelLayout (a : CellArena L) (id : CellId) : Array (L × KVector) :=
  let c := a.get id
  match c.kind with
  | .label d =>
    let positions := LabelCell.layoutPositions d c.cellRectangle c.padding (d.labels.map (·.2))
    d.labels.zipWith (fun (l, _) p => (l, p)) positions
  | _ => #[]

/-- `LabelCell.applyLabelLayout()` re-reading every label size through `getSize` (Java/Rust
call `label.getSize()` during the layout). Empty for non-label cells. -/
def applyLabelLayoutM {m : Type → Type} [Monad m] (a : CellArena L) (id : CellId) (getSize : L → m KVector) :
    m (Array (L × KVector)) := do
  let c := a.get id
  match c.kind with
  | .label d =>
    let sizes ← d.labels.mapM fun (l, _) => getSize l
    let positions := LabelCell.layoutPositions d c.cellRectangle c.padding sizes
    return d.labels.zipWith (fun (l, _) p => (l, p)) positions
  | _ => return #[]

end CellArena

end Elk.Alg.Common.NodeSpacing.CellSystem
