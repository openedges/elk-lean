import Elk.Alg.Layered.Intermediate.Loops.SelfLoopPort
/-!
# `org.eclipse.elk.alg.layered.intermediate.loops.SelfHyperLoopLabels`

Port of elk-rs `intermediate/loops/self_hyper_loop_labels.rs` (pure data; see `SelfLoopPort`).
The labels are arena ids, so every operation that reads label sizes takes a
`sizeOf : LLabelId → KVector` lookup (the monadic wrappers in `Loops.Ops` pass the arena's
label sizes). `applyPlacement` returns the new label positions instead of writing them.

Rust/Java difference (Rust followed): Java reads the layout direction and the label-label spacing
in the constructor; Rust creates the labels with `horizontal = true`, spacing `0.0` and lets
`SelfLoopPreProcessor` set both afterwards (each setter recalculates the size).
-/
/-! Float literals as global constants (FL): inside branches, loops and specialised code the compiler
shares a literal's `Nat`/`Bool` arguments with unrelated variables (CSE) and then parses it on every
evaluation (`FastFloat.ofScientificImpl`); a top-level constant is a load (PLAN §7.1 items 17, 22). -/
private def fl0p0 : Float := 0.0
private def fl2p0 : Float := 2.0

namespace Elk.Alg.Layered.Intermediate.Loops

open Elk.Core.Math Elk.Core.Options Elk.Core.Util Elk.Alg.Layered.Graph

namespace SelfHyperLoopLabels

/-- `SelfHyperLoopLabels.Alignment`: how the labels are aligned to the self loop. -/
elk_enum Alignment := center left right top

end SelfHyperLoopLabels

/-- `SelfHyperLoopLabels`: the labels of a self hyper loop, placed as one block. -/
structure SelfHyperLoopLabels where
  /-- `getLLabels()` (insertion order, no duplicates). -/
  lLabels : Array LLabelId := #[]
  /-- `getSize()`. -/
  size : KVector := {}
  /-- `getPosition()`. -/
  position : KVector := {}
  /-- `getSide()` (`UNDEFINED` until the label placer runs). -/
  side : PortSide := .undefined
  /-- `getAlignment()`. -/
  alignment : SelfHyperLoopLabels.Alignment := .center
  /-- `getAlignmentReferenceSLPort()`. -/
  alignmentReferenceSLPort : Option SelfLoopPortId := none
  /-- `labelLabelSpacing` (Rust default `0.0`). -/
  labelLabelSpacing : Float := fl0p0
  /-- `layoutDirectionHorizontal` (Rust default `true`). -/
  layoutDirectionHorizontal : Bool := true
  deriving Inhabited, Repr

namespace SelfHyperLoopLabels

/-- `recalculate_size()`: the stacked size of all labels (horizontal layouts stack vertically). -/
def recalculateSize (l : SelfHyperLoopLabels) (sizeOf : LLabelId → KVector) : SelfHyperLoopLabels := Id.run do
  let mut newSize : KVector := {}
  for h : i in [0:l.lLabels.size] do
    let s := sizeOf l.lLabels[i]
    if l.layoutDirectionHorizontal then
      newSize := { newSize with x := fmax newSize.x s.x, y := newSize.y + s.y }
      if i > 0 then newSize := { newSize with y := newSize.y + l.labelLabelSpacing }
    else
      newSize := { newSize with x := newSize.x + s.x, y := fmax newSize.y s.y }
      if i > 0 then newSize := { newSize with x := newSize.x + l.labelLabelSpacing }
  return { l with size := newSize }

/-- `set_label_label_spacing(spacing)`: also recalculates the size. -/
def setLabelLabelSpacing (l : SelfHyperLoopLabels) (spacing : Float) (sizeOf : LLabelId → KVector) : SelfHyperLoopLabels :=
  recalculateSize { l with labelLabelSpacing := spacing } sizeOf

/-- `set_layout_direction_horizontal(horizontal)`: also recalculates the size. -/
def setLayoutDirectionHorizontal (l : SelfHyperLoopLabels) (horizontal : Bool) (sizeOf : LLabelId → KVector) : SelfHyperLoopLabels :=
  recalculateSize { l with layoutDirectionHorizontal := horizontal } sizeOf

/-- `update_size(label)`: grows the size by a label that was just appended to `lLabels`. -/
def updateSize (l : SelfHyperLoopLabels) (s : KVector) : SelfHyperLoopLabels :=
  if l.layoutDirectionHorizontal then
    let size : KVector := ⟨fmax l.size.x s.x, l.size.y + s.y⟩
    let size := if l.lLabels.size > 1 then { size with y := size.y + l.labelLabelSpacing } else size
    { l with size := size }
  else
    let size : KVector := ⟨l.size.x + s.x, fmax l.size.y s.y⟩
    let size := if l.lLabels.size > 1 then { size with x := size.x + l.labelLabelSpacing } else size
    { l with size := size }

/-- `addLLabels(labels)`: appends the labels not yet contained (in order) and grows the size. -/
def addLLabels (l : SelfHyperLoopLabels) (labels : Array LLabelId) (sizeOf : LLabelId → KVector) : SelfHyperLoopLabels := Id.run do
  let mut l := l
  for label in labels do
    if l.lLabels.contains label then continue
    l := { l with lLabels := l.lLabels.push label }
    l := l.updateSize (sizeOf label)
  return l

/-- `apply_placement_for_horizontal_layout(offset)`: label positions, stacked top to bottom. -/
def placementForHorizontalLayout (l : SelfHyperLoopLabels) (offset : KVector) (sizeOf : LLabelId → KVector) :
    Array (LLabelId × KVector) := Id.run do
  let x := l.position.x
  let mut y := l.position.y
  let mut result := #[]
  for label in l.lLabels do
    let s := sizeOf label
    let labelX :=
      if l.alignment == .left || l.side == .east then x
      else if l.alignment == .right || l.side == .west then x + l.size.x - s.x
      else x + (l.size.x - s.x) / fl2p0
    result := result.push (label, ⟨labelX + offset.x, y + offset.y⟩)
    y := y + (s.y + l.labelLabelSpacing)
  return result

/-- `apply_placement_for_vertical_layout(offset)`: label positions, side by side (top aligned
except on the northern side). -/
def placementForVerticalLayout (l : SelfHyperLoopLabels) (offset : KVector) (sizeOf : LLabelId → KVector) :
    Array (LLabelId × KVector) := Id.run do
  let mut x := l.position.x
  let y := l.position.y
  let mut result := #[]
  for label in l.lLabels do
    let s := sizeOf label
    let labelY := if l.side == .north then y + l.size.y - s.y else y
    result := result.push (label, ⟨x + offset.x, labelY + offset.y⟩)
    x := x + (s.x + l.labelLabelSpacing)
  return result

/-- `applyPlacement(offset)`: the new position of every label (in `lLabels` order); the caller
writes them to the arena (`Loops.Ops.applyLabelPlacement`). -/
def placement (l : SelfHyperLoopLabels) (offset : KVector) (sizeOf : LLabelId → KVector) : Array (LLabelId × KVector) :=
  if l.layoutDirectionHorizontal then l.placementForHorizontalLayout offset sizeOf
  else l.placementForVerticalLayout offset sizeOf

/-- Size part of `apply_label_management(manager, targetWidth, spacing)`: after the label manager
has updated the label sizes (looked up through `sizeOf`), the block size is recomputed as a
vertical stack (`x = max`, `y = sum + spacing` between labels) regardless of the layout direction. -/
def sizeAfterLabelManagement (l : SelfHyperLoopLabels) (labelLabelSpacing : Float) (sizeOf : LLabelId → KVector) :
    SelfHyperLoopLabels := Id.run do
  let mut newSize : KVector := {}
  for h : i in [0:l.lLabels.size] do
    let s := sizeOf l.lLabels[i]
    newSize := ⟨fmax newSize.x s.x, newSize.y + s.y⟩
    if i > 0 then newSize := { newSize with y := newSize.y + labelLabelSpacing }
  return { l with size := newSize }

end SelfHyperLoopLabels

end Elk.Alg.Layered.Intermediate.Loops
