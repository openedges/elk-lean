import Elk.Core.Math
import Elk.Alg.Common.NodeSpacing.CellSystem.ContainerArea
import Elk.Alg.Common.NodeSpacing.CellSystem.HorizontalLabelAlignment
import Elk.Alg.Common.NodeSpacing.CellSystem.VerticalLabelAlignment
import Elk.Graph.ArrayModify
/-!
# `org.eclipse.elk.alg.common.nodespacing.cellsystem.Cell` (+ the shared cell arena)

The Java cell system is a mutable object tree whose cells are shared by several maps of
`NodeContext` (`insidePortLabelCells`, `outsideNodeLabelContainers`, …) and by
`PortContext.portLabelCell`. elk-rs keeps copies instead (and has to re-sync them, see
`NodeContext.syncInsidePortLabelCellRectangles`). The Lean port stores every cell in one
arena, `CellArena L`, and refers to cells through `CellId`s; every holder of a `CellId`
therefore sees the same cell, exactly like the Java object references.

* `Cell L` holds the fields of the abstract Java `Cell` (`padding`, `cellRectangle`,
  `contributesToMinimumWidth/Height`) plus a `kind : CellKind L` with the data of the
  concrete subclass (`AtomicCell`, `LabelCell`, `StripContainerCell`, `GridContainerCell`).
  The data structures of all subclasses live here because `CellKind` is a closed inductive;
  the subclass behaviour lives in the per-class modules (`AtomicCell.lean`, …) and the
  virtual dispatch of `getMinimumWidth()`/`getMinimumHeight()`/`layoutChildren*()` in
  `CellDispatch.lean`.
* `L` is the label handle type of label cells (`LabelId` for `ElkGraph`, the layered label id
  for `LGraph`, …). A label cell stores each label together with its size at `addLabel` time.
* A missing child (Java `null`, elk-rs `CellChild::None`) is `none : Option CellId`.
* All functions are pure (`CellArena L → … → CellArena L`); invalid ids read as a default
  atomic cell and writes to invalid ids are ignored (no panics).
-/
namespace Elk.Alg.Common.NodeSpacing.CellSystem

open Elk Elk.Core.Math

/-- Typed index of a cell in a `CellArena`. -/
structure CellId where
  idx : Nat
  deriving BEq, Hashable, Repr, Inhabited, DecidableEq

instance : ToString CellId := ⟨fun c => s!"cell#{c.idx}"⟩

/-- `StripContainerCell.Strip`: whether a strip lays out its children as rows (`VERTICAL`) or
as columns (`HORIZONTAL`). Declared here because `StripCellData` (part of `CellKind`) needs it. -/
elk_enum Strip := vertical horizontal

/-- Data of a `LabelCell` (elk-rs `LabelCell`/`DynLabelCell`). -/
structure LabelCellData (L : Type) where
  /-- `horizontalLayoutMode`: labels stacked vertically (`true`) or placed side by side. -/
  horizontalLayoutMode : Bool := true
  /-- `horizontalAlignment` (default `CENTER`). -/
  horizontalAlignment : HorizontalLabelAlignment := .center
  /-- `verticalAlignment` (default `CENTER`). -/
  verticalAlignment : VerticalLabelAlignment := .center
  /-- `gap` between two consecutive labels. -/
  gap : Float := 0.0
  /-- `labels`: label handle and the label size read when it was added. -/
  labels : Array (L × KVector) := #[]
  /-- `minimumContentAreaSize`: space needed to place the labels (without padding). -/
  minimumContentAreaSize : KVector := {}
  deriving Inhabited

/-- Data of a `StripContainerCell`. -/
structure StripCellData where
  /-- `containerMode`. -/
  containerMode : Strip
  /-- `symmetrical`: whether the outer cells get the same size. -/
  symmetrical : Bool
  /-- `gap` inserted between consecutive non-empty children. -/
  gap : Float
  /-- `cells`: the three children, indexed by `ContainerArea.index`. -/
  cells : Array (Option CellId) := #[none, none, none]
  deriving Inhabited

/-- Data of a `GridContainerCell`. -/
structure GridCellData where
  /-- `gap` inserted between consecutive non-empty rows/columns. -/
  gap : Float
  /-- `tabular`: column widths locked across the three rows. -/
  tabular : Bool
  /-- `symmetrical`: outer columns/rows get the same width/height. -/
  symmetrical : Bool
  /-- `cells`: 3×3 children in row-major order, index `3 * row.index + col.index`. -/
  cells : Array (Option CellId) := Array.replicate 9 none
  /-- `centerCellMinimumSize` (Java `null` = `none`). -/
  centerCellMinimumSize : Option KVector := none
  /-- `onlyCenterCellContributesToMinimumSize`. -/
  onlyCenterCellContributes : Bool := false
  /-- `centerCellRect`: area left free by the outer rows and columns (set by the layout). -/
  centerCellRect : ElkRectangle := {}
  deriving Inhabited

/-- The concrete Java subclass of a cell together with its specific fields. -/
inductive CellKind (L : Type) where
  /-- `AtomicCell` with its `minimumContentAreaSize`. -/
  | atomic (minimumContentAreaSize : KVector)
  /-- `LabelCell`. -/
  | label (data : LabelCellData L)
  /-- `StripContainerCell`. -/
  | strip (data : StripCellData)
  /-- `GridContainerCell`. -/
  | grid (data : GridCellData)

instance {L : Type} : Inhabited (CellKind L) := ⟨.atomic {}⟩

/-- `Cell`: the fields shared by all cells plus the subclass data. -/
structure Cell (L : Type) where
  /-- `padding` (included in the cell rectangle). -/
  padding : ElkPadding := {}
  /-- `cellRectangle`: actual size and position of the cell, including the padding. -/
  cellRectangle : ElkRectangle := {}
  /-- `contributesToMinimumWidth` (default `false`). -/
  contributesToMinimumWidth : Bool := false
  /-- `contributesToMinimumHeight` (default `false`). -/
  contributesToMinimumHeight : Bool := false
  /-- Subclass and its data. -/
  kind : CellKind L
  deriving Inhabited

/-- Arena of all cells of one cell system (one `NodeContext`). -/
structure CellArena (L : Type) where
  /-- The cells, indexed by `CellId.idx`. -/
  cells : Array (Cell L) := #[]
  deriving Inhabited

namespace CellArena

variable {L : Type}

/-- The empty arena. -/
def empty : CellArena L := {}

/-- Number of cells. -/
@[inline] def size (a : CellArena L) : Nat := a.cells.size

/-- Adds a cell and returns its id. -/
def add (a : CellArena L) (c : Cell L) : CellArena L × CellId :=
  -- the id is read first so that `a` is dead when its array is pushed (in place)
  let id : CellId := ⟨a.cells.size⟩
  ({ a with cells := a.cells.push c }, id)

/-- The cell with the given id (a default atomic cell for an invalid id). -/
@[inline] def get (a : CellArena L) (id : CellId) : Cell L := a.cells[id.idx]?.getD default

/-- Replaces the cell with the given id (ignored for an invalid id). -/
@[inline] def set (a : CellArena L) (id : CellId) (c : Cell L) : CellArena L :=
  { a with cells := a.cells.setIfInBounds id.idx c }

/-- Updates the cell with the given id in place (ignored for an invalid id). -/
@[inline] def modify (a : CellArena L) (id : CellId) (f : Cell L → Cell L) : CellArena L :=
  { a with cells := a.cells.modifyIn id.idx f }

/-- `Cell.getPadding()`. -/
@[inline] def padding (a : CellArena L) (id : CellId) : ElkPadding := (a.get id).padding

/-- Replaces the cell's padding (Java: mutating the object returned by `getPadding()`). -/
def setPadding (a : CellArena L) (id : CellId) (p : ElkPadding) : CellArena L :=
  a.modify id fun c => { c with padding := p }

/-- Updates the cell's padding (Rust `padding()` mutable access). -/
def modifyPadding (a : CellArena L) (id : CellId) (f : ElkPadding → ElkPadding) : CellArena L :=
  a.modify id fun c => { c with padding := f c.padding }

/-- `Cell.getCellRectangle()`. -/
@[inline] def cellRectangle (a : CellArena L) (id : CellId) : ElkRectangle := (a.get id).cellRectangle

/-- Replaces the cell rectangle (Java: mutating the object returned by `getCellRectangle()`). -/
def setCellRectangle (a : CellArena L) (id : CellId) (r : ElkRectangle) : CellArena L :=
  a.modify id fun c => { c with cellRectangle := r }

/-- Updates the cell rectangle (Rust `cell_rectangle()` mutable access). -/
def modifyCellRectangle (a : CellArena L) (id : CellId) (f : ElkRectangle → ElkRectangle) : CellArena L :=
  a.modify id fun c => { c with cellRectangle := f c.cellRectangle }

/-- `Cell.isContributingToMinimumWidth()`. -/
@[inline] def isContributingToMinimumWidth (a : CellArena L) (id : CellId) : Bool :=
  (a.get id).contributesToMinimumWidth

/-- `Cell.setContributesToMinimumWidth(b)`. -/
def setContributesToMinimumWidth (a : CellArena L) (id : CellId) (b : Bool) : CellArena L :=
  a.modify id fun c => { c with contributesToMinimumWidth := b }

/-- `Cell.isContributingToMinimumHeight()`. -/
@[inline] def isContributingToMinimumHeight (a : CellArena L) (id : CellId) : Bool :=
  (a.get id).contributesToMinimumHeight

/-- `Cell.setContributesToMinimumHeight(b)`. -/
def setContributesToMinimumHeight (a : CellArena L) (id : CellId) (b : Bool) : CellArena L :=
  a.modify id fun c => { c with contributesToMinimumHeight := b }

/-- Java `cell instanceof AtomicCell` (elk-rs `CellChild::is_atomic`). -/
def isAtomic (a : CellArena L) (id : CellId) : Bool :=
  match (a.get id).kind with | .atomic _ => true | _ => false

/-- Java `cell instanceof LabelCell` (elk-rs `matches!(c, CellChild::Label(_))`). -/
def isLabel (a : CellArena L) (id : CellId) : Bool :=
  match (a.get id).kind with | .label _ => true | _ => false

/-- Java `cell instanceof StripContainerCell`. -/
def isStrip (a : CellArena L) (id : CellId) : Bool :=
  match (a.get id).kind with | .strip _ => true | _ => false

/-- Java `cell instanceof GridContainerCell`. -/
def isGrid (a : CellArena L) (id : CellId) : Bool :=
  match (a.get id).kind with | .grid _ => true | _ => false

/-- Java `cell instanceof ContainerCell` (strip or grid). -/
def isContainer (a : CellArena L) (id : CellId) : Bool :=
  match (a.get id).kind with | .strip _ | .grid _ => true | _ => false

/-! ### Optional-child helpers (elk-rs `CellChild` methods on a possibly empty slot) -/

/-- elk-rs `CellChild::set_contributes_to_minimum_width` (no-op for an empty slot). -/
def setContributesToMinimumWidthOpt (a : CellArena L) (id : Option CellId) (b : Bool) : CellArena L :=
  match id with | some c => a.setContributesToMinimumWidth c b | none => a

/-- elk-rs `CellChild::set_contributes_to_minimum_height` (no-op for an empty slot). -/
def setContributesToMinimumHeightOpt (a : CellArena L) (id : Option CellId) (b : Bool) : CellArena L :=
  match id with | some c => a.setContributesToMinimumHeight c b | none => a

/-- elk-rs `CellChild::cell_rectangle` (zero rectangle for an empty slot). -/
def cellRectangleOpt (a : CellArena L) (id : Option CellId) : ElkRectangle :=
  match id with | some c => a.cellRectangle c | none => {}

/-- elk-rs `CellChild::padding` (zero padding for an empty slot). -/
def paddingOpt (a : CellArena L) (id : Option CellId) : ElkPadding :=
  match id with | some c => a.padding c | none => {}

end CellArena

end Elk.Alg.Common.NodeSpacing.CellSystem
