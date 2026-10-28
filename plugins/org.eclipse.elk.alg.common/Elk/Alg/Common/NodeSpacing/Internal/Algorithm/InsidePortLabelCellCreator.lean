import Elk.Alg.Common.NodeSpacing.Internal.NodeContext
/-!
# `org.eclipse.elk.alg.common.nodespacing.internal.algorithm.InsidePortLabelCellCreator`

Sets up the inside port label cells (elk-rs `internal::algorithm::InsidePortLabelCellCreator`).
They are created even without inside port labels because they also determine how much space the
ports need along the node borders. NORTH/SOUTH cells are the BEGIN/END cells of `nodeContainer`,
WEST/EAST cells the BEGIN/END cells of `nodeContainerMiddleRow`.

elk-rs keeps two copies of every cell (one in the cell tree, one in `inside_port_label_cells`) and
applies each update to both; here both places hold the same `CellId`, so every update is applied
once to the shared arena cell (all of them are idempotent assignments, so the result is the same).
-/
/-! Float literals as global constants (FL): inside branches, loops and specialised code the compiler
shares a literal's `Nat`/`Bool` arguments with unrelated variables (CSE) and then parses it on every
evaluation (`FastFloat.ofScientificImpl`); a top-level constant is a load (PLAN §7.1 items 17, 22). -/
private def fl0p0 : Float := 0.0

namespace Elk.Alg.Common.NodeSpacing.Internal.Algorithm

open Elk Elk.Core.Math Elk.Core.Util Elk.Core.Options
open Elk.Alg.Common.NodeSpacing.CellSystem Elk.Alg.Common.NodeSpacing.Internal

namespace InsidePortLabelCellCreator

variable {N P L : Type}

/-- `InsidePortLabelCellCreator.createInsidePortLabelCell(nodeContext, container, area, side)`:
a new atomic cell put into the given area of the container strip and registered for the side. -/
def createInsidePortLabelCell (ctx : NodeContext N P L) (container : CellId) (containerArea : ContainerArea)
    (portSide : PortSide) : NodeContext N P L :=
  let (ctx, portLabelCell) := ctx.modifyCellsGet fun cells =>
    let (cells, portLabelCell) := cells.createAtomic
    (cells.setCell container containerArea (some portLabelCell), portLabelCell)
  NodeContext.setInsidePortLabelCell ctx portSide (some portLabelCell)

/-- `InsidePortLabelCellCreator.setupNorthOrSouthPortLabelCell(nodeContext, side)`: the top
(NORTH) or bottom (SOUTH) padding becomes `portLabelSpacingVertical` unless that is negative; the
left and right paddings become the surrounding port margins. -/
def setupNorthOrSouthPortLabelCell (ctx : NodeContext N P L) (portSide : PortSide) : NodeContext N P L :=
  match ctx.insidePortLabelCell portSide with
  | none => ctx
  | some cell =>
    let spacing := ctx.portLabelSpacingVertical
    let margins := ctx.surroundingPortMargins
    ctx.modifyCells (·.modifyPadding cell fun p =>
      -- A negative port label spacing must not become a padding (it would enlarge the node)
      let p := match portSide with
        | .north => if spacing >= fl0p0 then { p with top := spacing } else p
        | .south => if spacing >= fl0p0 then { p with bottom := spacing } else p
        | _ => p
      { p with left := margins.left, right := margins.right })

/-- `InsidePortLabelCellCreator.calculateWidthDueToLabels(nodeContext, side)`: the cell's minimum
content width grows to the widest port label cell of the side (elk-rs: maximum over the side's
port contexts starting at `0`, then `fmax` with the current width); if the cell has a positive
width by then, its right (EAST) or left (WEST) padding becomes `portLabelSpacingHorizontal`. -/
def calculateWidthDueToLabels (ctx : NodeContext N P L) (portSide : PortSide) : NodeContext N P L :=
  -- Find the maximum label width for ports on this side
  let maxLabelWidth := (ctx.portContextsOf portSide).foldl (init := 0.0) fun acc pc =>
    match pc.portLabelCell with
    | some labelCell => fmax acc (ctx.cells.minimumWidth labelCell)
    | none => acc
  match portSide, ctx.insidePortLabelCell portSide with
  | .west, some cell | .east, some cell =>
    let spacing := ctx.portLabelSpacingHorizontal
    ctx.modifyCells fun cells =>
      let cells := cells.modifyMinimumContentAreaSize cell fun s => { s with x := fmax s.x maxLabelWidth }
      if (cells.minimumContentAreaSize cell).x > 0.0 then
        cells.modifyPadding cell fun p =>
          if portSide == .east then { p with right := spacing }
          else { p with left := spacing }
      else cells
  | _, _ => ctx

/-- `InsidePortLabelCellCreator.setupTopAndBottomPadding(nodeContext, side)`: the top and bottom
paddings of the EAST/WEST cell become the surrounding port margins. -/
def setupTopAndBottomPadding (ctx : NodeContext N P L) (portSide : PortSide) : NodeContext N P L :=
  match portSide, ctx.insidePortLabelCell portSide with
  | .west, some cell | .east, some cell =>
    let margins := ctx.surroundingPortMargins
    ctx.modifyCells (·.modifyPadding cell fun p => { p with top := margins.top, bottom := margins.bottom })
  | _, _ => ctx

/-- `InsidePortLabelCellCreator.setupEastOrWestPortLabelCell(nodeContext, side)`: the label
width (only for `INSIDE` port labels), then the top/bottom padding. -/
def setupEastOrWestPortLabelCell (ctx : NodeContext N P L) (portSide : PortSide) : NodeContext N P L :=
  let ctx := if ctx.portLabelsPlacement.contains .inside then calculateWidthDueToLabels ctx portSide else ctx
  setupTopAndBottomPadding ctx portSide

/-- `InsidePortLabelCellCreator.createInsidePortLabelCells(nodeContext)` (elk-rs
`create_inside_port_label_cells`): creates the NORTH (node container BEGIN), SOUTH (node container
END), WEST (middle row BEGIN) and EAST (middle row END) cells, then sets up NORTH, SOUTH, EAST and
WEST. -/
def createInsidePortLabelCells (ctx : NodeContext N P L) : NodeContext N P L :=
  let ctx := createInsidePortLabelCell ctx ctx.nodeContainer .begin .north
  let ctx := createInsidePortLabelCell ctx ctx.nodeContainer .«end» .south
  let ctx := createInsidePortLabelCell ctx ctx.nodeContainerMiddleRow .begin .west
  let ctx := createInsidePortLabelCell ctx ctx.nodeContainerMiddleRow .«end» .east
  let ctx := setupNorthOrSouthPortLabelCell ctx .north
  let ctx := setupNorthOrSouthPortLabelCell ctx .south
  let ctx := setupEastOrWestPortLabelCell ctx .east
  setupEastOrWestPortLabelCell ctx .west

end InsidePortLabelCellCreator

end Elk.Alg.Common.NodeSpacing.Internal.Algorithm
