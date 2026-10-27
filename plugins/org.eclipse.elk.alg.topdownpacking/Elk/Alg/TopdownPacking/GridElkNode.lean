import Elk.Graph
import Elk.Alg.TopdownPacking.Grid
/-!
# `org.eclipse.elk.alg.topdownpacking.GridElkNode`

Port of `grid_elk_node.rs` (elk-rs): an `ElkNode` (arena id) together with the grid of its
children. In Rust the wrapper holds the node by reference; here the wrapper is a plain value
that the topdown packing monad (`GridM`) keeps as state, and the node attributes are read and
written through `ElkM`.

`put` follows the Rust `Vec::insert(col, Some(item))` exactly (the row grows by one element
per placed item; the items stay in front of the remaining empty cells).
-/
namespace Elk.Alg.TopdownPacking

open Elk.Graph

/-- `GridElkNode`. -/
structure GridElkNode where
  /-- The wrapped node. -/
  node : NodeId
  /-- `grid`: `rows` rows of cells. -/
  grid : Array (Array (Option NodeId)) := #[]
  /-- `rows`. -/
  rows : Nat := 0
  /-- `cols`. -/
  cols : Nat := 0

namespace GridElkNode

/-- `GridElkNode::new(node)`. -/
def new (node : NodeId) : GridElkNode := { node }

/-- `ensure_bounds(col, row)`: `panic!` in Rust. -/
private def ensureBounds (g : GridElkNode) (col row : Nat) : Except String Unit :=
  if col >= g.cols || row >= g.rows then
    .error s!"java.lang.IndexOutOfBoundsException: The grid has a size of ({g.cols} x {g.rows}). The requested index of ({col} x {row}) is out of bounds."
  else .ok ()

/-- `identifier()`: the node identifier or the empty string. -/
def identifier (g : GridElkNode) : ElkM String := do
  return (← ElkM.getNode g.node).identifier.getD ""

/-- `width()`. -/
def width (g : GridElkNode) : ElkM Float := do return (← ElkM.getNode g.node).width

/-- `height()`. -/
def height (g : GridElkNode) : ElkM Float := do return (← ElkM.getNode g.node).height

/-- `set_dimensions(width, height)`. -/
def setDimensions (g : GridElkNode) (width height : Float) : ElkM Unit :=
  ElkM.modifyNode g.node fun n => { n with width := width, height := height }

/-- `children()`. -/
def children (g : GridElkNode) : ElkM (Array NodeId) := do
  return (← ElkM.getNode g.node).children

instance : Grid GridElkNode NodeId where
  put g col row item := do
    g.ensureBounds col row
    match g.grid[row]? with
    | none => throw "java.lang.IllegalStateException: row exists"
    | some r =>
      let r := if col <= r.size then r.insertIdx! col (some item) else r
      return { g with grid := g.grid.set! row r }
  get g col row := do
    g.ensureBounds col row
    return (g.grid[row]?.bind (·[col]?)).bind id
  getRow g row :=
    if row >= g.rows then
      .error s!"java.lang.IndexOutOfBoundsException: The grid has a size of ({g.cols} x {g.rows}). The requested row {row} is out of bounds."
    else .ok (g.grid[row]?.getD #[])
  getColumn g col :=
    if col >= g.cols then
      .error s!"java.lang.IndexOutOfBoundsException: The grid has a size of ({g.cols} x {g.rows}). The requested column {col} is out of bounds."
    else .ok (g.grid.map fun r => (r[col]?).bind id)
  columns g := g.cols
  rows g := g.rows
  setGridSize g cols rows :=
    { g with cols := cols, rows := rows, grid := Array.replicate rows (Array.replicate cols none) }

end GridElkNode

/-- The monad of the topdown packing phases: the `ElkGraph` arena plus the `GridElkNode` being
laid out (the Rust phases receive it as `&mut GridElkNode`). -/
abbrev GridM := StateRefT GridElkNode ElkM

namespace GridM

/-- Lifts a bounds-checked `Except` grid operation (`panic!` in Rust) into `GridM`. -/
def liftExcept {α : Type} (x : Except String α) : GridM α :=
  match x with
  | .ok a => pure a
  | .error e => throw (IO.userError e)

end GridM

end Elk.Alg.TopdownPacking
