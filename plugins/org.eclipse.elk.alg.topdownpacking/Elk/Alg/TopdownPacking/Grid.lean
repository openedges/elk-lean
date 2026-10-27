/-!
# `org.eclipse.elk.alg.topdownpacking.Grid`

Port of `grid.rs` (elk-rs): a two-dimensional grid of items. Out-of-bounds access throws
(`panic!` in Rust) as `Except String` carrying the `IndexOutOfBoundsException` message.
-/
namespace Elk.Alg.TopdownPacking

/-- `Grid<T>`: `g` is the grid type, `T` the item type. -/
class Grid (g : Type) (T : outParam Type) where
  /-- `put(col, row, item)`. -/
  put : g → Nat → Nat → T → Except String g
  /-- `get(col, row)`. -/
  get : g → Nat → Nat → Except String (Option T)
  /-- `get_row(row)`. -/
  getRow : g → Nat → Except String (Array (Option T))
  /-- `get_column(col)`. -/
  getColumn : g → Nat → Except String (Array (Option T))
  /-- `columns()`. -/
  columns : g → Nat
  /-- `rows()`. -/
  rows : g → Nat
  /-- `set_grid_size(cols, rows)`. -/
  setGridSize : g → Nat → Nat → g

end Elk.Alg.TopdownPacking
