/-!
# `org.eclipse.elk.alg.common.polyomino.structures.IThreeValueGrid`

A grid whose cells are empty, blocked or weakly blocked (elk-rs
`structures/i_three_value_grid.rs`). A typeclass over value-type grids: the setters return the
updated grid. Implemented by `TwoBitGrid` and `PlanarGrid`.
-/
namespace Elk.Alg.Common.Polyomino.Structures

/-- `IThreeValueGrid`. -/
class IThreeValueGrid (G : Type) where
  /-- `getWidth()`. -/
  width : G → Nat
  /-- `getHeight()`. -/
  height : G → Nat
  /-- `isEmpty(x, y)`. -/
  isEmpty : G → Nat → Nat → Bool
  /-- `isBlocked(x, y)`. -/
  isBlocked : G → Nat → Nat → Bool
  /-- `isWeaklyBlocked(x, y)`. -/
  isWeaklyBlocked : G → Nat → Nat → Bool
  /-- `inBounds(x, y)`. -/
  inBounds : G → Nat → Nat → Bool
  /-- `reinitialize(width, height)`: an empty grid of the new size. -/
  reinitialize : G → Nat → Nat → G
  /-- `setEmpty(x, y)`. -/
  setEmpty : G → Nat → Nat → G
  /-- `setBlocked(x, y)`. -/
  setBlocked : G → Nat → Nat → G
  /-- `setWeaklyBlocked(x, y)`. -/
  setWeaklyBlocked : G → Nat → Nat → G

end Elk.Alg.Common.Polyomino.Structures
