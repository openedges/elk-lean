import Elk.Alg.Common.Polyomino.Structures.Direction
import Elk.Alg.Common.Polyomino.Structures.PlanarGrid
/-!
# `org.eclipse.elk.alg.common.polyomino.structures.Polyomino`

A polyomino: a low resolution `PlanarGrid` with a position and extensions (elk-rs
`structures/polyomino.rs`).

`PolyominoLike` (the Rust trait; Java `Polyomino extends PlanarGrid`) is a typeclass because
other plugins provide their own polyomino types (disco `DCPolyomino`). Its required methods
are the Rust ones; `modifyGrid` replaces Rust `grid_mut` so that grid updates stay in place.
The provided Rust trait methods (`get_width`, `is_blocked`, `set_blocked`, …) are functions in
the `PolyominoLike` namespace.

Extensions are `(direction, offset, width)` tuples (Rust `UniqueTriple<Direction, i32, i32>`).

This module also contains the `PolyominoLike`-generic `PlanarGrid` operations
(`intersectsWithCenterBasedPolyomino`, `addFilledCellsFromPolyomino`), which Rust defines in
`planar_grid.rs`.
-/
namespace Elk.Alg.Common.Polyomino.Structures

/-- A polyomino extension `(direction, offset, width)` (Rust `UniqueTriple`). -/
abbrev PolyominoExtension := Direction × Int × Int

/-- `PolyominoLike` (Rust trait). -/
class PolyominoLike (P : Type) where
  /-- `grid()`. -/
  grid : P → PlanarGrid
  /-- `grid_mut()`: updates the grid. -/
  modifyGrid : P → (PlanarGrid → PlanarGrid) → P
  /-- `getPolyominoExtensions()`. -/
  polyominoExtensions : P → Array PolyominoExtension
  /-- `setX(value)`. -/
  setX : P → Int → P
  /-- `setY(value)`. -/
  setY : P → Int → P
  /-- `getX()`. -/
  x : P → Int
  /-- `getY()`. -/
  y : P → Int
  /-- `addExtension(dir, offset, width)`. -/
  addExtension : P → Direction → Int → Int → P

namespace PolyominoLike

variable {P : Type} [PolyominoLike P]

/-- `getWidth()`. -/
@[inline] def width (p : P) : Nat := (grid p).width
/-- `getHeight()`. -/
@[inline] def height (p : P) : Nat := (grid p).height
/-- `getCenterX()`. -/
@[inline] def centerX (p : P) : Int := (grid p).centerX
/-- `getCenterY()`. -/
@[inline] def centerY (p : P) : Int := (grid p).centerY
/-- `isEmpty(x, y)`. -/
@[inline] def isEmpty (p : P) (x y : Nat) : Bool := (grid p).isEmpty x y
/-- `isBlocked(x, y)`. -/
@[inline] def isBlocked (p : P) (x y : Nat) : Bool := (grid p).isBlocked x y
/-- `isWeaklyBlocked(x, y)`. -/
@[inline] def isWeaklyBlocked (p : P) (x y : Nat) : Bool := (grid p).isWeaklyBlocked x y
/-- `setBlocked(x, y)`. -/
@[inline] def setBlocked (p : P) (x y : Nat) : P := modifyGrid p (·.setBlocked x y)
/-- `setWeaklyBlocked(x, y)`. -/
@[inline] def setWeaklyBlocked (p : P) (x y : Nat) : P := modifyGrid p (·.setWeaklyBlocked x y)
/-- `setEmpty(x, y)`. -/
@[inline] def setEmpty (p : P) (x y : Nat) : P := modifyGrid p (·.setEmpty x y)

end PolyominoLike

/-- `Polyomino`. -/
structure Polyomino where
  /-- The cells of the polyomino. -/
  grid : PlanarGrid := {}
  /-- `x`: position (upper left corner) in the packing grid. -/
  x : Int := 0
  /-- `y`. -/
  y : Int := 0
  /-- `polyominoExtensions`. -/
  polyominoExtensions : Array PolyominoExtension := #[]
  deriving Inhabited, BEq

namespace Polyomino

/-- `new Polyomino(width, height)`. -/
def new (width height : Nat) : Polyomino := { grid := PlanarGrid.new width height }

/-- `new Polyomino(width, height, extensions)`. -/
def withExtensions (width height : Nat) (extensions : Array PolyominoExtension) : Polyomino :=
  { grid := PlanarGrid.new width height, polyominoExtensions := extensions }

/-- `reinitialize(width, height)`: resizes (and clears) the grid. -/
def reinitialize (p : Polyomino) (width height : Nat) : Polyomino :=
  { p with grid := p.grid.reinitialize width height }

instance : PolyominoLike Polyomino where
  grid p := p.grid
  modifyGrid p f := { p with grid := f p.grid }
  polyominoExtensions p := p.polyominoExtensions
  setX p v := { p with x := v }
  setY p v := { p with y := v }
  x p := p.x
  y p := p.y
  addExtension p dir offset width :=
    { p with polyominoExtensions := p.polyominoExtensions.push (dir, offset, width) }

end Polyomino

namespace PlanarGrid

variable {P : Type} [PolyominoLike P]

/-- `intersectsWithCenterBasedPolyomino(other, xOffset, yOffset)`: the cells intersect
(`intersectsWithCenterBasedGrid`) or the area of one of the extensions (to the grid border)
contains a blocked cell. -/
def intersectsWithCenterBasedPolyomino (g : PlanarGrid) (other : P) (xOffset yOffset : Int) :
    Except String Bool := do
  if g.intersectsWithCenterBasedGrid (PolyominoLike.grid other) xOffset yOffset then
    return true
  for (dir, second, third) in PolyominoLike.polyominoExtensions other do
    -- transformations for center based coordinates
    let leftX := g.centerX - PolyominoLike.centerX other + xOffset
    let rightX := leftX + (PolyominoLike.width other : Int)
    let topY := g.centerY - PolyominoLike.centerY other + yOffset
    let bottomY := topY + (PolyominoLike.height other : Int)
    let intersects ← match dir with
      | .north => g.weaklyIntersectsArea (leftX + second) 0 (leftX + third) (topY - 1)
      | .east => g.weaklyIntersectsArea rightX (topY + second) ((g.width : Int) - 1) (topY + third)
      | .south => g.weaklyIntersectsArea (leftX + second) bottomY (leftX + third) ((g.height : Int) - 1)
      | .west => g.weaklyIntersectsArea 0 (topY + second) (leftX - 1) (topY + third)
    if intersects then return true
  return false

/-- `addFilledCellsFromPolyomino(other, xOffset, yOffset)`: adds the cells of `other`, sets its
position and weakly blocks the areas of its extensions. Returns the updated grid and
polyomino. -/
def addFilledCellsFromPolyomino (g : PlanarGrid) (other : P) (xOffset yOffset : Int) :
    Except String (PlanarGrid × P) := do
  let mut g ← g.addFilledCellsFromGrid (PolyominoLike.grid other) xOffset yOffset
  let mut other := PolyominoLike.setX other (g.xCenter - PolyominoLike.centerX other + xOffset)
  other := PolyominoLike.setY other (g.yCenter - PolyominoLike.centerY other + yOffset)
  let ox := PolyominoLike.x other
  let oy := PolyominoLike.y other
  let ow : Int := PolyominoLike.width other
  let oh : Int := PolyominoLike.height other
  for (dir, second, third) in PolyominoLike.polyominoExtensions other do
    g ← match dir with
      | .north => g.weaklyBlockArea (ox + second) 0 (ox + third) (oy - 1)
      | .east => g.weaklyBlockArea (ox + ow) (oy + second) ((g.width : Int) - 1) (oy + third)
      | .south => g.weaklyBlockArea (ox + second) (oy + oh) (ox + third) ((g.height : Int) - 1)
      | .west => g.weaklyBlockArea 0 (oy + second) (ox - 1) (oy + third)
  return (g, other)

end PlanarGrid

end Elk.Alg.Common.Polyomino.Structures
