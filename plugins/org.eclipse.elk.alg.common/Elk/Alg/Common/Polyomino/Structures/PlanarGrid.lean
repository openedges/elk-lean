import Elk.Alg.Common.Polyomino.Structures.TwoBitGrid
/-!
# `org.eclipse.elk.alg.common.polyomino.structures.PlanarGrid`

A `TwoBitGrid` with a center, addressable in center-based coordinates (elk-rs
`structures/planar_grid.rs`). `xCenter = (width - 1) >> 1` (arithmetic shift, `-1` for an
empty grid), likewise `yCenter`.

The operations that Rust implements with a panic on out-of-bounds cells (`to_index`,
`to_index_non_center`: the center-based getters/setters, `addFilledCellsFromGrid`,
`weaklyBlockArea`, `weaklyIntersectsArea`) return `Except String` with the Rust message; the
polyomino variants (`intersectsWithCenterBasedPolyomino`, `addFilledCellsFromPolyomino`) need
`PolyominoLike` and live in `Elk.Alg.Common.Polyomino.Structures.Polyomino`.
`getFilledBounds` returns the Rust `Quadruple` as a tuple `(minX, minY, width, height)`.
-/
namespace Elk.Alg.Common.Polyomino.Structures

/-- `PlanarGrid`. -/
structure PlanarGrid where
  /-- The underlying cells. -/
  grid : TwoBitGrid := {}
  /-- `xCenter`. -/
  xCenter : Int := -1
  /-- `yCenter`. -/
  yCenter : Int := -1
  deriving Inhabited, BEq

namespace PlanarGrid

/-- `new PlanarGrid(width, height)`. -/
def new (width height : Nat) : PlanarGrid :=
  { grid := TwoBitGrid.new width height
    xCenter := ((width : Int) - 1) >>> 1
    yCenter := ((height : Int) - 1) >>> 1 }

/-- `getWidth()`. -/
@[inline] def width (g : PlanarGrid) : Nat := g.grid.width
/-- `getHeight()`. -/
@[inline] def height (g : PlanarGrid) : Nat := g.grid.height
/-- `isEmpty(x, y)`. -/
@[inline] def isEmpty (g : PlanarGrid) (x y : Nat) : Bool := g.grid.isEmpty x y
/-- `isBlocked(x, y)`. -/
@[inline] def isBlocked (g : PlanarGrid) (x y : Nat) : Bool := g.grid.isBlocked x y
/-- `isWeaklyBlocked(x, y)`. -/
@[inline] def isWeaklyBlocked (g : PlanarGrid) (x y : Nat) : Bool := g.grid.isWeaklyBlocked x y
/-- `inBounds(x, y)`. -/
@[inline] def inBounds (g : PlanarGrid) (x y : Nat) : Bool := g.grid.inBounds x y

/-- `reinitialize(width, height)`: empty grid of the new size, new center. -/
def reinitialize (_ : PlanarGrid) (width height : Nat) : PlanarGrid := new width height

/-- `setEmpty(x, y)`. -/
@[inline] def setEmpty (g : PlanarGrid) (x y : Nat) : PlanarGrid := { g with grid := g.grid.setEmpty x y }
/-- `setBlocked(x, y)`. -/
@[inline] def setBlocked (g : PlanarGrid) (x y : Nat) : PlanarGrid := { g with grid := g.grid.setBlocked x y }
/-- `setWeaklyBlocked(x, y)`. -/
@[inline] def setWeaklyBlocked (g : PlanarGrid) (x y : Nat) : PlanarGrid :=
  { g with grid := g.grid.setWeaklyBlocked x y }

/-- `getCenterX()`. -/
@[inline] def centerX (g : PlanarGrid) : Int := g.xCenter
/-- `getCenterY()`. -/
@[inline] def centerY (g : PlanarGrid) : Int := g.yCenter

/-- `to_index(x, y)`: center-based → array coordinates, failing outside the grid. -/
def toIndex (g : PlanarGrid) (x y : Int) : Except String (Nat × Nat) :=
  let xi := x + g.xCenter
  let yi := y + g.yCenter
  if xi < 0 || yi < 0 || !g.inBounds xi.toNat yi.toNat then
    .error (TwoBitGrid.boundsMessage g.width g.height x y)
  else .ok (xi.toNat, yi.toNat)

/-- `to_index_non_center(x, y)`: bounds check of plain coordinates. -/
def toIndexNonCenter (g : PlanarGrid) (x y : Int) : Except String (Nat × Nat) :=
  if x < 0 || y < 0 || !g.inBounds x.toNat y.toNat then
    .error (TwoBitGrid.boundsMessage g.width g.height x y)
  else .ok (x.toNat, y.toNat)

/-- `isEmptyCenterBased(x, y)`. -/
def isEmptyCenterBased (g : PlanarGrid) (x y : Int) : Except String Bool := do
  let (xu, yu) ← g.toIndex x y
  return g.isEmpty xu yu

/-- `isBlockedCenterBased(x, y)`. -/
def isBlockedCenterBased (g : PlanarGrid) (x y : Int) : Except String Bool := do
  let (xu, yu) ← g.toIndex x y
  return g.isBlocked xu yu

/-- `isWeaklyBlockedCenterBased(x, y)`. -/
def isWeaklyBlockedCenterBased (g : PlanarGrid) (x y : Int) : Except String Bool := do
  let (xu, yu) ← g.toIndex x y
  return g.isWeaklyBlocked xu yu

/-- `inBoundsCenterBased(x, y)`. -/
def inBoundsCenterBased (g : PlanarGrid) (x y : Int) : Bool :=
  let xi := x + g.xCenter
  let yi := y + g.yCenter
  if xi < 0 || yi < 0 then false else g.inBounds xi.toNat yi.toNat

/-- `setBlockedCenterBased(x, y)`. -/
def setBlockedCenterBased (g : PlanarGrid) (x y : Int) : Except String PlanarGrid := do
  let (xu, yu) ← g.toIndex x y
  return g.setBlocked xu yu

/-- `setEmptyCenterBased(x, y)`. -/
def setEmptyCenterBased (g : PlanarGrid) (x y : Int) : Except String PlanarGrid := do
  let (xu, yu) ← g.toIndex x y
  return g.setEmpty xu yu

/-- `setWeaklyBlockedCenterBased(x, y)`. -/
def setWeaklyBlockedCenterBased (g : PlanarGrid) (x y : Int) : Except String PlanarGrid := do
  let (xu, yu) ← g.toIndex x y
  return g.setWeaklyBlocked xu yu

/-- `intersectsWithCenterBasedGrid(other, xOffset, yOffset)`: some cell of `other` translated by
the offset (center-based) lies inside this grid and either a non-empty cell of `other` meets a
blocked cell, or a blocked cell of `other` meets a non-empty cell. -/
def intersectsWithCenterBasedGrid (g other : PlanarGrid) (xOffset yOffset : Int) : Bool := Id.run do
  for x in [0:other.width] do
    let xT := (x : Int) - other.centerX + xOffset
    for y in [0:other.height] do
      let yT := (y : Int) - other.centerY + yOffset
      if g.inBoundsCenterBased xT yT then
        -- in bounds: the center-based lookups cannot fail
        let xu := (xT + g.xCenter).toNat
        let yu := (yT + g.yCenter).toNat
        if (!other.isEmpty x y && g.isBlocked xu yu) || (other.isBlocked x y && !g.isEmpty xu yu) then
          return true
  return false

/-- `addFilledCellsFromGrid(other, xOffset, yOffset)`: copies the blocked cells of `other`
(unless weakly blocked here) and its weakly blocked cells (unless blocked here). -/
def addFilledCellsFromGrid (g other : PlanarGrid) (xOffset yOffset : Int) :
    Except String PlanarGrid := do
  let mut g := g
  for x in [0:other.width] do
    let xT := (x : Int) - other.centerX + xOffset
    for y in [0:other.height] do
      let yT := (y : Int) - other.centerY + yOffset
      if other.isBlocked x y then
        if !(← g.isWeaklyBlockedCenterBased xT yT) then
          g ← g.setBlockedCenterBased xT yT
      else if other.isWeaklyBlocked x y then
        if !(← g.isBlockedCenterBased xT yT) then
          g ← g.setWeaklyBlockedCenterBased xT yT
  return g

/-- `getFilledBounds()`: `(minX, minY, width, height)` of the blocked cells, `(0, 0, 0, 0)` if
there are none. -/
def filledBounds (g : PlanarGrid) : Int × Int × Int × Int := Id.run do
  let i32Max : Int := 2147483647
  let i32Min : Int := -2147483648
  let mut minX := i32Max
  let mut maxX := i32Min
  let mut minY := i32Max
  let mut maxY := i32Min
  for xi in [0:g.width] do
    for yi in [0:g.height] do
      if g.isBlocked xi yi then
        minX := min minX xi
        maxX := max maxX xi
        minY := min minY yi
        maxY := max maxY yi
  if minX == i32Max then return (0, 0, 0, 0)
  return (minX, minY, maxX - minX + 1, maxY - minY + 1)

/-- `weaklyBlockArea(xUpperLeft, yUpperLeft, xBottomRight, yBottomRight)` (inclusive bounds,
plain coordinates): weakly blocks every cell of the area that is not blocked. -/
def weaklyBlockArea (g : PlanarGrid) (xUpperLeft yUpperLeft xBottomRight yBottomRight : Int) :
    Except String PlanarGrid := do
  let mut g := g
  let mut yi := yUpperLeft
  while yi <= yBottomRight do
    let mut xi := xUpperLeft
    while xi <= xBottomRight do
      let (xu, yu) ← g.toIndexNonCenter xi yi
      if !g.isBlocked xu yu then
        g := g.setWeaklyBlocked xu yu
      xi := xi + 1
    yi := yi + 1
  return g

/-- `weaklyIntersectsArea(xUpperLeft, yUpperLeft, xBottomRight, yBottomRight)`: some cell of the
area (inclusive bounds, plain coordinates) is blocked. -/
def weaklyIntersectsArea (g : PlanarGrid) (xUpperLeft yUpperLeft xBottomRight yBottomRight : Int) :
    Except String Bool := do
  let mut yi := yUpperLeft
  while yi <= yBottomRight do
    let mut xi := xUpperLeft
    while xi <= xBottomRight do
      let (xu, yu) ← g.toIndexNonCenter xi yi
      if g.isBlocked xu yu then return true
      xi := xi + 1
    yi := yi + 1
  return false

instance : ToString PlanarGrid := ⟨fun g => toString g.grid⟩

instance : IThreeValueGrid PlanarGrid where
  width := width
  height := height
  isEmpty := isEmpty
  isBlocked := isBlocked
  isWeaklyBlocked := isWeaklyBlocked
  inBounds := inBounds
  reinitialize := reinitialize
  setEmpty := setEmpty
  setBlocked := setBlocked
  setWeaklyBlocked := setWeaklyBlocked

end PlanarGrid

end Elk.Alg.Common.Polyomino.Structures
