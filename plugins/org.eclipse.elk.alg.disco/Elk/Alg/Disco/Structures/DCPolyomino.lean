import Elk.Alg.Common.Polyomino.Structures.Polyomino
import Elk.Alg.Disco.Graph.DCGraph
/-!
# `org.eclipse.elk.alg.disco.structures.DCPolyomino`

A low resolution representation of a `DCComponent` (elk-rs `structures/dc_polyomino.rs`): the
component's bounding rectangle is covered by a grid of `cellSizeX * cellSizeY` cells and every
cell that intersects an element is blocked. Extensions of elements are added as polyomino
extensions and weakly block the area between the element and the border.

Rust holds the represented component as `Arc<Mutex<DCComponent>>`; here it is a
`DCComponentId` and every operation that reads the component takes the `DCGraph` (its
arena). The grid operations that can run out of bounds (a Rust panic) make `new` return
`Except String`.
-/
namespace Elk.Alg.Disco.Structures

open Elk.Core.Math Elk.Core.Util Elk.Alg.Common.Polyomino.Structures Elk.Alg.Disco.Graph

/-- `DCPolyomino`. -/
structure DCPolyomino where
  /-- The underlying polyomino (grid, position and extensions). -/
  poly : Polyomino
  /-- `getRepresentee()`. -/
  representee : DCComponentId
  /-- Width of the low resolution grid in cells. -/
  pWidth : Nat
  /-- Height of the low resolution grid in cells. -/
  pHeight : Nat
  /-- `getCellSizeX()`. -/
  cellSizeX : Float
  /-- `getCellSizeY()`. -/
  cellSizeY : Float
  deriving Inhabited

namespace DCPolyomino

/-- `PolyominoLike` (Rust trait impl delegating to the inner `Polyomino`). -/
instance : PolyominoLike DCPolyomino where
  grid p := PolyominoLike.grid p.poly
  modifyGrid p f := { p with poly := PolyominoLike.modifyGrid p.poly f }
  polyominoExtensions p := PolyominoLike.polyominoExtensions p.poly
  setX p v := { p with poly := PolyominoLike.setX p.poly v }
  setY p v := { p with poly := PolyominoLike.setY p.poly v }
  x p := PolyominoLike.x p.poly
  y p := PolyominoLike.y p.poly
  addExtension p dir offset width := { p with poly := PolyominoLike.addExtension p.poly dir offset width }

/-- `compute_low_res_dimension`: `ceil(dim / cellSize)` computed as truncation (saturating cast
to `usize`: NaN and negative values give `0`) plus one if the quotient is larger than the
truncated value. -/
def computeLowResDimension (dim cellSize : Float) : Nat :=
  let cellFit := dim / cellSize
  let fitTruncated : UInt64 := cellFit.toUInt64
  if cellFit > fitTruncated.toFloat then (fitTruncated + 1).toNat else fitTruncated.toNat

/-- Rust `x as i32` for an `f64`: truncation toward zero, saturating, NaN gives `0`. -/
private def toI32 (x : Float) : Int :=
  let v := Float.toIntTrunc x
  if v > 2147483647 then 2147483647 else if v < -2147483648 then -2147483648 else v

/-- `getOffset()`: `-0.5 * (boundingRectangle - gridSize)`, the shift between the component and
its low resolution grid. -/
def getOffset (g : DCGraph) (p : DCPolyomino) : KVector :=
  let dims := g.componentDimensions p.representee
  let offset := dims.subValues (p.pWidth.toFloat * p.cellSizeX) (p.pHeight.toFloat * p.cellSizeY)
  offset.scale (-0.5)

/-- `getMinCornerOnCanvas()`: `component.minCorner - getOffset()`. -/
def getMinCornerOnCanvas (g : DCGraph) (p : DCPolyomino) : KVector :=
  (g.componentMinCorner p.representee).sub (getOffset g p)

/-- `getId()` (the id of the represented component). -/
def getId (g : DCGraph) (p : DCPolyomino) : Int := g.componentId p.representee

/-- `fillCells()`: blocks every cell whose rectangle intersects the component. Rows are visited
top to bottom, cells left to right; the coordinates advance by repeated addition like Rust. -/
private def fillCells (g : DCGraph) (poly : DCPolyomino) : DCPolyomino := Id.run do
  let compCorner := g.componentMinCorner poly.representee
  let polyoOffset := getOffset g poly
  let baseX := compCorner.x - polyoOffset.x
  let mut curY := compCorner.y - polyoOffset.y
  let mut poly := poly
  for y in [0:poly.pHeight] do
    let mut curX := baseX
    for x in [0:poly.pWidth] do
      let rect := ElkRectangle.ofValues curX curY poly.cellSizeX poly.cellSizeY
      if g.componentIntersects poly.representee rect then
        poly := PolyominoLike.setBlocked poly x y
      curX := curX + poly.cellSizeX
    curY := curY + poly.cellSizeY
  return poly

/-- `weaklyBlockArea(...)` of the grid (inclusive plain coordinates). -/
private def weaklyBlockArea (p : DCPolyomino) (xUpperLeft yUpperLeft xBottomRight yBottomRight : Int) :
    Except String DCPolyomino := do
  let grid ← (PolyominoLike.grid p).weaklyBlockArea xUpperLeft yUpperLeft xBottomRight yBottomRight
  return PolyominoLike.modifyGrid p fun _ => grid

/-- `DCDirection` → polyomino `Direction`. -/
private def toPolyominoDirection : DCDirection → Direction
  | .north => .north
  | .east => .east
  | .south => .south
  | .west => .west

/-- `addExtensions(DCElement)` (Rust `add_extensions_to_poly`): registers every extension of the
element as a polyomino extension and weakly blocks the area between the element and the grid
border. -/
private def addExtensionsToPoly (g : DCGraph) (poly : DCPolyomino) (elem : DCElement) :
    Except String DCPolyomino := do
  let compCorner := g.componentMinCorner poly.representee
  let polyoOffset := getOffset g poly
  let baseX := compCorner.x - polyoOffset.x
  let baseY := compCorner.y - polyoOffset.y
  let elemPos := elem.bounds
  let baseX := elemPos.x - baseX
  let baseY := elemPos.y - baseY
  let mut poly := poly
  for extension in elem.extensions do
    let pos := extension.offset
    let xe := baseX + pos.x
    let ye := baseY + pos.y
    let xp := toI32 (xe / poly.cellSizeX)
    let yp := toI32 (ye / poly.cellSizeY)
    let dir := extension.direction
    let polyDir := toPolyominoDirection dir
    if dir.isHorizontal then
      let ypPlusWidth := toI32 ((ye + extension.width) / poly.cellSizeY)
      poly := PolyominoLike.addExtension poly polyDir yp ypPlusWidth
      if dir == .west then
        poly ← weaklyBlockArea poly 0 yp xp ypPlusWidth
      else
        poly ← weaklyBlockArea poly xp yp ((poly.pWidth : Int) - 1) ypPlusWidth
    else
      let xpPlusWidth := toI32 ((xe + extension.width) / poly.cellSizeX)
      poly := PolyominoLike.addExtension poly polyDir xp xpPlusWidth
      if dir == .north then
        poly ← weaklyBlockArea poly xp 0 xpPlusWidth yp
      else
        poly ← weaklyBlockArea poly xp yp xpPlusWidth ((poly.pHeight : Int) - 1)
  return poly

/-- `new DCPolyomino(comp, cellSizeX, cellSizeY)`: computes the low resolution size, blocks the
cells covered by the component and adds the extensions (elements in component order). -/
def new (g : DCGraph) (comp : DCComponentId) (cellSizeX cellSizeY : Float) :
    Except String DCPolyomino := do
  let dims := g.componentDimensions comp
  let pWidth := computeLowResDimension dims.x cellSizeX
  let pHeight := computeLowResDimension dims.y cellSizeY
  let poly := (Polyomino.new pWidth pHeight).reinitialize pWidth pHeight
  let mut result : DCPolyomino := { poly, representee := comp, pWidth, pHeight, cellSizeX, cellSizeY }
  result := fillCells g result
  for elemId in g.components[comp.idx]!.shapes do
    let elem := g.elements[elemId.idx]!
    if !elem.extensions.isEmpty then
      result ← addExtensionsToPoly g result elem
  return result

end DCPolyomino

end Elk.Alg.Disco.Structures
