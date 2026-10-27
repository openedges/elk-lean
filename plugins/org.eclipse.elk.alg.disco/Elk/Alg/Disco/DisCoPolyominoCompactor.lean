import Elk.Core.Options
import Elk.Core.Exceptions
import Elk.Alg.Common.Compaction.Options.PolyominoOptions
import Elk.Alg.Common.Polyomino
import Elk.Alg.Disco.ICompactor
import Elk.Alg.Disco.Options.DisCoOptions
import Elk.Alg.Disco.Structures.DCPolyomino
/-!
# `org.eclipse.elk.alg.disco.DisCoPolyominoCompactor`

Connected components layout based on polyominoes (elk-rs `disco_polyomino_compactor.rs`, after
Freivalds, Dogrusoz and Kikusts, "Disconnected Graph Layout and the Polyomino Packing
Approach"). Every component is represented by a low resolution polyomino (`DCPolyomino`), the
polyominoes are packed by `PolyominoCompactor`, and the resulting grid positions are translated
back into an offset per component and the dimensions of the graph.

The polyomino packing options (`lowLevelSort`, `highLevelSort`, `traversalStrategy`) are read from
the `Polyominoes` holder, which does not copy the graph's options (Rust/Java: defaults). Only
`polyomino.fill` and `aspectRatio` are taken from the graph's options.

The debug polyominoes (`DEBUG_DISCO_POLYS`) are returned by `compactWithPolys` instead of being
stored as a graph property (see `DisCoOptions`).
-/
namespace Elk.Alg.Disco

open Elk.Core Elk.Core.Math Elk.Core.Options Elk.Alg.Common.Compaction.Options
open Elk.Alg.Common.Polyomino Elk.Alg.Common.Polyomino.Structures
open Elk.Alg.Disco.Graph Elk.Alg.Disco.Options Elk.Alg.Disco.Structures

/-- `DisCoPolyominoCompactor`. -/
structure DisCoPolyominoCompactor where
  /-- `upperBound`: upper bound on the size of a grid cell, 100 is the recommendation of the
  paper. -/
  upperBound : Float := 100.0

namespace DisCoPolyominoCompactor

/-- `new DisCoPolyominoCompactor()`. -/
def new : DisCoPolyominoCompactor := {}

/-- `computeCellSize(graph)`: the positive solution `l` of
`(c*n-1)*l^2 - sum(W_i + H_i)*l - sum(W_i*H_i) = 0` of the paper, with `c` the upper bound and
`n` the number of components. -/
def computeCellSize (self : DisCoPolyominoCompactor) (graph : DCGraph) : Float := Id.run do
  let mut sumTerm := 0.0
  let mut prodTerm := 0.0
  let numOfComps := graph.components.size.toFloat
  for i in [0:graph.components.size] do
    let bounds := graph.componentDimensions ⟨i⟩
    let width := bounds.x
    let height := bounds.y
    sumTerm := sumTerm + (width + height)
    prodTerm := prodTerm + width * height
  let four := 4.0
  let numerator :=
    Float.sqrt (four * self.upperBound * numOfComps * prodTerm - four * prodTerm + sumTerm * sumTerm) + sumTerm
  let denominator := 2.0 * (self.upperBound * numOfComps - 1.0)
  if denominator == 0.0 then
    return numerator
  return numerator / denominator

/-- `createPolyominoes()`: one `DCPolyomino` per component, in component order. -/
def createPolyominoes (graph : DCGraph) (cellSizeX cellSizeY : Float) :
    IO (Array DCPolyomino) := do
  let mut polys : Array DCPolyomino := Array.mkEmpty graph.components.size
  for i in [0:graph.components.size] do
    match DCPolyomino.new graph ⟨i⟩ cellSizeX cellSizeY with
    | .ok p => polys := polys.push p
    | .error e => throw (javaException indexOutOfBoundsExceptionClass e)
  return polys

/-- `packPolyominoes()`: numbers the components (debug ids), packs the polyominoes and returns
them in packing order (sorted) together with the packing grid. -/
def packPolyominoes (graph : DCGraph) (polys : Array DCPolyomino) (aspectRatio : Float)
    (fill : Bool) : IO (DCGraph × Array DCPolyomino × PlanarGrid) := do
  let mut graph := graph
  let mut id : Int := 0
  for poly in polys do
    graph := graph.setComponentId poly.representee id
    id := id + 1
  let polyHolder := Polyominoes.new polys aspectRatio fill
  let packed ← PolyominoCompactor.packPolyominoesIO polyHolder
  return (graph, packed.polys, packed.grid)

/-- `applyToDCGraph()`: sets the dimensions of the graph (the filled part of the packing grid plus
padding) and the offset of every component (new canvas position minus original min corner). -/
def applyToDCGraph (graph : DCGraph) (polys : Array DCPolyomino) (grid : PlanarGrid)
    (gridCellSizeX gridCellSizeY : Float) : DCGraph := Id.run do
  let (cropX, cropY, cropWidth, cropHeight) := grid.filledBounds
  let padding := ((graph.properties.get DisCoOptions.PADDING).getD {})
  let paddingHori := padding.left + padding.right
  let paddingVert := padding.top + padding.bottom
  let parentWidth := Float.ofInt cropWidth * gridCellSizeX + paddingHori
  let parentHeight := Float.ofInt cropHeight * gridCellSizeY + paddingVert
  let mut graph := { graph with dimensions := KVector.mk' parentWidth parentHeight }
  for poly in polys do
    let absoluteIntX := PolyominoLike.x poly - cropX
    let absoluteIntY := PolyominoLike.y poly - cropY
    let absolutePosition :=
      ((KVector.mk' (Float.ofInt absoluteIntX) (Float.ofInt absoluteIntY)).scaleValues
        poly.cellSizeX poly.cellSizeY).add (DCPolyomino.getOffset graph poly)
    let originalCoordinates := graph.componentMinCorner poly.representee
    graph := graph.setComponentOffset poly.representee (absolutePosition.sub originalCoordinates)
  return graph

/-- `compact(graph)`: computes the grid cell size, creates and packs the polyominoes and applies
the result to the graph. Returns the packed polyominoes (the value of `DEBUG_DISCO_POLYS`). -/
def compactWithPolys (self : DisCoPolyominoCompactor) (graph : DCGraph) :
    IO (DCGraph × Array DCPolyomino) := do
  let gridCellRecommendation := self.computeCellSize graph
  let mut gridCellSizeX := gridCellRecommendation
  let mut gridCellSizeY := gridCellRecommendation
  let fill := (graph.properties.get PolyominoOptions.POLYOMINO_FILL).getD false
  let mut aspectRatio := (graph.properties.get DisCoOptions.ASPECT_RATIO).getD 1.0
  if aspectRatio == 0.0 then
    aspectRatio := 1.0
  if aspectRatio > 1.0 then
    gridCellSizeX := gridCellSizeX * aspectRatio
  else
    gridCellSizeY := gridCellSizeY / aspectRatio
  let polys ← createPolyominoes graph gridCellSizeX gridCellSizeY
  let (graph, polys, grid) ← packPolyominoes graph polys aspectRatio fill
  return (applyToDCGraph graph polys grid gridCellSizeX gridCellSizeY, polys)

/-- `ICompactor.compact(graph)`. -/
def compact (self : DisCoPolyominoCompactor) (graph : DCGraph) : IO DCGraph := do
  return (← self.compactWithPolys graph).1

/-- The compactor as an `ICompactor`. -/
def toICompactor (self : DisCoPolyominoCompactor) : ICompactor := ⟨self.compact⟩

end DisCoPolyominoCompactor

end Elk.Alg.Disco
