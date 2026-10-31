import Elk.Core.Util.Sort
import Elk.Core.Util.Java
import Elk.Core.Exceptions
import Elk.Alg.Common.Compaction.Options.PolyominoOptions
import Elk.Alg.Common.Polyomino.Structures.Polyominoes
import Elk.Alg.Common.Polyomino.SuccessorCombination
import Elk.Alg.Common.Polyomino.SuccessorJitter
import Elk.Alg.Common.Polyomino.SuccessorLineByLine
import Elk.Alg.Common.Polyomino.SuccessorManhattan
import Elk.Alg.Common.Polyomino.SuccessorMaxNormWindingInMathPosSense
import Elk.Alg.Common.Polyomino.SuccessorQuadrantsGeneric
/-!
# `org.eclipse.elk.alg.common.polyomino.PolyominoCompactor`

Greedy polyomino packing (Java `PolyominoCompactor.packPolyominoes`): the polyominoes are sorted
(Java `List.sort`, stable, with consistent comparators: the low-level criterion first, then the
high-level criterion's sorts), then each one is placed at the first candidate offset of the
traversal strategy where it does not intersect the already placed cells, starting at `(0, 0)`.

Java sorts with the low-level comparator `.reversed()` (largest polyominoes first); elk-rs sorts
ascending (`polys.sort_by(min_perimeter_cmp)`) — the main DisCo difference between elk-rs and ELK
Java, which the Lean port follows. The comparator values are Java `int` arithmetic (`w * w`
wraps).

`packPolyominoes` returns `Except String` because the grid operations can run out of bounds
(a Rust panic); `packPolyominoesIO` throws `java.lang.IndexOutOfBoundsException` instead.
-/
namespace Elk.Alg.Common.Polyomino

open Elk.Core Elk.Core.Util Elk.Alg.Common.Compaction.Options Structures

namespace PolyominoCompactor

variable {P : Type} [PolyominoLike P]

/-- `MinPerimeterComparator`: by `width + height` (Java `int`). -/
def minPerimeterCmp (a b : P) : Ordering :=
  let value (p : P) : Int :=
    Int.wrap32 ((PolyominoLike.width p : Int) + (PolyominoLike.height p : Int))
  compare (value a) (value b)

/-- `MinPerimeterComparatorWithShape`: by `w * w + h` (if `w < h`) or `w + h * h`, in Java `int`
arithmetic. -/
def minPerimeterShapeCmp (a b : P) : Ordering :=
  let value (p : P) : Int :=
    let w : Int := PolyominoLike.width p
    let h : Int := PolyominoLike.height p
    if w < h then Int.wrap32 (Int.wrap32 (w * w) + h) else Int.wrap32 (w + Int.wrap32 (h * h))
  compare (value a) (value b)

/-- `MinNumOfExtensionsComparator`. -/
def minNumExtensionsCmp (a b : P) : Ordering :=
  compare (PolyominoLike.polyominoExtensions a).size (PolyominoLike.polyominoExtensions b).size

/-- Distinct extension directions in first-occurrence order (Rust `num_extension_dirs`). -/
def extensionDirs (p : P) : Array Direction :=
  (PolyominoLike.polyominoExtensions p).foldl
    (fun dirs (d, _, _) => if dirs.contains d then dirs else dirs.push d) #[]

/-- `MinNumOfExtensionDirectionsComparator`. -/
def minNumExtensionDirectionsCmp (a b : P) : Ordering :=
  compare (extensionDirs a).size (extensionDirs b).size

/-- `SingleExtensionSideGreaterThanRest`-style comparator: polyominoes with exactly one
extension direction last. -/
def singleExtensionSideCmp (a b : P) : Ordering :=
  let v (p : P) : Nat := if (extensionDirs p).size == 1 then 1 else 0
  compare (v a) (v b)

/-- `is_corner_case`: exactly two extension directions, one of them horizontal. -/
def isCornerCase (p : P) : Bool :=
  let dirs := extensionDirs p
  dirs.size == 2 && (dirs.filter (·.isHorizontal)).size == 1

/-- `CornerCasesGreaterThanRest`-style comparator: corner cases last. -/
def cornerCasesCmp (a b : P) : Ordering :=
  let v (p : P) : Nat := if isCornerCase p then 1 else 0
  compare (v a) (v b)

/-- The successor function of a traversal strategy (Rust `match traversal`). -/
def successorFor (traversal : TraversalStrategy) : SuccessorFunction P :=
  match traversal with
  | .spiral => SuccessorMaxNormWindingInMathPosSense
  | .lineByLine => SuccessorLineByLine
  | .manhattan => SuccessorManhattan
  | .jitter => SuccessorJitter
  | .quadrantsManhattan => SuccessorQuadrantsGeneric SuccessorManhattan
  | .quadrantsLineByLine => SuccessorQuadrantsGeneric SuccessorLineByLine
  | .quadrantsJitter => SuccessorQuadrantsGeneric SuccessorJitter
  | .combineLineByLineManhattan =>
    SuccessorCombination (SuccessorQuadrantsGeneric SuccessorLineByLine)
      (SuccessorQuadrantsGeneric SuccessorManhattan)
  | .combineJitterManhattan =>
    SuccessorCombination (SuccessorQuadrantsGeneric SuccessorJitter)
      (SuccessorQuadrantsGeneric SuccessorManhattan)

/-- Sorts the polyominoes by the configured criteria: Java's stable `List.sort` calls, the
low-level comparator `.reversed()` (descending), then the high-level ones ascending. -/
def sortPolys [Inhabited P] (polys : Array P) (lowLevel : LowLevelSortingCriterion)
    (highLevel : HighLevelSortingCriterion) : Array P :=
  let polys := match lowLevel with
    | .bySize => stableSort polys (fun a b => minPerimeterCmp b a)
    | .bySizeAndShape => stableSort polys (fun a b => minPerimeterShapeCmp b a)
  match highLevel with
  | .cornerCasesThanSingleSideLast =>
    let polys := stableSort polys minNumExtensionsCmp
    let polys := stableSort polys singleExtensionSideCmp
    stableSort polys cornerCasesCmp
  | .numOfExternalSidesThanNumOfExtensionsLast =>
    let polys := stableSort polys minNumExtensionsCmp
    stableSort polys minNumExtensionDirectionsCmp

/-- `PolyominoCompactor.packPolyominoes(polyHolder)`: sorts the polyominoes (the holder keeps the
sorted order) and places them one after another; each placed polyomino gets its `x`/`y`. -/
def packPolyominoes [Inhabited P] (holder : Polyominoes P) : Except String (Polyominoes P) := do
  let lowLevel := (holder.getProperty PolyominoOptions.POLYOMINO_LOW_LEVEL_SORT).getD
    LowLevelSortingCriterion.rustDefault
  let highLevel := (holder.getProperty PolyominoOptions.POLYOMINO_HIGH_LEVEL_SORT).getD
    HighLevelSortingCriterion.rustDefault
  let traversal := (holder.getProperty PolyominoOptions.POLYOMINO_TRAVERSAL_STRATEGY).getD
    TraversalStrategy.rustDefault
  let { properties, polys, grid } := holder
  let mut polys := sortPolys polys lowLevel highLevel
  let successor : SuccessorFunction P := successorFor traversal
  let mut grid := grid
  for i in [0:polys.size] do
    let poly := polys[i]!
    let mut offX : Int := 0
    let mut offY : Int := 0
    let mut next : Int × Int := (offX, offY)
    repeat
      if !(← grid.intersectsWithCenterBasedPolyomino poly offX offY) then break
      next := successor next poly
      offX := next.1
      offY := next.2
    let (grid', poly') ← grid.addFilledCellsFromPolyomino poly offX offY
    grid := grid'
    polys := polys.set! i poly'
  return { properties, polys, grid }

/-- `packPolyominoes` in `IO`: grid index errors become `java.lang.IndexOutOfBoundsException`. -/
def packPolyominoesIO [Inhabited P] (holder : Polyominoes P) : IO (Polyominoes P) :=
  match packPolyominoes holder with
  | .ok h => pure h
  | .error e => throw (javaException indexOutOfBoundsExceptionClass e)

end PolyominoCompactor

end Elk.Alg.Common.Polyomino
