import Elk.Alg.Layered.P5Edges.Orthogonal.HyperEdgeSegmentDependency
import Elk.Core.Util.Sort
/-!
# `org.eclipse.elk.alg.layered.p5edges.orthogonal.HyperEdgeSegmentSplitter`

Port of elk-rs `p5edges/orthogonal/hyper_edge_segment_splitter.rs`: resolves critical dependency
cycles by splitting one segment of each offending dependency into two segments connected by a
horizontal piece placed in a free area between the connection coordinates.

Java/Rust call back into the routing generator (`createDependencyIfNecessary`, the static
`countCrossings`); since `OrthogonalRoutingGenerator` imports this module, the splitter is a
structure holding those two generator functions (Java keeps the generator as a field).
-/
namespace Elk.Alg.Layered.P5Edges.Orthogonal

open Elk.Graph Elk.Core.Util

/-- `HyperEdgeSegmentSplitter` with its `routingGenerator` callbacks. -/
structure HyperEdgeSegmentSplitter where
  /-- `routingGenerator.createDependencyIfNecessary(he1, he2)` (the splitter ignores the returned critical
  dependency count). -/
  createDependency : SegmentGraph → Nat → Nat → SegmentGraph
  /-- `OrthogonalRoutingGenerator.countCrossings(posis, start, end)`. -/
  countCrossings : Array Float → Float → Float → Int

namespace HyperEdgeSegmentSplitter

/-- `FreeArea`: a coordinate interval free of connection coordinates. -/
structure FreeArea where
  startPosition : Float
  endPosition : Float
  size : Float
  deriving Inhabited

/-- `FreeArea::new(start, end)` (Rust asserts `end >= start`). -/
def FreeArea.new (startPosition endPosition : Float) : FreeArea :=
  { startPosition := startPosition, endPosition := endPosition, size := endPosition - startPosition }

/-- `AreaRating`: dependencies and crossings a split in an area would cause. -/
structure AreaRating where
  dependencies : Int := 0
  crossings : Int := 0
  deriving Inhabited

/-- `center(p1, p2)`. -/
@[inline] def centerValues (p1 p2 : Float) : Float := (p1 + p2) / 2.0

/-- `center(area)`. -/
@[inline] def centerArea (area : FreeArea) : Float := centerValues area.startPosition area.endPosition

/-- `findFreeAreas(segments, criticalConflictThreshold)`: gaps of at least twice the threshold between
consecutive (sorted) connection coordinates of all segments, shrunk by the threshold on both sides. -/
def findFreeAreas (g : SegmentGraph) (criticalConflictThreshold : Float) : Array FreeArea := Id.run do
  let mut coordinates : Array Float := #[]
  for seg in g.segments do
    coordinates := coordinates ++ seg.incomingConnectionCoordinates
    coordinates := coordinates ++ seg.outgoingConnectionCoordinates
  -- Rust `sort_by(partial_cmp().unwrap())` (a NaN would panic there)
  let sorted := stableSort coordinates Float.comparePartial
  let mut freeAreas : Array FreeArea := #[]
  for i in [1:sorted.size] do
    if sorted[i]! - sorted[i - 1]! >= 2.0 * criticalConflictThreshold then
      freeAreas := freeAreas.push
        (FreeArea.new (sorted[i - 1]! + criticalConflictThreshold) (sorted[i]! - criticalConflictThreshold))
  return freeAreas

/-- `decideWhichSegmentsToSplit(dependencies)`: per dependency (skipping those touching an already chosen
segment) its source, or its target when only the source represents a hyperedge; sets `splitBy` of the
chosen segment to the other one. -/
def decideWhichSegmentsToSplit (deps : Array Nat) (g : SegmentGraph) : Array Nat × SegmentGraph := Id.run do
  let mut g := g
  let mut segmentsToSplit : Array Nat := #[]
  for d in deps do
    let dep := g.dependency d
    let (some source, some target) := (dep.source, dep.target) | continue
    if segmentsToSplit.contains source || segmentsToSplit.contains target then continue
    let mut segmentToSplit := source
    let mut segmentCausingSplit := target
    if (g.segment source).representsHyperedge && !(g.segment target).representsHyperedge then
      segmentToSplit := target
      segmentCausingSplit := source
    let causing := segmentCausingSplit
    g := g.modifySegment segmentToSplit fun s => { s with splitBy := some causing }
    segmentsToSplit := segmentsToSplit.push segmentToSplit
  return (segmentsToSplit, g)

/-- `countCrossingsForSingleOrdering(left, right)`: crossings when `left` is routed left of `right`. -/
def countCrossingsForSingleOrdering (sp : HyperEdgeSegmentSplitter) (left right : HyperEdgeSegment) : Int :=
  sp.countCrossings left.outgoingConnectionCoordinates right.startPosition right.endPosition +
    sp.countCrossings right.incomingConnectionCoordinates left.startPosition left.endPosition

/-- `updateConsideringBothOrderings(rating, s1, s2)`. -/
def updateConsideringBothOrderings (sp : HyperEdgeSegmentSplitter) (rating : AreaRating) (s1 s2 : HyperEdgeSegment) :
    AreaRating :=
  let crossingsS1Left := sp.countCrossingsForSingleOrdering s1 s2
  let crossingsS2Left := sp.countCrossingsForSingleOrdering s2 s1
  if crossingsS1Left == crossingsS2Left then
    if crossingsS1Left > 0 then
      { rating with dependencies := rating.dependencies + 2, crossings := rating.crossings + crossingsS1Left }
    else rating
  else
    { rating with dependencies := rating.dependencies + 1,
                  crossings := rating.crossings + min crossingsS1Left crossingsS2Left }

/-- `rateArea(segment, splitSegment, splitPartner, area)`: places the simulated split at the area's
centre (outgoing coordinate of the split segment, incoming of the partner; the extents are not
recomputed, as in Rust) and rates the result against the segment's dependency neighbours and the
segment causing the split. -/
def rateArea (sp : HyperEdgeSegmentSplitter) (g : SegmentGraph) (segment : Nat) (splitSegment splitPartner : HyperEdgeSegment)
    (area : FreeArea) : AreaRating := Id.run do
  let areaCenter := centerArea area
  let split := { splitSegment with outgoingConnectionCoordinates := #[areaCenter] }
  let partner := { splitPartner with incomingConnectionCoordinates := #[areaCenter] }
  let mut rating : AreaRating := {}
  let seg := g.segment segment
  for d in seg.incomingSegmentDependencies do
    let sourceCode := g.depSourceCode d
    if sourceCode != 0 then
      let otherSeg := g.segment (sourceCode - 1)
      rating := sp.updateConsideringBothOrderings rating split otherSeg
      rating := sp.updateConsideringBothOrderings rating partner otherSeg
  for d in seg.outgoingSegmentDependencies do
    let targetCode := g.depTargetCode d
    if targetCode != 0 then
      let otherSeg := g.segment (targetCode - 1)
      rating := sp.updateConsideringBothOrderings rating split otherSeg
      rating := sp.updateConsideringBothOrderings rating partner otherSeg
  rating := { rating with dependencies := rating.dependencies + 2 }
  if let some splitBy := seg.splitBy then
    let splitBySeg := g.segment splitBy
    rating := { rating with crossings := rating.crossings + sp.countCrossingsForSingleOrdering split splitBySeg }
    rating := { rating with crossings := rating.crossings + sp.countCrossingsForSingleOrdering splitBySeg partner }
  return rating

/-- `isBetter(currArea, currRating, bestArea, bestRating)`: fewer crossings, then fewer dependencies,
then a larger area. -/
def isBetter (currArea : FreeArea) (currRating : AreaRating) (bestArea : FreeArea) (bestRating : AreaRating) : Bool :=
  if currRating.crossings < bestRating.crossings then true
  else currRating.crossings == bestRating.crossings &&
    (currRating.dependencies < bestRating.dependencies ||
      (currRating.dependencies == bestRating.dependencies && currArea.size > bestArea.size))

/-- `chooseBestAreaIndex(segment, freeAreas, fromIndex, toIndex)`. -/
def chooseBestAreaIndex (sp : HyperEdgeSegmentSplitter) (g : SegmentGraph) (segment : Nat) (freeAreas : Array FreeArea)
    (fromIndex toIndex : Nat) : Nat := Id.run do
  let mut bestAreaIndex := fromIndex
  if fromIndex < toIndex then
    let (splitSegment, splitPartner) := (g.segment segment).simulateSplit
    let mut bestArea := freeAreas[bestAreaIndex]!
    let mut bestRating := sp.rateArea g segment splitSegment splitPartner bestArea
    for i in [fromIndex + 1:toIndex + 1] do
      let currArea := freeAreas[i]!
      let currRating := sp.rateArea g segment splitSegment splitPartner currArea
      if isBetter currArea currRating bestArea bestRating then
        bestArea := currArea
        bestRating := currRating
        bestAreaIndex := i
  return bestAreaIndex

/-- `useArea(freeAreas, usedAreaIndex, criticalConflictThreshold)`: removes the used area and re-inserts
what remains on both sides of its centre (keeping the threshold distance). -/
def useArea (freeAreas : Array FreeArea) (usedAreaIndex : Nat) (criticalConflictThreshold : Float) : Array FreeArea := Id.run do
  let oldArea := freeAreas[usedAreaIndex]!
  let mut freeAreas := freeAreas.eraseIdx! usedAreaIndex
  if oldArea.size / 2.0 >= criticalConflictThreshold then
    let mut insertIndex := usedAreaIndex
    let oldAreaCenter := centerArea oldArea
    let newEnd1 := oldAreaCenter - criticalConflictThreshold
    if oldArea.startPosition <= newEnd1 then
      freeAreas := freeAreas.insertIdx! insertIndex (FreeArea.new oldArea.startPosition newEnd1)
      insertIndex := insertIndex + 1
    let newStart2 := oldAreaCenter + criticalConflictThreshold
    if newStart2 <= oldArea.endPosition then
      freeAreas := freeAreas.insertIdx! insertIndex (FreeArea.new newStart2 oldArea.endPosition)
  return freeAreas

/-- `computePositionToSplitAndUpdateFreeAreas(segment, freeAreas, criticalConflictThreshold)`: the
centre of the best free area overlapping the segment (which is then used up), else the segment's
centre. -/
def computePositionToSplitAndUpdateFreeAreas (sp : HyperEdgeSegmentSplitter) (g : SegmentGraph) (segment : Nat)
    (freeAreas : Array FreeArea) (criticalConflictThreshold : Float) : Float × Array FreeArea := Id.run do
  let mut firstPossible : Option Nat := none
  let mut lastPossible : Option Nat := none
  let seg := g.segment segment
  let segmentStart := seg.startPosition
  let segmentEnd := seg.endPosition
  for idx in [0:freeAreas.size] do
    let area := freeAreas[idx]!
    if area.startPosition > segmentEnd then break
    else if area.endPosition >= segmentStart then
      if firstPossible.isNone then firstPossible := some idx
      lastPossible := some idx
  let mut splitPosition := centerValues segmentStart segmentEnd
  let mut freeAreas := freeAreas
  if let (some firstIndex, some lastIndex) := (firstPossible, lastPossible) then
    let bestIndex := sp.chooseBestAreaIndex g segment freeAreas firstIndex lastIndex
    splitPosition := centerArea freeAreas[bestIndex]!
    freeAreas := useArea freeAreas bestIndex criticalConflictThreshold
  return (splitPosition, freeAreas)

/-- `updateDependencies(segment, segments)`: critical dependencies `segment → splitBy → splitPartner`,
then regular dependencies of every other segment with the two halves. -/
def updateDependencies (sp : HyperEdgeSegmentSplitter) (g : SegmentGraph) (segment : Nat) : SegmentGraph := Id.run do
  let seg := g.segment segment
  let (some splitCausing, some splitPartner) := (seg.splitBy, seg.splitPartner) | return g
  let mut g := (g.createAndAddCritical segment splitCausing).1
  g := (g.createAndAddCritical splitCausing splitPartner).1
  for other in [0:g.segments.size] do
    if other != splitCausing && other != segment && other != splitPartner then
      g := sp.createDependency g other segment
      g := sp.createDependency g other splitPartner
  return g

/-- `split(segment, segments, freeAreas, criticalConflictThreshold)`. -/
def split (sp : HyperEdgeSegmentSplitter) (g : SegmentGraph) (segment : Nat) (freeAreas : Array FreeArea)
    (criticalConflictThreshold : Float) : SegmentGraph × Array FreeArea :=
  let (splitPosition, freeAreas) := sp.computePositionToSplitAndUpdateFreeAreas g segment freeAreas criticalConflictThreshold
  let (g, _) := g.splitAt segment splitPosition
  (sp.updateDependencies g segment, freeAreas)

/-- `splitSegments(dependenciesToResolve, segments, criticalConflictThreshold)`: splits the chosen
segments, shortest first (stable sort by length, NaN equal). -/
def splitSegments (sp : HyperEdgeSegmentSplitter) (dependenciesToResolve : Array Nat) (g : SegmentGraph)
    (criticalConflictThreshold : Float) : SegmentGraph := Id.run do
  if dependenciesToResolve.isEmpty then return g
  let mut freeAreas := findFreeAreas g criticalConflictThreshold
  let (segmentsToSplit, g') := decideWhichSegmentsToSplit dependenciesToResolve g
  let mut g := g'
  let lengths := g.segments.map (·.length)
  let segmentsToSplit := stableSort segmentsToSplit fun a b => Float.comparePartial lengths[a]! lengths[b]!
  for segment in segmentsToSplit do
    let (g', areas) := sp.split g segment freeAreas criticalConflictThreshold
    g := g'
    freeAreas := areas
  return g

end HyperEdgeSegmentSplitter

end Elk.Alg.Layered.P5Edges.Orthogonal
