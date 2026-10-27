import Elk.Core.Exceptions
import Elk.Alg.RectPacking.Options.OptimizationGoal
import Elk.Alg.RectPacking.P1WidthApproximation.Calculations
import Elk.Alg.RectPacking.P1WidthApproximation.AreaFilter
import Elk.Alg.RectPacking.P1WidthApproximation.AspectRatioFilter
import Elk.Alg.RectPacking.P1WidthApproximation.ScaleMeasureFilter
/-!
# `org.eclipse.elk.alg.rectpacking.p1widthapproximation.AreaApproximation`

Port of `p1widthapproximation/area_approximation.rs` (elk-rs): the greedy first iteration that
places the rectangles one by one at the best of four candidate positions (right of / below the
last placed rectangle, right of / below the whole drawing) and returns the resulting drawing.
-/
namespace Elk.Alg.RectPacking.P1WidthApproximation

open Elk.Graph Elk.Core.Util Elk.Core.Math Elk.Alg.RectPacking.Util Elk.Alg.RectPacking.Options

/-- `AreaApproximation`. -/
structure AreaApproximation where
  aspectRatio : Float
  goal : OptimizationGoal
  lpShift : Bool

namespace AreaApproximation

/-- `AreaApproximation::new(aspect_ratio, goal, lp_shift)`. -/
def new (aspectRatio : Float) (goal : OptimizationGoal) (lpShift : Bool) : AreaApproximation :=
  { aspectRatio, goal, lpShift }

/-- The filters of an optimization goal, in application order. -/
def filtersFor : OptimizationGoal → Array BestCandidateFilter
  | .maxScaleDriven => #[ScaleMeasureFilter.filter, AreaFilter.filter, AspectRatioFilter.filter]
  | .aspectRatioDriven => #[AspectRatioFilter.filter, AreaFilter.filter, ScaleMeasureFilter.filter]
  | .areaDriven => #[AreaFilter.filter, ScaleMeasureFilter.filter, AspectRatioFilter.filter]

/-- `calc_values_for_opt(option, to_place, last_placed, drawing, placed_rects,
node_node_spacing)`: the drawing obtained by placing `toPlace` at the candidate position. -/
def calcValuesForOpt (self : AreaApproximation) (g : ElkGraph) (option : DrawingDataDescriptor)
    (toPlace lastPlaced : NodeId) (drawing : DrawingData) (placedRects : Array NodeId)
    (nodeNodeSpacing : Float) : DrawingData := Id.run do
  let mut x : Float := 0.0
  let mut y : Float := 0.0
  let drawingWidth := drawing.drawingWidth
  let drawingHeight := drawing.drawingHeight
  let tp := g.node toPlace
  let widthToPlace := tp.width
  let heightToPlace := tp.height
  let lp := g.node lastPlaced
  let mut width : Float := 0.0
  let mut height : Float := 0.0
  match option with
  | .candidatePositionLastPlacedRight =>
    x := lp.x + lp.width + nodeNodeSpacing
    if self.lpShift then
      y := Calculations.calculateYForLpr g x placedRects lastPlaced nodeNodeSpacing
    else
      y := lp.y
    width := Calculations.widthLprOrLpb drawingWidth x widthToPlace
    height := Calculations.heightLprOrLpb drawingHeight y heightToPlace
  | .candidatePositionLastPlacedBelow =>
    y := lp.y + lp.height + nodeNodeSpacing
    if self.lpShift then
      x := Calculations.calculateXForLpb g y placedRects lastPlaced nodeNodeSpacing
    else
      x := lp.x
    width := Calculations.widthLprOrLpb drawingWidth x widthToPlace
    height := Calculations.heightLprOrLpb drawingHeight y heightToPlace
  | .candidatePositionWholeDrawingRight =>
    x := drawingWidth + nodeNodeSpacing
    y := 0.0
    width := drawingWidth + nodeNodeSpacing + widthToPlace
    height := fmax drawingHeight heightToPlace
  | .candidatePositionWholeDrawingBelow =>
    x := 0.0
    y := drawingHeight + nodeNodeSpacing
    width := fmax drawingWidth widthToPlace
    height := drawingHeight + nodeNodeSpacing + heightToPlace
  | .wholeDrawing =>
    width := drawingWidth
    height := drawingHeight
  return DrawingData.withCoordinates self.aspectRatio width height option x y

/-- `check_special_cases(drawing1, drawing2, last_placed, to_place)`: tie break of two remaining
candidates: two "below" candidates prefer WDB, two "right" candidates prefer WDR, LPR vs LPB
compare the bounding box areas (`LPR` if not larger); any other pair takes the first. -/
def checkSpecialCases (g : ElkGraph) (drawing1 drawing2 : DrawingData) (lastPlaced toPlace : NodeId) :
    DrawingData :=
  let firstOpt := drawing1.placementOption
  let secondOpt := drawing2.placementOption
  let isLpbOrWdb : DrawingDataDescriptor → Bool
    | .candidatePositionLastPlacedBelow | .candidatePositionWholeDrawingBelow => true
    | _ => false
  let isLprOrWdr : DrawingDataDescriptor → Bool
    | .candidatePositionLastPlacedRight | .candidatePositionWholeDrawingRight => true
    | _ => false
  let isLprOrLpb : DrawingDataDescriptor → Bool
    | .candidatePositionLastPlacedRight | .candidatePositionLastPlacedBelow => true
    | _ => false
  if isLpbOrWdb firstOpt && isLpbOrWdb secondOpt then
    if drawing1.placementOption == .candidatePositionWholeDrawingBelow then drawing1 else drawing2
  else if isLprOrWdr firstOpt && isLprOrWdr secondOpt then
    if drawing1.placementOption == .candidatePositionWholeDrawingRight then drawing1 else drawing2
  else if isLprOrLpb firstOpt && isLprOrLpb secondOpt then
    let (lprOpt, lpbOpt) :=
      if firstOpt == .candidatePositionLastPlacedRight then (drawing1, drawing2) else (drawing2, drawing1)
    let areaLpr := Calculations.calculateAreaLpr g lastPlaced toPlace lprOpt
    let areaLpb := Calculations.calculateAreaLpb g lastPlaced toPlace lpbOpt
    if areaLpr <= areaLpb then
      if drawing1.placementOption == .candidatePositionLastPlacedRight then drawing1 else drawing2
    else
      if drawing1.placementOption == .candidatePositionLastPlacedBelow then drawing1 else drawing2
  else drawing1

/-- `find_best_candidate(opt1, opt2, opt3, opt4, to_place, last_placed, padding)`: applies the
goal's filters while more than one candidate remains; one candidate wins, two go to
`checkSpecialCases`, otherwise the first remaining one. Rust panics (`expect`) when the filters
removed every candidate (only possible with NaN metrics); that is an
`IllegalStateException` here. -/
def findBestCandidate (self : AreaApproximation) (g : ElkGraph) (opt1 opt2 opt3 opt4 : DrawingData)
    (toPlace lastPlaced : NodeId) (padding : ElkPadding) : Except String DrawingData := Id.run do
  let mut candidates := #[opt1, opt2, opt3, opt4]
  for filter in filtersFor self.goal do
    if candidates.size > 1 then
      candidates := filter.filterList candidates self.aspectRatio padding
  if h : candidates.size = 1 then return .ok candidates[0]
  if h : candidates.size = 2 then
    return .ok (checkSpecialCases g candidates[0] candidates[1] lastPlaced toPlace)
  match candidates[0]? with
  | some c => return .ok c
  | none => return .error "java.lang.IllegalStateException: candidate exists"

/-- `approx_bounding_box(rectangles, node_node_spacing, padding)`: places the first rectangle at
`(0, 0)` and every further one at its best candidate position (moving the rectangles), and
returns the final drawing. Rust panics on an empty list ("at least one rectangle needed"); that
is an `IllegalStateException` here. -/
def approxBoundingBox (self : AreaApproximation) (rectangles : Array NodeId) (nodeNodeSpacing : Float)
    (padding : ElkPadding) : ElkM DrawingData := do
  let some firstRect := rectangles[0]?
    | throw (IO.userError "java.lang.IllegalStateException: at least one rectangle needed")
  ElkM.modifyNode firstRect fun n => { n with x := 0.0, y := 0.0 }
  let mut placedRects : Array NodeId := #[firstRect]
  let mut lastPlaced := firstRect
  let first ← ElkM.getNode firstRect
  let mut currentValues := DrawingData.new self.aspectRatio first.width first.height .wholeDrawing
  for toPlace in rectangles.extract 1 rectangles.size do
    let g ← get
    let opt1 := self.calcValuesForOpt g .candidatePositionLastPlacedRight toPlace lastPlaced
      currentValues placedRects nodeNodeSpacing
    let opt2 := self.calcValuesForOpt g .candidatePositionLastPlacedBelow toPlace lastPlaced
      currentValues placedRects nodeNodeSpacing
    let opt3 := self.calcValuesForOpt g .candidatePositionWholeDrawingRight toPlace lastPlaced
      currentValues placedRects nodeNodeSpacing
    let opt4 := self.calcValuesForOpt g .candidatePositionWholeDrawingBelow toPlace lastPlaced
      currentValues placedRects nodeNodeSpacing
    let bestOpt ← match self.findBestCandidate g opt1 opt2 opt3 opt4 toPlace lastPlaced padding with
      | .ok d => pure d
      | .error msg => throw (IO.userError msg)
    ElkM.modifyNode toPlace fun n => { n with x := bestOpt.nextXCoordinate, y := bestOpt.nextYCoordinate }
    currentValues := bestOpt.setPlacementOption .wholeDrawing
    lastPlaced := toPlace
    placedRects := placedRects.push toPlace
  return currentValues

end AreaApproximation

end Elk.Alg.RectPacking.P1WidthApproximation
