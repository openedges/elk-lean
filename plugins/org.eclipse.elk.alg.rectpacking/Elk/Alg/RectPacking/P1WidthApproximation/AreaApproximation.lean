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
/-! Float literals as global constants (FL): inside branches, loops and specialised code the compiler
shares a literal's `Nat`/`Bool` arguments with unrelated variables (CSE) and then parses it on every
evaluation (`FastFloat.ofScientificImpl`); a top-level constant is a load (PLAN §7.1 items 17, 22). -/
private def fl0p0 : Float := 0.0

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
node_node_spacing)` with the shifted coordinate already computed: `shifted` is
`calculate_y_for_lpr` for `LPR` and `calculate_x_for_lpb` for `LPB` (used only with `lpShift`). -/
def calcValuesForOptWith (self : AreaApproximation) (g : ElkGraph) (option : DrawingDataDescriptor)
    (toPlace lastPlaced : NodeId) (drawing : DrawingData) (shifted : Float)
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
      y := shifted
    else
      y := lp.y
    width := Calculations.widthLprOrLpb drawingWidth x widthToPlace
    height := Calculations.heightLprOrLpb drawingHeight y heightToPlace
  | .candidatePositionLastPlacedBelow =>
    y := lp.y + lp.height + nodeNodeSpacing
    if self.lpShift then
      x := shifted
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

/-- `calc_values_for_opt(option, to_place, last_placed, drawing, placed_rects,
node_node_spacing)` with the placed rectangles given by their geometry
(`Calculations.PlacedRects`). -/
def calcValuesForOptSoA (self : AreaApproximation) (g : ElkGraph) (option : DrawingDataDescriptor)
    (toPlace lastPlaced : NodeId) (drawing : DrawingData) (placedRects : Calculations.PlacedRects)
    (nodeNodeSpacing : Float) : DrawingData :=
  let lp := g.node lastPlaced
  let shifted :=
    if !self.lpShift then fl0p0
    else match option with
      | .candidatePositionLastPlacedRight =>
        Calculations.calculateYForLprSoA (lp.x + lp.width + nodeNodeSpacing) placedRects lp.y nodeNodeSpacing
      | .candidatePositionLastPlacedBelow =>
        Calculations.calculateXForLpbSoA (lp.y + lp.height + nodeNodeSpacing) placedRects lp.x nodeNodeSpacing
      | _ => fl0p0
  self.calcValuesForOptWith g option toPlace lastPlaced drawing shifted nodeNodeSpacing

/-- `calc_values_for_opt(option, to_place, last_placed, drawing, placed_rects,
node_node_spacing)`: the drawing obtained by placing `toPlace` at the candidate position. -/
def calcValuesForOpt (self : AreaApproximation) (g : ElkGraph) (option : DrawingDataDescriptor)
    (toPlace lastPlaced : NodeId) (drawing : DrawingData) (placedRects : Array NodeId)
    (nodeNodeSpacing : Float) : DrawingData :=
  self.calcValuesForOptSoA g option toPlace lastPlaced drawing
    (Calculations.PlacedRects.ofNodes g placedRects) nodeNodeSpacing

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
  ElkM.modifyNode firstRect fun n => { n with x := fl0p0, y := fl0p0 }
  let first ← ElkM.getNode firstRect
  -- the geometry of the placed rectangles (they do not move again in this loop)
  let mut placedRects : Calculations.PlacedRects := ({} : Calculations.PlacedRects).push
    first.x first.y first.width first.height
  let mut lastPlaced := firstRect
  let mut currentValues := DrawingData.new self.aspectRatio first.width first.height .wholeDrawing
  for toPlace in rectangles.extract 1 rectangles.size do
    let g ← get
    -- the LPR y and the LPB x scans in one pass (`calcValuesForOptSoA` per option otherwise)
    let lp := g.node lastPlaced
    let (lprY, lpbX) :=
      if self.lpShift then
        Calculations.calculateLprAndLpbSoA (lp.x + lp.width + nodeNodeSpacing)
          (lp.y + lp.height + nodeNodeSpacing) placedRects lp.x lp.y nodeNodeSpacing
      else (fl0p0, fl0p0)
    let opt1 := self.calcValuesForOptWith g .candidatePositionLastPlacedRight toPlace lastPlaced
      currentValues lprY nodeNodeSpacing
    let opt2 := self.calcValuesForOptWith g .candidatePositionLastPlacedBelow toPlace lastPlaced
      currentValues lpbX nodeNodeSpacing
    let opt3 := self.calcValuesForOptWith g .candidatePositionWholeDrawingRight toPlace lastPlaced
      currentValues fl0p0 nodeNodeSpacing
    let opt4 := self.calcValuesForOptWith g .candidatePositionWholeDrawingBelow toPlace lastPlaced
      currentValues fl0p0 nodeNodeSpacing
    let bestOpt ← match self.findBestCandidate g opt1 opt2 opt3 opt4 toPlace lastPlaced padding with
      | .ok d => pure d
      | .error msg => throw (IO.userError msg)
    ElkM.modifyNode toPlace fun n => { n with x := bestOpt.nextXCoordinate, y := bestOpt.nextYCoordinate }
    let placed ← ElkM.getNode toPlace
    placedRects := placedRects.push placed.x placed.y placed.width placed.height
    currentValues := bestOpt.setPlacementOption .wholeDrawing
    lastPlaced := toPlace
  return currentValues

end AreaApproximation

end Elk.Alg.RectPacking.P1WidthApproximation
