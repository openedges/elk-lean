import Elk.Alg.Layered.Intermediate.Loops.Routing.OrthogonalSelfLoopRouter
/-!
# `org.eclipse.elk.alg.layered.intermediate.loops.routing.SplineSelfLoopRouter`

Port of the `EdgeRouting::Splines` arm of `modify_bend_points` in elk-rs
`intermediate/self_loop_router.rs`: the control polygon is the source anchor, then per pair of
consecutive orthogonal bend points the first point and the midpoint pushed `SPACING_EDGE_LABEL`
away from the node (direction of the current side, turning with the routing direction), the last
bend point and the target anchor; the result are the Bézier control points of the clamped cubic
NUB spline through that polygon (`NubSpline::new(true, 3, points).get_bezier_cp_default()`).

TODO(I2b): the NUB spline (`p5edges/splines/nub_spline.rs`) and `SplinesMath.port_side_to_direction`
are not ported yet (P5 splines task); `NubSplineSubset` below is a private 1:1 port of the parts
used here (`new_from_vec` clamped, `create_uniform_knot_vector`, `PolarCP::from_two`,
`get_multiplicity`, `insert_knot_at_current_position`, `to_bezier`, `get_bezier_cp(false, false)`).
Replace it by `Elk.Alg.Layered.P5Edges.Splines.NubSpline` once that module exists.
-/
namespace Elk.Alg.Layered.Intermediate.Loops.Routing

open Elk.Core.Math Elk.Core.Options Elk.Core.Util

namespace SplineSelfLoopRouter

/-- `SplinesMath::HALF_PI`. -/
def HALF_PI : Float := Float.pi / 2.0
/-- `SplinesMath::THREE_HALF_PI` (`HALF_PI + HALF_PI + HALF_PI`). -/
def THREE_HALF_PI : Float := HALF_PI + HALF_PI + HALF_PI

/-- `SplinesMath::port_side_to_direction(side)`: the outward direction angle of a side. -/
def portSideToDirection : PortSide → Float
  | .north => THREE_HALF_PI
  | .east => 0.0
  | .south => HALF_PI
  | .west => Float.pi
  | .undefined => 0.0

namespace NubSplineSubset

/-- `NubSpline::EPSILON`. -/
private def EPSILON : Float := 0.000001

/-- `PolarCP`: a control point and its polar coordinate (knots). -/
private structure PolarCP where
  cp : KVector
  polarCoordinate : Array Float
  deriving Inhabited

/-- The mutable parts of a clamped `NubSpline` of dimension `dim`. -/
private structure Spline where
  knotVector : Array Float
  controlPoints : Array PolarCP
  dim : Nat
  maxKnot : Float
  deriving Inhabited

/-- `PolarCP::from_two(first, second, newKnot)`: the point on the segment for `newKnot` (blossom
step) with the polar coordinate of `first` minus its first knot, `newKnot` inserted in order. -/
private def fromTwo (first second : PolarCP) (newKnot : Float) : PolarCP := Id.run do
  let firstFactor := (first.polarCoordinate[0]?).getD 0.0
  let secondFactor := (second.polarCoordinate.back?).getD 0.0
  let aScaled := first.cp.scale (secondFactor - newKnot)
  let bScaled := second.cp.scale (newKnot - firstFactor)
  let total := (aScaled + bScaled).scale (1.0 / (secondFactor - firstFactor))
  let mut polar : Array Float := #[]
  let mut needsToBeAdded := true
  for nextKnot in first.polarCoordinate.extract 1 first.polarCoordinate.size do
    if needsToBeAdded && nextKnot - newKnot > EPSILON then
      polar := polar.push newKnot
      needsToBeAdded := false
    polar := polar.push nextKnot
  if needsToBeAdded then polar := polar.push newKnot
  return { cp := total, polarCoordinate := polar }

/-- `get_multiplicity(knot)`: the number of knots equal to `knot` (up to `EPSILON`), counted
until the first larger knot. -/
private def multiplicity (knots : Array Float) (knotToCheck : Float) : Nat := Id.run do
  let mut count := 0
  for currentKnot in knots do
    let diff := currentKnot - knotToCheck
    if diff > EPSILON then return count
    else if diff > -EPSILON then count := count + 1
  return count

/-- `new_from_vec(true, dim, points)`: pads the control polygon with copies of the first point up
to `dim + 1` points, builds the clamped uniform knot vector and the polar coordinates. -/
private def create (dim : Nat) (points : Array KVector) : Spline := Id.run do
  let mut kVectors := points
  let mut i := kVectors.size - 1
  for _ in [0:dim + 1] do
    if i ≥ dim then break
    kVectors := kVectors.insertIdx! 0 kVectors[0]!
    i := i + 1
  -- create_uniform_knot_vector(clamped = true, size)
  let size := kVectors.size + dim - 1
  let mut knots : Array Float := #[]
  for _ in [0:dim] do knots := knots.push 0.0
  let mySize := size + 1 - 2 * dim
  let fraction := mySize.toFloat
  for k in [1:mySize] do knots := knots.push (k.toFloat / fraction)
  for _ in [0:dim] do knots := knots.push 1.0
  -- polar coordinates
  let mut polar : Array Float := #[]
  let mut knotIdx := 0
  for _ in [0:dim - 1] do
    if knotIdx < knots.size then
      polar := polar.push knots[knotIdx]!
      knotIdx := knotIdx + 1
  let mut cps : Array PolarCP := #[]
  for v in kVectors do
    if knotIdx < knots.size then
      polar := polar.push knots[knotIdx]!
      knotIdx := knotIdx + 1
    cps := cps.push { cp := v, polarCoordinate := polar }
    if !polar.isEmpty then polar := polar.eraseIdx! 0
  return { knotVector := knots, controlPoints := cps, dim := dim, maxKnot := 1.0 }

/-- `insert_knot_at_current_position(insertions, knot, cpIndex, knotIndex)`: inserts the knot
`insertions` times (de Boor), returning the updated control point and knot indices. -/
private def insertKnotAtCurrentPosition (s : Spline) (insertions : Nat) (knotToInsert : Float)
    (cpIndex knotIndex : Nat) : Spline × Nat × Nat := Id.run do
  let mult := multiplicity s.knotVector knotToInsert
  let dim := s.dim
  let mut knots := s.knotVector
  let mut cps := s.controlPoints
  let mut cpIndex := cpIndex
  let mut knotIndex := knotIndex
  for i in [0:insertions] do
    knots := knots.insertIdx! knotIndex knotToInsert
    knotIndex := knotIndex + 1
    let mut newCps : Array PolarCP := #[]
    let mut secondCp := cps[cpIndex]!
    cpIndex := cpIndex + 1
    for _ in [mult + i:dim] do
      let firstCp := secondCp
      secondCp := cps[cpIndex]!
      cpIndex := cpIndex + 1
      newCps := newCps.push (fromTwo firstCp secondCp knotToInsert)
    for j in [mult + i:dim] do
      if cpIndex == 0 then break
      cpIndex := cpIndex - 1
      if j > mult + i then cps := cps.eraseIdx! cpIndex
    for cp in newCps do
      cps := cps.insertIdx! cpIndex cp
      cpIndex := cpIndex + 1
    if i + 1 < insertions then
      for _ in [mult + i:dim] do
        if cpIndex == 0 then break
        cpIndex := cpIndex - 1
  return ({ s with knotVector := knots, controlPoints := cps }, cpIndex, knotIndex)

/-- `to_bezier()` of a clamped spline: raises the multiplicity of every inner knot to `dim`.
Every round of the outer loop moves `knotIndex` past one distinct inner knot, so the number of
knots bounds the rounds (Rust: `while max_knot - current_knot > EPSILON`). -/
private def toBezier (s : Spline) : Spline := Id.run do
  let mut s := s
  let mut knotIndex := s.dim
  let mut cpIndex := 0
  let mut currentKnot := s.knotVector[knotIndex]!
  for _ in [0:s.knotVector.size + 1] do
    if !(s.maxKnot - currentKnot > EPSILON) then break
    let knotToCount := currentKnot
    let mut occurrence := 0
    for _ in [0:s.knotVector.size + 1] do
      if !((currentKnot - knotToCount).abs < EPSILON) then break
      occurrence := occurrence + 1
      knotIndex := knotIndex + 1
      cpIndex := cpIndex + 1
      currentKnot := s.knotVector[knotIndex]!
    if occurrence < s.dim then
      knotIndex := knotIndex - 1
      let (s', newCpIndex, newKnotIndex) := insertKnotAtCurrentPosition s (s.dim - occurrence) knotToCount cpIndex knotIndex
      s := s'
      cpIndex := newCpIndex
      knotIndex := newKnotIndex + 1
    cpIndex := cpIndex - 1
  return s

/-- `NubSpline::new(true, dim, points).get_bezier_cp_default()`: the Bézier control points without
the first and the last one. -/
def bezierControlPoints (dim : Nat) (points : Array KVector) : Array KVector :=
  if points.isEmpty || dim == 0 then #[]
  else
    let s := toBezier (create dim points)
    ((s.controlPoints.extract 1 s.controlPoints.size).map (·.cp)).pop

end NubSplineSubset

/-- `modify_bend_points` for `EdgeRouting::Splines`. -/
def modifyBendPoints : BendPointModifier := fun m => Id.run do
  let mut splinePoints : Array KVector := #[m.sourceAnchor]
  let bendPoints := m.bendPoints
  if bendPoints.size ≥ 2 then
    let mut currSide := m.sourceSide
    for i in [0:bendPoints.size - 1] do
      let firstBp := bendPoints[i]!
      let secondBp := bendPoints[i + 1]!
      splinePoints := splinePoints.push firstBp
      -- midpoint offset away from the node
      let direction := portSideToDirection currSide
      let mid : KVector :=
        ⟨(firstBp.x + secondBp.x) * 0.5 + direction.cos * m.edgeLabelDistance,
         (firstBp.y + secondBp.y) * 0.5 + direction.sin * m.edgeLabelDistance⟩
      splinePoints := splinePoints.push mid
      currSide := if m.clockwise then currSide.right else currSide.left
    splinePoints := splinePoints.push bendPoints[bendPoints.size - 1]!
  splinePoints := splinePoints.push m.targetAnchor
  return .ok (NubSplineSubset.bezierControlPoints 3 splinePoints)

/-- The `SplineSelfLoopRouter` (the orthogonal routing with `modifyBendPoints`). -/
def router : AbstractSelfLoopRouter :=
  { name := "SplineSelfLoopRouter"
    routeSelfLoops := OrthogonalSelfLoopRouter.routeSelfLoopsWith modifyBendPoints }

end SplineSelfLoopRouter

end Elk.Alg.Layered.Intermediate.Loops.Routing
