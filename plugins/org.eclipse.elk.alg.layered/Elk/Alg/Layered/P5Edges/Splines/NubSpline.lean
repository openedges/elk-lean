import Elk.Alg.Layered.P5Edges.Splines.Rectangle
/-!
# `org.eclipse.elk.alg.layered.p5edges.splines.NubSpline`

Port of elk-rs `p5edges/splines/nub_spline.rs`: a non-uniform B-spline (not rational, no weights)
whose control points are stored as `PolarCP`s (control point + polar coordinates, see Senderberg:
"An introduction to B-Spline Curves", 2005). A control point whose polar coordinates are all equal
lies on the curve. The knot vector does not store the irrelevant first and last knots.

## API (value type)

`NubSpline` is an immutable value; the Rust `&mut self` methods return the updated spline:
- `NubSpline.new clamped dimension kVectors : Except String NubSpline` (Rust `new`/`new_from_vec`;
  the Rust panics become `IllegalArgumentException` errors), `NubSpline.newIO` throws instead.
- `getBezierCP s withSourceVector withTargetVector : KVectorChain × NubSpline` and
  `getBezierCPDefault s` (= `getBezierCP s false false`): converts to Bezier form (`toBezier`) if
  needed and returns the Bezier control points. This is what `FinalSplineBendpointsCalculator` and
  `SelfLoopRouter` use: `(NubSpline.new true 3 cps).map (·.getBezierCPDefault.1)`.
- `toBezier`, `getPointOnCurve s t modify : KVector × NubSpline`, `getControlPoints`,
  `getControlPoint`, `getControlPointsSize`, `getKnotVector`, `getDim`, `getOuterBox`,
  `setOuterBox`, `generateDerivedNubs`, `generateInvertedNubs`, `getFirst/LastVertical/HorizontalPoint`,
  `generateNiceCurve`.

## Rust details kept
- `insert_knot` passes `knot_index - 1` to `insert_knot_at_current_position`, which inserts at
  that index: for a knot that is not yet in the vector Rust therefore inserts one position earlier
  than Java's `ListIterator.add` (Java keeps the vector sorted). Bezier conversion is unaffected
  (it only inserts copies of an existing knot); `getPointOnCurve` follows Rust.
- `to_bezier` on an unclamped spline starts at index `dim - 1` after removing `dim - 1` leading
  knots (Java starts at index 0) and removes the trailing knots at `knot_index`.
- `get_t_from_polar` sums with `Iterator::sum` (neutral element `-0.0`).
- Rust panics on out-of-range indices (`Vec` indexing, `Vec::insert`); the Lean port stops the
  scan / skips the operation instead (unreachable for splines built by `new`).

`Display` impls (debug output only) are not ported.
-/
/-! Float literals as global constants (FL): inside branches, loops and specialised code the compiler
shares a literal's `Nat`/`Bool` arguments with unrelated variables (CSE) and then parses it on every
evaluation (`FastFloat.ofScientificImpl`); a top-level constant is a load (PLAN §7.1 items 17, 22). -/
private def fl0p0 : Float := 0.0
private def fl1p0 : Float := 1.0
private def fl0p5 : Float := 0.5
private def fl10p0 : Float := 10.0
private def fl12p0 : Float := 12.0
private def fl23p0 : Float := 23.0
private def fl2p2 : Float := 2.2
private def fl2p5 : Float := 2.5
private def fl3p5 : Float := 3.5
private def fl3p8 : Float := 3.8
private def fl4p0 : Float := 4.0
private def fl50p0 : Float := 50.0
private def fl5p0 : Float := 5.0
private def fl5p5 : Float := 5.5
private def fl6p0 : Float := 6.0
private def fl7p0 : Float := 7.0
private def fl80p0 : Float := 80.0
private def fl8p0 : Float := 8.0
private def fl9p0 : Float := 9.0

namespace Elk.Alg.Layered.P5Edges.Splines

open Elk.Core.Math Elk.Core.Util

/-- `NubSpline.PolarCP`: a control point with its polar coordinates. -/
structure PolarCP where
  cp : KVector := {}
  polarCoordinate : Array Float := #[]
  deriving Inhabited, BEq, Repr

/-- `NubSpline`. -/
structure NubSpline where
  /-- `knotVector`. -/
  knotVector : Array Float := #[]
  /-- `controlPoints`. -/
  controlPoints : Array PolarCP := #[]
  /-- `dimNUBS`. -/
  dimNubs : Nat := 0
  /-- `isUniform`. -/
  isUniform : Bool := true
  /-- `isClamped`. -/
  isClamped : Bool := false
  /-- `outerBox` (cached bounding box of the control points). -/
  outerBox : Option Rectangle := none
  /-- `isBezier`. -/
  isBezier : Bool := false
  /-- `minKnot`. -/
  minKnot : Float := fl0p0
  /-- `maxKnot`. -/
  maxKnot : Float := fl0p0
  deriving Inhabited, Repr

namespace NubSpline

/-- `DIM` (`3`). -/
def DIM : Nat := 3
/-- `EPSILON` (`0.000001`). -/
def EPSILON : Float := 0.000001

end NubSpline

namespace PolarCP

/-- `PolarCP(controlPoint, polarCoordinate)`. -/
@[inline] def new (controlPoint : KVector) (polarCoordinate : Array Float) : PolarCP :=
  { cp := controlPoint, polarCoordinate := polarCoordinate }

/-- `PolarCP(firstCP, secondCP, newKnot)` (Rust `from_two`): the de Boor combination of two
neighbouring control points for the inserted knot `newKnot`. -/
def fromTwo (firstCP secondCP : PolarCP) (newKnot : Float) : PolarCP := Id.run do
  let firstFactor := firstCP.polarCoordinate[0]?.getD 0.0
  let secondFactor := secondCP.polarCoordinate.back?.getD 0.0
  let aScaled := firstCP.cp.scale (secondFactor - newKnot)
  let bScaled := secondCP.cp.scale (newKnot - firstFactor)
  let total := (aScaled + bScaled).scale (1.0 / (secondFactor - firstFactor))
  -- the polar coordinates without the first one, `newKnot` inserted before the first larger one
  -- (beyond `EPSILON`), else appended
  let pc := firstCP.polarCoordinate
  let i := insertionIndex pc newKnot 1
  return { cp := total, polarCoordinate := (pc.extract 1 i).push newKnot ++ pc.extract i pc.size }
where
  /-- The first index from `i` on whose knot exceeds `newKnot` by more than `EPSILON`, else the size. -/
  insertionIndex (pc : Array Float) (newKnot : Float) (i : Nat) : Nat :=
    if h : i < pc.size then
      if (pc[i] - newKnot) > NubSpline.EPSILON then i else insertionIndex pc newKnot (i + 1)
    else pc.size
  termination_by pc.size - i

end PolarCP

namespace NubSpline

/-- Builds the `PolarCP`s of `kVectors` from the knot vector: the first `dim - 1` knots seed the
polar coordinate window, which then slides by one knot per control point (shared by the
constructor, `generateDerivedNUBS` and `generateInvertedNUBS`). -/
private def polarControlPoints (knots : Array Float) (dim : Nat) (kVectors : Array KVector) : Array PolarCP :=
  -- the window of control point `k` is `knots[k : k + dim]` (clipped to the knots; one knot for
  -- `dim = 0`): the seed holds `dim - 1` knots and every control point adds one before and drops one
  -- after it is created
  let width := (dim - 1) + 1
  kVectors.mapIdx fun k kVector => PolarCP.new kVector (knots.extract k (k + width))

/-- `createUniformKnotVector(clamped, size)`: a uniform knot vector (clamped: `dim` leading zeros and
trailing ones). -/
private def createUniformKnotVector (s : NubSpline) (clamped : Bool) (size : Nat) : Except String NubSpline := Id.run do
  if size < 2 * s.dimNubs then
    return .error "java.lang.IllegalArgumentException: The knot vector must have at least two time the dimension elements."
  let mut s := s
  let mut mySize := 0
  if clamped then
    s := { s with minKnot := fl0p0, maxKnot := fl1p0 }
    for _ in [0:s.dimNubs] do
      s := { s with knotVector := s.knotVector.push fl0p0 }
    mySize := size + 1 - 2 * s.dimNubs
  else
    mySize := size + 1
    let ddim := s.dimNubs.toFloat
    s := { s with minKnot := ddim / (mySize.toFloat + fl1p0), maxKnot := (mySize.toFloat - ddim) / mySize.toFloat }
  let fraction := mySize.toFloat
  for i in [1:mySize] do
    s := { s with knotVector := s.knotVector.push (i.toFloat / fraction) }
  if s.isClamped then
    for _ in [0:s.dimNubs] do
      s := { s with knotVector := s.knotVector.push fl1p0 }
  return .ok s

/-- `NubSpline(clamped, dimension, kVectors)` (Rust `new`/`new_from_vec`): pads the control points
by repeating the first one until there are `dimension + 1`, then builds a uniform knot vector. -/
def new (clamped : Bool) (dimension : Nat) (kVectors : Array KVector) : Except String NubSpline := do
  if dimension < 1 then throw "java.lang.IllegalArgumentException: The dimension must be at least 1!"
  let some first := kVectors[0]? | throw "java.lang.IllegalArgumentException: At least one control point is required"
  let mut kv := kVectors
  let mut i := kv.size - 1
  while i < dimension do
    kv := #[first] ++ kv
    i := i + 1
  if kv.size < dimension + 1 then
    throw "java.lang.IllegalArgumentException: At (least dimension + 1) control points are necessary!"
  let spline : NubSpline := { dimNubs := dimension, isUniform := true, isClamped := clamped }
  let spline ← spline.createUniformKnotVector clamped (kv.size + spline.dimNubs - 1)
  return { spline with controlPoints := polarControlPoints spline.knotVector spline.dimNubs kv }

/-- Rust `new_from_vec` (same as `new`, `KVectorChain` = `Array KVector`). -/
@[inline] def newFromVec (clamped : Bool) (dimension : Nat) (kVectors : Array KVector) : Except String NubSpline :=
  new clamped dimension kVectors

/-- `new` that throws the `IllegalArgumentException` as an `IO.userError`. -/
def newIO (clamped : Bool) (dimension : Nat) (kVectors : Array KVector) : IO NubSpline :=
  match new clamped dimension kVectors with
  | .ok s => pure s
  | .error e => throw (IO.userError e)

/-- The private constructor `NubSpline(clamped, uniform, bezier, dim, knotVec, polarVectors)`
(Rust `new_with_params`): `minKnot`/`maxKnot` are the first/last knot. -/
private def newWithParams (clamped uniform bezier : Bool) (dim : Nat) (knotVec : Array Float)
    (polarVectors : Array PolarCP) : NubSpline :=
  { isClamped := clamped, isUniform := uniform, isBezier := bezier, dimNubs := dim,
    knotVector := knotVec, controlPoints := polarVectors,
    minKnot := knotVec[0]?.getD 0.0, maxKnot := knotVec.back?.getD 0.0, outerBox := none }

/-- `generateDerivedNUBS(nubSpline)` (Rust `generate_derived_nubs`): the first derivative (dimension
`dim - 1`, knot vector without its first and last knot). -/
def generateDerivedNubs (s : NubSpline) : NubSpline := Id.run do
  let oldDim := s.dimNubs
  let newDim := oldDim - 1
  let oldKnotVector := s.knotVector
  let newKnotVector := oldKnotVector.extract 1 (oldKnotVector.size - 1)
  let mut newControlPoints : Array KVector := #[]
  for i in [0:s.controlPoints.size - 1] do
    let next := (s.controlPoints[i + 1]?.map (·.cp)).getD {}
    let prev := (s.controlPoints[i]?.map (·.cp)).getD {}
    let newCp := next - prev
    let denom := oldKnotVector[i + oldDim]?.getD fl0p0 - oldKnotVector[i]?.getD fl0p0
    newControlPoints := newControlPoints.push (newCp.scale (oldDim.toFloat / denom))
  return newWithParams s.isClamped s.isUniform s.isBezier newDim newKnotVector
    (polarControlPoints newKnotVector newDim newControlPoints)

/-- `getControlPoints()`: the control points as a vector chain. -/
def getControlPoints (s : NubSpline) : KVectorChain := s.controlPoints.map (·.cp)

/-- `generateInvertedNUBS(nubSpline)` (Rust `generate_inverted_nubs`): the same curve traversed
backwards (knots mirrored at the last knot). -/
def generateInvertedNubs (s : NubSpline) : NubSpline :=
  let maxVector := s.knotVector.back?.getD 0.0
  let newKnotVector := s.knotVector.reverse.map (maxVector - ·)
  let newControlPoints := KVectorChain.reverse s.getControlPoints
  newWithParams s.isClamped s.isUniform s.isBezier s.dimNubs newKnotVector
    (polarControlPoints newKnotVector s.dimNubs newControlPoints)

/-- `getDim()`. -/
@[inline] def getDim (s : NubSpline) : Nat := s.dimNubs

/-- `calculateOuterBox()`: the bounding box of the control points (Rust `from_vectors_iter`). -/
private def calculateOuterBox (s : NubSpline) : Except String NubSpline := do
  let box ← Rectangle.fromVectorsIter s.getControlPoints
  return { s with outerBox := some box }

/-- `getOuterBox()`: the cached bounding box, computed on first use. -/
def getOuterBox (s : NubSpline) : Except String (Rectangle × NubSpline) := do
  let s ← if s.outerBox.isNone then s.calculateOuterBox else pure s
  match s.outerBox with
  | some box => return (box, s)
  | none => throw "java.lang.IllegalArgumentException: The list of vectors may not be empty."

/-- `setOuterBox(outerRectangle)`. -/
@[inline] def setOuterBox (s : NubSpline) (outerRectangle : Rectangle) : NubSpline :=
  { s with outerBox := some outerRectangle }

/-- `getControlPoint(i)` (Rust panics out of range; `(0,0)` here). -/
def getControlPoint (s : NubSpline) (i : Nat) : KVector := (s.controlPoints[i]?.map (·.cp)).getD {}

/-- `getControlPointsSize()`. -/
@[inline] def getControlPointsSize (s : NubSpline) : Nat := s.controlPoints.size

/-- `getKnotVector()`. -/
@[inline] def getKnotVector (s : NubSpline) : Array Float := s.knotVector

/-- `getIndexInKnotVector(knot)`: index of the first knot within `EPSILON` of `knot`, else the
knot vector size. -/
def getIndexInKnotVector (s : NubSpline) (knot : Float) : Nat := Id.run do
  for h : index in [0:s.knotVector.size] do
    if (s.knotVector[index] - knot).abs < EPSILON then return index
  return s.knotVector.size

/-- `getMultiplicity(knotToCheck)`: number of knots within `EPSILON` of `knotToCheck` (the scan
stops at the first larger knot). -/
def getMultiplicity (s : NubSpline) (knotToCheck : Float) : Nat := Id.run do
  let mut count := 0
  for currentKnot in s.knotVector do
    let diff := currentKnot - knotToCheck
    if diff > EPSILON then return count
    else if diff > -EPSILON then count := count + 1
  return count

/-- `getTFromPolar(polar)`: the mean of the polar coordinates. -/
def getTFromPolar (polar : Array Float) : Float :=
  polar.foldl (· + ·) (-0.0) / polar.size.toFloat

/-- `insertKnotAtCurrentPosition(insertions, knotToInsert, iterCP, iterKnot)` (Rust
`insert_knot_at_current_position`): inserts `knotToInsert` `insertions` times at `knotIndex` and
replaces the affected control points, starting at `cpIndex`. Returns the spline with the updated
`(cpIndex, knotIndex)` cursor positions. -/
def insertKnotAtCurrentPosition (s : NubSpline) (insertions : Nat) (knotToInsert : Float)
    (cpIndex knotIndex : Nat) : NubSpline × Nat × Nat := Id.run do
  let multiplicity := s.getMultiplicity knotToInsert
  let dim := s.dimNubs
  let mut knots := s.knotVector
  let mut cps := s.controlPoints
  let mut cpIndex := cpIndex
  let mut knotIndex := knotIndex
  for i in [0:insertions] do
    knots := knots.insertIdxIfInBounds knotIndex knotToInsert
    knotIndex := knotIndex + 1
    let mut newCPs : Array PolarCP := #[]
    let mut secondCP := cps[cpIndex]?.getD default
    cpIndex := cpIndex + 1
    for _ in [multiplicity + i:dim] do
      let firstCP := secondCP
      secondCP := cps[cpIndex]?.getD default
      cpIndex := cpIndex + 1
      newCPs := newCPs.push (PolarCP.fromTwo firstCP secondCP knotToInsert)
    for j in [multiplicity + i:dim] do
      if cpIndex == 0 then break
      cpIndex := cpIndex - 1
      if j > multiplicity + i then
        cps := cps.eraseIdxIfInBounds cpIndex
    for cp in newCPs do
      cps := cps.insertIdxIfInBounds cpIndex cp
      cpIndex := cpIndex + 1
    if i < insertions - 1 then
      for _ in [multiplicity + i:dim] do
        if cpIndex == 0 then break
        cpIndex := cpIndex - 1
  return ({ s with knotVector := knots, controlPoints := cps }, cpIndex, knotIndex)

/-- `insertKnot(knotToInsert, insertions)`: inserts a knot after all identical knots (see the
module doc for the Rust index quirk). -/
def insertKnot (s : NubSpline) (knotToInsert : Float) (insertions : Nat) : NubSpline := Id.run do
  let mut knotIndex := if s.isClamped then s.dimNubs else s.dimNubs - 1
  let mut cpIndex := 0
  let some first := s.knotVector[knotIndex]? | return s
  let mut currentKnot := first
  while currentKnot - knotToInsert < EPSILON do
    knotIndex := knotIndex + 1
    cpIndex := cpIndex + 1
    match s.knotVector[knotIndex]? with
    | some k => currentKnot := k
    | none => break
  knotIndex := knotIndex - 1
  return (s.insertKnotAtCurrentPosition insertions knotToInsert cpIndex knotIndex).1

/-- `getPointOnCurve(t, modify)`: the point at parameter `t` (inserting `t` until its multiplicity
is `dim`); with `modify` the returned spline carries the inserted knots, otherwise it is `s`. -/
def getPointOnCurve (s : NubSpline) (t : Float) (modify : Bool) : KVector × NubSpline :=
  let multiplicity := s.getMultiplicity t
  if multiplicity == s.dimNubs then (s.getControlPoint (s.getIndexInKnotVector t), s)
  else if modify then
    let s' := s.insertKnot t (s.dimNubs - multiplicity)
    (s'.getControlPoint (s'.getIndexInKnotVector t), s')
  else
    let copy := s.insertKnot t (s.dimNubs - multiplicity)
    (copy.getControlPoint (copy.getIndexInKnotVector t), s)

/-- Shared body of `getZeroXOfControlPoligon`/`getZeroYOfControlPoligon`: the parameter of the first
sign change (or zero) of the coordinate `coord` along the control polygon, `0.0` if none. -/
private def zeroOfControlPolygon (s : NubSpline) (coord : KVector → Float) : Float := Id.run do
  let some first := s.controlPoints[0]? | return fl0p0
  let mut secondCP := first
  let mut secondV := coord secondCP.cp
  let mut secondIsPositive : Bool := secondV > EPSILON
  let mut secondIsNegative : Bool := secondV < -EPSILON
  for nextCP in s.controlPoints.extract 1 s.controlPoints.size do
    let firstCP := secondCP
    let firstV := secondV
    let firstIsPositive := secondIsPositive
    let firstIsNegative := secondIsNegative
    secondCP := nextCP
    secondV := coord secondCP.cp
    secondIsPositive := secondV > EPSILON
    secondIsNegative := secondV < -EPSILON
    if !(secondIsPositive || secondIsNegative) then
      return getTFromPolar secondCP.polarCoordinate
    if (firstIsPositive && secondIsNegative) || (firstIsNegative && secondIsPositive) then
      let factor := firstV / (firstV - secondV)
      let t1 := getTFromPolar firstCP.polarCoordinate
      let t2 := getTFromPolar secondCP.polarCoordinate
      return factor * t1 + (fl1p0 - factor) * t2
  return fl0p0

/-- `getZeroYOfControlPoligon(nubSpline)`. -/
def getZeroYOfControlPolygon (s : NubSpline) : Float := s.zeroOfControlPolygon (·.y)

/-- `getZeroXOfControlPoligon(nubSpline)`. -/
def getZeroXOfControlPolygon (s : NubSpline) : Float := s.zeroOfControlPolygon (·.x)

/-- Newton-like search shared by the four extremum functions: iterates `zero` on the derivative
`firstDerive` until the coordinate `coord` of the point is within `accuracy`; returns the knot. -/
private def extremumKnot (firstDerive : NubSpline) (zero : NubSpline → Float) (coord : KVector → Float)
    (accuracy : Float) (maxRecursion : Nat) : Float := Id.run do
  let mut firstDerive := firstDerive
  let mut currentAccuracy := Float.posInf
  let mut loopCount := 0
  let mut knot := 0.0
  while currentAccuracy > accuracy && loopCount < maxRecursion do
    knot := zero firstDerive
    let (vector, derive') := firstDerive.getPointOnCurve knot true
    firstDerive := derive'
    currentAccuracy := (coord vector).abs
    loopCount := loopCount + 1
  return knot

/-- `getFirstVerticalPoint(nubSpline, accuracy, maxRecursion)`. -/
def getFirstVerticalPoint (s : NubSpline) (accuracy : Float) (maxRecursion : Nat) : KVector :=
  let knot := extremumKnot (generateDerivedNubs s) getZeroXOfControlPolygon (·.x) accuracy maxRecursion
  (s.getPointOnCurve knot false).1

/-- `getLastVerticalPoint(nubSpline, accuracy, maxRecursion)`. -/
def getLastVerticalPoint (s : NubSpline) (accuracy : Float) (maxRecursion : Nat) : KVector :=
  let knot := extremumKnot (generateInvertedNubs (generateDerivedNubs s)) getZeroXOfControlPolygon (·.x)
    accuracy maxRecursion
  let maxVal := s.knotVector.back?.getD 0.0
  (s.getPointOnCurve (maxVal - knot) false).1

/-- `getFirstHorizontalPoint(nubSpline, accuracy, maxRecursion)`. -/
def getFirstHorizontalPoint (s : NubSpline) (accuracy : Float) (maxRecursion : Nat) : KVector :=
  let knot := extremumKnot (generateDerivedNubs s) getZeroYOfControlPolygon (·.y) accuracy maxRecursion
  (s.getPointOnCurve knot false).1

/-- `getLastHorizontalPoint(nubSpline, accuracy, maxRecursion)`. -/
def getLastHorizontalPoint (s : NubSpline) (accuracy : Float) (maxRecursion : Nat) : KVector :=
  let knot := extremumKnot (generateInvertedNubs (generateDerivedNubs s)) getZeroYOfControlPolygon (·.y)
    accuracy maxRecursion
  let maxVal := s.knotVector.back?.getD 0.0
  (s.getPointOnCurve (maxVal - knot) false).1

/-- `toBezier()`: raises the multiplicity of every inner knot to `dim` (Bezier form). -/
def toBezier (s : NubSpline) : NubSpline := Id.run do
  let mut s := s
  let dim := s.dimNubs
  let mut knotIndex := 0
  if s.isClamped then
    knotIndex := dim
  else
    for _ in [0:dim - 1] do
      if !s.knotVector.isEmpty then
        s := { s with knotVector := s.knotVector.eraseIdxIfInBounds 0 }
    knotIndex := dim - 1
  let mut cpIndex := 0
  -- Rust indexes out of range (panic) only for degenerate vectors; `maxKnot` ends the scan here
  let mut currentKnot := s.knotVector[knotIndex]?.getD s.maxKnot
  while s.maxKnot - currentKnot > EPSILON do
    let knotToCount := currentKnot
    let mut occurrence := 0
    while (currentKnot - knotToCount).abs < EPSILON do
      occurrence := occurrence + 1
      knotIndex := knotIndex + 1
      cpIndex := cpIndex + 1
      currentKnot := s.knotVector[knotIndex]?.getD s.maxKnot
    if occurrence < dim then
      knotIndex := knotIndex - 1
      let (s', cpIndex', knotIndex') := s.insertKnotAtCurrentPosition (dim - occurrence) knotToCount cpIndex knotIndex
      s := s'
      cpIndex := cpIndex'
      knotIndex := knotIndex' + 1
    cpIndex := cpIndex - 1
  if !s.isClamped then
    for _ in [0:dim - 1] do
      if knotIndex < s.knotVector.size then
        s := { s with knotVector := s.knotVector.eraseIdxIfInBounds knotIndex }
  return { s with isClamped := true, isBezier := true }

/-- `getBezierCP(withSourceVector, withTargetVector)`: the Bezier control points (converting with
`toBezier` first if necessary), optionally without the first/last point. -/
def getBezierCP (s : NubSpline) (withSourceVector withTargetVector : Bool) : KVectorChain × NubSpline :=
  let s := if !s.isBezier then s.toBezier else s
  let cps := if withSourceVector then s.controlPoints else s.controlPoints.extract 1 s.controlPoints.size
  let retVal : KVectorChain := cps.map (·.cp)
  let retVal := if withTargetVector then retVal else retVal.pop
  (retVal, s)

/-- `getBezierCP()` (Rust `get_bezier_cp_default`): without the source and target vector. -/
@[inline] def getBezierCPDefault (s : NubSpline) : KVectorChain × NubSpline := s.getBezierCP false false

/-- `mirrorOnX(original, xVal)`: the point mirrored at the vertical line `x = xVal`. -/
private def mirrorOnX (original : KVector) (xVal : Float) : KVector := ⟨xVal + xVal - original.x, original.y⟩

/-- `generateNiceCurve()`: a sample clamped cubic spline (scaled by 5, offset by `(-50, -80)`). -/
def generateNiceCurve : NubSpline :=
  let vector1 : KVector := ⟨fl5p5, fl23p0⟩
  let vector2 : KVector := ⟨fl2p5, fl12p0⟩
  let vector3 : KVector := ⟨fl5p0, fl10p0⟩
  let vector4 : KVector := ⟨fl5p0, fl9p0⟩
  let vector5 : KVector := ⟨fl3p8, fl5p5⟩
  let vector6 : KVector := ⟨fl7p0, fl4p0⟩
  let vector7 : KVector := ⟨fl7p0, fl3p5⟩
  let vector8 : KVector := ⟨fl6p0, fl2p2⟩
  let vector9 : KVector := ⟨fl8p0, fl0p5⟩
  let chain : KVectorChain := #[vector1, vector1, vector1, vector2, vector3, vector4, vector5, vector6,
    vector7, vector8, vector9, mirrorOnX vector8 vector9.x, mirrorOnX vector7 vector9.x,
    mirrorOnX vector6 vector9.x, mirrorOnX vector5 vector9.x, mirrorOnX vector4 vector9.x,
    mirrorOnX vector3 vector9.x, mirrorOnX vector2 vector9.x, mirrorOnX vector1 vector9.x,
    mirrorOnX vector1 vector9.x, mirrorOnX vector1 vector9.x]
  let chain := KVectorChain.offsetValues (chain.map (·.scale fl5p0)) (-fl50p0) (-fl80p0)
  -- 21 control points, dimension 3: the constructor cannot fail
  match new true 3 chain with
  | .ok s => s
  | .error _ => {}

end NubSpline

end Elk.Alg.Layered.P5Edges.Splines
