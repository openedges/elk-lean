import Elk.Alg.Layered.P5Edges.Splines.NubSpline
import Elk.Alg.Layered.P5Edges.Splines.SplinesMath
/-!
# `org.eclipse.elk.alg.layered.p5edges.splines.NubsSelfLoop`

Port of elk-rs `p5edges/splines/nubs_self_loop.rs`: a `NubSpline` (Rust `Deref` target, here the
field `spline`) describing a self loop, plus the position of its first label. The factory functions
build the control polygon from the two ports (positions relative to the node: `position + anchor`)
and take the `LGraphArena`; they return `Except` because the spline constructor (and the Rust
`assert!`s on the number of corner bend points) can fail.
-/
namespace Elk.Alg.Layered.P5Edges.Splines

open Elk.Core.Math Elk.Core.Options Elk.Core.Util Elk.Alg.Layered.Graph

/-- `NubsSelfLoop`. -/
structure NubsSelfLoop where
  /-- The spline (Rust `Deref<Target = NubSpline>`). -/
  spline : NubSpline
  /-- `firstLabelPosition`. -/
  firstLabelPosition : KVector := {}
  deriving Inhabited

namespace NubsSelfLoop

/-- `FRACTION` (`1.3`). -/
def FRACTION : Float := 1.3
/-- `HALF` (`0.5`). -/
def HALF : Float := 0.5
/-- `DIM` (`3`). -/
def DIM : Nat := 3

/-- `NubsSelfLoop(dimension, kVectors)` (clamped). -/
def new (dimension : Nat) (kVectors : Array KVector) : Except String NubsSelfLoop := do
  return { spline := ← NubSpline.new true dimension kVectors }

/-- `NubsSelfLoop(clamped, dimension, kVectors)` (Rust `new_with_clamped`). -/
def newWithClamped (clamped : Bool) (dimension : Nat) (kVectors : Array KVector) : Except String NubsSelfLoop := do
  return { spline := ← NubSpline.new clamped dimension kVectors }

/-- `setFirstLabelPosition(position)`. -/
@[inline] def setFirstLabelPosition (s : NubsSelfLoop) (position : KVector) : NubsSelfLoop :=
  { s with firstLabelPosition := position }

/-- Rust `port_position`: the port's position plus its anchor (relative to the node). -/
def portPosition (a : LGraphArena) (port : LPortId) : KVector :=
  let pt := a.port port
  pt.position + pt.anchor

/-- `createSideSelfLoop(source, target, length)`: a loop between two ports on the same side. -/
def createSideSelfLoop (a : LGraphArena) (source target : LPortId) (length : Float) : Except String NubsSelfLoop :=
  let sourcePos := portPosition a source
  let targetPos := portPosition a target
  let direction := SplinesMath.portSideToDirection (a.port source).side
  let firstCp := (KVector.fromAngle direction).scale length + sourcePos
  let thirdCp := (KVector.fromAngle direction).scale length + targetPos
  let mid := (firstCp - thirdCp).scale 0.5
  let secondCp := thirdCp + mid
  let midDir := (KVector.fromAngle direction).scale mid.length
  let secondCp := secondCp + midDir
  new DIM #[sourcePos, firstCp, secondCp, thirdCp, targetPos]

/-- `createCornerSelfLoop(source, target, sourceHeight, targetHeight)`: a loop between two ports on
adjacent sides. -/
def createCornerSelfLoop (a : LGraphArena) (source target : LPortId) (sourceHeight targetHeight : Float) :
    Except String NubsSelfLoop := Id.run do
  let sourceSide := (a.port source).side
  let targetSide := (a.port target).side
  let sourceDir := SplinesMath.portSideToDirection sourceSide
  let targetDir := SplinesMath.portSideToDirection targetSide
  let sourcePos := portPosition a source
  let targetPos := portPosition a target
  let firstCp := (KVector.fromAngle sourceDir).scale (FRACTION * sourceHeight) + sourcePos
  let thirdCp := (KVector.fromAngle targetDir).scale (FRACTION * targetHeight) + targetPos
  let mut cornerX := 0.0
  let mut cornerY := 0.0
  match sourceSide with
  | .west => cornerX := 2.0 * (sourcePos.x - sourceHeight) - HALF * (firstCp.x + thirdCp.x)
  | .east => cornerX := 2.0 * (sourcePos.x + sourceHeight) - HALF * (firstCp.x + thirdCp.x)
  | .north => cornerY := 2.0 * (sourcePos.y - sourceHeight) - HALF * (firstCp.y + thirdCp.y)
  | .south => cornerY := 2.0 * (sourcePos.y + sourceHeight) - HALF * (firstCp.y + thirdCp.y)
  | .undefined => pure ()
  match targetSide with
  | .west => cornerX := 2.0 * (targetPos.x - targetHeight) - HALF * (thirdCp.x + firstCp.x)
  | .east => cornerX := 2.0 * (targetPos.x + targetHeight) - HALF * (thirdCp.x + firstCp.x)
  | .north => cornerY := 2.0 * (targetPos.y - targetHeight) - HALF * (thirdCp.y + firstCp.y)
  | .south => cornerY := 2.0 * (targetPos.y + targetHeight) - HALF * (thirdCp.y + firstCp.y)
  | .undefined => pure ()
  let secondCp : KVector := ⟨cornerX, cornerY⟩
  return new DIM #[sourcePos, firstCp, secondCp, thirdCp, targetPos]

/-- `createAcrossSelfLoop(source, target, sourceBendPoint, cornerBendPoints, targetBendPoint)`: a
loop between opposite sides (two corner bend points, Rust `assert!`). -/
def createAcrossSelfLoop (a : LGraphArena) (source target : LPortId) (sourceBendPoint : KVector)
    (cornerBendPoints : Array KVector) (targetBendPoint : KVector) : Except String NubsSelfLoop := do
  let sourcePos := portPosition a source
  let targetPos := portPosition a target
  let (some thirdCp, some fourthCp) := (cornerBendPoints[0]?, cornerBendPoints[1]?)
    | throw "java.lang.IllegalStateException: assertion failed: corner_bend_points.len() == 2"
  if cornerBendPoints.size != 2 then
    throw "java.lang.IllegalStateException: assertion failed: corner_bend_points.len() == 2"
  let middleCp := (fourthCp + thirdCp).scale HALF
  new DIM #[sourcePos, sourceBendPoint, thirdCp, middleCp, fourthCp, targetBendPoint, targetPos]

/-- `createThreeSideSelfLoop(…)`: three corner bend points (Rust `assert!`). -/
def createThreeSideSelfLoop (a : LGraphArena) (source target : LPortId) (sourceBendPoint : KVector)
    (cornerBendPoints : Array KVector) (targetBendPoint : KVector) : Except String NubsSelfLoop := do
  if cornerBendPoints.size != 3 then
    throw "java.lang.IllegalStateException: assertion failed: corner_bend_points.len() == 3"
  let sourcePos := portPosition a source
  let targetPos := portPosition a target
  new DIM (#[sourcePos, sourceBendPoint] ++ cornerBendPoints ++ #[targetBendPoint, targetPos])

/-- `createFourSideSelfLoop(…)`: four corner bend points (Rust `assert!`). -/
def createFourSideSelfLoop (a : LGraphArena) (source target : LPortId) (sourceBendPoint : KVector)
    (cornerBendPoints : Array KVector) (targetBendPoint : KVector) : Except String NubsSelfLoop := do
  if cornerBendPoints.size != 4 then
    throw "java.lang.IllegalStateException: assertion failed: corner_bend_points.len() == 4"
  let sourcePos := portPosition a source
  let targetPos := portPosition a target
  new DIM (#[sourcePos, sourceBendPoint] ++ cornerBendPoints ++ #[targetBendPoint, targetPos])

end NubsSelfLoop

end Elk.Alg.Layered.P5Edges.Splines
