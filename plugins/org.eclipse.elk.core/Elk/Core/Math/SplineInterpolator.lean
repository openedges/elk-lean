import Elk.Core.Math.BezierSpline
/-!
# `org.eclipse.elk.core.math.ISplineInterpolator`

The Rust trait is a structure of functions. The `LinkedList` overloads of the
reference take the same data as the slice overloads; in Lean both are `Array`,
so the list variants are thin aliases.
-/
namespace Elk.Core.Math

/-- `ISplineInterpolator`. -/
structure SplineInterpolator where
  /-- `interpolatePoints(points)`. -/
  interpolatePoints : Array KVector → BezierSpline
  /-- `interpolatePoints(points, startVec, endVec, tangentScale)`. -/
  interpolatePointsWithTangents : Array KVector → KVector → KVector → Bool → BezierSpline

namespace SplineInterpolator

/-- `interpolatePoints(LinkedList)`. -/
def interpolatePointsList (i : SplineInterpolator) (points : Array KVector) : BezierSpline :=
  i.interpolatePoints points

/-- `interpolatePoints(LinkedList, startVec, endVec, tangentScale)`. -/
def interpolatePointsListWithTangents (i : SplineInterpolator) (points : Array KVector)
    (startVec endVec : KVector) (tangentScale : Bool) : BezierSpline :=
  i.interpolatePointsWithTangents points startVec endVec tangentScale

end SplineInterpolator

end Elk.Core.Math
