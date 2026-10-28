import Elk.Alg.Layered.Intermediate.Loops.Routing.OrthogonalSelfLoopRouter
import Elk.Alg.Layered.P5Edges.Splines.NubSpline
import Elk.Alg.Layered.P5Edges.Splines.SplinesMath
/-!
# `org.eclipse.elk.alg.layered.intermediate.loops.routing.SplineSelfLoopRouter`

Port of the `EdgeRouting::Splines` arm of `modify_bend_points` in elk-rs
`intermediate/self_loop_router.rs`: the control polygon is the source anchor, then per pair of
consecutive orthogonal bend points the first point and the midpoint pushed `SPACING_EDGE_LABEL`
away from the node (direction of the current side, turning with the routing direction), the last
bend point and the target anchor; the result are the Bézier control points of the clamped cubic
NUB spline through that polygon (`NubSpline::new(true, 3, points).get_bezier_cp_default()`, P5's
`Elk.Alg.Layered.P5Edges.Splines.NubSpline`; the Rust panic of `NubSpline::new` is the modifier's
error). The directions are `SplinesMath.portSideToDirection`.
-/
/-! Float literals as global constants (FL): inside branches, loops and specialised code the compiler
shares a literal's `Nat`/`Bool` arguments with unrelated variables (CSE) and then parses it on every
evaluation (`FastFloat.ofScientificImpl`); a top-level constant is a load (PLAN §7.1 items 17, 22). -/
private def fl0p5 : Float := 0.5

namespace Elk.Alg.Layered.Intermediate.Loops.Routing

open Elk.Core.Math Elk.Core.Options Elk.Core.Util Elk.Alg.Layered.P5Edges.Splines

namespace SplineSelfLoopRouter

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
      -- midpoint offset away from the node (`new KVector(direction)`: `Math.cos`, `Math.sin`)
      let direction := KVector.fromAngle (SplinesMath.portSideToDirection currSide)
      let mid : KVector :=
        ⟨(firstBp.x + secondBp.x) * fl0p5 + direction.x * m.edgeLabelDistance,
         (firstBp.y + secondBp.y) * fl0p5 + direction.y * m.edgeLabelDistance⟩
      splinePoints := splinePoints.push mid
      currSide := if m.clockwise then currSide.right else currSide.left
    splinePoints := splinePoints.push bendPoints[bendPoints.size - 1]!
  splinePoints := splinePoints.push m.targetAnchor
  return (NubSpline.new true 3 splinePoints).map (·.getBezierCPDefault.1)

/-- The `SplineSelfLoopRouter` (the orthogonal routing with `modifyBendPoints`). -/
def router : AbstractSelfLoopRouter :=
  { name := "SplineSelfLoopRouter"
    routeSelfLoops := OrthogonalSelfLoopRouter.routeSelfLoopsWith modifyBendPoints }

end SplineSelfLoopRouter

end Elk.Alg.Layered.Intermediate.Loops.Routing
