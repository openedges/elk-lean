import Elk.Alg.Layered.Intermediate.Loops.Routing.OrthogonalSelfLoopRouter
/-!
# `org.eclipse.elk.alg.layered.intermediate.loops.routing.PolylineSelfLoopRouter`

Port of elk-rs `intermediate/loops/routing/polyline_self_loop_router.rs` (`cut_corners`) and of the
`EdgeRouting::Polyline` arm of `modify_bend_points` in `intermediate/self_loop_router.rs`: the
orthogonal route (with the port anchors added at both ends) has every corner replaced by two
points `distance` (10, `POLYLINE_SELF_LOOP_CORNER_DISTANCE`) before and after it, at most half the
adjacent segment length. Like Rust (and Java), duplicate points are kept.

Rust `assert!`s (more than two points, orthogonal corners) are `Except` errors here; the router
throws them as `IllegalStateException`.
-/
/-! Float literals as global constants (FL): inside branches, loops and specialised code the compiler
shares a literal's `Nat`/`Bool` arguments with unrelated variables (CSE) and then parses it on every
evaluation (`FastFloat.ofScientificImpl`); a top-level constant is a load (PLAN §7.1 items 17, 22). -/
private def fl0p0 : Float := 0.0
private def fl2p0 : Float := 2.0

namespace Elk.Alg.Layered.Intermediate.Loops.Routing

open Elk.Core.Math Elk.Core.Util

namespace PolylineSelfLoopRouter

/-- `TOLERANCE`. -/
def TOLERANCE : Float := 0.01

/-- `POLYLINE_SELF_LOOP_CORNER_DISTANCE` (`self_loop_router.rs`). -/
def POLYLINE_SELF_LOOP_CORNER_DISTANCE : Float := 10.0

/-- `are_orthogonally_routed(previous, corner, next)`. -/
def areOrthogonallyRouted (previous corner next : KVector) : Bool :=
  let verticalHorizontal := (previous.x - corner.x).abs ≤ TOLERANCE && (corner.y - next.y).abs ≤ TOLERANCE
  let horizontalVertical := (previous.y - corner.y).abs ≤ TOLERANCE && (corner.x - next.x).abs ≤ TOLERANCE
  verticalHorizontal || horizontalVertical

/-- `near_zero_to_zero(vector)`. -/
def nearZeroToZero (v : KVector) : KVector :=
  let x := if v.x ≥ -TOLERANCE && v.x ≤ TOLERANCE then fl0p0 else v.x
  let y := if v.y ≥ -TOLERANCE && v.y ≤ TOLERANCE then fl0p0 else v.y
  ⟨x, y⟩

/-- `java_signum(value)` (`0.0` for zero and NaN). -/
def javaSignum (value : Float) : Float :=
  if value > 0.0 then 1.0 else if value < 0.0 then -1.0 else 0.0

/-- `cut_corners(bendPoints, distance)`: two points per inner point of the chain. -/
def cutCorners (bendPoints : KVectorChain) (distance : Float) : Except String KVectorChain := do
  if !(bendPoints.size > 2) then throw "need more than two bend points"
  let mut result : KVectorChain := #[]
  for i in [1:bendPoints.size - 1] do
    let previous := bendPoints[i - 1]!
    let corner := bendPoints[i]!
    let next := bendPoints[i + 1]!
    if !areOrthogonallyRouted previous corner next then throw "bend points must be orthogonally routed"
    let offset1 := nearZeroToZero (KVector.diff previous corner)
    let offset2 := nearZeroToZero (KVector.diff next corner)
    let mut effectiveDistance := distance
    effectiveDistance := fmin effectiveDistance ((offset1.x + offset1.y).abs / fl2p0)
    effectiveDistance := fmin effectiveDistance ((offset2.x + offset2.y).abs / fl2p0)
    let offset1 : KVector := ⟨javaSignum offset1.x * effectiveDistance, javaSignum offset1.y * effectiveDistance⟩
    let offset2 : KVector := ⟨javaSignum offset2.x * effectiveDistance, javaSignum offset2.y * effectiveDistance⟩
    result := result.push (corner + offset1)
    result := result.push (corner + offset2)
  return result

/-- `modify_bend_points` for `EdgeRouting::Polyline`: the chain source anchor, bend points, target
anchor with its corners cut. -/
def modifyBendPoints : BendPointModifier := fun m =>
  cutCorners (#[m.sourceAnchor] ++ m.bendPoints ++ #[m.targetAnchor]) POLYLINE_SELF_LOOP_CORNER_DISTANCE

/-- The `PolylineSelfLoopRouter` (the orthogonal routing with `modifyBendPoints`). -/
def router : AbstractSelfLoopRouter :=
  { name := "PolylineSelfLoopRouter"
    routeSelfLoops := OrthogonalSelfLoopRouter.routeSelfLoopsWith modifyBendPoints }

end PolylineSelfLoopRouter

end Elk.Alg.Layered.Intermediate.Loops.Routing
