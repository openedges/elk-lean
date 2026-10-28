import Elk.Graph
import Elk.Core.Options
import Elk.Alg.Radial.RadialUtil
import Elk.Alg.Radial.Intermediate.Optimization.IEvaluation
/-!
# `org.eclipse.elk.alg.radial.intermediate.optimization.CrossingMinimizationPosition`

Port of `crossing_minimization_position.rs` (elk-rs): counts the pairs of lines (center of a
successor of the root to its `POSITION` property, shifted by the root) that intersect.

Parity quirk kept from the Rust port (and Java): the root center is computed as
`(x + width / 2, x + width / 2)`, i.e. the y component also uses `x` and `width`.
-/
/-! Float literals as global constants (FL): inside branches, loops and specialised code the compiler
shares a literal's `Nat`/`Bool` arguments with unrelated variables (CSE) and then parses it on every
evaluation (`FastFloat.ofScientificImpl`); a top-level constant is a load (PLAN §7.1 items 17, 22). -/
private def fl0p0 : Float := 0.0
private def fl2p0 : Float := 2.0

namespace Elk.Alg.Radial.Intermediate.Optimization

open Elk.Graph Elk.Core.Options

namespace CrossingMinimizationPosition

/-- Pre-extracted node data: `(center_x, center_y, position_x, position_y)`. -/
abbrev NodeCrossingData := Float × Float × Float × Float

/-- `is_crossing_soa(d1, d2)`. -/
def isCrossing (d1 d2 : NodeCrossingData) : Bool :=
  let (cx1, cy1, px1, py1) := d1
  let (cx2, cy2, px2, py2) := d2
  let m1 := (cy1 - py1) / (cx1 - px1)
  let b1 := cy1 - m1 * cx1
  let m2 := (cy2 - py2) / (cx2 - px2)
  let b2 := cy2 - m2 * cx2
  let xCut := (b1 - b2) / (m2 - m1)
  if (px1 < xCut && cx1 < xCut) || (xCut < px1 && xCut < cx1) then false
  else if (px2 < xCut && cx2 < xCut) || (xCut < px2 && xCut < cx2) then false
  else true

/-- `evaluate(root_node)`. -/
def evaluate (rootNode : NodeId) : ElkM Float := do
  let g ← get
  let r := g.node rootNode
  let rootX := r.x + r.width / fl2p0
  let rootY := r.x + r.width / fl2p0
  let nodes := RadialUtil.successorsPure g rootNode
  let nodeData : Array NodeCrossingData := nodes.map fun node =>
    let n := g.node node
    let cx := n.x + n.width / fl2p0
    let cy := n.y + n.height / fl2p0
    let pos := (n.props.get CoreOptions.POSITION).getD ⟨fl0p0, fl0p0⟩
    (cx, cy, pos.x + rootX, pos.y + rootY)
  let mut crossings : Nat := 0
  for i in [0:nodeData.size] do
    for j in [i + 1:nodeData.size] do
      if isCrossing nodeData[i]! nodeData[j]! then crossings := crossings + 1
  return crossings.toFloat

/-- The `IEvaluation` of this class. -/
def evaluation : IEvaluation := { evaluate := evaluate }

end CrossingMinimizationPosition

end Elk.Alg.Radial.Intermediate.Optimization
