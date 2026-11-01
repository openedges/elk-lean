import Std.Data.HashMap
import Elk.Graph
import Elk.Core.Options
import Elk.Alg.Radial.RadialUtil
import Elk.Alg.Radial.Intermediate.Optimization.IEvaluation
import Elk.Core.Util.FloatConst
open Elk.Core.Util.FloatConst
/-!
# `org.eclipse.elk.alg.radial.intermediate.optimization.CrossingMinimizationPosition`

Port of `crossing_minimization_position.rs` (elk-rs): counts the pairs of lines (center of a
successor of the root to its `POSITION` property, shifted by the root) that intersect.

Parity quirk kept from the Rust port (and Java): the root center is computed as
`(x + width / 2, x + width / 2)`, i.e. the y component also uses `x` and `width`.

Java semantics (agent OPT; elk-rs reads an unset position as `(0, 0)` and never changes it):
`isCrossing(node1, node2)` adds the root center to the `POSITION` vectors of both nodes *in place*
(`position1.x = position1.x + rootX`, ...), so every comparison moves the stored positions and the
evaluations of later rotation offsets see the moved values; an unset position is a
`NullPointerException` (`"position1"` for the first node of the pair, then `"position2"`).
-/

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

/-- `evaluate(rootNode)`: the pairs `(node1, nodes[i])`, `i > index of node1`, in Java order, with
the in-place updates of the stored positions (see the module doc). -/
def evaluate (rootNode : NodeId) : ElkM Float := do
  let g ← get
  let r := g.node rootNode
  let rootX := r.x + r.width / fl2p0
  let rootY := r.x + r.width / fl2p0
  let nodes := RadialUtil.successorsPure g rootNode
  let centers : Array (Float × Float) := nodes.map fun node =>
    let n := g.node node
    (n.x + n.width / fl2p0, n.y + n.height / fl2p0)
  -- the stored `POSITION` vectors (one per node; a node listed twice shares its vector)
  let mut positions : Std.HashMap NodeId Elk.Core.Math.KVector := {}
  let mut crossings : Nat := 0
  for k in [0:nodes.size] do
    for i in [k + 1:nodes.size] do
      let n1 := nodes[k]!
      let n2 := nodes[i]!
      let some p1 := (positions.get? n1).orElse fun _ => (g.node n1).props.get CoreOptions.POSITION
        | throw (IO.userError "java.lang.NullPointerException: Cannot read field \"x\" because \"position1\" is null")
      let p1 : Elk.Core.Math.KVector := ⟨p1.x + rootX, p1.y + rootY⟩
      positions := positions.insert n1 p1
      let some p2 := (positions.get? n2).orElse fun _ => (g.node n2).props.get CoreOptions.POSITION
        | throw (IO.userError "java.lang.NullPointerException: Cannot read field \"x\" because \"position2\" is null")
      let p2 : Elk.Core.Math.KVector := ⟨p2.x + rootX, p2.y + rootY⟩
      positions := positions.insert n2 p2
      let (cx1, cy1) := centers[k]!
      let (cx2, cy2) := centers[i]!
      if isCrossing (cx1, cy1, p1.x, p1.y) (cx2, cy2, p2.x, p2.y) then crossings := crossings + 1
  for (node, position) in positions do
    ElkM.setNodeProp node CoreOptions.POSITION position
  return crossings.toFloat

/-- The `IEvaluation` of this class. -/
def evaluation : IEvaluation := { evaluate := evaluate }

end CrossingMinimizationPosition

end Elk.Alg.Radial.Intermediate.Optimization
