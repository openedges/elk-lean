import Elk.Core.Util.Java
import Elk.Core.Options
import Elk.Alg.MrTree.Graph.TArena
/-!
# `org.eclipse.elk.alg.mrtree.p4route.MultiLevelEdgeNodeNodeGap`

ELK Java's `MultiLevelEdgeNodeNodeGap` (elk-rs `p4route/multi_level_edge_node_node_gap.rs` was the code
reference): the gap between two neighbouring nodes
of one tree level (`neighbor_one` left of the gap, `neighbor_two` right of it; either may be missing
at the ends of the level) through which several multi-level edges pass. Every edge reserves two bend
points (by index into its bend point chain); `update_bend_points` spreads the edges over the gap:

* both neighbours: interpolation `(i + 1) / (count + 1)` between the far side of `neighbor_one` and
  the near side of `neighbor_two`;
* only `neighbor_one` (`on_last_node_side`): `padding * (i + 1)` behind `neighbor_one`;
* only `neighbor_two` (`on_first_node_side`): `padding * (i + 1)` before `neighbor_two`;
* no neighbour: nothing (Java returns from the loop).

The two bend points cross the level from `LEVELMIN - padding` to `LEVELMAX + padding` of the
reference neighbour (reversed for `LEFT` and `UP`). Node data are read live from the arena; an index
beyond the current chain is ignored. `addBendPoints` re-sorts the edges by the position of their
targets (`LinkedList.sort` with `Double.compare`: stable, `javaSortByDouble`).
-/
namespace Elk.Alg.MrTree.P4Route

open Elk.Core.Util Elk.Core.Math Elk.Core.Options Elk.Alg.MrTree.Graph

/-- `MultiLevelEdgeNodeNodeGap`. -/
structure MultiLevelEdgeNodeNodeGap where
  neighborOne : Option TNodeId
  neighborTwo : Option TNodeId
  /-- `BendRef`s: edge, first and second bend point index. -/
  bendPoints : Array (TEdgeId × Nat × Nat)
  direction : Direction
  nodeBendpointPadding : Float
  onFirstNodeSide : Bool := false
  onLastNodeSide : Bool := false
  deriving Inhabited

namespace MultiLevelEdgeNodeNodeGap

/-- `node_data(node)`: position, size, `LEVELMIN`, `LEVELMAX`. -/
@[inline] private def nodeData (a : TArena) (n : TNodeId) : KVector × KVector × Float × Float :=
  let x := a.node n
  (x.position, x.size, x.internal.levelMin, x.internal.levelMax)

/-- `edge_target_pos(edge)`. -/
@[inline] private def edgeTargetPos (a : TArena) (e : TEdgeId) : KVector :=
  match (a.edge e).target with
  | some t => (a.node t).position
  | none => {}

/-- The two bend points of a gap for the reference coordinate `bendTmp`. -/
private def bendPair (direction : Direction) (pad levelMin levelMax bendTmp : Float) : KVector × KVector :=
  match direction with
  | .left => (⟨levelMax + pad, bendTmp⟩, ⟨levelMin - pad, bendTmp⟩)
  | .right => (⟨levelMin - pad, bendTmp⟩, ⟨levelMax + pad, bendTmp⟩)
  | .up => (⟨bendTmp, levelMax + pad⟩, ⟨bendTmp, levelMin - pad⟩)
  | _ => (⟨bendTmp, levelMin - pad⟩, ⟨bendTmp, levelMax + pad⟩)

/-- The two bend points of the `i`-th of `count` edges (`none` without neighbours). -/
private def bendsOf (a : TArena) (gap : MultiLevelEdgeNodeNodeGap) (i count : Nat) :
    Option (KVector × KVector) :=
  let pad := gap.nodeBendpointPadding
  let horizontal := gap.direction == .left || gap.direction == .right
  let interpolation := Float.ofNat (i + 1) / Float.ofNat (count + 1)
  match gap.neighborOne, gap.neighborTwo with
  | none, none => none
  | some one, none =>
    let (pos, size, levelMin, levelMax) := nodeData a one
    let bendTmp := if horizontal then pos.y + size.y + pad * (Float.ofNat i + 1.0)
      else pos.x + size.x + pad * (Float.ofNat i + 1.0)
    some (bendPair gap.direction pad levelMin levelMax bendTmp)
  | some one, some two =>
    let (posOne, sizeOne, levelMin, levelMax) := nodeData a one
    let (posTwo, _, _, _) := nodeData a two
    let bendTmp := if horizontal
      then posTwo.y * interpolation + (posOne.y + sizeOne.y) * (1.0 - interpolation)
      else posTwo.x * interpolation + (posOne.x + sizeOne.x) * (1.0 - interpolation)
    some (bendPair gap.direction pad levelMin levelMax bendTmp)
  | none, some two =>
    let (pos, _, levelMin, levelMax) := nodeData a two
    let bendTmp := if horizontal then pos.y - pad * (Float.ofNat i + 1.0)
      else pos.x - pad * (Float.ofNat i + 1.0)
    some (bendPair gap.direction pad levelMin levelMax bendTmp)

/-- `update_bend_points()`. -/
def updateBendPoints (gap : MultiLevelEdgeNodeNodeGap) : MrTreeM MultiLevelEdgeNodeNodeGap := do
  let mut gap := gap
  let count := gap.bendPoints.size
  for i in [0:count] do
    let (edge, firstIndex, secondIndex) := gap.bendPoints[i]!
    let some (bend1, bend2) := bendsOf (← get) gap i count | return gap
    if gap.neighborOne.isSome && gap.neighborTwo.isNone then gap := { gap with onLastNodeSide := true }
    if gap.neighborOne.isNone && gap.neighborTwo.isSome then gap := { gap with onFirstNodeSide := true }
    MrTreeM.modifyEdge edge fun e =>
      let bps := e.bendPoints
      let bps := if firstIndex < bps.size then bps.set! firstIndex bend1 else bps
      let bps := if secondIndex < bps.size then bps.set! secondIndex bend2 else bps
      { e with bendPoints := bps }
  return gap

/-- `MultiLevelEdgeNodeNodeGap::new(...)`. -/
def create (neighborOne neighborTwo : Option TNodeId) (edge : TEdgeId) (firstIndex secondIndex : Nat)
    (direction : Direction) (nodeBendpointPadding : Float) : MrTreeM MultiLevelEdgeNodeNodeGap :=
  updateBendPoints
    { neighborOne, neighborTwo, bendPoints := #[(edge, firstIndex, secondIndex)], direction,
      nodeBendpointPadding }

/-- `add_bend_points(edge, first_index, second_index)`. -/
def addBendPoints (gap : MultiLevelEdgeNodeNodeGap) (edge : TEdgeId) (firstIndex secondIndex : Nat) :
    MrTreeM MultiLevelEdgeNodeNodeGap := do
  let bendPoints := gap.bendPoints.push (edge, firstIndex, secondIndex)
  let a ← get
  let horizontal := gap.direction == .left || gap.direction == .right
  let sorted := javaSortByDouble bendPoints fun x =>
    let p := edgeTargetPos a x.1
    if horizontal then p.y else p.x
  updateBendPoints { gap with bendPoints := sorted }

end MultiLevelEdgeNodeNodeGap

end Elk.Alg.MrTree.P4Route
