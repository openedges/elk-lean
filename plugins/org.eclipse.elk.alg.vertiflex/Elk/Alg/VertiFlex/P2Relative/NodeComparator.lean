import Elk.Graph
import Elk.Core.Util.Java
import Elk.Alg.VertiFlex.InternalProperties
/-!
# `org.eclipse.elk.alg.vertiflex.p2relative.NodeComparator`

Port of `node_comparator.rs` (elk-rs): orders nodes by their y coordinate (descending when
`invert`), ties broken by the `NODE_MODEL_ORDER` internal property. The comparator itself is
pure over a `NodeKey` (the two properties it reads); `NodeComparator.key` reads them from the
graph.
-/
namespace Elk.Alg.VertiFlex.P2Relative

open Elk.Graph Elk.Core.Util

/-- The values `NodeComparator::compare` reads from a node: its y coordinate and its
`NODE_MODEL_ORDER` (`unwrap_or(0)`). -/
structure NodeKey where
  /-- The node. -/
  node : NodeId
  /-- `node_y(node)`. -/
  y : Float
  /-- `NODE_MODEL_ORDER.unwrap_or(0)` (`i32`). -/
  modelOrder : Int
  deriving Inhabited

namespace NodeComparator

/-- Reads the sort key of a node. -/
def key (node : NodeId) : VertiFlexM NodeKey := do
  let y := (← ElkM.getNode node).y
  let order := ((← VertiFlexM.getProps node).nodeModelOrder).getD 0
  return { node, y, modelOrder := order }

/-- `NodeComparator::compare(a, b)`: `partial_cmp(..).unwrap_or(Equal)` on the y coordinates
(swapped when `invert`), then `NODE_MODEL_ORDER`. -/
def compare (invert : Bool) (a b : NodeKey) : Ordering :=
  let cmp := if invert then Float.comparePartial b.y a.y else Float.comparePartial a.y b.y
  match cmp with
  | .eq => Ord.compare a.modelOrder b.modelOrder
  | c => c

end NodeComparator

end Elk.Alg.VertiFlex.P2Relative
