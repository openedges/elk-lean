import Std.Data.HashSet
import Elk.Core.Util.Sort
import Elk.Alg.Common.Geometry.ICostFunction
import Elk.Alg.Common.Geometry.Tree
/-!
# `org.eclipse.elk.alg.common.NaiveMinST`

Simple minimum spanning tree calculation (elk-rs `naive_min_st.rs`): expects a
list of edges that are pairs of vertices, a cost function for these edges and a
root vertex to start the spanning tree.

Precondition: the edge list `E` represents a connected graph `(V, E)` and
`root ∈ V`. Postcondition: the returned tree connects all vertices in `V` once.

## Order
Rust collects the input `HashSet<TEdge>` into a `Vec` (hash iteration order)
and stable-sorts it by cost (`partial_cmp().unwrap_or(Equal)`); the Lean port
stable-sorts the input array in its given order, so ties keep the caller's
order. The `HashMap<TEdge, f64>` of weights only caches `cost(edge)` and the
`HashSet<KVector>` of tree nodes is only used for membership tests, so neither
order is observable. SVG debug output is not ported (TODO(debug)).
-/
namespace Elk.Alg.Common

open Elk.Core.Util Elk.Core.Math

namespace NaiveMinST

/-- `NaiveMinST.createSpanningTree(tEdges, root, costFunction, debugOutputFile)`: Prim-style
growth over the edges sorted by ascending cost; each step takes the first edge (in sorted
order) with exactly one endpoint in the tree. The debug output file is ignored. -/
def createSpanningTree (tEdges : Array TEdge) (root : KVector) (costFunction : ICostFunction)
    (_debugOutputFile : Option String := none) : Tree KVector := Id.run do
  let weighted : Array (TEdge × Float) := tEdges.map fun e => (e, costFunction e)
  let sorted := stableSort weighted fun e1 e2 => Float.comparePartial e1.2 e2.2
  let mut edges : Array TEdge := sorted.map (·.1)

  let mut minST := Tree.new root
  let mut treeNodes : Std.HashSet KVector := Std.HashSet.emptyWithCapacity
  treeNodes := treeNodes.insert root

  while !edges.isEmpty do
    let mut next : Option (Nat × KVector × KVector) := none
    let mut idx := 0
    for edge in edges do
      if treeNodes.contains edge.u && !treeNodes.contains edge.v then
        next := some (idx, edge.v, edge.u)
        break
      if treeNodes.contains edge.v && !treeNodes.contains edge.u then
        next := some (idx, edge.u, edge.v)
        break
      idx := idx + 1
    let some (edgeIndex, nextNode, nodeInTree) := next | break
    minST := (minST.addChildTo nodeInTree nextNode).1
    treeNodes := treeNodes.insert nextNode
    edges := edges.eraseIdxIfInBounds edgeIndex
  return minST

/-- `createSpanningTree(tEdges, root, costFunction)` without debug output. -/
@[inline] def createSpanningTreeWithoutDebug (tEdges : Array TEdge) (root : KVector)
    (costFunction : ICostFunction) : Tree KVector :=
  createSpanningTree tEdges root costFunction none

end NaiveMinST

end Elk.Alg.Common
