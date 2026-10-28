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
Java copies the input `Set<TEdge>` into a list (the set's iteration order: callers pass
`JavaHashSet.toArray`) and sorts it by cost with `Double.compareTo` (stable TimSort; any stable sort
gives the same result for this total order, NaN last). The `HashMap<TEdge, Double>` of weights only
caches `cost(edge)` and the `HashMap<KVector, Tree>` of tree nodes is only used for membership tests
and lookups, so neither order is observable. An edge whose weight is NaN is never taken
(`weight <= minWeight` with `minWeight = +∞` is false). SVG debug output is not ported
(TODO(debug)).
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
  let sorted := stableSort weighted fun e1 e2 => Float.compareJava e1.2 e2.2
  let mut edges : Array (TEdge × Float) := sorted

  let mut minST := Tree.new root
  let mut treeNodes : Std.HashSet KVector := Std.HashSet.emptyWithCapacity
  treeNodes := treeNodes.insert root

  while !edges.isEmpty do
    let mut next : Option (Nat × KVector × KVector) := none
    let mut idx := 0
    for (edge, weight) in edges do
      if weight <= Float.posInf then
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
