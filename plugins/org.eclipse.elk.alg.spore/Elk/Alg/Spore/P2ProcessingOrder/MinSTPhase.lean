import Elk.Alg.Common.Geometry.NaiveMinST
import Elk.Alg.Spore.SporePhases
import Elk.Alg.Spore.P2ProcessingOrder.CostFunction
/-!
# `org.eclipse.elk.alg.spore.p2processingorder.MinSTPhase`

Port of `p2processingorder/min_st_phase.rs` (elk-rs) and `MinSTPhase.java`: finds a minimum
spanning tree for the edges of the graph with the root `Graph.preferredRoot` (default: the first
vertex), using `NaiveMinST` with the `GraphCostFunction`, and converts it to a `Tree Node`
(`convertTree`, also used by `MaxSTPhase`).

Order: the input edges are the insertion-ordered `Graph.tEdges`; the Rust `HashSet<TEdge>` is
iterated in random order, which makes the result of elk-rs nondeterministic when edge costs tie
(see `NaiveMinST`). The SVG debug output is not ported (TODO(debug)).
-/
namespace Elk.Alg.Spore.P2ProcessingOrder

open Elk.Core.Alg Elk.Core.Util Elk.Core.Math Elk.Alg.Common Elk.Alg.Common.Spore
open Elk.Alg.Spore.Graph

namespace MinSTPhase

/-- `add_node(root, t_tree, node_map)`: adds, below `root`, the node trees of the children of
`tTree` whose vertex is known (unknown children and their subtrees are skipped). -/
def addNode (nodeMap : Std.HashMap KVector Node) (root : Tree Node) (tTree : Tree KVector) :
    Tree Node := Id.run do
  let mut root := root
  for _h : child in tTree.children do
    if let some node := nodeMap.get? child.node then
      root := { root with children := root.children.push (addNode nodeMap (Tree.new node) child) }
  return root
termination_by tTree
decreasing_by exact Tree.sizeOf_lt_of_mem ‹_›

/-- `convert_tree(t_tree, graph)`: converts a tree of vectors to a tree of the graph's nodes (looked
up by `originalVertex`); the tree is `None` when the root vertex is unknown. -/
def convertTree (tTree : Tree KVector) (g : Graph) : Graph :=
  let nodeMap : Std.HashMap KVector Node := g.vertices.foldl
    (fun m node => m.insert node.originalVertex node) {}
  match nodeMap.get? tTree.node with
  | none => { g with tree := none }
  | some rootNode => { g with tree := some (addNode nodeMap (Tree.new rootNode) tTree) }

/-- `process(graph, progressMonitor)`: the minimum spanning tree phase. -/
def process (_graph : Unit) (monitor : ProgressMonitor) : SporeM Unit := do
  let _ ← monitor.begin "Minimum spanning tree construction" 1.0
  modify fun g =>
    match g.vertices[0]? with
    | none => g
    | some first =>
      let root := (g.preferredRoot.getD first).originalVertex
      match g.tEdges with
      | none => g
      | some edges =>
        let tree := NaiveMinST.createSpanningTree edges root (GraphCostFunction.new g)
        convertTree tree g
  monitor.done

/-- The `MinSTPhase` phase (no intermediate processors). -/
def phase : SporePhase :=
  { name := "MinSTPhase", process := process, getLayoutProcessorConfiguration := fun _ => noProcessors }

end MinSTPhase

end Elk.Alg.Spore.P2ProcessingOrder
