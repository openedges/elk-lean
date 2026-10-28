import Std.Data.HashMap
import Std.Data.HashSet
import Elk.Graph
import Elk.Core.Math
import Elk.Core.Options
import Elk.Core.Util.Java
import Elk.Alg.Radial.InternalProperties
/-!
# `org.eclipse.elk.alg.radial.RadialUtil`

Port of `radial_util.rs` (elk-rs): tree helpers of the radial algorithm (successors of a node,
the root of a graph, leaf counts, level-wise traversal, node centering and the polar comparison).

The graph reading helpers come in a pure form over the `ElkGraph` arena (`...Pure`, used by the
hot loops) and as `ElkM` wrappers. Edge order everywhere is `ElkGraphUtil.allOutgoingEdges`
(node edges, then the edges of its ports in port order).

Deliberate difference to Rust: `get_number_of_leaves` and the tree caches are plain recursions
over `Std.HashMap` caches keyed by `NodeId` instead of node addresses; the values are identical.
-/
/-! Float literals as global constants (FL): inside branches, loops and specialised code the compiler
shares a literal's `Nat`/`Bool` arguments with unrelated variables (CSE) and then parses it on every
evaluation (`FastFloat.ofScientificImpl`); a top-level constant is a load (PLAN §7.1 items 17, 22). -/
private def fl0p0 : Float := 0.0
private def fl2p0 : Float := 2.0

namespace Elk.Alg.Radial

open Elk.Graph Elk.Core.Math Elk.Core.Options Elk.Core.Util

namespace RadialUtil

/-- `RadialUtil::TWO_PI`. -/
def TWO_PI : Float := 2.0 * Float.pi
/-- `RadialUtil::EPSILON`. -/
def EPSILON : Float := 1e-10

/-- Local `fuzzy_compare(a, b, epsilon)` of `radial_util.rs`. -/
def fuzzyCompare (a b epsilon : Float) : Ordering :=
  if (a - b).abs <= epsilon then .eq else if a < b then .lt else .gt

/-- Local `fuzzy_equals(a, b, epsilon)` of `radial_util.rs`. -/
def fuzzyEquals (a b epsilon : Float) : Bool := (a - b).abs <= epsilon

/-- `get_successors` / `get_successor_set` on the arena: the targets (nodes) of the outgoing
edges of `node` whose first source is not a port and whose target is not a child of `node`;
`dedup` keeps only the first occurrence of each target (`get_successor_set`). -/
def successorsPure (g : ElkGraph) (node : NodeId) (dedup : Bool := false) : Array NodeId := Id.run do
  let childSet : Std.HashSet NodeId := (g.node node).children.foldl (·.insert ·) {}
  let mut successors : Array NodeId := #[]
  let mut seen : Std.HashSet NodeId := {}
  for e in ElkGraphUtil.allOutgoingEdges g node do
    let edge := g.edge e
    if let some (ConnectableId.port _) := edge.sources[0]? then continue
    let some targetShape := edge.targets[0]? | continue
    let some target := ElkGraphUtil.connectableShapeToNode g targetShape | continue
    if childSet.isEmpty || !childSet.contains target then
      if dedup then
        if !seen.contains target then
          seen := seen.insert target
          successors := successors.push target
      else
        successors := successors.push target
  return successors

/-- `RadialUtil::get_successors(node)`. -/
def getSuccessors (node : NodeId) : ElkM (Array NodeId) :=
  ElkM.withGraph fun g => successorsPure g node

/-- `RadialUtil::get_successor_set(node)`. -/
def getSuccessorSet (node : NodeId) : ElkM (Array NodeId) :=
  ElkM.withGraph fun g => successorsPure g node true

/-- `find_root(graph)` on the arena: the first child without incoming edges. -/
def findRootPure (g : ElkGraph) (graph : NodeId) : Option NodeId :=
  (g.node graph).children.find? fun child => (ElkGraphUtil.allIncomingEdges g child).isEmpty

/-- `RadialUtil::find_root(graph)`. -/
def findRoot (graph : NodeId) : ElkM (Option NodeId) :=
  ElkM.withGraph fun g => findRootPure g graph

/-- `RadialUtil::root_from_graph(graph)`: the `ROOT_NODE` of the graph if it is still a child,
otherwise `find_root`. -/
def rootFromGraph (graph : NodeId) : RadialM (Option NodeId) := do
  match ← InternalProperties.rootNode graph with
  | some root =>
    if (← ElkM.getNode graph).children.contains root then return some root
    findRoot graph
  | none => findRoot graph

/-- `get_tree_parent(node)` on the arena: the node of the first source of the first incoming edge. -/
def treeParentPure (g : ElkGraph) (node : NodeId) : Option NodeId := do
  let e ← (ElkGraphUtil.allIncomingEdges g node)[0]?
  let source ← (g.edge e).sources[0]?
  ElkGraphUtil.connectableShapeToNode g source

/-- `RadialUtil::get_tree_parent(node)`. -/
def getTreeParent (node : NodeId) : ElkM (Option NodeId) :=
  ElkM.withGraph fun g => treeParentPure g node

/-- `RadialUtil::find_root_of_node(node)`: follows the tree parents up to the root. -/
partial def findRootOfNodePure (g : ElkGraph) (node : NodeId) : NodeId :=
  match treeParentPure g node with
  | some parent => findRootOfNodePure g parent
  | none => node

/-- `RadialUtil::find_root_of_node(node)`. -/
def findRootOfNode (node : NodeId) : ElkM NodeId :=
  ElkM.withGraph fun g => findRootOfNodePure g node

/-- `RadialUtil::get_number_of_leaves(node)`. -/
partial def numberOfLeavesPure (g : ElkGraph) (node : NodeId) : Float :=
  let successors := successorsPure g node
  if successors.isEmpty then 1.0
  else successors.foldl (fun acc s => acc + numberOfLeavesPure g s) 0.0

/-- `RadialUtil::get_number_of_leaves(node)`. -/
def getNumberOfLeaves (node : NodeId) : ElkM Float :=
  ElkM.withGraph fun g => numberOfLeavesPure g node

/-- `build_caches_recursive`: fills the successor and leaf count caches below `node` and returns
the leaf count of `node`. -/
partial def buildCachesRec (g : ElkGraph) (node : NodeId)
    (successorCache : Std.HashMap NodeId (Array NodeId)) (leafCache : Std.HashMap NodeId Float) :
    Float × Std.HashMap NodeId (Array NodeId) × Std.HashMap NodeId Float :=
  match leafCache.get? node with
  | some count => (count, successorCache, leafCache)
  | none =>
    let successors := successorsPure g node
    if successors.isEmpty then
      (1.0, successorCache.insert node successors, leafCache.insert node 1.0)
    else
      let (count, successorCache, leafCache) :=
        successors.foldl (fun (acc, sc, lc) s =>
          let (c, sc, lc) := buildCachesRec g s sc lc
          (acc + c, sc, lc)) (0.0, successorCache, leafCache)
      (count, successorCache.insert node successors, leafCache.insert node count)

/-- `RadialUtil::build_tree_caches(root)`: the successor cache and the leaf count cache of the
whole tree below `root`. -/
def buildTreeCachesPure (g : ElkGraph) (root : NodeId) :
    Std.HashMap NodeId (Array NodeId) × Std.HashMap NodeId Float :=
  let (_, successorCache, leafCache) := buildCachesRec g root {} {}
  (successorCache, leafCache)

/-- `RadialUtil::build_tree_caches(root)`. -/
def buildTreeCaches (root : NodeId) : ElkM (Std.HashMap NodeId (Array NodeId) × Std.HashMap NodeId Float) :=
  ElkM.withGraph fun g => buildTreeCachesPure g root

/-- `polar_arc(node, radial_offset, node_offset_y)`: the polar angle of the `POSITION` property
(`(0, 0)` if unset), shifted by `radial_offset`. -/
def polarArc (node : ElkNode) (radialOffset nodeOffsetY : Float) : Float :=
  let position := (node.props.get CoreOptions.POSITION).getD ⟨0.0, 0.0⟩
  let xPos := position.x
  let yPos := position.y + nodeOffsetY
  let arc := javaAtan2 yPos xPos
  let arc := if arc < 0.0 then arc + TWO_PI else arc
  let arc := arc + radialOffset
  if arc > TWO_PI then arc - TWO_PI else arc

/-- `RadialUtil::compare_polar(node1, node2, radial_offset, node_offset_y)`. -/
def comparePolar (node1 node2 : NodeId) (radialOffset nodeOffsetY : Float) : ElkM Ordering := do
  let n1 ← ElkM.getNode node1
  let n2 ← ElkM.getNode node2
  return fuzzyCompare (polarArc n1 radialOffset nodeOffsetY) (polarArc n2 radialOffset nodeOffsetY) EPSILON

/-- `RadialUtil::find_largest_node_in_graph(graph)`: the largest diagonal of a descendant node. -/
partial def largestNodePure (g : ElkGraph) (graph : NodeId) : Float :=
  (g.node graph).children.foldl (fun largest child =>
    let n := g.node child
    let diameter := Float.sqrt (n.width * n.width + n.height * n.height)
    let largest := fmax largest diameter
    fmax largest (largestNodePure g child)) 0.0

/-- `RadialUtil::find_largest_node_in_graph(graph)`. -/
def findLargestNodeInGraph (graph : NodeId) : ElkM Float :=
  ElkM.withGraph fun g => largestNodePure g graph

/-- `RadialUtil::get_next_level_nodes(nodes)`: the concatenated successors. -/
def nextLevelNodesPure (g : ElkGraph) (nodes : Array NodeId) : Array NodeId :=
  nodes.foldl (fun acc node => acc ++ successorsPure g node) #[]

/-- `RadialUtil::get_next_level_nodes(nodes)`. -/
def getNextLevelNodes (nodes : Array NodeId) : ElkM (Array NodeId) :=
  ElkM.withGraph fun g => nextLevelNodesPure g nodes

/-- `RadialUtil::get_next_level_nodes_cached(nodes, cache)`. -/
def getNextLevelNodesCached (nodes : Array NodeId) (cache : Std.HashMap NodeId (Array NodeId)) :
    Array NodeId :=
  nodes.foldl (fun acc node => acc ++ (cache.get? node).getD #[]) #[]

/-- `RadialUtil::get_next_level_node_set(nodes)`: the successors without duplicates. -/
def getNextLevelNodeSet (nodes : Array NodeId) : ElkM (Array NodeId) := do
  let g ← get
  let mut successors : Array NodeId := #[]
  let mut seen : Std.HashSet NodeId := {}
  for node in nodes do
    for next in successorsPure g node true do
      if !seen.contains next then
        seen := seen.insert next
        successors := successors.push next
  return successors

/-- `RadialUtil::get_last_level_nodes(nodes)`: the tree parents. -/
def getLastLevelNodes (nodes : Array NodeId) : ElkM (Array NodeId) :=
  ElkM.withGraph fun g => nodes.filterMap (treeParentPure g)

/-- `RadialUtil::center_nodes_on_radi(node, x_pos, y_pos)`. -/
def centerNodesOnRadi (node : NodeId) (xPos yPos : Float) : ElkM Unit :=
  ElkM.modifyNode node fun n => { n with x := xPos - n.width / fl2p0, y := yPos - n.height / fl2p0 }

/-- `RadialUtil::shift_closest_edge_to_radi(node, x_pos, y_pos)`. -/
def shiftClosestEdgeToRadi (node : NodeId) (xPos yPos : Float) : ElkM Unit :=
  ElkM.modifyNode node fun n =>
    let w := n.width
    let h := n.height
    if fuzzyEquals xPos fl0p0 EPSILON && fuzzyEquals yPos fl0p0 EPSILON then
      { n with x := xPos - w / fl2p0, y := yPos - h / fl2p0 }
    else if xPos < fl0p0 then
      if yPos < fl0p0 then { n with x := xPos - w, y := yPos }
      else { n with x := xPos - w, y := yPos + h }
    else if yPos < fl0p0 then { n with x := xPos, y := yPos }
    else { n with x := xPos, y := yPos + h }

end RadialUtil

end Elk.Alg.Radial
