import Std.Data.HashSet
import Elk.Core.Options
import Elk.Core.Util.Java
import Elk.Core.Util.Sort
import Elk.Alg.MrTree.Graph.TArena
import Elk.Alg.MrTree.Options.MrTreeOptions
/-!
# `org.eclipse.elk.alg.mrtree.TreeUtil`

Port of `tree_util.rs` (elk-rs): read-only helpers over the tree graph. They are pure functions of the
`TArena` (call them as `TreeUtil.f (← get) …`, without keeping the arena across writes);
`toNodeBorder` returns the moved point instead of mutating its argument.

Rust semantics kept (they differ from Java `TreeUtil`): `getChildren` deduplicates the targets of the
outgoing edges; `getAllIncomingEdges`/`getAllOutgoingEdges` match the node by its integer `id` (not
by identity), skip edges inside one tree level, deduplicate and sort by the x coordinate of the other
end point (`partial_cmp`, stable); `getLowestParent` takes the parent whose centre has the largest
projection on the direction vector (first one on ties).
-/
/-! Float literals as global constants (FL): inside branches, loops and specialised code the compiler
shares a literal's `Nat`/`Bool` arguments with unrelated variables (CSE) and then parses it on every
evaluation (`FastFloat.ofScientificImpl`); a top-level constant is a load (PLAN §7.1 items 17, 22). -/
private def fl0p0 : Float := 0.0
private def fl2p0 : Float := 2.0

namespace Elk.Alg.MrTree

open Elk.Graph Elk.Core.Math Elk.Core.Util Elk.Core.Options Elk.Alg.MrTree.Graph Elk.Alg.MrTree.Options

namespace TreeUtil

/-- `TREE_LEVEL` of a node (`unwrap_or(0)`). -/
@[inline] private def treeLevel (a : TArena) (n : TNodeId) : Int :=
  ((a.node n).props.get MrTreeOptions.TREE_LEVEL).getD 0

/-- `get_root(graph)`: the first node of the graph with `ROOT` set. -/
def getRoot (a : TArena) (g : TGraphId) : Option TNodeId :=
  (a.graph g).nodes.find? fun n => (a.node n).internal.root

/-- `get_children(node)`: the distinct targets of the outgoing edges, in edge order. -/
def getChildren (a : TArena) (n : TNodeId) : Array TNodeId := Id.run do
  let mut seen : Std.HashSet TNodeId := {}
  let mut children := #[]
  for e in (a.node n).outgoingEdges do
    if let some t := (a.edge e).target then
      if !seen.contains t then
        seen := seen.insert t
        children := children.push t
  return children

/-- `depth(root)`: the number of levels of the subtree (1 for a leaf). -/
partial def depth (a : TArena) (root : TNodeId) : Int :=
  let children := getChildren a root
  if children.isEmpty then 1
  else (children.foldl (fun m c => max m (depth a c)) 0) + 1

/-- `root_distance(node, root)`: the number of `parent()` steps from `node` to `root` (0 if the root
is not reached). -/
partial def rootDistance (a : TArena) (node root : TNodeId) : Int :=
  if node == root then 0
  else match a.parent node with
    | some p => rootDistance a p root + 1
    | none => 0

/-- Shared part of `get_all_incoming_edges`/`get_all_outgoing_edges`. -/
private def levelEdges (a : TArena) (node : TNodeId) (g : TGraphId) (incoming : Bool) : Array TEdgeId :=
  Id.run do
    let nodeId := (a.node node).id
    let mut seen : Std.HashSet TEdgeId := {}
    let mut result := #[]
    for e in (a.graph g).edges do
      let (some s, some t) := ((a.edge e).source, (a.edge e).target) | continue
      if incoming then
        if (a.node t).id != nodeId then continue
      else
        if (a.node s).id != nodeId then continue
        if (a.node s).label == some "SUPER_ROOT" then continue
      if treeLevel a s == treeLevel a t then continue
      if !seen.contains e then
        seen := seen.insert e
        result := result.push e
    let otherX (e : TEdgeId) : Float :=
      let other := if incoming then (a.edge e).source else (a.edge e).target
      match other with
      | some n => (a.node n).position.x
      | none => fl0p0
    return stableSort result fun x y => Float.comparePartial (otherX x) (otherX y)

/-- `get_all_incoming_edges(node, graph)`: edges of the graph into a node with the same `id` that
cross tree levels, sorted by the x coordinate of their sources. -/
def getAllIncomingEdges (a : TArena) (node : TNodeId) (g : TGraphId) : Array TEdgeId :=
  levelEdges a node g true

/-- `get_all_outgoing_edges(node, graph)`: edges of the graph out of a node with the same `id` (not
the `SUPER_ROOT`) that cross tree levels, sorted by the x coordinate of their targets. -/
def getAllOutgoingEdges (a : TArena) (node : TNodeId) (g : TGraphId) : Array TEdgeId :=
  levelEdges a node g false

/-- `get_subtree(node)`: the nodes of the subtree in post-order (children first, the node last). -/
partial def getSubtree (a : TArena) (node : TNodeId) : Array TNodeId :=
  let children := getChildren a node
  if children.isEmpty then #[node]
  else (children.foldl (fun acc c => acc ++ getSubtree a c) #[]).push node

/-- `get_first_point(edge)`: the first bend point, else the target position. -/
def getFirstPoint (a : TArena) (e : TEdgeId) : KVector :=
  let edge := a.edge e
  match edge.bendPoints[0]? with
  | some p => p
  | none => match edge.target with
    | some t => (a.node t).position
    | none => {}

/-- `get_last_point(edge)`: the last bend point, else the source position. -/
def getLastPoint (a : TArena) (e : TEdgeId) : KVector :=
  let edge := a.edge e
  match edge.bendPoints.back? with
  | some p => p
  | none => match edge.source with
    | some s => (a.node s).position
    | none => {}

/-- `get_direction(graph)` (`unwrap_or(Down)`; the property default `UNDEFINED` wins). -/
def getDirection (a : TArena) (g : TGraphId) : Direction :=
  ((a.graph g).props.get MrTreeOptions.DIRECTION).getD .down

/-- `get_direction_vector(direction)`. -/
def getDirectionVector : Direction → KVector
  | .up => ⟨0.0, -1.0⟩
  | .right => ⟨1.0, 0.0⟩
  | .left => ⟨-1.0, 0.0⟩
  | _ => ⟨0.0, 1.0⟩

/-- `get_node_size_in_direction(node, direction)`: half the extent, signed by the direction. -/
def getNodeSizeInDirection (a : TArena) (n : TNodeId) (direction : Direction) : Float :=
  let size := (a.node n).size
  match direction with
  | .left => -size.x / 2.0
  | .up => -size.y / 2.0
  | .right => size.x / 2.0
  | _ => size.y / 2.0

/-- `get_node_size_vector_in_direction(node, direction)`. -/
def getNodeSizeVectorInDirection (a : TArena) (n : TNodeId) (direction : Direction) : KVector :=
  let size := (a.node n).size
  match direction with
  | .left => ⟨-size.x / 2.0, 0.0⟩
  | .up => ⟨0.0, -size.y / 2.0⟩
  | .right => ⟨size.x / 2.0, 0.0⟩
  | _ => ⟨0.0, size.y / 2.0⟩

/-- `turn_right(direction)`. -/
def turnRight : Direction → Direction
  | .left => .up
  | .up => .right
  | .right => .down
  | _ => .left

/-- `turn_left(direction)`. -/
def turnLeft : Direction → Direction
  | .right => .up
  | .up => .left
  | .left => .down
  | _ => .right

/-- `to_node_border(center, next, size)`: moves `center` towards `next` onto the border of a box of
`size` around it; returns the moved point. -/
def toNodeBorder (center next size : KVector) : KVector := Id.run do
  let wh := size.x / 2.0
  let hh := size.y / 2.0
  let absx := (next.x - center.x).abs
  let absy := (next.y - center.y).abs
  let mut xscale := 1.0
  let mut yscale := 1.0
  if absx > wh then xscale := wh / absx
  if absy > hh then yscale := hh / absy
  let scale := fmin xscale yscale
  return ⟨center.x + scale * (next.x - center.x), center.y + scale * (next.y - center.y)⟩

/-- `is_cycle_inducing(edge, graph)`: the edge does not point along the layout direction. -/
def isCycleInducing (a : TArena) (e : TEdgeId) (g : TGraphId) : Bool :=
  let dirVec := getDirectionVector (getDirection a g)
  let pos (n : Option TNodeId) : KVector := match n with
    | some n => (a.node n).position
    | none => {}
  let s := pos (a.edge e).source
  let t := pos (a.edge e).target
  let edgeVec : KVector := ⟨t.x - s.x, t.y - s.y⟩
  dirVec.dotProduct edgeVec <= 0.0

/-- `get_unique_long(a, b)`: `((a as u64) << 32) | (b as u32 as u64)` (two's complement of the
`i32` arguments). -/
def getUniqueLong (a b : Int) : UInt64 :=
  let au := UInt64.ofNat (a % (2 ^ 64 : Int)).toNat
  let bu := UInt64.ofNat (b % (2 ^ 32 : Int)).toNat
  (au <<< 32) ||| bu

/-- `get_lowest_parent(node, graph, direction)`: among the sources of the incoming edges, the one
whose centre projects furthest onto the direction vector (the first one on ties). -/
def getLowestParent (a : TArena) (node : TNodeId) (direction : Direction) : Option TNodeId := Id.run do
  let parents := (a.node node).incomingEdges.filterMap fun e => (a.edge e).source
  if parents.isEmpty then return none
  let dirVec := getDirectionVector direction
  let mut best : Option (Float × TNodeId) := none
  for p in parents do
    let pn := a.node p
    let center : KVector := ⟨pn.position.x + pn.size.x / fl2p0, pn.position.y + pn.size.y / fl2p0⟩
    let score := center.dotProduct dirVec
    let replace : Bool := match best with
      | some (bestScore, _) => score > bestScore
      | none => true
    if replace then best := some (score, p)
  return best.map (·.2)

/-- `get_left_most(current_level, depth)`: the first node `depth - 1` levels below the given level;
with a negative depth the first node of the deepest level. -/
partial def getLeftMost (a : TArena) (currentLevel : Array TNodeId) (depth : Int) : Option TNodeId :=
  if currentLevel.isEmpty then none
  else if depth > 1 then
    getLeftMost a (currentLevel.foldl (fun acc n => acc ++ a.children n) #[]) (depth - 1)
  else if depth < 0 then
    let nextLevel := currentLevel.foldl (fun acc n => acc ++ a.children n) #[]
    if !nextLevel.isEmpty then getLeftMost a nextLevel depth else currentLevel[0]?
  else currentLevel[0]?

end TreeUtil

end Elk.Alg.MrTree
