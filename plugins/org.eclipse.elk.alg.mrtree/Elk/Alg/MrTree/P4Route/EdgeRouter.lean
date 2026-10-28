import Std.Data.HashMap
import Std.Data.HashSet
import Elk.Core.Util.Java
import Elk.Core.Util.RustSort
import Elk.Alg.MrTree.TreeLayoutPhases
import Elk.Alg.MrTree.TreeUtil
import Elk.Alg.MrTree.Options.MrTreeOptions
import Elk.Alg.MrTree.P4Route.MultiLevelEdgeNodeNodeGap
/-!
# `org.eclipse.elk.alg.mrtree.p4route.EdgeRouter`

Port of `p4route/edge_router.rs` (elk-rs), the phase `P4_EDGE_ROUTING`. The mode is the graph's
`EDGE_ROUTING_MODE` (`unwrap_or(AVOID_OVERLAP)`):

* `NONE`: nothing;
* `MIDDLE_TO_MIDDLE`: every edge of the graph (`middle_to_middle_edge_route`) gets the centre of its
  source prepended and the centre of its target appended to its bend points; the first point is then
  moved onto the source border towards the second point, the last point onto the target border
  towards the (already moved) second to last point;
* `AVOID_OVERLAP` (`avoid_overlap`): Rust's restructured version of the Java router. The node data
  (`TREE_LEVEL`, position, size, `LEVELMIN`/`LEVELMAX`, `SUPER_ROOT` label) and the aggregate
  statistics are read once (`build_node_data`), the edges are classified once (`build_edge_maps`:
  end points, cycle inducing edges, outgoing/incoming edges crossing levels, without outgoing edges
  of the `SUPER_ROOT`) and the nodes of every tree level are sorted by their position along the level
  (`build_level_nodes`). Then (1) `avoid_overlap_set_start_points` prepends two start bend points to
  every outgoing level-crossing edge of every non-`SUPER_ROOT` node (sorted by the target position;
  with `COMPACT_LEVEL_ASCENSION` only the cycle inducing ones), (2) `avoid_overlap_special_edges`
  routes the edges spanning several levels through the node gaps (`MultiLevelEdgeNodeNodeGap`),
  edges within one level middle-to-middle and edges against the level order around the tree
  (`avoid_overlap_handle_cycle_inducing_edges`), (3) `avoid_overlap_set_end_points` appends the end
  bend points of every incoming level-crossing edge (sorted by its current last point). Finally every
  edge of the graph with fewer than two bend points is routed middle-to-middle.

Data layout (performance, same values and orders): Rust keys the node data and the edge maps by
pointer (`HashMap`s); here the nodes are addressed by *slot*, their index in the graph's node list
(`Slots`: the `id` that `DFSTreeifyer.init` sets is that index; nodes whose `id` does not point back at
them are found in a small map), and the edges by their index in the list of distinct edges with both
end points (first occurrences in graph edge order, which is the order in which every Rust loop over
the edges handles them). The node data are arrays by slot (`NodeTable`), the classification of the
edges arrays by edge index (`EdgeTable`), the level-crossing edges of a node an array per slot and
the levels arrays of slots; the cycle-inducing test is stored per edge. A node outside the graph's
node list has no slot and the Rust defaults (level 0, zero position and size, not the `SUPER_ROOT`).

Rust behaviour kept on purpose: the node data are a snapshot taken before routing (Rust `NodeData`);
the start of a multi-level edge after its first gap is `(0, 0)` (Rust's placeholder for the last
bend point); the horizontal "first node" test compares `start.y < first.x`; `TREE_LEVEL` is never
computed by the elk-rs pipeline (`LEVEL_PROC` is not configured), so unless the input sets it (or
the compaction moves nodes between levels) all nodes are on level 0 and `AVOID_OVERLAP` routes every
edge middle-to-middle. Every Rust `sort_by` with a `partial_cmp` comparator is reproduced with
`rustSortBy` (element size 8: `Arc` handles). The Rust pointer-keyed maps are keyed by the typed ids;
their iteration order is never observed.

`get_layout_processor_configuration` slots `LEVEL_COORDS`, `COMPACTION_PROC` and
`GRAPH_BOUNDS_PROC` before `P4_EDGE_ROUTING`.
-/
/-! Float literals as global constants (FL): inside branches, loops and specialised code the compiler
shares a literal's `Nat`/`Bool` arguments with unrelated variables (CSE) and then parses it on every
evaluation (`FastFloat.ofScientificImpl`); a top-level constant is a load (PLAN §7.1 items 17, 22). -/
private def fl0p0 : Float := 0.0
private def fl1p0 : Float := 1.0
private def fl2p0 : Float := 2.0

namespace Elk.Alg.MrTree.P4Route

open Elk.Core.Alg Elk.Core.Util Elk.Core.Math Elk.Core.Options Elk.Alg.MrTree Elk.Alg.MrTree.Graph
open Elk.Alg.MrTree.Options Elk.Alg.MrTree.Intermediate

namespace EdgeRouter

/-- `EdgeRouter::ONE_HALF`. -/
def ONE_HALF : Float := 0.5
/-- `EdgeRouter::STEEP_END_EDGE_THRESHOLD_DISTANCE`. -/
def STEEP_END_EDGE_THRESHOLD_DISTANCE : Float := 50.0
/-- `EdgeRouter::STEEP_END_EDGE_RATIO`. -/
def STEEP_END_EDGE_RATIO : Float := 5.3
/-- `EdgeRouter::STEEP_END_EDGE_SAMPLE_HEIGHT`. -/
def STEEP_END_EDGE_SAMPLE_HEIGHT : Float := 40.0

/-- `NodeData`: the node data read once by `build_node_data`. -/
structure NodeData where
  level : Int
  pos : KVector
  size : KVector
  levelMin : Float
  levelMax : Float
  isSuperRoot : Bool
  deriving Inhabited

/-- `GraphStats`. -/
structure GraphStats where
  avgCenterH : Float
  avgCenterV : Float
  maxExtentH : Float
  maxExtentV : Float
  minExtentH : Float
  minExtentV : Float

namespace GraphStats

/-- `average_center(horizontal)`. -/
@[inline] def averageCenter (s : GraphStats) (horizontal : Bool) : Float :=
  if horizontal then s.avgCenterH else s.avgCenterV

/-- `max_node_extent(horizontal, padding)`. -/
@[inline] def maxNodeExtent (s : GraphStats) (horizontal : Bool) (padding : Float) : Float :=
  if horizontal then s.maxExtentH + padding else s.maxExtentV + padding

/-- `min_node_extent(horizontal, padding)`. -/
@[inline] def minNodeExtent (s : GraphStats) (horizontal : Bool) (padding : Float) : Float :=
  if horizontal then s.minExtentH - padding else s.minExtentV - padding

end GraphStats

/-- The slot of a node: its index in the graph's node list. `id` holds the slot of every node that
`DFSTreeifyer.init` numbered (`nodes[id] = node`); the other nodes of the list (the `SUPER_ROOT`, id
0) are in `extra`. Nodes outside the list have no slot. -/
structure Slots where
  nodes : Array TNodeId
  extra : Std.HashMap TNodeId Nat

namespace Slots

/-- The slots of the node list. -/
def build (a : TArena) (nodes : Array TNodeId) : Slots := Id.run do
  let mut extra : Std.HashMap TNodeId Nat := {}
  for h : i in [0:nodes.size] do
    let n := nodes[i]
    let id := (a.node n).id
    let byId := id >= 0 && nodes[id.toNat]? == some n
    if !byId then extra := extra.insert n i
  return { nodes, extra }

/-- The slot of a node (`none` outside the node list). -/
@[inline] def get? (s : Slots) (a : TArena) (n : TNodeId) : Option Nat :=
  let id := (a.node n).id
  if id >= 0 && s.nodes[id.toNat]? == some n then some id.toNat else s.extra.get? n

end Slots

/-- `build_node_data`'s map as an array by slot (see `Slots`). -/
abbrev NodeTable := Array NodeData

/-- `build_node_data(nodes)`: the data of every slot and the aggregate statistics (over the node list,
duplicates included, like Rust's loop). -/
def buildNodeData (a : TArena) (nodes : Array TNodeId) : NodeTable × GraphStats := Id.run do
  let mut data : NodeTable := Array.mkEmpty nodes.size
  let mut sumH := fl0p0
  let mut sumV := fl0p0
  let mut maxH := Float.minValue
  let mut maxV := Float.minValue
  let mut minH := Float.maxValue
  let mut minV := Float.maxValue
  let mut count := 0
  for node in nodes do
    let n := a.node node
    let level := (n.props.get MrTreeOptions.TREE_LEVEL).getD 0
    let pos := n.position
    let size := n.size
    let isSuperRoot := n.label == some "SUPER_ROOT"
    sumH := sumH + (pos.y + size.y / fl2p0)
    sumV := sumV + (pos.x + size.x / fl2p0)
    let extH := pos.y + size.y
    let extV := pos.x + size.x
    if extH > maxH then maxH := extH
    if extV > maxV then maxV := extV
    if pos.y < minH then minH := pos.y
    if pos.x < minV then minV := pos.x
    count := count + 1
    data := data.push
      { level, pos, size, levelMin := n.internal.levelMin, levelMax := n.internal.levelMax, isSuperRoot }
  let stats : GraphStats := if count > 0 then
      { avgCenterH := sumH / Float.ofNat count, avgCenterV := sumV / Float.ofNat count,
        maxExtentH := maxH, maxExtentV := maxV, minExtentH := minH, minExtentV := minV }
    else
      { avgCenterH := fl0p0, avgCenterV := fl0p0, maxExtentH := fl0p0, maxExtentV := fl0p0,
        minExtentH := fl0p0, minExtentV := fl0p0 }
  return (data, stats)

/-- The missing slot (`Nat` sentinel of the edge table). -/
def NO_SLOT : Nat := 0x7FFFFFFF

/-- `nd_level` of a slot. -/
@[inline] def ndLevel (nd : NodeTable) (s : Nat) : Int := (nd[s]?.map (·.level)).getD 0
/-- `nd_pos`. -/
@[inline] def ndPos (nd : NodeTable) (s : Nat) : KVector := (nd[s]?.map (·.pos)).getD {}
/-- `nd_size`. -/
@[inline] def ndSize (nd : NodeTable) (s : Nat) : KVector := (nd[s]?.map (·.size)).getD {}
/-- `nd_level_min`. -/
@[inline] def ndLevelMin (nd : NodeTable) (s : Nat) : Float := (nd[s]?.map (·.levelMin)).getD fl0p0
/-- `nd_level_max`. -/
@[inline] def ndLevelMax (nd : NodeTable) (s : Nat) : Float := (nd[s]?.map (·.levelMax)).getD fl0p0
/-- `nd_is_super_root`. -/
@[inline] def ndIsSuperRoot (nd : NodeTable) (s : Nat) : Bool := (nd[s]?.map (·.isSuperRoot)).getD false

/-- `EdgeMaps` as arrays: the distinct edges with both end points in first-occurrence order (`edges`,
the keys of Rust's `endpoints`) with their end points and their slots (`NO_SLOT` outside the node
list), the `cycle_inducing` flag per edge, and per node slot the indices of its level-crossing
`outgoing` (not for the `SUPER_ROOT`) and `incoming` edges, in edge order. -/
structure EdgeTable where
  edges : Array TEdgeId := #[]
  sourceSlot : Array Nat := #[]
  targetSlot : Array Nat := #[]
  cycleInducing : Array Bool := #[]
  outgoing : Array (Array Nat) := #[]
  incoming : Array (Array Nat) := #[]

/-- `build_edge_maps(edges, nd, direction)`. -/
def buildEdgeMaps (a : TArena) (slots : Slots) (edges : Array TEdgeId) (nd : NodeTable)
    (direction : Direction) : EdgeTable := Id.run do
  let dirVec := TreeUtil.getDirectionVector direction
  let n := nd.size
  let mut em : EdgeTable := { outgoing := Array.replicate n #[], incoming := Array.replicate n #[] }
  let mut seen : Std.HashSet TEdgeId := Std.HashSet.emptyWithCapacity edges.size
  for edge in edges do
    if seen.contains edge then continue
    seen := seen.insert edge
    let (some source, some target) := ((a.edge edge).source, (a.edge edge).target) | continue
    let ss := (slots.get? a source).getD NO_SLOT
    let ts := (slots.get? a target).getD NO_SLOT
    let sourceLevel := ndLevel nd ss
    let targetLevel := ndLevel nd ts
    let sourceIsSuperRoot := ndIsSuperRoot nd ss
    let sourcePos := ndPos nd ss
    let targetPos := ndPos nd ts
    let edgeVec : KVector := ⟨targetPos.x - sourcePos.x, targetPos.y - sourcePos.y⟩
    let k := em.edges.size
    em := { em with
      edges := em.edges.push edge, sourceSlot := em.sourceSlot.push ss, targetSlot := em.targetSlot.push ts
      cycleInducing := em.cycleInducing.push (dirVec.dotProduct edgeVec <= fl0p0) }
    if sourceLevel != targetLevel then
      -- both end points of a level-crossing edge are on a level other than the default 0 of a
      -- missing slot only if they have slots; the lists of nodes without a slot are never read
      if !sourceIsSuperRoot && ss < n then
        em := { em with outgoing := em.outgoing.modify ss (·.push k) }
      if ts < n then
        em := { em with incoming := em.incoming.modify ts (·.push k) }
  return em

/-- Whether the keys are in non-decreasing order (no key is NaN). -/
private def keysSorted (keys : FloatArray) (i : Nat) : Bool :=
  if h : i + 1 < keys.size then
    if keys[i] <= keys[i + 1] then keysSorted keys (i + 1) else false
  else true
  termination_by keys.size - i

/-- Whether some key is NaN. -/
private def keysHaveNaN (keys : FloatArray) (i : Nat) : Bool :=
  if h : i < keys.size then
    if keys[i].isNaN then true else keysHaveNaN keys (i + 1)
  else false
  termination_by keys.size - i

/-- Merges the sorted index runs `src[i..iEnd)` and `src[j..jEnd)` into `dst` from `k` on; an
element of the right run goes first only if its key is strictly smaller (stable). -/
private partial def mergeRuns (keys : FloatArray) (src dst : Array Nat) (i iEnd j jEnd k : Nat) :
    Array Nat :=
  if i < iEnd then
    if j < jEnd then
      let a := src[i]!
      let b := src[j]!
      if keys.get! b < keys.get! a then
        mergeRuns keys src (dst.set! k b) i iEnd (j + 1) jEnd (k + 1)
      else
        mergeRuns keys src (dst.set! k a) (i + 1) iEnd j jEnd (k + 1)
    else mergeRuns keys src (dst.set! k src[i]!) (i + 1) iEnd j jEnd (k + 1)
  else if j < jEnd then mergeRuns keys src (dst.set! k src[j]!) i iEnd (j + 1) jEnd (k + 1)
  else dst

/-- One bottom-up merge pass with run width `w`, from `lo` on. -/
private partial def mergePass (keys : FloatArray) (src dst : Array Nat) (w lo : Nat) : Array Nat :=
  let n := src.size
  if lo < n then
    let mid := min (lo + w) n
    let hi := min (lo + 2 * w) n
    mergePass keys src (mergeRuns keys src dst lo mid mid hi lo) w (lo + 2 * w)
  else dst

/-- Bottom-up merge passes until one run covers everything. -/
private partial def mergeAll (keys : FloatArray) (src dst : Array Nat) (w : Nat) : Array Nat :=
  if w < src.size then
    let merged := mergePass keys src dst w 0
    mergeAll keys merged src (2 * w)
  else src

/-- The indices `0 .. keys.size` stably sorted by their keys (no key is NaN): a stable merge sort,
so the permutation equals that of every stable sort with the comparator
`Float.comparePartial`. -/
private def sortIndicesByKeys (keys : FloatArray) : Array Nat :=
  let idx := Array.range keys.size
  mergeAll keys idx (Array.replicate keys.size 0) 1

/-- `sort_by` with a `partial_cmp` comparator on `key` (Rust panics on an order violation). The
keys are computed once per element (`key` is pure). Without NaN keys the comparator is a total
preorder, for which every stable sort (Rust `sort_by` included) yields the same permutation: the
input is returned as is when it is already sorted, otherwise it is sorted with a local stable merge
sort on the keys (`sortIndicesByKeys`). With
a NaN key (inconsistent comparator) the exact Rust algorithm (`rustSortBy`, element size 8) runs. -/
private def sortByFloat {α : Type} [Inhabited α] (xs : Array α) (key : α → Float) : MrTreeM (Array α) :=
  -- no comparison happens for fewer than two elements (every path returns the input)
  if xs.size < 2 then pure xs else
  let keys : FloatArray := xs.foldl (init := FloatArray.emptyWithCapacity xs.size) fun ks x => ks.push (key x)
  if keysHaveNaN keys 0 then
    let keyed := xs.map fun x => (key x, x)
    match rustSortBy keyed fun x y => Float.comparePartial x.1 y.1 with
    | .ok s => pure (s.map (·.2))
    | .error e => throw (IO.userError e)
  else if keysSorted keys 0 then
    pure xs
  else
    pure ((sortIndicesByKeys keys).map fun i => xs[i]!)

/-- `build_level_nodes(nodes, nd, direction)`: the nodes of every level (as slots; a node listed twice
twice), sorted by position. -/
def buildLevelNodes (nodeSlots : Array Nat) (nd : NodeTable) (direction : Direction) :
    MrTreeM (Array (Array Nat)) := do
  let maxLevel : Int := nodeSlots.foldl (fun m n => match m with
    | some v => some (max v (ndLevel nd n))
    | none => some (ndLevel nd n)) none |>.getD 0
  let len := (max (maxLevel + 1) 0).toNat
  let mut levels : Array (Array Nat) := Array.replicate len #[]
  for node in nodeSlots do
    let level := ndLevel nd node
    if level >= 0 && level.toNat < len then
      levels := levels.modify level.toNat (·.push node)
  let mut sorted : Array (Array Nat) := #[]
  for levelVec in levels do
    sorted := sorted.push (← sortByFloat levelVec fun n =>
      if direction.isHorizontal then (ndPos nd n).y else (ndPos nd n).x)
  return sorted

/-- `middle_to_middle_edge_route(edge)`. -/
def middleToMiddleEdgeRoute (edge : TEdgeId) : MrTreeM Unit := do
  let e ← MrTreeM.getEdge edge
  let (some source, some target) := (e.source, e.target) | return
  let s ← MrTreeM.getNode source
  let t ← MrTreeM.getNode target
  let sourcePoint : KVector := ⟨s.position.x + s.size.x / 2.0, s.position.y + s.size.y / 2.0⟩
  let targetPoint : KVector := ⟨t.position.x + t.size.x / 2.0, t.position.y + t.size.y / 2.0⟩
  MrTreeM.modifyEdge edge fun x => Id.run do
    let mut bps := (x.bendPoints.addFirst sourcePoint).addLast targetPoint
    if bps.size >= 2 then
      let sourceBorder := TreeUtil.toNodeBorder bps[0]! bps[1]! s.size
      bps := bps.set! 0 sourceBorder
      let lastIndex := bps.size - 1
      let targetBorder := TreeUtil.toNodeBorder bps[lastIndex]! bps[lastIndex - 1]! t.size
      bps := bps.set! lastIndex targetBorder
    return { x with bendPoints := bps }

/-- `middle_to_middle(graph)`. -/
def middleToMiddle (graph : TGraphId) : MrTreeM Unit := do
  for edge in (← MrTreeM.getGraph graph).edges do
    middleToMiddleEdgeRoute edge

/-- Appends a bend point to an edge. -/
@[inline] private def addBend (edge : TEdgeId) (x y : Float) : MrTreeM Unit :=
  MrTreeM.modifyEdge edge fun e => { e with bendPoints := e.bendPoints.addValues x y }

/-- Prepends a bend point to an edge. -/
@[inline] private def addFirstBend (edge : TEdgeId) (x y : Float) : MrTreeM Unit :=
  MrTreeM.modifyEdge edge fun e => { e with bendPoints := e.bendPoints.addFirst ⟨x, y⟩ }

/-- The current bend points of an edge. -/
@[inline] private def bendsOf (edge : TEdgeId) : MrTreeM KVectorChain := do
  return (← MrTreeM.getEdge edge).bendPoints

/-- `avoid_overlap_handle_cycle_inducing_edges(...)`: returns the updated side counters. -/
def handleCycleInducingEdges (edge : TEdgeId) (source target : Nat) (direction : Direction)
    (sideEdges : Int × Int) (pad tex : Float) (inOuts : Int × Int) (nd : NodeTable) (stats : GraphStats) :
    MrTreeM (Int × Int) := do
  let mut sideOneEdges := sideEdges.1
  let mut sideTwoEdges := sideEdges.2
  let sourcePos := ndPos nd source
  let sourceSize := ndSize nd source
  let targetPos := ndPos nd target
  let targetSize := ndSize nd target
  let mut bendTmp := fl0p0
  if direction.isHorizontal then
    let middleTree := stats.averageCenter true
    if sourcePos.y + sourceSize.y / fl2p0 > middleTree then
      sideTwoEdges := sideTwoEdges + 1
      bendTmp := stats.maxNodeExtent true (pad * Float.ofInt sideTwoEdges)
    else
      sideOneEdges := sideOneEdges + 1
      bendTmp := stats.minNodeExtent true (pad * Float.ofInt sideOneEdges)
  else
    let middleTree := stats.averageCenter false
    if sourcePos.x + sourceSize.x / fl2p0 > middleTree then
      sideTwoEdges := sideTwoEdges + 1
      bendTmp := stats.maxNodeExtent false (pad * Float.ofInt sideTwoEdges)
    else
      sideOneEdges := sideOneEdges + 1
      bendTmp := stats.minNodeExtent false (pad * Float.ofInt sideOneEdges)
  match direction with
  | .left =>
    let levelMin := ndLevelMin nd source
    addBend edge (levelMin - pad) bendTmp
    addBend edge (targetPos.x + targetSize.x + pad + tex) bendTmp
    addBend edge (targetPos.x + targetSize.x + pad + tex) (targetPos.y + targetSize.y / fl2p0)
    addBend edge (targetPos.x + targetSize.x) (targetPos.y + targetSize.y / fl2p0)
  | .right =>
    let levelMax := ndLevelMax nd source
    addBend edge (levelMax + pad) (sourcePos.y + sourceSize.y / fl2p0)
    addBend edge (sourcePos.x + sourceSize.x + pad) bendTmp
    addBend edge (targetPos.x - pad - tex) bendTmp
    addBend edge (targetPos.x - pad - tex) (targetPos.y + targetSize.y / fl2p0)
    addBend edge targetPos.x (targetPos.y + targetSize.y / fl2p0)
  | .up =>
    let levelMin := ndLevelMin nd source
    addBend edge bendTmp (levelMin - pad)
    addBend edge bendTmp (targetPos.y + targetSize.y + pad + tex)
    addBend edge (targetPos.x + targetSize.x / fl2p0) (targetPos.y + targetSize.y + pad + tex)
    addBend edge (targetPos.x + targetSize.x / fl2p0) (targetPos.y + targetSize.y + pad)
  | _ =>
    let outs := Float.ofInt inOuts.2
    let ins := Float.ofInt inOuts.1
    let bends ← bendsOf edge
    if !bends.isEmpty then
      let last := bends.last!
      let last : KVector := { last with y := ndLevelMax nd source + pad * outs }
      MrTreeM.modifyEdge edge fun e => { e with bendPoints := e.bendPoints.set! (e.bendPoints.size - 1) last }
    addBend edge bendTmp (ndLevelMax nd source + pad * outs)
    addBend edge bendTmp (targetPos.y - pad * ins - tex)
  return (sideOneEdges, sideTwoEdges)

/-- `avoid_overlap_special_edges(...)`. -/
def avoidOverlapSpecialEdges (direction : Direction) (pad tex : Float) (slots : Slots) (nd : NodeTable)
    (stats : GraphStats) (graphBounds : Float × Float × Float × Float) (em : EdgeTable)
    (levelNodes : Array (Array Nat)) : MrTreeM Unit := do
  let (graphXmin, graphXmax, graphYmin, graphYmax) := graphBounds
  let horizontal := direction.isHorizontal
  let mut sideOneEdges : Int := 0
  let mut sideTwoEdges : Int := 0
  let mut nodeGaps : Std.HashMap UInt64 MultiLevelEdgeNodeNodeGap := {}
  let maxLevel := levelNodes.size
  let mut outsPerLevel : Array Int := Array.replicate maxLevel 0
  let mut insPerLevel : Array Int := Array.replicate maxLevel 0
  for h : k in [0:em.edges.size] do
    let edge := em.edges[k]
    let source := em.sourceSlot[k]!
    let target := em.targetSlot[k]!
    let sourceLevel := ndLevel nd source
    let targetLevel := ndLevel nd target
    let levelDiff := targetLevel - sourceLevel
    if levelDiff > 1 then
      let mut hasBends := false
      let sourcePos := ndPos nd source
      let targetPos := ndPos nd target
      for k in [0:(levelDiff - 1).toNat] do
        let curLevel := sourceLevel + 1 + (k : Int)
        let nextLevelNodes : Array Nat :=
          if curLevel >= 0 && curLevel.toNat < levelNodes.size then levelNodes[curLevel.toNat]! else #[]
        let interpolation := Float.ofInt (curLevel - sourceLevel) / Float.ofInt (targetLevel - sourceLevel)
        let mut index := 0
        while index < nextLevelNodes.size do
          let pos := ndPos nd nextLevelNodes[index]!
          let projection := if horizontal
            then sourcePos.y * (fl1p0 - interpolation) + targetPos.y * interpolation
            else sourcePos.x * (fl1p0 - interpolation) + targetPos.x * interpolation
          if (if horizontal then pos.y else pos.x) > projection then break
          index := index + 1
        if !nextLevelNodes.isEmpty then
          let start : KVector := if hasBends then {} else sourcePos
          let lastNode := nextLevelNodes[nextLevelNodes.size - 1]!
          let firstNode := nextLevelNodes[0]!
          let lastPos := ndPos nd lastNode
          let lastSize := ndSize nd lastNode
          let last : KVector := ⟨lastPos.x + lastSize.x, lastPos.y + lastSize.y⟩
          let firstPos := ndPos nd firstNode
          let firstSize := ndSize nd firstNode
          let first : KVector := ⟨firstPos.x + firstSize.x, firstPos.y + firstSize.y⟩
          if horizontal then
            if index >= nextLevelNodes.size - 1 && start.y > last.y && targetPos.y > last.y then continue
            if index == 0 && start.y < first.x && targetPos.y < first.y then continue
          else
            if index >= nextLevelNodes.size - 1 && start.x > last.x && targetPos.x > last.x then continue
            if index == 0 && start.x < first.x && targetPos.x < first.x then continue
        let bends ← bendsOf edge
        let firstIndex := bends.size
        let secondIndex := bends.size + 1
        MrTreeM.modifyEdge edge fun e => { e with bendPoints := (e.bendPoints.push {}).push {} }
        hasBends := true
        let key := TreeUtil.getUniqueLong curLevel (index : Int)
        -- the neighbours of a gap are those of its key (level, index): `neighborOne`/`neighborTwo` of
        -- a stored gap equal `slotOne`/`slotTwo` here
        let slotOne := if index == 0 then none else some nextLevelNodes[index - 1]!
        let slotTwo := if index >= nextLevelNodes.size then none else some nextLevelNodes[index]!
        let gap ← match nodeGaps.get? key with
          | some gap => gap.addBendPoints edge firstIndex secondIndex
          | none =>
            MultiLevelEdgeNodeNodeGap.create (slotOne.map (slots.nodes[·]!)) (slotTwo.map (slots.nodes[·]!))
              edge firstIndex secondIndex direction pad
        nodeGaps := nodeGaps.insert key gap
        if !horizontal then
          if gap.onFirstNodeSide then
            if let some n2 := slotTwo then
              if (ndPos nd n2).x <= graphXmin then sideOneEdges := sideOneEdges + 1
          if gap.onLastNodeSide then
            if let some n1 := slotOne then
              if (ndPos nd n1).x + (ndSize nd n1).x >= graphXmax then sideTwoEdges := sideTwoEdges + 1
        else
          if gap.onFirstNodeSide then
            if let some n2 := slotTwo then
              if (ndPos nd n2).y <= graphYmin then sideOneEdges := sideOneEdges + 1
          if gap.onLastNodeSide then
            if let some n1 := slotOne then
              if (ndPos nd n1).y + (ndSize nd n1).y >= graphYmax then sideTwoEdges := sideTwoEdges + 1
    else if levelDiff == 0 then
      middleToMiddleEdgeRoute edge
    else if levelDiff < 0 then
      let sourceLevelN := (max sourceLevel 0).toNat
      let targetLevelN := (max targetLevel 0).toNat
      if sourceLevelN < outsPerLevel.size then
        outsPerLevel := outsPerLevel.modify sourceLevelN (· + 1)
      if targetLevelN < insPerLevel.size then
        insPerLevel := insPerLevel.modify targetLevelN (· + 1)
      let inOuts := (insPerLevel[targetLevelN]?.getD 0, outsPerLevel[sourceLevelN]?.getD 0)
      let (s1, s2) ← handleCycleInducingEdges edge source target direction (sideOneEdges, sideTwoEdges)
        pad tex inOuts nd stats
      sideOneEdges := s1
      sideTwoEdges := s2

/-- `avoid_overlap_set_start_points(...)`. -/
def avoidOverlapSetStartPoints (direction : Direction) (pad : Float) (nd : NodeTable) (em : EdgeTable)
    (nodes : Array TNodeId) (nodeSlots : Array Nat) : MrTreeM Unit := do
  for h : j in [0:nodes.size] do
    let node := nodes[j]
    let slot := nodeSlots[j]!
    if ndIsSuperRoot nd slot then continue
    let outs := em.outgoing[slot]?.getD #[]
    let targetCoord (k : Nat) : Float :=
      let t := em.targetSlot[k]!
      if direction.isHorizontal then (ndPos nd t).y else (ndPos nd t).x
    let outs ← sortByFloat outs targetCoord
    let skip := (← MrTreeM.getNode node).internal.compactLevelAscension
    let num := outs.size
    for i in [0:num] do
      let k := outs[i]!
      let edge := em.edges[k]!
      if skip && !em.cycleInducing[k]! then continue
      let interpolation := if num == 1 then ONE_HALF else Float.ofNat (i + 1) / Float.ofNat (num + 1)
      let pos := ndPos nd slot
      let size := ndSize nd slot
      let levelMin := ndLevelMin nd slot
      let levelMax := ndLevelMax nd slot
      match direction with
      | .left =>
        let y := pos.y + size.y * interpolation
        addFirstBend edge (fmin levelMin (pos.x - pad)) y
        addFirstBend edge pos.x y
      | .right =>
        let y := pos.y + size.y * interpolation
        addFirstBend edge (levelMax + pad) y
        addFirstBend edge (pos.x + size.x) y
      | .up =>
        let x := pos.x + size.x * interpolation
        addFirstBend edge x (fmin (pos.y - pad) levelMin)
        addFirstBend edge x pos.y
      | _ =>
        let x := pos.x + size.x * interpolation
        addFirstBend edge x (levelMax + pad)
        addFirstBend edge x (pos.y + size.y)

/-- The steep end-edge correction of `avoid_overlap_set_end_points` for the horizontal directions:
`some (x, y)` of the extra bend point. -/
private def steepHorizontal (last : KVector) (pos size : KVector) (tex interpolation xOffset : Float) :
    Option (Float × Float) :=
  let nextX := pos.x + size.x / 2.0
  let nextY := pos.y + size.y / 2.0
  let denom := (last.x - nextX).abs / STEEP_END_EDGE_SAMPLE_HEIGHT
  if tex > 0.0 && (last.y - nextY).abs / denom > STEEP_END_EDGE_THRESHOLD_DISTANCE then
    if nextY > last.y then some (xOffset, pos.y + size.y * interpolation - tex / 2.0)
    else some (xOffset, pos.y + size.y * interpolation + tex / 2.0)
  else none

/-- The steep end-edge correction for the vertical directions. -/
private def steepVertical (last : KVector) (pos size : KVector) (tex interpolation yOffset : Float) :
    Option (Float × Float) :=
  let nextX := pos.x + size.x / 2.0
  let nextY := pos.y + size.y / 2.0
  let denom := (last.y - nextY).abs / STEEP_END_EDGE_SAMPLE_HEIGHT
  if tex > 0.0 && (last.x - nextX).abs / denom > STEEP_END_EDGE_THRESHOLD_DISTANCE then
    if nextX > last.x then some (pos.x + size.x * interpolation - tex / 2.0, yOffset)
    else some (pos.x + size.x * interpolation + tex / 2.0, yOffset)
  else none

/-- `avoid_overlap_set_end_points(...)`. -/
def avoidOverlapSetEndPoints (direction : Direction) (pad tex : Float) (nd : NodeTable) (em : EdgeTable)
    (nodeSlots : Array Nat) : MrTreeM Unit := do
  for slot in nodeSlots do
    if ndIsSuperRoot nd slot then continue
    let ins := em.incoming[slot]?.getD #[]
    let ins ← if ins.size < 2 then pure ins else do
      let a ← get
      sortByFloat ins fun k =>
        let e := em.edges[k]!
        if direction.isHorizontal then (TreeUtil.getLastPoint a e).y else (TreeUtil.getLastPoint a e).x
    let num := ins.size
    for i in [0:num] do
      let k := ins[i]!
      let edge := em.edges[k]!
      let isCycleInducing := em.cycleInducing[k]!
      let interpolation := if num == 1 then ONE_HALF else Float.ofNat (i + 1) / Float.ofNat (num + 1)
      let pos := ndPos nd slot
      let size := ndSize nd slot
      let levelMin := ndLevelMin nd slot
      let levelMax := ndLevelMax nd slot
      let bends ← bendsOf edge
      match direction with
      | .left =>
        if pos.x + size.x + tex < levelMax then
          addBend edge (levelMax + pad) (pos.y + size.y * interpolation)
        else if !bends.isEmpty then
          if let some (x, y) := steepHorizontal bends.last! pos size tex interpolation
              (pos.x + size.x + tex / STEEP_END_EDGE_RATIO) then
            addBend edge x y
        addBend edge (pos.x + size.x) (pos.y + size.y * interpolation)
      | .right =>
        if pos.x - tex > levelMin then
          addBend edge (levelMin - pad) (pos.y + size.y * interpolation)
        else if !bends.isEmpty then
          if let some (x, y) := steepHorizontal bends.last! pos size tex interpolation
              (pos.x - tex / STEEP_END_EDGE_RATIO) then
            addBend edge x y
        addBend edge pos.x (pos.y + size.y * interpolation)
      | .up =>
        if pos.y + size.y + tex < levelMax then
          addBend edge (pos.x + size.x * interpolation) (levelMax + pad)
        else if !bends.isEmpty then
          if let some (x, y) := steepVertical bends.last! pos size tex interpolation
              (pos.y + tex / STEEP_END_EDGE_RATIO + size.y) then
            addBend edge x y
        addBend edge (pos.x + size.x * interpolation) (pos.y + size.y)
      | _ =>
        if isCycleInducing then
          if !bends.isEmpty then
            addBend edge (pos.x + size.x * interpolation) bends.last!.y
        else if pos.y - tex > levelMin then
          addBend edge (pos.x + size.x * interpolation) (levelMin - pad)
        else if !bends.isEmpty then
          if let some (x, y) := steepVertical bends.last! pos size tex interpolation
              (pos.y - tex / STEEP_END_EDGE_RATIO) then
            addBend edge x y
        addBend edge (pos.x + size.x * interpolation) pos.y

/-- The slots, the slot of every listed node, the node data, the statistics and the edge table of
`avoid_overlap` (a pure function of the arena, which is released before the routing writes). -/
def prepare (a : TArena) (nodes : Array TNodeId) (edges : Array TEdgeId) (direction : Direction) :
    Slots × Array Nat × NodeTable × GraphStats × EdgeTable :=
  let slots := Slots.build a nodes
  -- every listed node has a slot (`Slots.get?` finds `nodes[i]` at its `id` or in `extra`)
  let nodeSlots := nodes.map fun n => (slots.get? a n).getD NO_SLOT
  let (nd, stats) := buildNodeData a nodes
  (slots, nodeSlots, nd, stats, buildEdgeMaps a slots edges nd direction)

/-- `avoid_overlap(graph)`. -/
def avoidOverlap (graph : TGraphId) : MrTreeM Unit := do
  let g ← MrTreeM.getGraph graph
  let nodes := g.nodes
  let edges := g.edges
  let pad := (g.props.get MrTreeOptions.SPACING_EDGE_NODE).getD 0.0
  let tex := (g.props.get MrTreeOptions.EDGE_END_TEXTURE_LENGTH).getD 0.0
  let direction := (g.props.get MrTreeOptions.DIRECTION).getD .down
  let graphBounds := (g.internal.graphXmin, g.internal.graphXmax, g.internal.graphYmin, g.internal.graphYmax)
  let (slots, nodeSlots, nd, stats, em) := prepare (← get) nodes edges direction
  let levelNodes ← buildLevelNodes nodeSlots nd direction
  avoidOverlapSetStartPoints direction pad nd em nodes nodeSlots
  avoidOverlapSpecialEdges direction pad tex slots nd stats graphBounds em levelNodes
  avoidOverlapSetEndPoints direction pad tex nd em nodeSlots

/-- `EdgeRouter::process`. -/
def process (graph : TGraphId) (monitor : ProgressMonitor) : MrTreeM Unit := do
  discard <| monitor.begin "Edge routing" 1.0
  let mode := ((← MrTreeM.getGraph graph).props.get MrTreeOptions.EDGE_ROUTING_MODE).getD .avoidOverlap
  match mode with
  | .none => pure ()
  | .middleToMiddle => middleToMiddle graph
  | .avoidOverlap =>
    avoidOverlap graph
    for edge in (← MrTreeM.getGraph graph).edges do
      if (← bendsOf edge).size < 2 then middleToMiddleEdgeRoute edge
  monitor.done

/-- `get_layout_processor_configuration`. -/
def configuration : TreeProcessorConfiguration :=
  let c : TreeProcessorConfiguration := LayoutProcessorConfiguration.create
  let c := c.addBefore TreeLayoutPhases.p4EdgeRouting IntermediateProcessorStrategy.levelCoords
  let c := c.addBefore TreeLayoutPhases.p4EdgeRouting IntermediateProcessorStrategy.compactionProc
  c.addBefore TreeLayoutPhases.p4EdgeRouting IntermediateProcessorStrategy.graphBoundsProc

/-- The `EdgeRouter` phase. -/
def phase : TreePhase :=
  { name := "EdgeRouter", process, getLayoutProcessorConfiguration := fun _ => pure (some configuration) }

end EdgeRouter

end Elk.Alg.MrTree.P4Route
