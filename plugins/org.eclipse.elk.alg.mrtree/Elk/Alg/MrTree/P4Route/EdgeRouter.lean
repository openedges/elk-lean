import Std.Data.HashMap
import Std.Data.HashSet
import Elk.Core.Util.Java
import Elk.Alg.MrTree.TreeLayoutPhases
import Elk.Alg.MrTree.TreeUtil
import Elk.Alg.MrTree.Options.MrTreeOptions
import Elk.Alg.MrTree.P4Route.MultiLevelEdgeNodeNodeGap
import Elk.Core.Util.FloatConst
open Elk.Core.Util.FloatConst
/-!
# `org.eclipse.elk.alg.mrtree.p4route.EdgeRouter`

The phase `P4_EDGE_ROUTING` of ELK Java (`EdgeRouter.java`; elk-rs `p4route/edge_router.rs` was the
code reference, ELK Java decides where they differ). The mode is the graph's `EDGE_ROUTING_MODE`:

* `NONE`: nothing;
* `MIDDLE_TO_MIDDLE`: every entry of the graph's edge list (`middleToMiddleEdgeRoute`) gets the
  centre of its source prepended and the centre of its target appended to its bend points; the first
  point is then moved onto the source border towards the second point, the last point onto the target
  border towards the (already moved) second to last point;
* `AVOID_OVERLAP` (`avoidOverlap`): (1) `avoidOverlapSetStartPoints` prepends two start bend points to
  the outgoing level-crossing edges of every non-`SUPER_ROOT` node (with `COMPACT_LEVEL_ASCENSION`
  only to the cycle inducing ones), (2) `avoidOverlapSpecialEdges` routes the edges spanning several
  levels through the node gaps (`MultiLevelEdgeNodeNodeGap`), edges within one level middle-to-middle
  and edges against the level order around the tree (`avoidOverlapHandleCycleInducingEdges`), (3)
  `avoidOverlapSetEndPoints` appends the end bend points of the incoming level-crossing edges. Finally
  every edge of the list with fewer than two bend points is routed middle-to-middle.

ELK Java details (elk-rs restructured the router and differs in all of them):

* `TreeUtil.getAllOutgoingEdges(n)`/`getAllIncomingEdges(n)` scan the graph's edges for those whose
  source/target has the **`id`** of `n` (not the node itself), whose end points' `TREE_LEVEL`
  `Integer`s differ by `!=` (reference comparison: equal levels outside the `Integer` cache
  `-128..127` differ unless both ends are the same node), and keep an edge only if no kept edge has
  the same `toString()` (`n_<label or id>->n_<label or id>`: parallel edges, and edges between
  nodes with the same first label text, are routed only once — the others get the fallback); the
  list is sorted by the target's (outgoing) or source's (incoming) **x** coordinate first and then,
  by the router, by the first/last point of the edge (stable `List.sort`, `Double.compare`);
* the start point of the "skip unnecessary level side bend points" test of a multi-level edge is
  the edge's current last bend point (its start bend points, or the second bend point of its previous
  gap), the source position only for an edge without bend points; the horizontal test compares
  `start.y < first.x` (a Java typo, kept);
* the nodes of a level are the graph's nodes in list order (`CompactionProcessor` may have re-sorted
  the list), stably sorted by position (`Double.compare`);
* `avoidOverlapHandleCycleInducingEdges` takes the centre of the tree as `DoubleStream.average()`
  (Kahan summation, `javaDoubleAverage`) and the extreme node borders with `Double.compare`;
* a cycle inducing incoming edge without bend points makes `getLast()` throw
  `java.util.NoSuchElementException` (downward layouts).

Data layout (performance, same values): node positions, sizes, levels and level bounds do not change
while routing, so they are read once into a table (`NodeData`) by *slot*: the entries of the graph's
node list (the `id` that `DFSTreeifyer.init` sets is the list index; other listed nodes are found in a
small map), then the end points of edges that are not in the list. The distinct edges with both end
points (first-occurrence order, which is the order of every scan over the edge list after the
`toString()` deduplication) are indexed once (`EdgeTable`), with their level-crossing flag and
grouped by the `id` of their source and of their target. Bend points are read from the arena when
Java reads them.

`getLayoutProcessorConfiguration` slots `LEVEL_COORDS`, `COMPACTION_PROC` and `GRAPH_BOUNDS_PROC`
before `P4_EDGE_ROUTING`.
-/

namespace Elk.Alg.MrTree.P4Route

open Elk.Core.Alg Elk.Core.Util Elk.Core.Math Elk.Core.Options Elk.Alg.MrTree Elk.Alg.MrTree.Graph
open Elk.Alg.MrTree.Options Elk.Alg.MrTree.Intermediate

namespace EdgeRouter

/-- `EdgeRouter.oneHalf`. -/
def ONE_HALF : Float := 0.5
/-- `EdgeRouter.steepEndEdgeTheresholdDistance`. -/
def STEEP_END_EDGE_THRESHOLD_DISTANCE : Float := 50.0
/-- `EdgeRouter.steepEndEdgeRatio`. -/
def STEEP_END_EDGE_RATIO : Float := 5.3
/-- `EdgeRouter.steepEndEdgeSampleHeight`. -/
def STEEP_END_EDGE_SAMPLE_HEIGHT : Float := 40.0

/-- The data of a node the router reads (constant while routing). -/
structure NodeData where
  level : Int
  pos : KVector
  size : KVector
  levelMin : Float
  levelMax : Float
  isSuperRoot : Bool
  /-- `TGraphElement.id`. -/
  id : Int
  /-- `getLabel()`. -/
  label : Option String
  deriving Inhabited

/-- `getProperty(TREE_LEVEL)`, `getLabel().equals("SUPER_ROOT")` and the geometry of a node. -/
def NodeData.ofNode (n : TNode) : NodeData :=
  { level := (n.props.get MrTreeOptions.TREE_LEVEL).getD 0, pos := n.position, size := n.size,
    levelMin := n.internal.levelMin, levelMax := n.internal.levelMax,
    isSuperRoot := n.label == some "SUPER_ROOT", id := n.id, label := n.label }

/-- `TNode.toString()`: `n_<label>`, or `n_<id>` for a missing or empty label. -/
def NodeData.toJavaString (d : NodeData) : String :=
  match d.label with
  | some l => if l.isEmpty then s!"n_{d.id}" else s!"n_{l}"
  | none => s!"n_{d.id}"

/-- `GraphStats`: the aggregates of `avoidOverlapHandleCycleInducingEdges` over the node list. -/
structure GraphStats where
  /-- `average()` of the node centres along y (horizontal layouts) / x (vertical layouts). -/
  avgCenterH : Float
  avgCenterV : Float
  /-- `max(Double::compare)` of `pos + size` along y / x. -/
  maxExtentH : Float
  maxExtentV : Float
  /-- `min(Double::compare)` of `pos` along y / x. -/
  minExtentH : Float
  minExtentV : Float

/-- `Stream.max(Double::compare)` step (`BinaryOperator.maxBy`: the first of equal values). -/
@[inline] private def maxByJava (acc x : Float) : Float :=
  if Float.compareJava acc x == .lt then x else acc

/-- `Stream.min(Double::compare)` step. -/
@[inline] private def minByJava (acc x : Float) : Float :=
  if Float.compareJava acc x == .gt then x else acc

/-- The slot of a node: entries `0 .. nodes.size` are the graph's node list (`id` holds the list index
of every node that `DFSTreeifyer.init` numbered; other listed nodes are in `extra`), further slots
are end points of edges outside the list (`extra`). -/
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
    if !byId && !extra.contains n then extra := extra.insert n i
  return { nodes, extra }

/-- The slot of a node (`none` if it has none yet). -/
@[inline] def get? (s : Slots) (a : TArena) (n : TNodeId) : Option Nat :=
  let id := (a.node n).id
  if id >= 0 && s.nodes[id.toNat]? == some n then some id.toNat else s.extra.get? n

end Slots

/-- The node table by slot. -/
abbrev NodeTable := Array NodeData

/-- The data of the node list (one entry per list entry, duplicates included). -/
def buildNodeData (a : TArena) (nodes : Array TNodeId) : NodeTable :=
  nodes.map fun node => NodeData.ofNode (a.node node)

/-- The aggregates of the first `count` entries (the node list) of the table, computed when the first
cycle inducing edge needs them (Java recomputes them for every such edge; the nodes do not move). -/
def buildStats (nd : NodeTable) (count : Nat) : GraphStats := Id.run do
  let mut centersH : Array Float := Array.mkEmpty count
  let mut centersV : Array Float := Array.mkEmpty count
  let mut maxH := fl0p0
  let mut maxV := fl0p0
  let mut minH := fl0p0
  let mut minV := fl0p0
  for i in [0:min count nd.size] do
    let d := nd[i]!
    let pos := d.pos
    let size := d.size
    centersH := centersH.push (pos.y + size.y / fl2p0)
    centersV := centersV.push (pos.x + size.x / fl2p0)
    let extH := pos.y + size.y
    let extV := pos.x + size.x
    if i == 0 then
      maxH := extH; maxV := extV; minH := pos.y; minV := pos.x
    else
      maxH := maxByJava maxH extH
      maxV := maxByJava maxV extV
      minH := minByJava minH pos.y
      minV := minByJava minV pos.x
  return { avgCenterH := (javaDoubleAverage centersH).getD fl0p0, avgCenterV := (javaDoubleAverage centersV).getD fl0p0,
           maxExtentH := maxH, maxExtentV := maxV, minExtentH := minH, minExtentV := minV }

/-- `nd_pos` etc. of a slot. -/
@[inline] def ndLevel (nd : NodeTable) (s : Nat) : Int := (nd[s]?.map (·.level)).getD 0
@[inline] def ndPos (nd : NodeTable) (s : Nat) : KVector := (nd[s]?.map (·.pos)).getD {}
@[inline] def ndSize (nd : NodeTable) (s : Nat) : KVector := (nd[s]?.map (·.size)).getD {}
@[inline] def ndLevelMin (nd : NodeTable) (s : Nat) : Float := (nd[s]?.map (·.levelMin)).getD fl0p0
@[inline] def ndLevelMax (nd : NodeTable) (s : Nat) : Float := (nd[s]?.map (·.levelMax)).getD fl0p0
@[inline] def ndIsSuperRoot (nd : NodeTable) (s : Nat) : Bool := (nd[s]?.map (·.isSuperRoot)).getD false
@[inline] def ndId (nd : NodeTable) (s : Nat) : Int := (nd[s]?.map (·.id)).getD 0

/-- Whether the `TREE_LEVEL` `Integer`s of two nodes differ by Java `!=`: different values, or equal
values outside the `Integer.valueOf` cache on two different nodes (each node's level is a boxing of
its own). -/
@[inline] def levelsDiffer (ls lt : Int) (sameNode : Bool) : Bool :=
  ls != lt || (!sameNode && (ls < -128 || ls > 127))

/-- The distinct edges with both end points in first-occurrence order (`edges`) with the slots of
their end points, whether they cross levels (`crosses`, Java `!=` on the levels), whether they are
cycle inducing, and the level-crossing edges grouped by the `id` of their source (not for
`SUPER_ROOT` sources) and of their target, in edge order. -/
structure EdgeTable where
  edges : Array TEdgeId := #[]
  sourceSlot : Array Nat := #[]
  targetSlot : Array Nat := #[]
  cycleInducing : Array Bool := #[]
  outById : Std.HashMap Int (Array Nat) := {}
  inById : Std.HashMap Int (Array Nat) := {}

/-- The node table extended by the end points outside the node list, and the edge table. -/
def buildEdgeMaps (a : TArena) (slots : Slots) (edges : Array TEdgeId) (nd : NodeTable)
    (direction : Direction) : Slots × NodeTable × EdgeTable := Id.run do
  let dirVec := TreeUtil.getDirectionVector direction
  let mut slots := slots
  let mut nd := nd
  let mut em : EdgeTable := {}
  let mut seen : Std.HashSet TEdgeId := Std.HashSet.emptyWithCapacity edges.size
  for edge in edges do
    if seen.contains edge then continue
    seen := seen.insert edge
    let (some source, some target) := ((a.edge edge).source, (a.edge edge).target) | continue
    let ss ← match slots.get? a source with
      | some s => pure s
      | none =>
        let s := nd.size
        nd := nd.push (NodeData.ofNode (a.node source))
        slots := { slots with extra := slots.extra.insert source s }
        pure s
    let ts ← match slots.get? a target with
      | some s => pure s
      | none =>
        let s := nd.size
        nd := nd.push (NodeData.ofNode (a.node target))
        slots := { slots with extra := slots.extra.insert target s }
        pure s
    let sd := nd[ss]!
    let td := nd[ts]!
    let edgeVec : KVector := ⟨td.pos.x - sd.pos.x, td.pos.y - sd.pos.y⟩
    let k := em.edges.size
    em := { em with
      edges := em.edges.push edge, sourceSlot := em.sourceSlot.push ss, targetSlot := em.targetSlot.push ts
      cycleInducing := em.cycleInducing.push (dirVec.dotProduct edgeVec <= fl0p0) }
    if levelsDiffer sd.level td.level (source == target) then
      if !sd.isSuperRoot then
        em := { em with outById := em.outById.alter sd.id fun l => some ((l.getD #[]).push k) }
      em := { em with inById := em.inById.alter td.id fun l => some ((l.getD #[]).push k) }
  return (slots, nd, em)

/-- The nodes of every level (as slots, in node list order; a node listed twice twice), stably sorted
by position (`Double.compare`). -/
def buildLevelNodes (nodeSlots : Array Nat) (nd : NodeTable) (direction : Direction) :
    Array (Array Nat) := Id.run do
  let maxLevel : Int := nodeSlots.foldl (fun m n => match m with
    | some v => some (max v (ndLevel nd n))
    | none => some (ndLevel nd n)) none |>.getD 0
  let len := (max (maxLevel + 1) 0).toNat
  let mut levels : Array (Array Nat) := Array.replicate len #[]
  for node in nodeSlots do
    let level := ndLevel nd node
    if level >= 0 && level.toNat < len then
      levels := levels.modify level.toNat (·.push node)
  return levels.map fun lv =>
    javaSortByDouble lv fun n => if direction.isHorizontal then (ndPos nd n).y else (ndPos nd n).x

/-- `TreeUtil.getAllOutgoingEdges`/`getAllIncomingEdges` of a node: the level-crossing edges whose
source (`incoming = false`) or target has the node's `id`, without later edges whose `toString()`
equals that of a kept edge, sorted by the x coordinate of the other end point. -/
def javaEdgeList (nd : NodeTable) (em : EdgeTable) (id : Int) (incoming : Bool) : Array Nat := Id.run do
  let cands := ((if incoming then em.inById else em.outById).get? id).getD #[]
  if cands.size < 2 then return cands
  let mut seen : Std.HashSet String := {}
  let mut kept : Array Nat := Array.mkEmpty cands.size
  for k in cands do
    let s := s!"{nd[em.sourceSlot[k]!]!.toJavaString}->{nd[em.targetSlot[k]!]!.toJavaString}"
    if !seen.contains s then
      seen := seen.insert s
      kept := kept.push k
  return javaSortByDouble kept fun k => (ndPos nd (if incoming then em.sourceSlot[k]! else em.targetSlot[k]!)).x

/-- `middleToMiddleEdgeRoute(tEdge)`. -/
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

/-- `middleToMiddle(tGraph)`. -/
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

/-- `avoidOverlapHandleCycleInducingEdges(...)`: returns the updated side counters. -/
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
  -- `max over nodes of (border + padding * k)` = `(max of the borders) + padding * k` (`+` is monotone)
  if direction.isHorizontal then
    if sourcePos.y + sourceSize.y / fl2p0 > stats.avgCenterH then
      sideTwoEdges := sideTwoEdges + 1
      bendTmp := stats.maxExtentH + pad * Float.ofInt sideTwoEdges
    else
      sideOneEdges := sideOneEdges + 1
      bendTmp := stats.minExtentH - pad * Float.ofInt sideOneEdges
  else
    if sourcePos.x + sourceSize.x / fl2p0 > stats.avgCenterV then
      sideTwoEdges := sideTwoEdges + 1
      bendTmp := stats.maxExtentV + pad * Float.ofInt sideTwoEdges
    else
      sideOneEdges := sideOneEdges + 1
      bendTmp := stats.minExtentV - pad * Float.ofInt sideOneEdges
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
    if !(← bendsOf edge).isEmpty then
      let y := ndLevelMax nd source + pad * outs
      MrTreeM.modifyEdge edge fun e =>
        let i := e.bendPoints.size - 1
        { e with bendPoints := e.bendPoints.set! i { e.bendPoints[i]! with y } }
    addBend edge bendTmp (ndLevelMax nd source + pad * outs)
    addBend edge bendTmp (targetPos.y - pad * ins - tex)
  return (sideOneEdges, sideTwoEdges)

/-- `avoidOverlapSpecialEdges(...)`. -/
def avoidOverlapSpecialEdges (direction : Direction) (pad tex : Float) (slots : Slots) (nd : NodeTable)
    (nodeCount : Nat) (graphBounds : Float × Float × Float × Float) (em : EdgeTable)
    (levelNodes : Array (Array Nat)) : MrTreeM Unit := do
  let mut stats : Option GraphStats := none
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
          -- the edge's current last bend point (the source position without bend points)
          let start : KVector := (← bendsOf edge).back?.getD sourcePos
          let lastNode := nextLevelNodes[nextLevelNodes.size - 1]!
          let firstNode := nextLevelNodes[0]!
          let lastPos := ndPos nd lastNode
          let lastSize := ndSize nd lastNode
          let last : KVector := ⟨lastPos.x + lastSize.x, lastPos.y + lastSize.y⟩
          let firstPos := ndPos nd firstNode
          let firstSize := ndSize nd firstNode
          let first : KVector := ⟨firstPos.x + firstSize.x, firstPos.y + firstSize.y⟩
          if horizontal then
            if index + 1 >= nextLevelNodes.size && start.y > last.y && targetPos.y > last.y then continue
            if index == 0 && start.y < first.x && targetPos.y < first.y then continue
          else
            if index + 1 >= nextLevelNodes.size && start.x > last.x && targetPos.x > last.x then continue
            if index == 0 && start.x < first.x && targetPos.x < first.x then continue
        let bends ← bendsOf edge
        let firstIndex := bends.size
        let secondIndex := bends.size + 1
        MrTreeM.modifyEdge edge fun e => { e with bendPoints := (e.bendPoints.push {}).push {} }
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
      -- `outsPerLevel[sourceLevel]++; insPerLevel[targetLevel]++` (arrays of the maximal level + 1)
      if sourceLevel < 0 || sourceLevel >= (maxLevel : Int) then
        throw (IO.userError s!"java.lang.ArrayIndexOutOfBoundsException: Index {sourceLevel} out of bounds for length {maxLevel}")
      if targetLevel < 0 || targetLevel >= (maxLevel : Int) then
        throw (IO.userError s!"java.lang.ArrayIndexOutOfBoundsException: Index {targetLevel} out of bounds for length {maxLevel}")
      let sourceLevelN := sourceLevel.toNat
      let targetLevelN := targetLevel.toNat
      outsPerLevel := outsPerLevel.modify sourceLevelN (· + 1)
      insPerLevel := insPerLevel.modify targetLevelN (· + 1)
      let inOuts := (insPerLevel[targetLevelN]!, outsPerLevel[sourceLevelN]!)
      let st := stats.getD (buildStats nd nodeCount)
      stats := some st
      let (s1, s2) ← handleCycleInducingEdges edge source target direction (sideOneEdges, sideTwoEdges)
        pad tex inOuts nd st
      sideOneEdges := s1
      sideTwoEdges := s2

/-- `avoidOverlapSetStartPoints(...)`. -/
def avoidOverlapSetStartPoints (direction : Direction) (pad : Float) (nd : NodeTable) (em : EdgeTable)
    (nodes : Array TNodeId) (nodeSlots : Array Nat) : MrTreeM Unit := do
  for h : j in [0:nodes.size] do
    let node := nodes[j]
    let slot := nodeSlots[j]!
    if ndIsSuperRoot nd slot then continue
    let outs := javaEdgeList nd em (ndId nd slot) false
    -- `outs.sort` by `TreeUtil.getFirstPoint` (the first bend point, else the target position)
    let outs ← if outs.size < 2 then pure outs else do
      let mut keys : FloatArray := FloatArray.emptyWithCapacity outs.size
      for k in outs do
        let p := match (← bendsOf em.edges[k]!)[0]? with
          | some p => p
          | none => ndPos nd em.targetSlot[k]!
        keys := keys.push (if direction.isHorizontal then p.y else p.x)
      pure (javaSortByDoubleKeys outs keys)
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
        addFirstBend edge (javaMin levelMin (pos.x - pad)) y
        addFirstBend edge pos.x y
      | .right =>
        let y := pos.y + size.y * interpolation
        addFirstBend edge (levelMax + pad) y
        addFirstBend edge (pos.x + size.x) y
      | .up =>
        let x := pos.x + size.x * interpolation
        addFirstBend edge x (javaMin (pos.y - pad) levelMin)
        addFirstBend edge x pos.y
      | _ =>
        let x := pos.x + size.x * interpolation
        addFirstBend edge x (levelMax + pad)
        addFirstBend edge x (pos.y + size.y)

/-- The steep end-edge correction of `avoidOverlapSetEndPoints` for the horizontal directions:
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

/-- `avoidOverlapSetEndPoints(...)`. -/
def avoidOverlapSetEndPoints (direction : Direction) (pad tex : Float) (nd : NodeTable) (em : EdgeTable)
    (nodeSlots : Array Nat) : MrTreeM Unit := do
  for slot in nodeSlots do
    if ndIsSuperRoot nd slot then continue
    let ins := javaEdgeList nd em (ndId nd slot) true
    -- `ins.sort` by `TreeUtil.getLastPoint` (the last bend point, else the source position)
    let ins ← if ins.size < 2 then pure ins else do
      let mut keys : FloatArray := FloatArray.emptyWithCapacity ins.size
      for k in ins do
        let p := match (← bendsOf em.edges[k]!).back? with
          | some p => p
          | none => ndPos nd em.sourceSlot[k]!
        keys := keys.push (if direction.isHorizontal then p.y else p.x)
      pure (javaSortByDoubleKeys ins keys)
    let num := ins.size
    for i in [0:num] do
      let k := ins[i]!
      let edge := em.edges[k]!
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
        if em.cycleInducing[k]! then
          -- `ins.get(i).getBendPoints().getLast().y`
          let some last := bends.back? | throw (IO.userError "java.util.NoSuchElementException")
          addBend edge (pos.x + size.x * interpolation) last.y
        else if pos.y - tex > levelMin then
          addBend edge (pos.x + size.x * interpolation) (levelMin - pad)
        else if !bends.isEmpty then
          if let some (x, y) := steepVertical bends.last! pos size tex interpolation
              (pos.y - tex / STEEP_END_EDGE_RATIO) then
            addBend edge x y
        addBend edge (pos.x + size.x * interpolation) pos.y

/-- The slots (extended by end points outside the node list), the slot of every listed node, the node
data and the edge table of `avoidOverlap` (a pure function of the arena, which is
released before the routing writes). -/
def prepare (a : TArena) (nodes : Array TNodeId) (edges : Array TEdgeId) (direction : Direction) :
    Slots × Array Nat × NodeTable × EdgeTable :=
  let slots := Slots.build a nodes
  -- every listed node has a slot (`Slots.get?` finds `nodes[i]` at its `id` or in `extra`)
  let nodeSlots := nodes.map fun n => (slots.get? a n).getD 0
  let nd := buildNodeData a nodes
  let (slots, nd, em) := buildEdgeMaps a slots edges nd direction
  (slots, nodeSlots, nd, em)

/-- `avoidOverlap(tGraph)`. -/
def avoidOverlap (graph : TGraphId) : MrTreeM Unit := do
  let g ← MrTreeM.getGraph graph
  let nodes := g.nodes
  let edges := g.edges
  let pad := (g.props.get MrTreeOptions.SPACING_EDGE_NODE).getD 0.0
  let tex := (g.props.get MrTreeOptions.EDGE_END_TEXTURE_LENGTH).getD 0.0
  let direction := (g.props.get MrTreeOptions.DIRECTION).getD .down
  let graphBounds := (g.internal.graphXmin, g.internal.graphXmax, g.internal.graphYmin, g.internal.graphYmax)
  let (slots, nodeSlots, nd, em) := prepare (← get) nodes edges direction
  let levelNodes := buildLevelNodes nodeSlots nd direction
  avoidOverlapSetStartPoints direction pad nd em nodes nodeSlots
  avoidOverlapSpecialEdges direction pad tex slots nd nodes.size graphBounds em levelNodes
  avoidOverlapSetEndPoints direction pad tex nd em nodeSlots

/-- `EdgeRouter.process`. -/
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

/-- `getLayoutProcessorConfiguration`. -/
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
