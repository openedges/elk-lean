import Elk.Alg.Layered.Graph
import Elk.Alg.Layered.P3Order.Counting.CrossMinUtil
import Elk.Core.Util.Sort
import Std.Data.HashMap
/-!
# `org.eclipse.elk.alg.layered.intermediate.greedyswitch.BetweenLayerEdgeTwoNodeCrossingsCounter`

Counts the crossings between the between-layer edges of two nodes of the free layer, in both
orders, by merging their sorted adjacency lists (elk-rs
`between_layer_edge_two_node_crossings_counter.rs`). The ports of the neighbouring layers are
numbered per layer in `inNorthSouthEastWestOrder` (eastern ports of the western layer, western
ports of the eastern layer).

The adjacency lists are created lazily per side (first query) and reset before every use; the
consumed copies of a query are therefore not written back (Rust mutates them in place, but
`reset` plus the per-entry reset on advancing makes the leftover state unobservable).
-/
namespace Elk.Alg.Layered.Intermediate.GreedySwitch

open Elk.Core.Options Elk.Core.Util Elk.Alg.Layered.Graph Elk.Alg.Layered.P3Order.Counting

/-- `BetweenLayerEdgeTwoNodeCrossingsCounter.Adjacency`: a neighbouring position and how many
edges lead there. -/
structure Adjacency where
  position : Int
  cardinality : Nat := 1
  currentCardinality : Nat := 1
  deriving Inhabited

/-- `Adjacency.reset()`. -/
@[inline] def Adjacency.reset (adj : Adjacency) : Adjacency := { adj with currentCardinality := adj.cardinality }

/-- `BetweenLayerEdgeTwoNodeCrossingsCounter.AdjacencyList`: the adjacencies of one node on one
side, sorted by position, with a consuming cursor. -/
structure AdjacencyList where
  adjacencyList : Array Adjacency := #[]
  side : PortSide := .undefined
  size : Nat := 0
  currentSize : Nat := 0
  currentIndex : Nat := 0
  deriving Inhabited

/-- Java's unboxing `NullPointerException` (JDK helpful message) of
`int adjacentPortPosition = portPositions.get(adjacentPort)` in `AdjacencyList.addAdjacencyOf`: the
far end of a between-layer edge is not among the numbered ports (eastern ports of the western layer,
western ports of the eastern layer). -/
def greedySwitchPortPositionNullError : String :=
  "java.lang.NullPointerException: Cannot invoke \"java.lang.Integer.intValue()\" because the return value of " ++
  "\"java.util.Map.get(Object)\" is null"

namespace AdjacencyList

/-- `reset()`: rewinds the cursor. -/
def reset (l : AdjacencyList) : AdjacencyList :=
  { l with currentIndex := 0, currentSize := l.size, adjacencyList := l.adjacencyList.modify 0 Adjacency.reset }

/-- `isEmpty()`. -/
@[inline] def isEmpty (l : AdjacencyList) : Bool := l.currentSize == 0

/-- `first()`: position of the current adjacency (`0` past the end). -/
@[inline] def first (l : AdjacencyList) : Int := (l.adjacencyList[l.currentIndex]?.map (·.position)).getD 0

/-- `countAdjacenciesBelowNodeOfFirstPort()`. -/
def countAdjacenciesBelowNodeOfFirstPort (l : AdjacencyList) : Nat :=
  if l.currentSize == 0 then 0
  else l.currentSize - ((l.adjacencyList[l.currentIndex]?.map (·.currentCardinality)).getD 0)

/-- `incrementCurrentIndex()`. -/
def incrementCurrentIndex (l : AdjacencyList) : AdjacencyList :=
  let l := { l with currentIndex := l.currentIndex + 1 }
  if l.currentIndex < l.adjacencyList.size then
    { l with adjacencyList := l.adjacencyList.modify l.currentIndex Adjacency.reset }
  else l

/-- `removeFirst()`. -/
def removeFirst (l : AdjacencyList) : AdjacencyList :=
  if l.isEmpty then l
  else
    let l := match l.adjacencyList[l.currentIndex]? with
      | some adj =>
        if adj.currentCardinality == 1 then l.incrementCurrentIndex
        else { l with adjacencyList := l.adjacencyList.modify l.currentIndex fun x => { x with currentCardinality := x.currentCardinality - 1 } }
      | none => l
    { l with currentSize := l.currentSize - 1 }

/-- `addAdjacencyOf(edge)`: the far end's position joins the list (merged with an equal last entry).
`none` when the far end has no position: Java unboxes `portPositions.get(adjacentPort)` and throws
`greedySwitchPortPositionNullError` (the far end is not a numbered port of the neighbouring layer,
e.g. a `WEST` port with an outgoing edge on a node whose inverted ports were not processed). -/
private def addAdjacencyOf (l : AdjacencyList) (a : LGraphArena) (portPositions : Std.HashMap LPortId Int) (e : LEdgeId) :
    Option AdjacencyList :=
  let ed := a.edge e
  let adjacentPort := if l.side == .west then ed.source else ed.target
  match adjacentPort.bind (portPositions[·]?) with
  | none => none
  | some adjacentPosition =>
    let list := match l.adjacencyList.back? with
      | some last =>
        if last.position == adjacentPosition then
          l.adjacencyList.modify (l.adjacencyList.size - 1) fun x =>
            { x with cardinality := x.cardinality + 1, currentCardinality := x.currentCardinality + 1 }
        else l.adjacencyList.push { position := adjacentPosition }
      | none => l.adjacencyList.push { position := adjacentPosition }
    some { l with adjacencyList := list, size := l.size + 1, currentSize := l.currentSize + 1 }

/-- `new AdjacencyList(node, side)`: collects the between-layer edges (incoming on `WEST`,
outgoing otherwise) of the node's side ports in `inNorthSouthEastWestOrder`, skipping self loops
and in-layer edges; then sorts stably by position and resets. `none` where Java's `addAdjacencyOf`
throws (a far end without position). -/
def new (a : LGraphArena) (node : LNodeId) (side : PortSide) (portPositions : Std.HashMap LPortId Int) :
    Option AdjacencyList := Id.run do
  let mut l : AdjacencyList := { side }
  for port in CrossMinUtil.inNorthSouthEastWestOrder a node side do
    let pt := a.port port
    let edges := if side == .west then pt.incomingEdges else pt.outgoingEdges
    for e in edges do
      if a.edgeIsSelfLoop e || a.edgeIsInLayerEdge e then continue
      match l.addAdjacencyOf a portPositions e with
      | some l' => l := l'
      | none => return none
  l := { l with adjacencyList := stableSortByKey l.adjacencyList (·.position) }
  return some l.reset

end AdjacencyList

/-- `countCrossingsByMergingAdjacencyLists(upper, lower)`: `(upperLower, lowerUpper)` deltas. -/
def countCrossingsByMergingAdjacencyLists (upper lower : AdjacencyList) : Int × Int := Id.run do
  let mut upper := upper
  let mut lower := lower
  let mut upperLowerCrossings : Int := 0
  let mut lowerUpperCrossings : Int := 0
  while !upper.isEmpty && !lower.isEmpty do
    let upperFirst := upper.first
    let lowerFirst := lower.first
    if upperFirst > lowerFirst then
      upperLowerCrossings := upperLowerCrossings + upper.currentSize
      lower := lower.removeFirst
    else if lowerFirst > upperFirst then
      lowerUpperCrossings := lowerUpperCrossings + lower.currentSize
      upper := upper.removeFirst
    else
      upperLowerCrossings := upperLowerCrossings + upper.countAdjacenciesBelowNodeOfFirstPort
      lowerUpperCrossings := lowerUpperCrossings + lower.countAdjacenciesBelowNodeOfFirstPort
      upper := upper.removeFirst
      lower := lower.removeFirst
  return (upperLowerCrossings, lowerUpperCrossings)

/-- `countCrossingsByMergingAdjacencyLists` on two freshly reset lists without copying or mutating
them: the cursor of a list is its index `i`, the current cardinality `c` of entry `i` and the current
size `n` (a stored list is only reset, so every entry beyond the cursor still has
`currentCardinality = cardinality`, which is what `incrementCurrentIndex` restores). The same
comparisons and sums as the reference loop; `(ul, lu)` are the running `upperLowerCrossings` and
`lowerUpperCrossings`. -/
partial def mergeAdjacencies (us ls : Array Adjacency) (ui uc un li lc ln : Nat) (ul lu : Int) : Int × Int :=
  if un == 0 || ln == 0 then (ul, lu)
  else
    let uf : Int := if h : ui < us.size then us[ui].position else 0
    let lf : Int := if h : li < ls.size then ls[li].position else 0
    -- `removeFirst` of a non-empty list: the current entry loses one edge or the cursor advances
    let nextU (k : Nat → Nat → Nat → Int × Int) : Int × Int :=
      if ui < us.size then
        if uc == 1 then
          let ui' := ui + 1
          k ui' (if h : ui' < us.size then us[ui'].cardinality else uc) (un - 1)
        else k ui (uc - 1) (un - 1)
      else k ui uc (un - 1)
    let nextL (ui' uc' un' : Nat) (ul' lu' : Int) : Int × Int :=
      if li < ls.size then
        if lc == 1 then
          let li' := li + 1
          mergeAdjacencies us ls ui' uc' un' li' (if h : li' < ls.size then ls[li'].cardinality else lc) (ln - 1) ul' lu'
        else mergeAdjacencies us ls ui' uc' un' li (lc - 1) (ln - 1) ul' lu'
      else mergeAdjacencies us ls ui' uc' un' li lc (ln - 1) ul' lu'
    if uf > lf then nextL ui uc un (ul + un) lu
    else if lf > uf then nextU fun ui' uc' un' => mergeAdjacencies us ls ui' uc' un' li lc ln ul (lu + ln)
    else
      -- `countAdjacenciesBelowNodeOfFirstPort` (`Nat` subtraction of the current cardinality, `0` past
      -- the end)
      let ub : Int := ((un - (if ui < us.size then uc else 0) : Nat) : Int)
      let lb : Int := ((ln - (if li < ls.size then lc else 0) : Nat) : Int)
      nextU fun ui' uc' un' => nextL ui' uc' un' (ul + ub) (lu + lb)

/-- `countCrossingsByMergingAdjacencyLists(upper.reset(), lower.reset())` by `mergeAdjacencies`. -/
@[inline] def countCrossingsOfStoredLists (upper lower : AdjacencyList) : Int × Int :=
  let uc := if h : 0 < upper.adjacencyList.size then upper.adjacencyList[0].cardinality else 0
  let lc := if h : 0 < lower.adjacencyList.size then lower.adjacencyList[0].cardinality else 0
  mergeAdjacencies upper.adjacencyList lower.adjacencyList 0 uc upper.size 0 lc lower.size 0 0

/-- `BetweenLayerEdgeTwoNodeCrossingsCounter`. -/
structure BetweenLayerEdgeTwoNodeCrossingsCounter where
  /-- `upperLowerCrossings`. -/
  upperLowerRef : IO.Ref Int
  /-- `lowerUpperCrossings`. -/
  lowerUpperRef : IO.Ref Int
  /-- `currentNodeOrder`. -/
  currentNodeOrder : Array (Array LNodeId)
  /-- `freeLayerIndex`. -/
  freeLayerIndex : Nat
  /-- `portPositions` of the neighbouring layers' ports. -/
  portPositions : Std.HashMap LPortId Int
  /-- Index of each free-layer node. -/
  nodeIndices : Std.HashMap LNodeId Nat
  /-- `easternAdjacencies` (created on first use). -/
  easternAdjacencies : IO.Ref (Option (Array AdjacencyList))
  /-- `westernAdjacencies` (created on first use). -/
  westernAdjacencies : IO.Ref (Option (Array AdjacencyList))

namespace BetweenLayerEdgeTwoNodeCrossingsCounter

/-- `setPortPositionsForLayer(layerIndex, portSide)`: numbers the layer's `portSide` ports from 0. -/
private def setPortPositionsForLayer (a : LGraphArena) (order : Array (Array LNodeId)) (layerIndex : Nat) (side : PortSide)
    (positions : Std.HashMap LPortId Int) : Std.HashMap LPortId Int := Id.run do
  let mut positions := positions
  let mut portId : Int := 0
  for node in (order[layerIndex]?).getD #[] do
    for port in CrossMinUtil.inNorthSouthEastWestOrder a node side do
      positions := positions.insert port portId
      portId := portId + 1
  return positions

/-- `new BetweenLayerEdgeTwoNodeCrossingsCounter(currentNodeOrder, freeLayerIndex)`. -/
def new (currentNodeOrder : Array (Array LNodeId)) (freeLayerIndex : Nat) : LayeredM BetweenLayerEdgeTwoNodeCrossingsCounter := do
  let a ← get
  let mut positions : Std.HashMap LPortId Int := {}
  if freeLayerIndex > 0 then
    positions := setPortPositionsForLayer a currentNodeOrder (freeLayerIndex - 1) .east positions
  if freeLayerIndex + 1 < currentNodeOrder.size then
    positions := setPortPositionsForLayer a currentNodeOrder (freeLayerIndex + 1) .west positions
  let mut indices : Std.HashMap LNodeId Nat := {}
  let freeLayer := (currentNodeOrder[freeLayerIndex]?).getD #[]
  for h : i in [0:freeLayer.size] do
    indices := indices.insert freeLayer[i] i
  return {
    upperLowerRef := ← IO.mkRef 0, lowerUpperRef := ← IO.mkRef 0, currentNodeOrder, freeLayerIndex,
    portPositions := positions, nodeIndices := indices,
    easternAdjacencies := ← IO.mkRef none, westernAdjacencies := ← IO.mkRef none }

/-- `upperLowerCrossings` of the last count. -/
def upperLowerCrossings (c : BetweenLayerEdgeTwoNodeCrossingsCounter) : BaseIO Int := c.upperLowerRef.get

/-- `lowerUpperCrossings` of the last count. -/
def lowerUpperCrossings (c : BetweenLayerEdgeTwoNodeCrossingsCounter) : BaseIO Int := c.lowerUpperRef.get

/-- `resetCrossingCount()`. -/
private def resetCrossingCount (c : BetweenLayerEdgeTwoNodeCrossingsCounter) : BaseIO Unit := do
  c.upperLowerRef.set 0
  c.lowerUpperRef.set 0

/-- The adjacency lists of all free-layer nodes on `side`, created on first use. -/
private def ensureAdjacencies (c : BetweenLayerEdgeTwoNodeCrossingsCounter) (side : PortSide) :
    LayeredM (Array AdjacencyList) := do
  let target := if side == .west then c.westernAdjacencies else c.easternAdjacencies
  match ← target.get with
  | some lists => return lists
  | none =>
    let a ← get
    let mut lists : Array AdjacencyList := #[]
    for node in (c.currentNodeOrder[c.freeLayerIndex]?).getD #[] do
      match AdjacencyList.new a node side c.portPositions with
      | some l => lists := lists.push l
      | none => throw (IO.userError greedySwitchPortPositionNullError)
    target.set (some lists)
    return lists

/-- `addCrossings(upperNode, lowerNode, side)`. -/
private def addCrossings (c : BetweenLayerEdgeTwoNodeCrossingsCounter) (upperNode lowerNode : LNodeId) (side : PortSide) :
    LayeredM Unit := do
  let (some upperIndex, some lowerIndex) := (c.nodeIndices[upperNode]?, c.nodeIndices[lowerNode]?) | return
  let adjacencies ← c.ensureAdjacencies side
  if upperIndex == lowerIndex then return
  let upperAdjacencies := (adjacencies[upperIndex]?).getD default
  let lowerAdjacencies := (adjacencies[lowerIndex]?).getD default
  -- `reset` sets `currentSize := size`
  if upperAdjacencies.size == 0 || lowerAdjacencies.size == 0 then return
  let (upperDelta, lowerDelta) := countCrossingsOfStoredLists upperAdjacencies lowerAdjacencies
  c.upperLowerRef.modify (· + upperDelta)
  c.lowerUpperRef.modify (· + lowerDelta)

/-- `countEasternEdgeCrossings(upperNode, lowerNode)`. -/
def countEasternEdgeCrossings (c : BetweenLayerEdgeTwoNodeCrossingsCounter) (upperNode lowerNode : LNodeId) : LayeredM Unit := do
  c.resetCrossingCount
  if upperNode == lowerNode then return
  c.addCrossings upperNode lowerNode .east

/-- `countWesternEdgeCrossings(upperNode, lowerNode)`. -/
def countWesternEdgeCrossings (c : BetweenLayerEdgeTwoNodeCrossingsCounter) (upperNode lowerNode : LNodeId) : LayeredM Unit := do
  c.resetCrossingCount
  if upperNode == lowerNode then return
  c.addCrossings upperNode lowerNode .west

/-- `countBothSideCrossings(upperNode, lowerNode)`: western then eastern crossings. -/
def countBothSideCrossings (c : BetweenLayerEdgeTwoNodeCrossingsCounter) (upperNode lowerNode : LNodeId) : LayeredM Unit := do
  c.resetCrossingCount
  if upperNode == lowerNode then return
  c.addCrossings upperNode lowerNode .west
  c.addCrossings upperNode lowerNode .east

end BetweenLayerEdgeTwoNodeCrossingsCounter

end Elk.Alg.Layered.Intermediate.GreedySwitch
