import Elk.Alg.Layered.Graph
import Elk.Alg.Layered.P3Order.Counting.BinaryIndexedTree
import Elk.Alg.Layered.P3Order.Counting.CrossMinUtil
import Elk.Alg.Layered.P3Order.CrossMinSnapshot
import Elk.Core.Util.Sort
import Std.Data.HashSet
/-!
# `org.eclipse.elk.alg.layered.p3order.counting.CrossingsCounter`

Counts crossings with a binary indexed tree over port positions (elk-rs `crossings_counter.rs`).
Positions are indexed by the port's `id` (`LPort.id`, assigned by the `IInitializable`s), node
cardinalities by the node's `id` (its index in the layer), exactly like Java `port.id`/`node.id`
and the elk-rs `graph_element().id` path.

elk-rs additionally has a `CrossMinSnapshot` fast path (`set_snapshot`, used by the
`GraphInfoHolder`'s `AllCrossingsCounter`). It reads the same ids from the snapshot and filters
`node.ports` by side instead of `getPortSideView`; both coincide because ports are sorted by side
during crossing minimisation and ids/edges do not change after the snapshot is built (here the
views are Java's cached ranges on both paths). Here the
snapshot (`setSnapshot`) is used by `countCrossingsBetweenLayers` and `countInLayerCrossingsOnSide`
to read the far ends of a port's edges (`port_predecessors`, then `port_successors`, which is
`connectedEdges` order) as captured ids (the in-layer count only when every numbered port has
`CrossMinSnapshot.portEndsOk`); the ports themselves are still numbered through `getPortSideView`
(with the captured sides and ids for nodes without nested graph, which keep them while the snapshot
is used), and nodes of the snapshot without a port on the counted side are skipped. The north/south
count walks the side views in place (`…Fast`; the port loops are kept as
`countNorthSouthPortCrossingsInLayerPort` for the differential test).

Java's index tree bounds are checked on every counting path (live and snapshot): a far end whose
position (possibly stale, left by an earlier count in the shared array) lies outside the tree is
Java's `ArrayIndexOutOfBoundsException` (`javaTreeIndexError`; elk-rs ignored such indices).

Rust semantics kept where they differ from Java:
- the in-layer/two-port port sets are de-duplicated by port identity and *stably* sorted by
  position (Java uses a `TreeSet` keyed by position, which also drops ports with equal positions);
- long-edge dummies are pushed onto the north/south stack once, not once per eastern port;
- out-of-range ids read position `0`, writes grow the position array (Java throws);
- the `ends` deque is a local stack (it is always drained before the next port).
-/
namespace Elk.Alg.Layered.P3Order.Counting

open Elk.Core.Options Elk.Core.Util Elk.Alg.Layered.Graph Elk.Alg.Layered.Options

/-- `CrossingsCounter`: mutable port positions, the index tree and the node cardinalities of the
last `initPortPositionsForInLayerCrossings`. -/
structure CrossingsCounter where
  /-- `portPositions` (indexed by `LPort.id`; may be shared with other counters). -/
  portPositions : IO.Ref (Array Int)
  /-- `indexTree`. -/
  indexTree : IO.Ref BinaryIndexedTree
  /-- `nodeCardinalities` (indexed by `LNode.id`). -/
  nodeCardinalities : IO.Ref (Array Int)
  /-- elk-rs `snapshot` (`set_snapshot`). -/
  snapshot : IO.Ref (Option CrossMinSnapshot)
  /-- Scratch buffer of the snapshot path's captured port ids (Lean only). -/
  idScratch : IO.Ref (Array Nat)

namespace CrossingsCounter

/-! ## Pure helpers over the arena -/

/-- Rust `port_id(port)`: `port.id as usize`. -/
@[inline] def portIdOf (a : LGraphArena) (p : LPortId) : Nat := asUsize (a.port p).id

/-- Rust `node_id(node)`: `node.id as usize`. -/
@[inline] def nodeIdOf (a : LGraphArena) (n : LNodeId) : Nat := asUsize (a.node n).id

/-- `positionOf(port)`: `0` for ports without a slot. -/
@[inline] def positionIn (positions : Array Int) (a : LGraphArena) (p : LPortId) : Int :=
  positions[portIdOf a p]?.getD 0

/-- Rust `set_port_position`: grows the array when `pid` is beyond its end. Ids that are not
valid `i32` values (negative ids wrapped by `as usize`) are ignored (Rust would abort). -/
@[inline] def setPosition (positions : Array Int) (pid : Nat) (v : Int) : Array Int :=
  if pid >>> 32 != 0 then positions
  else
    let positions := if pid >= positions.size then positions ++ Array.replicate (pid + 1 - positions.size) 0 else positions
    positions.setIfInBounds pid v

/-- `otherEndOf(edge, fromPort)`: `none` when an end point is missing (Rust panics). -/
@[inline] def otherEndOf (a : LGraphArena) (e : LEdgeId) (fromPort : LPortId) : Option LPortId :=
  let ed := a.edge e
  match ed.source, ed.target with
  | some s, some t => some (if s == fromPort then t else s)
  | _, _ => none

/-- `isInLayer(edge)`: both end nodes lie in the same layer (self loops included). -/
def isInLayer (a : LGraphArena) (e : LEdgeId) : Bool :=
  let ed := a.edge e
  let layerOf (p : Option LPortId) : Option LayerId :=
    p.bind fun p => (a.port p).owner.bind fun n => (a.node n).layer
  match layerOf ed.source, layerOf ed.target with
  | some s, some t => s == t
  | _, _ => false

/-- `isPortSelfLoop(edge)`: source port equals target port. -/
@[inline] def isPortSelfLoop (a : LGraphArena) (e : LEdgeId) : Bool :=
  let ed := a.edge e
  match ed.source, ed.target with
  | some s, some t => s == t
  | _, _ => false

/-- `getPorts(node, side, topDown)`: `getPortSideView(side)`, reversed for `EAST` bottom-up and for
the other sides top-down (counter-clockwise numbering). -/
def getPorts (a : LGraphArena) (node : LNodeId) (side : PortSide) (topDown : Bool) : Array LPortId :=
  let ports := a.nodePortSideView node side
  let needReverse := if side == .east then !topDown else topDown
  if needReverse then ports.reverse else ports

/-- Numbers `ports[i:stop]` with consecutive positions from `next`. -/
private partial def numberPorts (a : LGraphArena) (ports : Array LPortId) (i stop : Nat) (next : Int)
    (positions : Array Int) : Array Int :=
  if h : i < stop ∧ i < ports.size then
    numberPorts a ports (i + 1) stop (next + 1) (setPosition positions (portIdOf a ports[i]) next)
  else positions

/-- The node loop of `initPositions` (`k`-th visited node, `nodes[k]` top-down or `nodes[n - 1 - k]`). -/
private partial def initPositionsLoop (a : LGraphArena) (nodes : Array LNodeId) (side : PortSide)
    (topDown getCardinalities needReverse : Bool) (k : Nat) (positions cards : Array Int) (ports : Array LPortId) :
    Array Int × Array Int × Array LPortId :=
  if k < nodes.size then
    let node := nodes[if topDown then k else nodes.size - 1 - k]!
    let start := ports.size
    let ports := appendSideView a node side needReverse ports
    let cards := if getCardinalities then cards.setIfInBounds (nodeIdOf a node) (ports.size - start) else cards
    let positions := numberPorts a ports start ports.size start positions
    initPositionsLoop a nodes side topDown getCardinalities needReverse (k + 1) positions cards ports
  else (positions, cards, ports)

/-- `initPositions(nodes, ports, side, topDown, getCardinalities)`: numbers the side's ports of
`nodes` (top-down or bottom-up) after the `ports` already collected; returns the updated
positions, cardinalities and port list. An empty `nodes` array changes nothing (Rust returns
before resetting the cardinalities). The ports of a node are `getPorts(node, side, topDown)`
(`getPortSideView(side)`, reversed for `EAST` bottom-up and for the other sides top-down), appended
without intermediate copies. -/
def initPositions (a : LGraphArena) (positions cards : Array Int) (nodes : Array LNodeId) (ports : Array LPortId)
    (side : PortSide) (topDown getCardinalities : Bool) : Array Int × Array Int × Array LPortId :=
  if nodes.isEmpty then (positions, cards, ports)
  else
    let cards := if getCardinalities then Array.replicate nodes.size 0 else cards
    let needReverse := if sideIs side .east then !topDown else topDown
    initPositionsLoop a nodes side topDown getCardinalities needReverse 0 positions cards ports

/-- `emptyStack(stack, ports, side, startIndex)`: numbers the first `side` port of every stacked
dummy (LIFO). -/
def emptyStack (a : LGraphArena) (stack : Array LNodeId) (ports : Array LPortId) (side : PortSide) (index : Int)
    (positions : Array Int) : Array LNodeId × Array LPortId × Int × Array Int := Id.run do
  let mut stack := stack
  let mut ports := ports
  let mut index := index
  let mut positions := positions
  while !stack.isEmpty do
    let dummy := stack.back!
    stack := stack.pop
    if let some p := (a.nodePortSideView dummy side)[0]? then
      positions := setPosition positions (portIdOf a p) index
      index := index + 1
      ports := ports.push p
  return (stack, ports, index, positions)

/-- `isLayoutUnitChanged(lastUnit, node)` on the already read layout unit of `node`. -/
@[inline] def isLayoutUnitChanged (lastUnit : Option LNodeId) (node : LNodeId) (unit : Option LNodeId) : Bool :=
  match lastUnit with
  | none => false
  | some last => if last == node then false else match unit with
    | some u => u != last
    | none => false

/-- Ports of `node` on `side` that have a `PORT_DUMMY` (`getNorthSouthPortsWithIncidentEdges`). -/
@[inline] def northSouthPortsWithIncidentEdges (a : LGraphArena) (node : LNodeId) (side : PortSide) : Array LPortId :=
  (a.nodePortSideView node side).filter fun p => (a.port p).internal.portDummy.isSome

/-- `initPositionsForNorthSouthCounting(nodes)`: northern ports of a normal node, then the stacked
north/south and long-edge dummies, then its southern ports (`INDEXING_SIDE = WEST`,
`STACK_SIDE = EAST`). -/
def initPositionsForNorthSouthCounting (a : LGraphArena) (positions : Array Int) (nodes : Array LNodeId) :
    Array Int × Array LPortId := Id.run do
  let mut ports : Array LPortId := #[]
  let mut stack : Array LNodeId := #[]
  let mut lastLayoutUnit : Option LNodeId := none
  let mut index : Int := 0
  let mut positions := positions
  for current in nodes do
    let nd := a.node current
    let layoutUnit := nd.internal.inLayerLayoutUnit
    if isLayoutUnitChanged lastLayoutUnit current layoutUnit then
      (stack, ports, index, positions) := emptyStack a stack ports .east index positions
    if layoutUnit.isSome then lastLayoutUnit := layoutUnit
    match nd.type with
    | .normal =>
      for p in northSouthPortsWithIncidentEdges a current .north do
        positions := setPosition positions (portIdOf a p) index
        index := index + 1
        ports := ports.push p
      (stack, ports, index, positions) := emptyStack a stack ports .east index positions
      for p in northSouthPortsWithIncidentEdges a current .south do
        positions := setPosition positions (portIdOf a p) index
        index := index + 1
        ports := ports.push p
    | .northSouthPort =>
      if let some p := (a.nodePortSideView current .west)[0]? then
        positions := setPosition positions (portIdOf a p) index
        index := index + 1
        ports := ports.push p
      if !(a.nodePortSideView current .east).isEmpty then stack := stack.push current
    | .longEdge =>
      for p in a.nodePortSideView current .west do
        positions := setPosition positions (portIdOf a p) index
        index := index + 1
        ports := ports.push p
      if !(a.nodePortSideView current .east).isEmpty then stack := stack.push current
    | _ => pure ()
  (_, ports, _, positions) := emptyStack a stack ports .east index positions
  return (positions, ports)

/-! ### Counting loops

The Rust loops collect the far-end positions above the current one in a deque and add them to the
tree after the port's ranks are summed. The tree additions commute, so here every edge list is
walked twice: once summing the ranks, once adding the positions (no deque). -/

/-- The far-end position of edge `e` seen from `port` (`none` when an end point is missing). -/
@[inline] private def endPositionOf (a : LGraphArena) (positions : Array Int) (e : LEdgeId) (port : LPortId) :
    Option Int :=
  match otherEndOf a e port with
  | some other => some (positionIn positions a other)
  | none => none

/-- Sums `tree.rank(endPosition)` over the edges `edges[i:]` whose far end lies above `cur`. -/
private partial def rankEnds (a : LGraphArena) (positions : Array Int) (tree : BinaryIndexedTree) (port : LPortId)
    (cur : Int) (edges : Array LEdgeId) (i : Nat) (acc : Int) : Int :=
  if h : i < edges.size then
    match endPositionOf a positions edges[i] port with
    | some endPosition =>
      rankEnds a positions tree port cur edges (i + 1) (if endPosition > cur then acc + tree.rank (asUsize endPosition) else acc)
    | none => rankEnds a positions tree port cur edges (i + 1) acc
  else acc

/-- Adds the far-end positions above `cur` of the edges `edges[i:]` to the tree. -/
private partial def addEnds (a : LGraphArena) (positions : Array Int) (port : LPortId) (cur : Int)
    (edges : Array LEdgeId) (i : Nat) (tree : BinaryIndexedTree) : BinaryIndexedTree :=
  if h : i < edges.size then
    match endPositionOf a positions edges[i] port with
    | some endPosition =>
      addEnds a positions port cur edges (i + 1) (if endPosition > cur then tree.add (asUsize endPosition) else tree)
    | none => addEnds a positions port cur edges (i + 1) tree
  else tree

/-- The port loop of `countCrossingsOnPorts`. -/
private partial def countOnPortsLoop (a : LGraphArena) (positions : Array Int) (ports : Array LPortId) (i : Nat)
    (tree : BinaryIndexedTree) (crossings : Int) : Int × BinaryIndexedTree :=
  if h : i < ports.size then
    let port := ports[i]
    let pt := a.port port
    let cur := positionIn positions a port
    let tree := tree.removeAll (asUsize cur)
    -- `connectedEdges` = incoming, then outgoing
    let crossings := rankEnds a positions tree port cur pt.incomingEdges 0 crossings
    let crossings := rankEnds a positions tree port cur pt.outgoingEdges 0 crossings
    let tree := addEnds a positions port cur pt.incomingEdges 0 tree
    let tree := addEnds a positions port cur pt.outgoingEdges 0 tree
    countOnPortsLoop a positions ports (i + 1) tree crossings
  else (crossings, tree)

/-- `countCrossingsOnPorts(ports)`. -/
def countCrossingsOnPorts (a : LGraphArena) (positions : Array Int) (tree : BinaryIndexedTree) (ports : Array LPortId) :
    Int × BinaryIndexedTree :=
  countOnPortsLoop a positions ports 0 tree 0

/-! ### Between-layer counting on the snapshot path

`countCrossingsBetweenLayers` with a snapshot fuses `initPortPositionsCounterClockwise` and
`count_crossings_on_ports_snap`: the side views are numbered in place (positions written at the live
`LPort.id`, exactly as `initPositions` does) while the ports' captured ids are collected, and the
count runs over those ids on a fresh packed tree (`BinaryIndexedTree.incLoopPacked`/`rankPacked`).

`removeAll(cur)` is deferred: its bucket is cleared at once (as `removeAll` does), the pair
`(cur, count)` is kept, and the pending removals are applied to the prefix sums before the next
`rank`. The tree updates commute, so every `rank` sees the same sums; removals after the last
`rank` (the ports of the right layer, whose far ends lie in the left layer) are never applied. The
tree is not stored back (`indexTree` keeps its previous value): every other use of the counter
starts with a fresh tree. -/

/-- `pids[len] := pid` (pushed when `len` is the size). -/
@[inline] private def writeAt (pids : Array Nat) (len pid : Nat) : Array Nat :=
  if len < pids.size then pids.set! len pid else pids.push pid

/-- Whether `node` is a captured node without nested graph none of whose ports lies on `side`
(`nodeSideMask`). The crossing minimisation only permutes the ports of such a node within their
sides and does not change the sides, and its side cache was made from these ports
(`GraphInfoHolder.initHolder` caches every node before the snapshot is built, the distributor
caches again after sorting), so the cache has no range for `side` and `getPortSideView(side)` is
empty. -/
@[inline] def noPortOnSide (s : CrossMinSnapshot) (node : LNodeId) (side : PortSide) : Bool :=
  let flat1 := s.nodeMap.get node.idx
  flat1 != 0 && !s.nodeHasNestedGraph (flat1 - 1) && s.nodeSideMask (flat1 - 1) &&& sideBit side == 0

/-- Whether `node` is a captured node without nested graph: while the snapshot is used its port list
is a permutation of the captured one and every port keeps its side and `LPort.id`, so the captured
side and id (`portFlags`, `portId`) are the live ones. -/
@[inline] def isStableNode (s : CrossMinSnapshot) (node : LNodeId) : Bool :=
  let flat1 := s.nodeMap.get node.idx
  flat1 != 0 && !s.nodeHasNestedGraph (flat1 - 1)

/-- Numbers the ports of `getPortSideView(side)` of the `nodes` (top-down, or bottom-up without
`topDown`; the views are not reversed, as for `EAST` top-down and `WEST` bottom-up), continuing
after the `len` ports numbered so far: `positions[LPort.id] := len`, and the captured id of the
port goes to `pids[len]` (`pids` is a scratch buffer; only `pids[0:len]` is meaningful). The state
is the current node's port list `ports` and the cursor `j < hi` in its view `ports[j:hi]` (`sideView`,
Java's range without re-validating the sides), `k` the next node to visit. -/
private partial def numberSideViewsSnap (a : LGraphArena) (s : CrossMinSnapshot) (nodes : Array LNodeId)
    (side : PortSide) (topDown : Bool) (k : Nat) (ports : Array LPortId) (j hi : Nat) (stable : Bool)
    (len : Nat) (positions : Array Int) (pids : Array Nat) : Array Int × Array Nat × Nat :=
  if h : j < hi ∧ j < ports.size then
    let p := ports[j]
    let pid := s.portId p
    -- `LPort.id` of the port: for a `stable` node (`isStableNode`) the captured one
    let liveId := if stable then pid else asUsize (a.port p).id
    numberSideViewsSnap a s nodes side topDown k ports (j + 1) hi stable (len + 1)
      (setPosition positions liveId len) (writeAt pids len pid)
  else if k < nodes.size then
    let node := nodes[if topDown then k else nodes.size - 1 - k]!
    let stable := isStableNode s node
    if stable && noPortOnSide s node side then
      numberSideViewsSnap a s nodes side topDown (k + 1) #[] 0 0 stable len positions pids
    else
      let nd := a.node node
      let v := sideView a node nd side
      numberSideViewsSnap a s nodes side topDown (k + 1) nd.ports v.lo v.hi stable len positions pids
  else (positions, pids, len)

/-- Marks the packed tree `t` of `n` buckets (`2 n + 2` entries) as having seen an `add` index outside
`[0, n)`: the extra slot `t[2 n + 1]` (Java's `numsPerIndex[index]`/`binarySums[index]` would have
thrown; the caller turns it into Java's exception). -/
@[inline] private def markOutOfRange (t : Array Nat) (n : Nat) : Array Nat := t.set! (2 * n + 1) 1

/-- Whether `markOutOfRange` was applied to the packed tree `t` of `n` buckets. -/
@[inline] private def outOfRangeMarked (t : Array Nat) (n : Nat) : Bool := t[2 * n + 1]?.getD 0 != 0

/-- Whether a far end of `ends[k:hi]` lies above `cur`. -/
private partial def anyEndAbove (positions : Array Int) (cur : Int) (ends : Array Nat) (k hi : Nat) : Bool :=
  if h : k < hi ∧ k < ends.size then (positions[ends[k]]?.getD 0) > cur || anyEndAbove positions cur ends (k + 1) hi
  else false

/-- Applies the deferred removals `pend[k:np]` (pairs of index and count) to the prefix sums of the
packed tree `t` (`bound = n + 1`). -/
private partial def flushRemovals (pend : Array Nat) (k np : Nat) (bound : USize) (t : Array Nat) : Array Nat :=
  if h : k + 1 < np ∧ k + 1 < pend.size then
    flushRemovals pend (k + 2) np bound (BinaryIndexedTree.decLoopPacked t bound (pend[k] + 1).toUSize pend[k + 1])
  else t

/-- Defers a removal (`np` is even and at most `pend.size`, which is even). -/
@[inline] private def pushPending (pend : Array Nat) (np x c : Nat) : Array Nat :=
  if np + 1 < pend.size then (pend.set! np x).set! (np + 1) c else (pend.push x).push c

/-- Sum of `rank(endPosition)` over the far ends `ends[k:hi]` above `cur` (packed tree of `n` buckets). -/
private partial def rankEndsPacked (positions : Array Int) (t : Array Nat) (n : Nat) (cur : Int) (ends : Array Nat)
    (k hi acc : Nat) : Nat :=
  if h : k < hi ∧ k < ends.size then
    let e := positions[ends[k]]?.getD 0
    rankEndsPacked positions t n cur ends (k + 1) hi
      (if e > cur then acc + BinaryIndexedTree.rankPacked t n (asUsize e) else acc)
  else acc

/-- `add(endPosition)` for the far ends `ends[k:hi]` above `cur`: the bucket `t[n + 1 + x]` and the
prefix sums (indices below `n` only, like `add`). -/
private partial def addEndsPacked (positions : Array Int) (cur : Int) (ends : Array Nat) (k hi n : Nat) (t : Array Nat) :
    Array Nat :=
  if h : k < hi ∧ k < ends.size then
    let e := positions[ends[k]]?.getD 0
    if e > cur then
      let x := asUsize e
      if x < n then
        let b := n + 1 + x
        let t := t.set! b (t[b]! + 1)
        addEndsPacked positions cur ends (k + 1) hi n (BinaryIndexedTree.incLoopPacked t (n + 1).toUSize (x + 1).toUSize)
      else addEndsPacked positions cur ends (k + 1) hi n (markOutOfRange t n)
    else addEndsPacked positions cur ends (k + 1) hi n t
  else t

/-- `count_crossings_on_ports_snap` over the captured ids `pids[i:n]` on a fresh packed tree `t` of
`n` buckets (deferred removals `pend[0:np]`). The far ends of a port (`port_predecessors`, then
`port_successors`) are the range `[endLo, endHi)` of the snapshot's flattened `endIds`. -/
private partial def countBetweenSnapLoop (s : CrossMinSnapshot) (positions : Array Int) (pids : Array Nat) (i n : Nat)
    (t pend : Array Nat) (np crossings : Nat) : Nat × Array Nat :=
  if h : i < n ∧ i < pids.size then
    let pid := pids[i]
    let cur := positions[pid]?.getD 0
    -- `removeAll(cur)`: the bucket now, the prefix sums before the next `rank`
    let x := asUsize cur
    let c := if x < n then t[n + 1 + x]! else 0
    let t := if c != 0 then t.set! (n + 1 + x) 0 else t
    let pend := if c != 0 then pushPending pend np x c else pend
    let np := if c != 0 then np + 2 else np
    let ends := s.endIds
    let lo := s.endLo pid
    let hi := s.endHi pid
    if hi == lo + 1 then
      -- a single far end: `rank` then `add` of the same position (the general case ranks all far ends
      -- before adding any)
      let e := positions[ends[lo]!]?.getD 0
      if e > cur then
        let t := flushRemovals pend 0 np (n + 1).toUSize t
        let x := asUsize e
        let crossings := crossings + BinaryIndexedTree.rankPacked t n x
        let t := if x < n then
            let b := n + 1 + x
            BinaryIndexedTree.incLoopPacked (t.set! b (t[b]! + 1)) (n + 1).toUSize (x + 1).toUSize
          else markOutOfRange t n
        countBetweenSnapLoop s positions pids (i + 1) n t pend 0 crossings
      else countBetweenSnapLoop s positions pids (i + 1) n t pend np crossings
    else if anyEndAbove positions cur ends lo hi then
      let t := flushRemovals pend 0 np (n + 1).toUSize t
      let crossings := rankEndsPacked positions t n cur ends lo hi crossings
      let t := addEndsPacked positions cur ends lo hi n t
      countBetweenSnapLoop s positions pids (i + 1) n t pend 0 crossings
    else countBetweenSnapLoop s positions pids (i + 1) n t pend np crossings
  else (crossings, t)

/-! ### In-layer counting on the snapshot path

`countInLayerCrossingsOnSide` with a snapshot numbers the side views top-down like
`initPositions` (the views reversed unless the side is `EAST`, see `numberSideViewsSnapRev`) and
counts on a packed tree over the captured ids (elk-rs `count_in_layer_crossings_on_ports_snap`):
the far ends of a port are its `endIds` range (incoming sources, then outgoing targets), in the same
layer when their captured owner layer is the port's. This equals the live loop when every numbered
port has `portEndsOk` (otherwise the live path runs, numbering the same positions again). The tree
keeps `add`'s size of entries beyond the buckets; like the between-layer path, the tree and the node
cardinalities are not stored (the `AllCrossingsCounter` never reads them before a reset). -/

/-- `numberSideViewsSnap` with every view reversed (`getPorts` top-down of a side other than `EAST`):
the current node's view `ports[lo:j]` is walked downwards. -/
private partial def numberSideViewsSnapRev (a : LGraphArena) (s : CrossMinSnapshot) (nodes : Array LNodeId)
    (side : PortSide) (k : Nat) (ports : Array LPortId) (j lo : Nat) (stable : Bool)
    (len : Nat) (positions : Array Int) (pids : Array Nat) : Array Int × Array Nat × Nat :=
  if lo < j then
    match ports[j - 1]? with
    | some p =>
      let pid := s.portId p
      let liveId := if stable then pid else asUsize (a.port p).id
      numberSideViewsSnapRev a s nodes side k ports (j - 1) lo stable (len + 1)
        (setPosition positions liveId len) (writeAt pids len pid)
    | none => numberSideViewsSnapRev a s nodes side k ports (j - 1) lo stable len positions pids
  else if h : k < nodes.size then
    let node := nodes[k]
    let stable := isStableNode s node
    if stable && noPortOnSide s node side then
      numberSideViewsSnapRev a s nodes side (k + 1) #[] 0 0 stable len positions pids
    else
      let nd := a.node node
      let v := sideView a node nd side
      numberSideViewsSnapRev a s nodes side (k + 1) nd.ports v.hi v.lo stable len positions pids
  else (positions, pids, len)

/-- Whether every captured id of `pids[i:n]` has `portEndsOk`. -/
private partial def allEndsOk (s : CrossMinSnapshot) (pids : Array Nat) (i n : Nat) : Bool :=
  if h : i < n ∧ i < pids.size then s.portEndsOkAt pids[i] && allEndsOk s pids (i + 1) n else true

/-- Sum of `rank(endPosition)` over the in-layer far ends `ends[k:hi]` (owner layer `li`) above `cur`. -/
private partial def rankInLayerSnap (s : CrossMinSnapshot) (positions : Array Int) (t : Array Nat) (n : Nat) (cur : Int)
    (li : Nat) (ends : Array Nat) (k hi acc : Nat) : Nat :=
  if h : k < hi ∧ k < ends.size then
    let other := ends[k]
    if s.portOwnerLayer other == li then
      let e := positions[other]?.getD 0
      rankInLayerSnap s positions t n cur li ends (k + 1) hi
        (if e > cur then acc + BinaryIndexedTree.rankPacked t n (asUsize e) else acc)
    else rankInLayerSnap s positions t n cur li ends (k + 1) hi acc
  else acc

/-- The number of far ends of `ends[k:hi]` outside layer `li` (between-layer edges). -/
private partial def countBetweenEnds (s : CrossMinSnapshot) (li : Nat) (ends : Array Nat) (k hi acc : Nat) : Nat :=
  if h : k < hi ∧ k < ends.size then
    countBetweenEnds s li ends (k + 1) hi (if s.portOwnerLayer ends[k] == li then acc else acc + 1)
  else acc

/-- `add(endPosition)` for the in-layer far ends of `ends[k:hi]` above `cur`; the tree size (`add`
counts an entry beyond the buckets too) is returned with the tree. -/
private partial def addInLayerSnap (s : CrossMinSnapshot) (positions : Array Int) (cur : Int) (li : Nat) (ends : Array Nat)
    (k hi n : Nat) (t : Array Nat) (size : Nat) : Array Nat × Nat :=
  if h : k < hi ∧ k < ends.size then
    let other := ends[k]
    if s.portOwnerLayer other == li then
      let e := positions[other]?.getD 0
      if e > cur then
        let x := asUsize e
        if x < n then
          let b := n + 1 + x
          addInLayerSnap s positions cur li ends (k + 1) hi n
            (BinaryIndexedTree.incLoopPacked (t.set! b (t[b]! + 1)) (n + 1).toUSize (x + 1).toUSize) (size + 1)
        else addInLayerSnap s positions cur li ends (k + 1) hi n (markOutOfRange t n) (size + 1)
      else addInLayerSnap s positions cur li ends (k + 1) hi n t size
    else addInLayerSnap s positions cur li ends (k + 1) hi n t size
  else (t, size)

/-- `countInLayerCrossingsOnPorts` over the captured ids `pids[i:n]` on a fresh packed tree `t` of
`n` buckets holding `size` entries. -/
private partial def countInLayerSnapLoop (s : CrossMinSnapshot) (positions : Array Int) (pids : Array Nat) (i n : Nat)
    (t : Array Nat) (size : Nat) (crossings : Int) : Int × Array Nat :=
  if h : i < n ∧ i < pids.size then
    let pid := pids[i]
    let cur := positions[pid]?.getD 0
    -- `removeAll(cur)`
    let x := asUsize cur
    let c := if x < n then t[n + 1 + x]! else 0
    let t := if c != 0 then BinaryIndexedTree.decLoopPacked (t.set! (n + 1 + x) 0) (n + 1).toUSize (x + 1).toUSize c else t
    let size := size - c
    let ends := s.endIds
    let lo := s.endLo pid
    let hi := s.endHi pid
    let li := s.portOwnerLayer pid
    let ranks := rankInLayerSnap s positions t n cur li ends lo hi 0
    let between := countBetweenEnds s li ends lo hi 0
    let crossings := crossings + (ranks : Int) + (size : Int) * (between : Int)
    let (t, size) := addInLayerSnap s positions cur li ends lo hi n t size
    countInLayerSnapLoop s positions pids (i + 1) n t size crossings
  else (crossings, t)

/-- Like `rankEnds` for the in-layer edges only; also counts the between-layer edges. -/
private partial def rankInLayerEnds (a : LGraphArena) (positions : Array Int) (tree : BinaryIndexedTree) (port : LPortId)
    (cur : Int) (edges : Array LEdgeId) (i : Nat) (acc betweenLayer : Int) : Int × Int :=
  if h : i < edges.size then
    let e := edges[i]
    if isInLayer a e then
      match endPositionOf a positions e port with
      | some endPosition =>
        rankInLayerEnds a positions tree port cur edges (i + 1)
          (if endPosition > cur then acc + tree.rank (asUsize endPosition) else acc) betweenLayer
      | none => rankInLayerEnds a positions tree port cur edges (i + 1) acc betweenLayer
    else rankInLayerEnds a positions tree port cur edges (i + 1) acc (betweenLayer + 1)
  else (acc, betweenLayer)

/-- Like `addEnds` for the in-layer edges only. -/
private partial def addInLayerEnds (a : LGraphArena) (positions : Array Int) (port : LPortId) (cur : Int)
    (edges : Array LEdgeId) (i : Nat) (tree : BinaryIndexedTree) : BinaryIndexedTree :=
  if h : i < edges.size then
    let e := edges[i]
    if isInLayer a e then
      match endPositionOf a positions e port with
      | some endPosition =>
        addInLayerEnds a positions port cur edges (i + 1) (if endPosition > cur then tree.add (asUsize endPosition) else tree)
      | none => addInLayerEnds a positions port cur edges (i + 1) tree
    else addInLayerEnds a positions port cur edges (i + 1) tree
  else tree

/-- The port loop of `countInLayerCrossingsOnPorts`. -/
private partial def countInLayerOnPortsLoop (a : LGraphArena) (positions : Array Int) (ports : Array LPortId) (i : Nat)
    (tree : BinaryIndexedTree) (crossings : Int) : Int × BinaryIndexedTree :=
  if h : i < ports.size then
    let port := ports[i]
    let pt := a.port port
    let cur := positionIn positions a port
    let tree := tree.removeAll (asUsize cur)
    let (crossings, between1) := rankInLayerEnds a positions tree port cur pt.incomingEdges 0 crossings 0
    let (crossings, between2) := rankInLayerEnds a positions tree port cur pt.outgoingEdges 0 crossings 0
    let crossings := crossings + tree.size * (between1 + between2)
    let tree := addInLayerEnds a positions port cur pt.incomingEdges 0 tree
    let tree := addInLayerEnds a positions port cur pt.outgoingEdges 0 tree
    countInLayerOnPortsLoop a positions ports (i + 1) tree crossings
  else (crossings, tree)

/-- `countInLayerCrossingsOnPorts(ports)`: in-layer edges by rank, every between-layer edge
crosses all open in-layer edges. -/
def countInLayerCrossingsOnPorts (a : LGraphArena) (positions : Array Int) (tree : BinaryIndexedTree) (ports : Array LPortId) :
    Int × BinaryIndexedTree :=
  countInLayerOnPortsLoop a positions ports 0 tree 0

/-- Adds the collected end positions to the tree (Rust drains the `ends` deque from the back). -/
@[inline] private def addEndsArray (tree : BinaryIndexedTree) (ends : Array Int) : BinaryIndexedTree := Id.run do
  let mut tree := tree
  for k in [0:ends.size] do
    tree := tree.add (asUsize ends[ends.size - 1 - k]!)
  return tree

/-- The "edges" of a port taking part in north/south counting (`countNorthSouthCrossingsOnPorts`):
for a normal node all ports of its `PORT_DUMMY`, for a long-edge dummy its other port, for a
north/south dummy the `ORIGIN` port; each with the degree to weight its crossings. -/
def northSouthTargetsAndDegrees (a : LGraphArena) (port : LPortId) : Array (LPortId × Int) :=
  let pt := a.port port
  let nodeType := match pt.owner with
    | some n => (a.node n).type
    | none => NodeType.normal
  match nodeType with
  | .normal =>
    match pt.internal.portDummy with
    | some dummy => (a.node dummy).ports.map fun dp => (dp, ((a.port dp).degree : Int))
    | none => #[]
  | .longEdge =>
    match pt.owner with
    | some n =>
      match (a.node n).ports.find? (· != port) with
      | some other => #[(other, ((a.port other).degree : Int))]
      | none => #[]
    | none => #[]
  | .northSouthPort =>
    match pt.internal.origin with
    | some (.lPort originPort) => #[(originPort, (pt.degree : Int))]
    | _ => #[]
  | _ => #[]

/-- `countNorthSouthCrossingsOnPorts(ports)`. -/
def countNorthSouthCrossingsOnPorts (a : LGraphArena) (positions : Array Int) (tree : BinaryIndexedTree) (ports : Array LPortId) :
    Int × BinaryIndexedTree := Id.run do
  let mut crossings : Int := 0
  let mut tree := tree
  for port in ports do
    let currentPosition := positionIn positions a port
    tree := tree.removeAll (asUsize currentPosition)
    let mut ends : Array Int := #[]
    for (targetPort, degree) in northSouthTargetsAndDegrees a port do
      let endPosition := positionIn positions a targetPort
      if endPosition > currentPosition then
        crossings := crossings + tree.rank (asUsize endPosition) * degree
        ends := ends.push endPosition
    tree := addEndsArray tree ends
  return (crossings, tree)

/-! ### North/south counting without intermediate arrays (Lean only)

`initPositionsForNorthSouthCountingFast`/`countNorthSouthCrossingsOnPortsFast` do what
`initPositionsForNorthSouthCounting`/`countNorthSouthCrossingsOnPorts` do (the same positions in
the same order, the same port list, the same tree operations in the same order) without building
the side views, the filtered port lists, the target lists or the `for` loop states: the side views
are walked in place (`sideView`, the same view as `getPortSideView`), and the targets of a port are
read twice (ranks, then additions; the additions of a port commute). -/

/-- The numbering state: positions, the numbered ports, the next index and the stack of dummies. -/
structure NSState where
  positions : Array Int
  ports : Array LPortId
  index : Int
  stack : Array LNodeId
  deriving Inhabited

/-- Numbers port `p` (`positions[LPort.id] := index`, pushed onto the ports). -/
@[inline] def nsNumber (a : LGraphArena) (p : LPortId) (st : NSState) : NSState :=
  match st with
  | ⟨positions, ports, index, stack⟩ => ⟨setPosition positions (portIdOf a p) index, ports.push p, index + 1, stack⟩

/-- Pushes a dummy onto the stack. -/
@[inline] def nsPush (n : LNodeId) (st : NSState) : NSState :=
  match st with
  | ⟨positions, ports, index, stack⟩ => ⟨positions, ports, index, stack.push n⟩

/-- Numbers the ports of a side view (`ports[lo:hi]`) from position `j`, only those with a
`PORT_DUMMY` with `needDummy`. -/
partial def nsNumberView (a : LGraphArena) (ports : Array LPortId) (v : SideView) (needDummy : Bool)
    (j : Nat) (st : NSState) : NSState :=
  if h : j < v.hi ∧ j < ports.size then
    let p := ports[j]
    let st := if !needDummy || (a.port p).internal.portDummy.isSome then nsNumber a p st else st
    nsNumberView a ports v needDummy (j + 1) st
  else st

/-- The position of `getPortSideView(side)[0]` in the node's port list (`ports.size`: empty view). -/
@[inline] def firstIdxOnSide (a : LGraphArena) (n : LNodeId) (nd : LNode) (side : PortSide) : Nat :=
  let v := sideView a n nd side
  if v.lo < v.hi && v.lo < nd.ports.size then v.lo else nd.ports.size

/-- Numbers `getPortSideView(side)[0]` of a node when the view is not empty. -/
@[inline] def nsNumberFirst (a : LGraphArena) (n : LNodeId) (nd : LNode) (side : PortSide) (st : NSState) : NSState :=
  let k := firstIdxOnSide a n nd side
  if h : k < nd.ports.size then nsNumber a nd.ports[k] st else st

/-- `emptyStack(stack, ports, EAST, index)`: numbers the first eastern port of every stacked dummy
(LIFO). -/
partial def nsEmptyStack (a : LGraphArena) (st : NSState) : NSState :=
  match st with
  | ⟨positions, ports, index, stack⟩ =>
    if stack.isEmpty then ⟨positions, ports, index, stack⟩
    else
      let dummy := stack.back!
      nsEmptyStack a (nsNumberFirst a dummy (a.node dummy) .east ⟨positions, ports, index, stack.pop⟩)

/-- The node loop of `initPositionsForNorthSouthCounting` from `nodes[i]` (`hasLast`/`last`: the last
layout unit). -/
partial def nsInitLoop (a : LGraphArena) (nodes : Array LNodeId) (i : Nat) (hasLast : Bool) (last : LNodeId)
    (st : NSState) : NSState :=
  if h : i < nodes.size then
    let current := nodes[i]
    let nd := a.node current
    let layoutUnit := nd.internal.inLayerLayoutUnit
    let changed := hasLast && last != current && (match layoutUnit with
      | some u => u != last
      | none => false)
    let st := if changed then nsEmptyStack a st else st
    let hasLast := hasLast || layoutUnit.isSome
    let last := match layoutUnit with
      | some u => u
      | none => last
    match nd.type with
    | .normal =>
      let vn := sideView a current nd .north
      let st := nsNumberView a nd.ports vn true vn.lo st
      let st := nsEmptyStack a st
      let vs := sideView a current nd .south
      let st := nsNumberView a nd.ports vs true vs.lo st
      nsInitLoop a nodes (i + 1) hasLast last st
    | .northSouthPort =>
      let st := nsNumberFirst a current nd .west st
      let st := if firstIdxOnSide a current nd .east < nd.ports.size then nsPush current st else st
      nsInitLoop a nodes (i + 1) hasLast last st
    | .longEdge =>
      let vw := sideView a current nd .west
      let st := nsNumberView a nd.ports vw false vw.lo st
      let st := if firstIdxOnSide a current nd .east < nd.ports.size then nsPush current st else st
      nsInitLoop a nodes (i + 1) hasLast last st
    | _ => nsInitLoop a nodes (i + 1) hasLast last st
  else nsEmptyStack a st

/-- `initPositionsForNorthSouthCounting(nodes)` (see "North/south counting without intermediate arrays"). -/
def initPositionsForNorthSouthCountingFast (a : LGraphArena) (positions : Array Int) (nodes : Array LNodeId) :
    Array Int × Array LPortId :=
  let st := nsInitLoop a nodes 0 false default ⟨positions, #[], 0, #[]⟩
  (st.positions, st.ports)

/-- Sum of `rank(endPosition) * degree` over the ports `targets[k:]` above `cur` (the degree of each
target's own port with `ownDegree`, else `degree`). -/
partial def nsRankPorts (a : LGraphArena) (positions : Array Int) (tree : BinaryIndexedTree) (cur : Int)
    (targets : Array LPortId) (k : Nat) (acc : Int) : Int :=
  if h : k < targets.size then
    let tp := targets[k]
    let e := positionIn positions a tp
    nsRankPorts a positions tree cur targets (k + 1)
      (if e > cur then acc + tree.rank (asUsize e) * ((a.port tp).degree : Int) else acc)
  else acc

/-- `add(endPosition)` for the ports `targets[k:]` above `cur`. -/
partial def nsAddPorts (a : LGraphArena) (positions : Array Int) (cur : Int) (targets : Array LPortId) (k : Nat)
    (tree : BinaryIndexedTree) : BinaryIndexedTree :=
  if h : k < targets.size then
    let e := positionIn positions a targets[k]
    nsAddPorts a positions cur targets (k + 1) (if e > cur then tree.add (asUsize e) else tree)
  else tree

/-- The port loop of `countNorthSouthCrossingsOnPorts` (the targets of `northSouthTargetsAndDegrees`). -/
partial def nsCountLoop (a : LGraphArena) (positions : Array Int) (ports : Array LPortId) (i : Nat)
    (tree : BinaryIndexedTree) (crossings : Int) : Int × BinaryIndexedTree :=
  if h : i < ports.size then
    let port := ports[i]
    let cur := positionIn positions a port
    let tree := tree.removeAll (asUsize cur)
    let pt := a.port port
    let nodeType := match pt.owner with
      | some n => (a.node n).type
      | none => NodeType.normal
    match nodeType with
    | .normal =>
      match pt.internal.portDummy with
      | some dummy =>
        let targets := (a.node dummy).ports
        let crossings := nsRankPorts a positions tree cur targets 0 crossings
        nsCountLoop a positions ports (i + 1) (nsAddPorts a positions cur targets 0 tree) crossings
      | none => nsCountLoop a positions ports (i + 1) tree crossings
    | .longEdge =>
      let other := match pt.owner with
        | some n => (a.node n).ports.find? (· != port)
        | none => none
      match other with
      | some o =>
        let e := positionIn positions a o
        if e > cur then
          let crossings := crossings + tree.rank (asUsize e) * ((a.port o).degree : Int)
          nsCountLoop a positions ports (i + 1) (tree.add (asUsize e)) crossings
        else nsCountLoop a positions ports (i + 1) tree crossings
      | none => nsCountLoop a positions ports (i + 1) tree crossings
    | .northSouthPort =>
      match pt.internal.origin with
      | some (.lPort originPort) =>
        let e := positionIn positions a originPort
        if e > cur then
          let crossings := crossings + tree.rank (asUsize e) * (pt.degree : Int)
          nsCountLoop a positions ports (i + 1) (tree.add (asUsize e)) crossings
        else nsCountLoop a positions ports (i + 1) tree crossings
      | _ => nsCountLoop a positions ports (i + 1) tree crossings
    | _ => nsCountLoop a positions ports (i + 1) tree crossings
  else (crossings, tree)

/-- `countNorthSouthCrossingsOnPorts(ports)` (see "North/south counting without intermediate arrays"). -/
def countNorthSouthCrossingsOnPortsFast (a : LGraphArena) (positions : Array Int) (tree : BinaryIndexedTree)
    (ports : Array LPortId) : Int × BinaryIndexedTree :=
  nsCountLoop a positions ports 0 tree 0

/-- `connectedInLayerPortsSortedByPosition(upperNode, lowerNode, side)`: the side's ports of both
nodes with non-self-loop edges plus the far ends of their in-layer edges, collected like Java's
`TreeSet` ordered by position: a port whose position equals that of a port collected before is
dropped (far ends outside the counted sides keep stale positions, so distinct ports can share one;
elk-rs de-duplicates by identity), then sorted by position. -/
def connectedInLayerPortsSortedByPosition (a : LGraphArena) (positions : Array Int) (upperNode lowerNode : LNodeId)
    (side : PortSide) : Array LPortId := Id.run do
  let mut ports : Array LPortId := #[]
  let mut seen : Std.HashSet Int := {}
  for node in #[upperNode, lowerNode] do
    for port in CrossMinUtil.inNorthSouthEastWestOrder a node side do
      for e in (a.port port).connectedEdges do
        if a.edgeIsSelfLoop e then continue
        let pos := positionIn positions a port
        if !seen.contains pos then
          seen := seen.insert pos
          ports := ports.push port
        if isInLayer a e then
          if let some other := otherEndOf a e port then
            let otherPos := positionIn positions a other
            if !seen.contains otherPos then
              seen := seen.insert otherPos
              ports := ports.push other
  return stableSortByKey ports (positionIn positions a ·)

/-- `connectedPortsSortedByPosition(upperPort, lowerPort)`: both ports and the far ends of their
edges (port self loops skipped), collected like Java's `TreeSet` ordered by position (a port whose
position was already collected is dropped, see `connectedInLayerPortsSortedByPosition`) and sorted
by position. -/
def connectedPortsSortedByPosition (a : LGraphArena) (positions : Array Int) (upperPort lowerPort : LPortId) :
    Array LPortId := Id.run do
  let mut ports : Array LPortId := #[]
  let mut seen : Std.HashSet Int := {}
  for port in #[upperPort, lowerPort] do
    let pos := positionIn positions a port
    if !seen.contains pos then
      seen := seen.insert pos
      ports := ports.push port
    for e in (a.port port).connectedEdges do
      if isPortSelfLoop a e then continue
      if let some other := otherEndOf a e port then
        let otherPos := positionIn positions a other
        if !seen.contains otherPos then
          seen := seen.insert otherPos
          ports := ports.push other
  return stableSortByKey ports (positionIn positions a ·)

/-! ### Port sets of the both-orders counts without hash sets

`connectedInLayerPortsSortedByPositionFast` and `connectedPortsSortedByPositionFast` collect the same
ports in the same order as the reference loops above (Java's `TreeSet` keyed by position: a port
whose position was collected before is dropped), with the collected positions searched linearly while
there are at most `PosSeen.linearMax` of them (then a hash set), the edges walked as `incomingEdges`
then `outgoingEdges` (`connectedEdges` without the concatenation) and the side view walked in place.
All collected positions are distinct, so the stable sort by position has exactly one result, which
`sortPortsByKeys` (insertion sort of the collected positions) produces. -/

/-- The positions collected so far, with their ports. -/
structure PosSeen where
  ports : Array LPortId := #[]
  poss : Array Int := #[]
  set : Std.HashSet Int := {}
  big : Bool := false
  deriving Inhabited

namespace PosSeen

/-- Up to this many positions `contains` scans `poss`. -/
def linearMax : Nat := 16

/-- Whether `x` occurs in `poss[i:]`. -/
partial def scan (poss : Array Int) (x : Int) (i : Nat) : Bool :=
  if h : i < poss.size then poss[i] == x || scan poss x (i + 1) else false

/-- Whether position `x` was collected. -/
@[inline] def contains (st : PosSeen) (x : Int) : Bool :=
  if st.big then st.set.contains x else scan st.poss x 0

/-- `poss[i:]` added to `set`. -/
partial def fill (poss : Array Int) (i : Nat) (set : Std.HashSet Int) : Std.HashSet Int :=
  if h : i < poss.size then fill poss (i + 1) (set.insert poss[i]) else set

/-- Collects port `p` at position `x` unless `x` was collected. -/
@[noinline] def add (st : PosSeen) (p : LPortId) (x : Int) : PosSeen :=
  if st.contains x then st
  else
    match st with
    | ⟨ports, poss, set, big⟩ =>
      let ports := ports.push p
      let poss := poss.push x
      if big then ⟨ports, poss, set.insert x, true⟩
      else if poss.size > linearMax then ⟨ports, poss, fill poss 0 set, true⟩
      else ⟨ports, poss, set, false⟩

end PosSeen

/-- Inserts `ports[i]` (key `keys[i]`) into the sorted prefix `[0, i)`: moves it down while the key
before is strictly greater (stable). -/
partial def insertByKey (keys : Array Int) (ports : Array LPortId) (j : Nat) (k : Int) (p : LPortId) :
    Array Int × Array LPortId :=
  if j > 0 then
    let kj := keys[j - 1]!
    if kj > k then insertByKey (keys.set! j kj) (ports.set! j ports[j - 1]!) (j - 1) k p
    else (keys.set! j k, ports.set! j p)
  else (keys.set! j k, ports.set! j p)

/-- Insertion sort of `ports` by `keys` from `i` on (stable). -/
partial def insertionSortByKey (keys : Array Int) (ports : Array LPortId) (i : Nat) : Array LPortId :=
  if i < keys.size && i < ports.size then
    let (keys, ports) := insertByKey keys ports i keys[i]! ports[i]!
    insertionSortByKey keys ports (i + 1)
  else ports

/-- The ports sorted stably by `keys` (their positions): the stable sort has a unique result, so an
insertion sort for short arrays and `stableSortByKey` otherwise. -/
def sortPortsByKeys (a : LGraphArena) (positions : Array Int) (ports : Array LPortId) (keys : Array Int) : Array LPortId :=
  if ports.size <= 32 then insertionSortByKey keys ports 1
  else stableSortByKey ports (positionIn positions a ·)

/-- `stableSortByKey ports (positionIn positions a ·)` (see `sortPortsByKeys`). -/
def sortPortsByPosition (a : LGraphArena) (positions : Array Int) (ports : Array LPortId) : Array LPortId :=
  if ports.size <= 32 then insertionSortByKey (ports.map (positionIn positions a ·)) ports 1
  else stableSortByKey ports (positionIn positions a ·)

/-- The edge loop of `connectedInLayerPortsSortedByPosition` for port `p` (position `pos`) over
`edges[k:]`. -/
partial def collectInLayerEdges (a : LGraphArena) (positions : Array Int) (p : LPortId) (pos : Int)
    (edges : Array LEdgeId) (k : Nat) (st : PosSeen) : PosSeen :=
  if h : k < edges.size then
    let e := edges[k]
    if a.edgeIsSelfLoop e then collectInLayerEdges a positions p pos edges (k + 1) st
    else
      let st := st.add p pos
      let st := if isInLayer a e then
          match otherEndOf a e p with
          | some other => st.add other (positionIn positions a other)
          | none => st
        else st
      collectInLayerEdges a positions p pos edges (k + 1) st
  else st

/-- The port loop of `connectedInLayerPortsSortedByPosition` over the view `ports[lo:hi]` of a node
(downwards from `hi` when `rev`). -/
partial def collectInLayerPorts (a : LGraphArena) (positions : Array Int) (ports : Array LPortId) (lo hi : Nat)
    (rev : Bool) (st : PosSeen) : PosSeen :=
  if lo < hi then
    let j := if rev then hi - 1 else lo
    match ports[j]? with
    | some p =>
      let pt := a.port p
      let pos := positionIn positions a p
      let st := collectInLayerEdges a positions p pos pt.incomingEdges 0 st
      let st := collectInLayerEdges a positions p pos pt.outgoingEdges 0 st
      if rev then collectInLayerPorts a positions ports lo (hi - 1) rev st
      else collectInLayerPorts a positions ports (lo + 1) hi rev st
    | none => st
  else st

/-- `connectedInLayerPortsSortedByPosition` without hash sets and intermediate arrays (see "Port sets
of the both-orders counts without hash sets"). -/
def connectedInLayerPortsSortedByPositionFast (a : LGraphArena) (positions : Array Int) (upperNode lowerNode : LNodeId)
    (side : PortSide) : Array LPortId :=
  let visit (node : LNodeId) (st : PosSeen) : PosSeen :=
    match side with
    | .undefined => st
    | _ =>
      let nd := a.node node
      let v := sideView a node nd side
      collectInLayerPorts a positions nd.ports v.lo v.hi (side matches .south | .west) st
  let st := visit lowerNode (visit upperNode {})
  sortPortsByKeys a positions st.ports st.poss

/-- The far ends of `edges[k:]` of `port` for `connectedPortsSortedByPosition` (port self loops
skipped). -/
partial def collectFarEnds (a : LGraphArena) (positions : Array Int) (port : LPortId) (edges : Array LEdgeId) (k : Nat)
    (st : PosSeen) : PosSeen :=
  if h : k < edges.size then
    let e := edges[k]
    if isPortSelfLoop a e then collectFarEnds a positions port edges (k + 1) st
    else
      match otherEndOf a e port with
      | some other => collectFarEnds a positions port edges (k + 1) (st.add other (positionIn positions a other))
      | none => collectFarEnds a positions port edges (k + 1) st
  else st

/-- `connectedPortsSortedByPosition` without hash sets and intermediate arrays. -/
def connectedPortsSortedByPositionFast (a : LGraphArena) (positions : Array Int) (upperPort lowerPort : LPortId) :
    Array LPortId :=
  let visit (port : LPortId) (st : PosSeen) : PosSeen :=
    let pt := a.port port
    let st := st.add port (positionIn positions a port)
    collectFarEnds a positions port pt.outgoingEdges 0 (collectFarEnds a positions port pt.incomingEdges 0 st)
  let st := visit lowerPort (visit upperPort {})
  sortPortsByKeys a positions st.ports st.poss

/-! ## Construction -/

/-- `new CrossingsCounter(portPositions)` sharing the given position array. -/
def new (portPositions : IO.Ref (Array Int)) : BaseIO CrossingsCounter := do
  return { portPositions, indexTree := ← IO.mkRef (BinaryIndexedTree.new 0), nodeCardinalities := ← IO.mkRef #[],
           snapshot := ← IO.mkRef none, idScratch := ← IO.mkRef #[] }

/-- elk-rs `set_snapshot(snapshot)`. -/
def setSnapshot (c : CrossingsCounter) (s : CrossMinSnapshot) : BaseIO Unit := c.snapshot.set (some s)

/-- elk-rs `CrossingsCounter::new(port_positions)`: a counter owning a copy of the positions. -/
def ofPositions (portPositions : Array Int) : BaseIO CrossingsCounter := do
  new (← IO.mkRef portPositions)

/-- Resets the counter to the state of a fresh `CrossingsCounter::new(portPositions)`. -/
def resetTo (c : CrossingsCounter) (portPositions : Array Int) : BaseIO Unit := do
  c.portPositions.set portPositions
  c.indexTree.set (BinaryIndexedTree.new 0)
  c.nodeCardinalities.set #[]

/-! ## Internal monadic steps -/

/-- `initPositions` on the counter's state. -/
private def initPositionsM (c : CrossingsCounter) (nodes : Array LNodeId) (ports : Array LPortId) (side : PortSide)
    (topDown getCardinalities : Bool) : LayeredM (Array LPortId) := do
  let a ← get
  let positions ← c.portPositions.swap #[]
  let cards ← c.nodeCardinalities.swap #[]
  let (positions, cards, ports) := initPositions a positions cards nodes ports side topDown getCardinalities
  c.portPositions.set positions
  c.nodeCardinalities.set cards
  return ports

/-- `initPortPositionsCounterClockwise(leftLayer, rightLayer)`: eastern ports of the left layer
top-down, then western ports of the right layer bottom-up. -/
private def initPortPositionsCounterClockwise (c : CrossingsCounter) (leftLayer rightLayer : Array LNodeId) :
    LayeredM (Array LPortId) := do
  let ports ← c.initPositionsM leftLayer #[] .east true false
  c.initPositionsM rightLayer ports .west false false

/-- The text of the `ArrayIndexOutOfBoundsException` Java throws while `countCrossingsOnPorts`
(`inLayer = false`) or `countInLayerCrossingsOnPorts` (`inLayer = true`) runs over `ports` with a tree
of `maxNum` buckets, if any: per port `removeAll(cur)` (`numsPerIndex[cur]`, length `maxNum`), per
(in-layer) edge whose far end lies above `rank(end)` (`binarySums[end]`, length `maxNum + 1`), then the
`add(end)`s (`numsPerIndex[end]`, after all ranks of the port; every failing `add` has index
`maxNum`). The accessed indices depend only on the positions. Positions are fresh for the ports a
counter numbered, but far ends elsewhere keep the positions an earlier numbering left in the shared
array (e.g. the other side's in-layer counter of a greedy switch decider), which can exceed the
tree. Only evaluated when the count set the tree's `outOfRange` flag. -/
def javaTreeIndexError (a : LGraphArena) (positions : Array Int) (maxNum : Nat) (ports : Array LPortId)
    (inLayer : Bool) : Option String := Id.run do
  let oob (i : Int) (len : Nat) : String :=
    s!"java.lang.ArrayIndexOutOfBoundsException: Index {i} out of bounds for length {len}"
  let m : Int := maxNum
  for port in ports do
    let cur := positionIn positions a port
    if cur < 0 || cur >= m then return some (oob cur maxNum)
    let pt := a.port port
    let mut addFails := false
    for edges in #[pt.incomingEdges, pt.outgoingEdges] do
      for e in edges do
        if inLayer && !isInLayer a e then continue
        let some other := otherEndOf a e port | continue
        let endPosition := positionIn positions a other
        if endPosition > cur then
          if endPosition > m then return some (oob endPosition (maxNum + 1))
          if endPosition == m then addFails := true
    if addFails then return some (oob m maxNum)
  return none

/-- A both-orders count with Java's index checks: the unchecked loop, then (only when the tree saw
an index outside its range) Java's exception text for the first failing access. -/
private def withTreeChecked (c : CrossingsCounter) (ports : Array LPortId) (inLayer : Bool) : LayeredM Int := do
  let a ← get
  let positions ← c.portPositions.get
  let tree ← c.indexTree.swap {}
  let maxNum := tree.maxNum
  let (crossings, tree) :=
    if inLayer then countInLayerCrossingsOnPorts a positions tree ports else countCrossingsOnPorts a positions tree ports
  c.indexTree.set tree
  if tree.outOfRange then
    if let some msg := javaTreeIndexError a positions maxNum ports inLayer then
      throw (IO.userError msg)
  return crossings

/-- Throws Java's exception for the first failing tree access of counting `ports` on a tree of
`ports.size` buckets (`javaTreeIndexError`); a generic one if none is found (cannot happen when a
far end above its port lies outside the tree). -/
private def throwJavaTreeIndexError {α : Type} (c : CrossingsCounter) (ports : Array LPortId) (inLayer : Bool) :
    LayeredM α := do
  let positions ← c.portPositions.get
  match javaTreeIndexError (← get) positions ports.size ports inLayer with
  | some msg => throw (IO.userError msg)
  | none => throw (IO.userError "java.lang.ArrayIndexOutOfBoundsException: binary indexed tree")

/-- Runs one of the pure counting loops on the counter's tree. -/
@[inline] private def withTree (c : CrossingsCounter)
    (count : LGraphArena → Array Int → BinaryIndexedTree → Array LPortId → Int × BinaryIndexedTree)
    (ports : Array LPortId) : LayeredM Int := do
  let a ← get
  let positions ← c.portPositions.get
  let tree ← c.indexTree.swap {}
  let (crossings, tree) := count a positions tree ports
  c.indexTree.set tree
  return crossings

/-! ## Public API -/

/-- `initPortPositionsForInLayerCrossings(nodes, side)`: numbers the side's ports top-down,
records the node cardinalities and resets the tree; returns the ports. -/
def initPortPositionsForInLayerCrossings (c : CrossingsCounter) (nodes : Array LNodeId) (side : PortSide) :
    LayeredM (Array LPortId) := do
  let ports ← c.initPositionsM nodes #[] side true true
  c.indexTree.set (BinaryIndexedTree.new ports.size)
  return ports

/-- `initForCountingBetween(leftLayerNodes, rightLayerNodes)`. -/
def initForCountingBetween (c : CrossingsCounter) (leftLayer rightLayer : Array LNodeId) : LayeredM Unit := do
  let ports ← c.initPortPositionsCounterClockwise leftLayer rightLayer
  c.indexTree.set (BinaryIndexedTree.new ports.size)

/-- `countCrossingsBetweenLayers(leftLayerNodes, rightLayerNodes)` (with a snapshot: see
"Between-layer counting on the snapshot path"). -/
def countCrossingsBetweenLayers (c : CrossingsCounter) (leftLayer rightLayer : Array LNodeId) : LayeredM Int := do
  match ← c.snapshot.get with
  | some s =>
    let a ← get
    let positions ← c.portPositions.swap #[]
    let pids ← c.idScratch.swap #[]
    let (positions, pids, len) := numberSideViewsSnap a s leftLayer .east true 0 #[] 0 0 false 0 positions pids
    let (positions, pids, n) := numberSideViewsSnap a s rightLayer .west false 0 #[] 0 0 false len positions pids
    c.portPositions.set positions
    let (crossings, t) := countBetweenSnapLoop s positions pids 0 n (Array.replicate (2 * n + 2) 0) #[] 0 0
    c.idScratch.set pids
    if outOfRangeMarked t n then
      -- a far end's stale position beyond the tree: Java's exception (the live numbering is the same)
      let ports ← c.initPortPositionsCounterClockwise leftLayer rightLayer
      c.throwJavaTreeIndexError ports false
    return crossings
  | none =>
    let ports ← c.initPortPositionsCounterClockwise leftLayer rightLayer
    c.indexTree.set (BinaryIndexedTree.new ports.size)
    c.withTreeChecked ports false

/-- `countInLayerCrossingsOnSide(nodes, side)`. -/
def countInLayerCrossingsOnSide (c : CrossingsCounter) (nodes : Array LNodeId) (side : PortSide) : LayeredM Int := do
  if let some s ← c.snapshot.get then
    if nodes.all (noPortOnSide s · side) then
      -- no node has a port on `side` (`noPortOnSide`): `initPortPositionsForInLayerCrossings` numbers
      -- nothing, so the cardinalities become zeros, the tree is empty and nothing crosses
      if !nodes.isEmpty then c.nodeCardinalities.set (Array.replicate nodes.size 0)
      c.indexTree.set (BinaryIndexedTree.new 0)
      return 0
    -- the snapshot path (see "In-layer counting on the snapshot path")
    let a ← get
    let positions ← c.portPositions.swap #[]
    let pids ← c.idScratch.swap #[]
    -- `getPorts(node, side, true)`: the `EAST` views as they are, the others reversed
    let (positions, pids, n) := if sideIs side .east then
        numberSideViewsSnap a s nodes side true 0 #[] 0 0 false 0 positions pids
      else numberSideViewsSnapRev a s nodes side 0 #[] 0 0 false 0 positions pids
    if !allEndsOk s pids 0 n then
      -- ports whose far ends the snapshot does not know: the live path (which numbers the same again)
      c.portPositions.set positions
      c.idScratch.set pids
    else
      let (crossings, t) := countInLayerSnapLoop s positions pids 0 n (Array.replicate (2 * n + 2) 0) 0 0
      c.portPositions.set positions
      c.idScratch.set pids
      if outOfRangeMarked t n then
        -- a far end's stale position beyond the tree: Java's exception (the live numbering is the same)
        let ports ← c.initPortPositionsForInLayerCrossings nodes side
        c.throwJavaTreeIndexError ports true
      return crossings
  let ports ← c.initPortPositionsForInLayerCrossings nodes side
  c.withTreeChecked ports true

/-- `countNorthSouthPortCrossingsInLayer(layer)` (with the `…Fast` loops). -/
def countNorthSouthPortCrossingsInLayer (c : CrossingsCounter) (layer : Array LNodeId) : LayeredM Int := do
  let a ← get
  let positions ← c.portPositions.swap #[]
  let (positions, ports) := initPositionsForNorthSouthCountingFast a positions layer
  c.portPositions.set positions
  c.indexTree.set (BinaryIndexedTree.new ports.size)
  c.withTree countNorthSouthCrossingsOnPortsFast ports

/-- `countNorthSouthPortCrossingsInLayer(layer)` with the line-by-line port loops (reference of the
differential test). -/
def countNorthSouthPortCrossingsInLayerPort (c : CrossingsCounter) (layer : Array LNodeId) : LayeredM Int := do
  let a ← get
  let positions ← c.portPositions.swap #[]
  let (positions, ports) := initPositionsForNorthSouthCounting a positions layer
  c.portPositions.set positions
  c.indexTree.set (BinaryIndexedTree.new ports.size)
  c.withTree countNorthSouthCrossingsOnPorts ports

/-- `switchPorts(topPort, bottomPort)`: swaps the two positions (no-op when a port has no slot). -/
def switchPorts (c : CrossingsCounter) (topPort bottomPort : LPortId) : LayeredM Unit := do
  let a ← get
  let topIndex := portIdOf a topPort
  let bottomIndex := portIdOf a bottomPort
  c.portPositions.modify fun pos =>
    if topIndex >= pos.size || bottomIndex >= pos.size then pos else pos.swapIfInBounds topIndex bottomIndex

/-- `switchNodes(wasUpperNode, wasLowerNode, side)`: shifts the side's ports of the former upper
node down by the lower node's cardinality and vice versa. -/
def switchNodes (c : CrossingsCounter) (wasUpper wasLower : LNodeId) (side : PortSide) : LayeredM Unit := do
  let a ← get
  let cards ← c.nodeCardinalities.get
  let upperShift := cards[nodeIdOf a wasLower]?.getD 0
  let lowerShift := cards[nodeIdOf a wasUpper]?.getD 0
  let upperPorts := CrossMinUtil.inNorthSouthEastWestOrder a wasUpper side
  let lowerPorts := CrossMinUtil.inNorthSouthEastWestOrder a wasLower side
  c.portPositions.modify fun pos => Id.run do
    let mut pos := pos
    for p in upperPorts do
      pos := pos.modify (portIdOf a p) (· + upperShift)
    for p in lowerPorts do
      pos := pos.modify (portIdOf a p) (· - lowerShift)
    return pos

/-- `countCrossingsBetweenPortsInBothOrders(upperPort, lowerPort)`: crossings of the edges at the
two ports in the current and in the switched order. Initialise with `initForCountingBetween`
(or `initPortPositionsForInLayerCrossings` at the graph border) first. -/
def countCrossingsBetweenPortsInBothOrders (c : CrossingsCounter) (upperPort lowerPort : LPortId) :
    LayeredM (Int × Int) := do
  let a ← get
  let ports := connectedPortsSortedByPositionFast a (← c.portPositions.get) upperPort lowerPort
  let upperLowerCrossings ← c.withTreeChecked ports false
  c.indexTree.modify (·.clear)
  c.switchPorts upperPort lowerPort
  let ports := sortPortsByPosition a (← c.portPositions.get) ports
  let lowerUpperCrossings ← c.withTreeChecked ports false
  c.indexTree.modify (·.clear)
  c.switchPorts lowerPort upperPort
  return (upperLowerCrossings, lowerUpperCrossings)

/-- `countInLayerCrossingsBetweenNodesInBothOrders(upperNode, lowerNode, side)`: in-layer
crossings at the two nodes in the current and in the switched order. Initialise with
`initPortPositionsForInLayerCrossings` first. -/
def countInLayerCrossingsBetweenNodesInBothOrders (c : CrossingsCounter) (upperNode lowerNode : LNodeId)
    (side : PortSide) : LayeredM (Int × Int) := do
  let a ← get
  let ports := connectedInLayerPortsSortedByPositionFast a (← c.portPositions.get) upperNode lowerNode side
  let upperLowerCrossings ← c.withTreeChecked ports true
  c.switchNodes upperNode lowerNode side
  c.indexTree.modify (·.clear)
  let ports := sortPortsByPosition a (← c.portPositions.get) ports
  let lowerUpperCrossings ← c.withTreeChecked ports true
  c.switchNodes lowerNode upperNode side
  c.indexTree.modify (·.clear)
  return (upperLowerCrossings, lowerUpperCrossings)

/-- Current port positions (testing/debugging). -/
def currentPositions (c : CrossingsCounter) : BaseIO (Array Int) := c.portPositions.get

end CrossingsCounter

end Elk.Alg.Layered.P3Order.Counting
