import Elk.Alg.Layered.Graph
import Elk.Alg.Layered.P3Order.Counting.BinaryIndexedTree
import Elk.Alg.Layered.P3Order.Counting.CrossMinUtil
import Elk.Core.Util.Sort
import Std.Data.HashMap
import Std.Data.HashSet
/-!
# `org.eclipse.elk.alg.layered.p3order.counting.HyperedgeCrossingsCounter`

Approximates the crossings between two layers when ports carry several edges (hyperedges), after
Gansner et al. / Sander (elk-rs `hyperedge_crossings_counter.rs`). Port positions are indexed by
`LPort.id` in `portPositions`, which `AllCrossingsCounter` shares with its `CrossingsCounter`
(`shared`, Java's single `portPos` array; elk-rs used a separate one).

The hyperedge identity used as the last sort key (Rust: address of the first source port, Java:
`hashCode()`) is the arena index of that port. Identities are unique per active hyperedge, so the
count does not depend on their actual values. The `edges` list of the Rust `Hyperedge` is only
used for tracing and is not kept. `countCrossings` runs `countCrossingsFast` (see "Allocation-poor
counting"); `countCrossingsPure` is the line-by-line port (`countCrossingsPort`, differential test).
-/
namespace Elk.Alg.Layered.P3Order.Counting

open Elk.Core.Options Elk.Core.Util Elk.Alg.Layered.Graph

/-- `HyperedgeCrossingsCounter.Hyperedge`: its ports and the position bounds on both sides. -/
structure Hyperedge where
  identity : Nat
  ports : Array LPortId := #[]
  upperLeft : Int := 0
  lowerLeft : Int := 0
  upperRight : Int := 0
  lowerRight : Int := 0
  deriving Inhabited

namespace Hyperedge

/-- `Hyperedge.compareTo`: by upper left, upper right, identity. -/
def compare (a b : Hyperedge) : Ordering :=
  (Ord.compare a.upperLeft b.upperLeft).then ((Ord.compare a.upperRight b.upperRight).then (Ord.compare a.identity b.identity))

end Hyperedge

/-- `HyperedgeCorner`: `upper = true` for an upper corner. -/
structure HyperedgeCorner where
  identity : Nat
  position : Int
  oppositePosition : Int
  upper : Bool
  deriving Inhabited

namespace HyperedgeCorner

/-- `HyperedgeCorner.compareTo`: by position, opposite position, identity, upper before lower. -/
def compare (a b : HyperedgeCorner) : Ordering :=
  let typeOrder : Ordering := match a.upper, b.upper with
    | true, false => .lt
    | false, true => .gt
    | _, _ => .eq
  (Ord.compare a.position b.position).then
    ((Ord.compare a.oppositePosition b.oppositePosition).then ((Ord.compare a.identity b.identity).then typeOrder))

end HyperedgeCorner

/-- The scratch arrays of `HyperedgeCrossingsCounter.countCrossingsFast` (zero between calls; Lean
only). -/
structure HyperedgeCrossingsCounter.Scratch where
  /-- Per node arena index: bit `0` in the left layer, bit `1` in the right layer. -/
  marks : ByteArray := ByteArray.empty
  /-- Per port arena index: `hyperedge index + 1` (`0`: none). -/
  slots : Array Nat := #[]
  deriving Inhabited

/-- `HyperedgeCrossingsCounter`. -/
structure HyperedgeCrossingsCounter where
  /-- `portPos` (indexed by `LPort.id`). -/
  portPositions : IO.Ref (Array Int)
  /-- The scratch of `countCrossingsFast` (Lean only). -/
  scratch : IO.Ref HyperedgeCrossingsCounter.Scratch

namespace HyperedgeCrossingsCounter

/-- `new HyperedgeCrossingsCounter(inLayerEdgeCount, hasNorthSouthPorts, portPos)`; the first two
arguments are unused (as in Java/elk-rs). -/
def new (_inLayerEdgeCount : Array Int) (_hasNorthSouthPorts : Array Bool) (portPositions : Array Int) :
    BaseIO HyperedgeCrossingsCounter := do
  return { portPositions := ← IO.mkRef portPositions, scratch := ← IO.mkRef {} }

/-- `new HyperedgeCrossingsCounter(inLayerEdgeCount, hasNorthSouthPorts, portPos)` sharing the array
`portPos` with other counters (Java `AllCrossingsCounter` hands the same `int[]` to its
`CrossingsCounter`). -/
def shared (portPositions : IO.Ref (Array Int)) : BaseIO HyperedgeCrossingsCounter := do
  return { portPositions, scratch := ← IO.mkRef {} }

/-- Rust `port_id(port)`: `port.id as usize`. -/
@[inline] private def portIdOf (a : LGraphArena) (p : LPortId) : Nat := asUsize (a.port p).id

/-- Rust `set_port_position` (grows the array; invalid ids are ignored). -/
private def setPosition (positions : Array Int) (a : LGraphArena) (p : LPortId) (v : Int) : Array Int :=
  let pid := portIdOf a p
  if pid >>> 32 != 0 then positions
  else
    let positions := if pid >= positions.size then positions ++ Array.replicate (pid + 1 - positions.size) 0 else positions
    positions.setIfInBounds pid v

/-- Rust `port_position(port)` (`0` without a slot). -/
@[inline] private def positionOf (positions : Array Int) (a : LGraphArena) (p : LPortId) : Int :=
  positions[portIdOf a p]?.getD 0

/-- Whether the node at the far end of `port` (`target` for `useTarget`, else `source`) of `e` is
in `nodes` (Rust `is_out_in_layer`/`is_in_in_layer`). -/
@[inline] private def endInSet (a : LGraphArena) (nodes : Std.HashSet LNodeId) (e : LEdgeId) (useTarget : Bool) : Bool :=
  let ed := a.edge e
  let p := if useTarget then ed.target else ed.source
  match p.bind fun p => (a.port p).owner with
  | some n => nodes.contains n
  | none => false

/-- Positions of the left layer's ports with outgoing between-layer edges (top-down), then
of the right layer's ports with incoming between-layer edges (northern ports first, the others
bottom-up per node). Returns the positions and the source/target counts. -/
private def assignPositions (a : LGraphArena) (positions : Array Int) (leftLayer rightLayer : Array LNodeId)
    (leftSet rightSet : Std.HashSet LNodeId) : Array Int × Int × Int := Id.run do
  let mut positions := positions
  let mut sourceCount : Int := 0
  for node in leftLayer do
    for port in (a.node node).ports do
      let portEdges := ((a.port port).outgoingEdges.filter fun e => !endInSet a leftSet e true).size
      if portEdges > 0 then
        positions := setPosition positions a port sourceCount
        sourceCount := sourceCount + 1
  let mut targetCount : Int := 0
  for node in rightLayer do
    let ports := (a.node node).ports
    let mut northInputPorts : Int := 0
    for port in ports do
      let pt := a.port port
      if pt.side == .north then
        if pt.incomingEdges.any fun e => !endInSet a rightSet e false then
          northInputPorts := northInputPorts + 1
      else
        break
    let mut otherInputPorts : Int := 0
    for k in [0:ports.size] do
      let port := ports[ports.size - 1 - k]!
      let pt := a.port port
      let portEdges := (pt.incomingEdges.filter fun e => !endInSet a rightSet e false).size
      if portEdges > 0 then
        if pt.side == .north then
          positions := setPosition positions a port targetCount
          targetCount := targetCount + 1
        else
          positions := setPosition positions a port (targetCount + northInputPorts + otherInputPorts)
          otherInputPorts := otherInputPorts + 1
    targetCount := targetCount + otherInputPorts
  return (positions, sourceCount, targetCount)

/-- Groups the between-layer edges leaving `leftLayer` into hyperedges (union of the edges that
share a port), in creation order; merged hyperedges are dropped. -/
private def collectHyperedges (a : LGraphArena) (leftLayer : Array LNodeId) (leftSet : Std.HashSet LNodeId) :
    Array Hyperedge := Id.run do
  let mut portToHyperedge : Std.HashMap LPortId Nat := {}
  let mut hyperedges : Array Hyperedge := #[]
  let mut active : Array Bool := #[]
  for node in leftLayer do
    for sourcePort in (a.node node).ports do
      for e in (a.port sourcePort).outgoingEdges do
        let some targetPort := (a.edge e).target | continue
        if endInSet a leftSet e true then continue
        match portToHyperedge[sourcePort]?, portToHyperedge[targetPort]? with
        | none, none =>
          let id := hyperedges.size
          hyperedges := hyperedges.push { identity := sourcePort.idx, ports := #[sourcePort, targetPort] }
          active := active.push true
          portToHyperedge := (portToHyperedge.insert sourcePort id).insert targetPort id
        | none, some targetId =>
          hyperedges := hyperedges.modify targetId fun h => { h with ports := h.ports.push sourcePort }
          portToHyperedge := portToHyperedge.insert sourcePort targetId
        | some sourceId, none =>
          hyperedges := hyperedges.modify sourceId fun h => { h with ports := h.ports.push targetPort }
          portToHyperedge := portToHyperedge.insert targetPort sourceId
        | some sourceId, some targetId =>
          if sourceId != targetId && sourceId < hyperedges.size && targetId < hyperedges.size then
            let targetPorts := hyperedges[targetId]!.ports
            for p in targetPorts do
              portToHyperedge := portToHyperedge.insert p sourceId
            hyperedges := hyperedges.modify sourceId fun h => { h with ports := h.ports ++ targetPorts }
            hyperedges := hyperedges.modify targetId fun h => { h with ports := #[] }
            active := active.set! targetId false
  let mut result : Array Hyperedge := #[]
  for i in [0:hyperedges.size] do
    if active[i]! then result := result.push hyperedges[i]!
  return result

/-- Crossings among the hyperedges' straight segments (inversions of the upper right positions
after compressing them, counted with an accumulator tree). -/
private def countStraightCrossings (hyperedges : Array Hyperedge) (targetCount : Int) : Int := Id.run do
  let mut southSequence : Array Int := #[]
  let mut compressDeltas : Array Int := Array.replicate (targetCount + 1).toNat 0
  for h in hyperedges do
    southSequence := southSequence.push h.upperRight
    compressDeltas := compressDeltas.setIfInBounds (asUsize h.upperRight) 1
  let mut delta : Int := 0
  for i in [0:compressDeltas.size] do
    if compressDeltas[i]! == 1 then
      compressDeltas := compressDeltas.set! i delta
    else
      delta := delta - 1
  let mut q : Int := 0
  for i in [0:southSequence.size] do
    let value := southSequence[i]!
    let value := value + (compressDeltas[asUsize value]?.getD 0)
    southSequence := southSequence.set! i value
    q := max q (value + 1)
  let mut firstIndex : Int := 1
  while firstIndex < q do
    firstIndex := firstIndex * 2
  let treeSize := 2 * firstIndex - 1
  firstIndex := firstIndex - 1
  let mut tree : Array Int := Array.replicate treeSize.toNat 0
  let mut crossings : Int := 0
  for value in southSequence do
    let mut index := value + firstIndex
    tree := tree.modify index.toNat (· + 1)
    while index > 0 do
      if index % 2 > 0 then
        crossings := crossings + (tree[(index + 1).toNat]?.getD 0)
      index := (index - 1) / 2
      tree := tree.modify index.toNat (· + 1)
  return crossings

/-- Crossings caused by overlapping hyperedge extents on one side (sweep over sorted corners). -/
private def countOverlapCrossings (corners : Array HyperedgeCorner) : Int := Id.run do
  let corners := stableSort corners HyperedgeCorner.compare
  let mut openHyperedges : Int := 0
  let mut crossings : Int := 0
  for corner in corners do
    if corner.upper then
      openHyperedges := openHyperedges + 1
    else
      openHyperedges := openHyperedges - 1
      crossings := crossings + openHyperedges
  return crossings

/-- Pure core of `countCrossings`: returns the crossings and the updated port positions. -/
def countCrossingsPure (a : LGraphArena) (positions : Array Int) (leftLayer rightLayer : Array LNodeId) :
    Int × Array Int := Id.run do
  if leftLayer.isEmpty || rightLayer.isEmpty then return (0, positions)
  let leftSet : Std.HashSet LNodeId := leftLayer.foldl (·.insert ·) {}
  let rightSet : Std.HashSet LNodeId := rightLayer.foldl (·.insert ·) {}
  let (positions, sourceCount, targetCount) := assignPositions a positions leftLayer rightLayer leftSet rightSet
  let mut hyperedges := collectHyperedges a leftLayer leftSet
  for i in [0:hyperedges.size] do
    let mut h := hyperedges[i]!
    h := { h with upperLeft := sourceCount, upperRight := targetCount }
    for port in h.ports do
      let pos := positionOf positions a port
      match (a.port port).owner with
      | some n =>
        if leftSet.contains n then
          h := { h with upperLeft := min h.upperLeft pos, lowerLeft := max h.lowerLeft pos }
        else if rightSet.contains n then
          h := { h with upperRight := min h.upperRight pos, lowerRight := max h.lowerRight pos }
      | none => pure ()
    hyperedges := hyperedges.set! i h
  hyperedges := stableSort hyperedges Hyperedge.compare
  let mut crossings := countStraightCrossings hyperedges targetCount
  let leftCorners := hyperedges.foldl (fun acc h =>
    (acc.push { identity := h.identity, position := h.upperLeft, oppositePosition := h.lowerLeft, upper := true }).push
      { identity := h.identity, position := h.lowerLeft, oppositePosition := h.upperLeft, upper := false }) #[]
  crossings := crossings + countOverlapCrossings leftCorners
  let rightCorners := hyperedges.foldl (fun acc h =>
    (acc.push { identity := h.identity, position := h.upperRight, oppositePosition := h.lowerRight, upper := true }).push
      { identity := h.identity, position := h.lowerRight, oppositePosition := h.upperRight, upper := false }) #[]
  crossings := crossings + countOverlapCrossings rightCorners
  return (crossings, positions)

/-! ### Allocation-poor counting (Lean only)

`countCrossingsFast` computes what `countCrossingsPure` computes (the same crossings and the same
writes to the position array) with node membership marks and port → hyperedge slots in scratch
arrays indexed by arena index (all zero between calls) instead of `HashSet`/`HashMap`s,
short-circuiting `any` tests where the port counts `filter(..).size > 0`, the sorts of the
hyperedges and corners as `keyedStableSort` over unboxed keys (the same comparisons and moves as
`stableSort` with `Hyperedge.compare`/`HyperedgeCorner.compare`, hence the same order), and tail
recursive loops. The differential test `hyperedge fast = port` compares both on random layers. -/

/-- The mark of a node (`0` beyond the marks). -/
@[inline] def markOf (marks : ByteArray) (n : LNodeId) : UInt8 :=
  if h : n.idx < marks.size then marks[n.idx] else 0

/-- Sets bit `b` of the marks of `nodes[i:]` (`b = 0`: clears them). -/
partial def markNodes (nodes : Array LNodeId) (i : Nat) (b : UInt8) (marks : ByteArray) : ByteArray :=
  if h : i < nodes.size then
    let k := nodes[i].idx
    let marks := if k < marks.size then marks else marks ++ ByteArray.mk (Array.replicate (k + 1 - marks.size) 0)
    markNodes nodes (i + 1) b (marks.set! k (if b == 0 then 0 else marks.get! k ||| b))
  else marks

/-- Whether the owner of the far end (`target` with `useTarget`, else `source`) of `e` has mark bit `b`
(`endInSet`). -/
@[inline] def endMarked (a : LGraphArena) (marks : ByteArray) (e : LEdgeId) (useTarget : Bool) (b : UInt8) : Bool :=
  let ed := a.edge e
  match (if useTarget then ed.target else ed.source) with
  | some p =>
    match (a.port p).owner with
    | some n => markOf marks n &&& b != 0
    | none => false
  | none => false

/-- Whether an edge of `edges[k:]` has its far end outside the nodes with mark bit `b`. -/
partial def anyEndUnmarked (a : LGraphArena) (marks : ByteArray) (edges : Array LEdgeId) (useTarget : Bool) (b : UInt8)
    (k : Nat) : Bool :=
  if h : k < edges.size then !endMarked a marks edges[k] useTarget b || anyEndUnmarked a marks edges useTarget b (k + 1)
  else false

/-- Whether a port lies on the north side (without the derived `BEq`). -/
@[inline] def isNorth (side : PortSide) : Bool :=
  match side with
  | .north => true
  | _ => false

/-- `assignPositions`, left layer: the ports of `nodes[i:]` (ports `ports[j:]` of the current node)
with an outgoing edge leaving the left layer get consecutive positions from `count`. -/
partial def assignLeft (a : LGraphArena) (marks : ByteArray) (nodes : Array LNodeId) (i : Nat) (ports : Array LPortId)
    (j : Nat) (count : Int) (positions : Array Int) : Array Int × Int :=
  if h : j < ports.size then
    let port := ports[j]
    if anyEndUnmarked a marks (a.port port).outgoingEdges true 1 0 then
      assignLeft a marks nodes i ports (j + 1) (count + 1) (setPosition positions a port count)
    else assignLeft a marks nodes i ports (j + 1) count positions
  else if h : i < nodes.size then assignLeft a marks nodes (i + 1) (a.node nodes[i]).ports 0 count positions
  else (positions, count)

/-- The leading northern ports of `ports[j:]` with an incoming edge from outside the right layer. -/
partial def northInputs (a : LGraphArena) (marks : ByteArray) (ports : Array LPortId) (j : Nat) (acc : Int) : Int :=
  if h : j < ports.size then
    let pt := a.port ports[j]
    if isNorth pt.side then
      northInputs a marks ports (j + 1) (if anyEndUnmarked a marks pt.incomingEdges false 2 0 then acc + 1 else acc)
    else acc
  else acc

/-- The reversed port loop of `assignPositions` over `ports[0:j]` of a right-layer node. -/
partial def assignRightPorts (a : LGraphArena) (marks : ByteArray) (ports : Array LPortId) (j : Nat)
    (northInputPorts : Int) (targetCount otherInputPorts : Int) (positions : Array Int) : Array Int × Int × Int :=
  if j > 0 then
    match ports[j - 1]? with
    | some port =>
      let pt := a.port port
      if anyEndUnmarked a marks pt.incomingEdges false 2 0 then
        if isNorth pt.side then
          assignRightPorts a marks ports (j - 1) northInputPorts (targetCount + 1) otherInputPorts
            (setPosition positions a port targetCount)
        else
          assignRightPorts a marks ports (j - 1) northInputPorts targetCount (otherInputPorts + 1)
            (setPosition positions a port (targetCount + northInputPorts + otherInputPorts))
      else assignRightPorts a marks ports (j - 1) northInputPorts targetCount otherInputPorts positions
    | none => assignRightPorts a marks ports (j - 1) northInputPorts targetCount otherInputPorts positions
  else (positions, targetCount, otherInputPorts)

/-- `assignPositions`, right layer, over `nodes[i:]`. -/
partial def assignRight (a : LGraphArena) (marks : ByteArray) (nodes : Array LNodeId) (i : Nat) (targetCount : Int)
    (positions : Array Int) : Array Int × Int :=
  if h : i < nodes.size then
    let ports := (a.node nodes[i]).ports
    let north := northInputs a marks ports 0 0
    let (positions, targetCount, other) := assignRightPorts a marks ports ports.size north targetCount 0 positions
    assignRight a marks nodes (i + 1) (targetCount + other) positions
  else (positions, targetCount)

/-- The slot of a port (`hyperedge index + 1`, `0`: none). -/
@[inline] def slotOf (slots : Array Nat) (p : LPortId) : Nat :=
  if h : p.idx < slots.size then slots[p.idx] else 0

/-- Sets the slot of a port (growing the slots). -/
@[inline] def setSlot (slots : Array Nat) (p : LPortId) (v : Nat) : Array Nat :=
  let slots := if p.idx < slots.size then slots else slots ++ Array.replicate (p.idx + 1 - slots.size) 0
  slots.set! p.idx v

/-- Sets the slots of `ports[k:]` to `v`. -/
partial def setSlots (ports : Array LPortId) (k v : Nat) (slots : Array Nat) : Array Nat :=
  if h : k < ports.size then setSlots ports (k + 1) v (setSlot slots ports[k] v) else slots

/-- The hyperedges being collected (and whether each is still active) and the slots. -/
structure Collect where
  hyperedges : Array Hyperedge
  active : Array Bool
  slots : Array Nat
  deriving Inhabited

/-- One edge `sourcePort → targetPort` of `collectHyperedges` (the four slot cases). -/
@[inline] def collectEdge (sourcePort targetPort : LPortId) (st : Collect) : Collect :=
  match st with
  | ⟨hyperedges, active, slots⟩ =>
    let s := slotOf slots sourcePort
    let t := slotOf slots targetPort
    if s == 0 then
      if t == 0 then
        let id := hyperedges.size
        ⟨hyperedges.push { identity := sourcePort.idx, ports := #[sourcePort, targetPort] }, active.push true,
          setSlot (setSlot slots sourcePort (id + 1)) targetPort (id + 1)⟩
      else
        ⟨hyperedges.modifyIn (t - 1) fun h => { h with ports := h.ports.push sourcePort }, active,
          setSlot slots sourcePort t⟩
    else if t == 0 then
      ⟨hyperedges.modifyIn (s - 1) fun h => { h with ports := h.ports.push targetPort }, active,
        setSlot slots targetPort s⟩
    else
      let sourceId := s - 1
      let targetId := t - 1
      if sourceId != targetId && sourceId < hyperedges.size && targetId < hyperedges.size then
        let targetPorts := hyperedges[targetId]!.ports
        let slots := setSlots targetPorts 0 s slots
        let hyperedges := hyperedges.modifyIn sourceId fun h => { h with ports := h.ports ++ targetPorts }
        let hyperedges := hyperedges.modifyIn targetId fun h => { h with ports := #[] }
        ⟨hyperedges, active.set! targetId false, slots⟩
      else st

/-- `collectHyperedges` over the left nodes `nodes[i:]`, their ports `ports[j:]` and the outgoing
edges `edges[k:]` of the current port `port`. -/
partial def collectLoop (a : LGraphArena) (marks : ByteArray) (nodes : Array LNodeId) (i : Nat) (ports : Array LPortId)
    (j : Nat) (port : LPortId) (edges : Array LEdgeId) (k : Nat) (st : Collect) : Collect :=
  if h : k < edges.size then
    let e := edges[k]
    match (a.edge e).target with
    | some targetPort =>
      if endMarked a marks e true 1 then collectLoop a marks nodes i ports j port edges (k + 1) st
      else collectLoop a marks nodes i ports j port edges (k + 1) (collectEdge port targetPort st)
    | none => collectLoop a marks nodes i ports j port edges (k + 1) st
  else if h : j < ports.size then
    let p := ports[j]
    collectLoop a marks nodes i ports (j + 1) p (a.port p).outgoingEdges 0 st
  else if h : i < nodes.size then collectLoop a marks nodes (i + 1) (a.node nodes[i]).ports 0 port #[] 0 st
  else st

/-- The bounds of a hyperedge over its ports `ports[k:]`. -/
partial def boundsLoop (a : LGraphArena) (marks : ByteArray) (positions : Array Int) (ports : Array LPortId) (k : Nat)
    (ul ll ur lr : Int) : Hyperedge → Hyperedge :=
  if h : k < ports.size then
    let port := ports[k]
    let pos := positionOf positions a port
    match (a.port port).owner with
    | some n =>
      let m := markOf marks n
      if m &&& 1 != 0 then boundsLoop a marks positions ports (k + 1) (min ul pos) (max ll pos) ur lr
      else if m &&& 2 != 0 then boundsLoop a marks positions ports (k + 1) ul ll (min ur pos) (max lr pos)
      else boundsLoop a marks positions ports (k + 1) ul ll ur lr
    | none => boundsLoop a marks positions ports (k + 1) ul ll ur lr
  else fun h => { h with upperLeft := ul, lowerLeft := ll, upperRight := ur, lowerRight := lr }

/-- The active hyperedges of `hs[i:]` with their bounds, pushed onto `out`; the slots of their ports
are cleared. -/
partial def finishHyperedges (a : LGraphArena) (marks : ByteArray) (positions : Array Int) (sourceCount targetCount : Int)
    (hs : Array Hyperedge) (active : Array Bool) (i : Nat) (out : Array Hyperedge) (slots : Array Nat) :
    Array Hyperedge × Array Nat :=
  if h : i < hs.size then
    if active[i]! then
      let he := hs[i]
      let he := boundsLoop a marks positions he.ports 0 sourceCount he.lowerLeft targetCount he.lowerRight he
      finishHyperedges a marks positions sourceCount targetCount hs active (i + 1) (out.push he) (setSlots he.ports 0 0 slots)
    else finishHyperedges a marks positions sourceCount targetCount hs active (i + 1) out slots
  else (out, slots)

/-- `Hyperedge.compare h1 h2 == .gt`. -/
@[inline] def hyperedgeGreater (h1 h2 : Hyperedge) : Bool :=
  if h1.upperLeft != h2.upperLeft then h1.upperLeft > h2.upperLeft
  else if h1.upperRight != h2.upperRight then h1.upperRight > h2.upperRight
  else h1.identity > h2.identity

/-- The tree loop of `countStraightCrossings` for one value (`index` its leaf). -/
partial def straightUp (index : Int) (tree : Array Int) (crossings : Int) : Array Int × Int :=
  if index > 0 then
    let crossings := if index % 2 > 0 then crossings + (tree[(index + 1).toNat]?.getD 0) else crossings
    let index := (index - 1) / 2
    straightUp index (tree.modify index.toNat (· + 1)) crossings
  else (tree, crossings)

/-- Marks the upper right positions `ur[i:]` in the compression table. -/
partial def markDeltas (ur : Array Int) (i : Nat) (deltas : Array Int) : Array Int :=
  if h : i < ur.size then markDeltas ur (i + 1) (deltas.setIfInBounds (asUsize ur[i]) 1) else deltas

/-- The compression table from position `i` on: a marked entry gets the running `delta`, every
unmarked one decrements it. -/
partial def fillDeltas (i : Nat) (delta : Int) (deltas : Array Int) : Array Int :=
  if h : i < deltas.size then
    if deltas[i] == 1 then fillDeltas (i + 1) delta (deltas.set i delta) else fillDeltas (i + 1) (delta - 1) deltas
  else deltas

/-- The compressed values of `ur[i:]` (written in place) and their maximum `+ 1` (at least `q`). -/
partial def compressValues (deltas : Array Int) (i : Nat) (q : Int) (ur : Array Int) : Array Int × Int :=
  if h : i < ur.size then
    let value := ur[i] + (deltas[asUsize ur[i]]?.getD 0)
    compressValues deltas (i + 1) (max q (value + 1)) (ur.set i value)
  else (ur, q)

/-- The smallest power of two `≥ q` (from `firstIndex`). -/
partial def powerAbove (q firstIndex : Int) : Int := if firstIndex < q then powerAbove q (firstIndex * 2) else firstIndex

/-- The tree pass of `countStraightCrossings` over the compressed values `values[i:]`. -/
partial def straightLoop (values : Array Int) (firstIndex : Int) (i : Nat) (tree : Array Int) (crossings : Int) : Int :=
  if h : i < values.size then
    let index := values[i] + firstIndex
    let (tree, crossings) := straightUp index (tree.modify index.toNat (· + 1)) crossings
    straightLoop values firstIndex (i + 1) tree crossings
  else crossings

/-- `straightUp` on natural numbers (`index ≥ 0`: the same steps; the tree holds counts). -/
partial def straightUpNat (index : Nat) (tree : Array Nat) (crossings : Nat) : Array Nat × Nat :=
  if index > 0 then
    let crossings := if index % 2 == 1 then crossings + (tree[index + 1]?.getD 0) else crossings
    let index := (index - 1) / 2
    straightUpNat index (tree.modify index (· + 1)) crossings
  else (tree, crossings)

/-- `straightLoop` on natural numbers. -/
partial def straightLoopNat (values : Array Int) (firstIndex : Nat) (i : Nat) (tree : Array Nat) (crossings : Nat) : Nat :=
  if h : i < values.size then
    let index := values[i].toNat + firstIndex
    let (tree, crossings) := straightUpNat index (tree.modify index (· + 1)) crossings
    straightLoopNat values firstIndex (i + 1) tree crossings
  else crossings

/-- `countStraightCrossings` on the upper right positions `ur` of the sorted hyperedges. When no
position is negative (always: they are port positions or counts), every compressed value, index and
count is a natural number and the tree pass runs on `Nat`s (the same steps). -/
def countStraightCrossingsOf (ur : Array Int) (targetCount : Int) : Int :=
  let deltas := fillDeltas 0 0 (markDeltas ur 0 (Array.replicate (targetCount + 1).toNat 0))
  let (values, q) := compressValues deltas 0 0 ur
  let firstIndex := powerAbove q 1
  let treeSize := 2 * firstIndex - 1
  if values.all (· ≥ 0) && firstIndex ≥ 1 then
    (straightLoopNat values (firstIndex - 1).toNat 0 (Array.replicate treeSize.toNat 0) 0 : Int)
  else straightLoop values (firstIndex - 1) 0 (Array.replicate treeSize.toNat 0) 0

/-- `HyperedgeCorner.compare c1 c2 == .gt` on the corner keys `i` and `j` (position, opposite
position, identity, upper). -/
@[inline] def cornerGreater (pos opp : Array Int) (ids : Array Nat) (upper : ByteArray) (i j : Nat) : Bool :=
  let pi := pos[i]!
  let pj := pos[j]!
  if pi != pj then pi > pj
  else
    let oi := opp[i]!
    let oj := opp[j]!
    if oi != oj then oi > oj
    else
      let ii := ids[i]!
      let ij := ids[j]!
      if ii != ij then ii > ij
      else upper.get! i == 0 && upper.get! j != 0

/-- The sweep of `countOverlapCrossings` over the sorted corner indices `perm[k:]`. -/
partial def overlapSweep (upper : ByteArray) (perm : Array Nat) (k : Nat) (open_ crossings : Int) : Int :=
  if h : k < perm.size then
    if upper.get! perm[k] != 0 then overlapSweep upper perm (k + 1) (open_ + 1) crossings
    else overlapSweep upper perm (k + 1) (open_ - 1) (crossings + (open_ - 1))
  else crossings

/-- The corner positions and opposite positions of `hyperedges[i:]` (upper, then lower corner of each;
`left`: the left bounds, else the right ones), pushed onto `pos` and `opp`. -/
partial def cornerPositions (hyperedges : Array Hyperedge) (left : Bool) (i : Nat) (pos opp : Array Int) :
    Array Int × Array Int :=
  if h : i < hyperedges.size then
    let he := hyperedges[i]
    let u := if left then he.upperLeft else he.upperRight
    let l := if left then he.lowerLeft else he.lowerRight
    cornerPositions hyperedges left (i + 1) ((pos.push u).push l) ((opp.push l).push u)
  else (pos, opp)

/-- The corner identities of `hyperedges[i:]` (twice each), pushed onto `ids`. -/
partial def cornerIds (hyperedges : Array Hyperedge) (i : Nat) (ids : Array Nat) : Array Nat :=
  if h : i < hyperedges.size then
    let id := hyperedges[i].identity
    cornerIds hyperedges (i + 1) ((ids.push id).push id)
  else ids

/-- `k` pairs of corner kinds (upper `1`, lower `0`) pushed onto `upper`. -/
partial def cornerUppers (k : Nat) (upper : ByteArray) : ByteArray :=
  if k == 0 then upper else cornerUppers (k - 1) ((upper.push 1).push 0)

/-- `countOverlapCrossings` of one side: the corners `(upper, lower, id, upper corner)` and
`(lower, upper, id, lower corner)` of every hyperedge (`left`: the left bounds, else the right ones),
in hyperedge order. -/
def countOverlapCrossingsOf (hyperedges : Array Hyperedge) (left : Bool) : Int :=
  let n := 2 * hyperedges.size
  let (pos, opp) := cornerPositions hyperedges left 0 (Array.emptyWithCapacity n) (Array.emptyWithCapacity n)
  let ids := cornerIds hyperedges 0 (Array.emptyWithCapacity n)
  let upper := cornerUppers hyperedges.size (ByteArray.emptyWithCapacity n)
  overlapSweep upper (keyedStableSort n (cornerGreater pos opp ids upper)) 0 0 0

/-- `countCrossingsPure` with the scratch arrays (see "Allocation-poor counting"); the scratch is
returned zeroed. -/
def countCrossingsFast (a : LGraphArena) (positions : Array Int) (scratch : Scratch) (leftLayer rightLayer : Array LNodeId) :
    Int × Array Int × Scratch :=
  if leftLayer.isEmpty || rightLayer.isEmpty then (0, positions, scratch)
  else
    let marks := markNodes rightLayer 0 2 (markNodes leftLayer 0 1 scratch.marks)
    let (positions, sourceCount) := assignLeft a marks leftLayer 0 #[] 0 0 positions
    let (positions, targetCount) := assignRight a marks rightLayer 0 0 positions
    let st := collectLoop a marks leftLayer 0 #[] 0 default #[] 0 ⟨#[], #[], scratch.slots⟩
    let (hyperedges, slots) := finishHyperedges a marks positions sourceCount targetCount st.hyperedges st.active 0
      (Array.emptyWithCapacity st.hyperedges.size) st.slots
    let marks := markNodes rightLayer 0 0 (markNodes leftLayer 0 0 marks)
    let perm := keyedStableSort hyperedges.size fun i j => hyperedgeGreater hyperedges[i]! hyperedges[j]!
    let sorted := perm.map fun i => hyperedges[i]!
    let crossings := countStraightCrossingsOf (sorted.map (·.upperRight)) targetCount
    let crossings := crossings + countOverlapCrossingsOf sorted true
    let crossings := crossings + countOverlapCrossingsOf sorted false
    (crossings, positions, ⟨marks, slots⟩)

/-- `countCrossings(leftLayer, rightLayer)`. -/
def countCrossings (c : HyperedgeCrossingsCounter) (leftLayer rightLayer : Array LNodeId) : LayeredM Int := do
  let a ← get
  let positions ← c.portPositions.swap #[]
  let scratch ← c.scratch.swap {}
  let (crossings, positions, scratch) := countCrossingsFast a positions scratch leftLayer rightLayer
  c.scratch.set scratch
  c.portPositions.set positions
  return crossings

/-- `countCrossings` with the line-by-line port `countCrossingsPure` (reference of the differential
test). -/
def countCrossingsPort (c : HyperedgeCrossingsCounter) (leftLayer rightLayer : Array LNodeId) : LayeredM Int := do
  let a ← get
  let positions ← c.portPositions.swap #[]
  let (crossings, positions) := countCrossingsPure a positions leftLayer rightLayer
  c.portPositions.set positions
  return crossings

end HyperedgeCrossingsCounter

end Elk.Alg.Layered.P3Order.Counting
