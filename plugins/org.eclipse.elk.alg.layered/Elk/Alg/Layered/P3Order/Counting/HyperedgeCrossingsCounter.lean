import Elk.Alg.Layered.Graph
import Elk.Alg.Layered.P3Order.Counting.BinaryIndexedTree
import Elk.Core.Util.Sort
import Std.Data.HashMap
import Std.Data.HashSet
/-!
# `org.eclipse.elk.alg.layered.p3order.counting.HyperedgeCrossingsCounter`

Approximates the crossings between two layers when ports carry several edges (hyperedges), after
Gansner et al. / Sander (elk-rs `hyperedge_crossings_counter.rs`). Port positions are indexed by
`LPort.id` and kept in the counter's own array (Java shares it with the `CrossingsCounter`;
elk-rs uses a separate one).

The hyperedge identity used as the last sort key (Rust: address of the first source port, Java:
`hashCode()`) is the arena index of that port. Identities are unique per active hyperedge, so the
count does not depend on their actual values. The `edges` list of the Rust `Hyperedge` is only
used for tracing and is not kept.
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

/-- `HyperedgeCrossingsCounter`. -/
structure HyperedgeCrossingsCounter where
  /-- `portPos` (indexed by `LPort.id`). -/
  portPositions : IO.Ref (Array Int)

namespace HyperedgeCrossingsCounter

/-- `new HyperedgeCrossingsCounter(inLayerEdgeCount, hasNorthSouthPorts, portPos)`; the first two
arguments are unused (as in Java/elk-rs). -/
def new (_inLayerEdgeCount : Array Int) (_hasNorthSouthPorts : Array Bool) (portPositions : Array Int) :
    BaseIO HyperedgeCrossingsCounter := do
  return { portPositions := ← IO.mkRef portPositions }

/-- Rust `port_id(port)`: `port.id as usize`. -/
@[inline] private def portIdOf (a : LGraphArena) (p : LPortId) : Nat := asUsize (a.port p).id

/-- Rust `set_port_position` (grows the array; invalid ids are ignored). -/
private def setPosition (positions : Array Int) (a : LGraphArena) (p : LPortId) (v : Int) : Array Int :=
  let pid := portIdOf a p
  if pid >= 4294967296 then positions
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

/-- `countCrossings(leftLayer, rightLayer)`. -/
def countCrossings (c : HyperedgeCrossingsCounter) (leftLayer rightLayer : Array LNodeId) : LayeredM Int := do
  let a ← get
  let positions ← c.portPositions.swap #[]
  let (crossings, positions) := countCrossingsPure a positions leftLayer rightLayer
  c.portPositions.set positions
  return crossings

end HyperedgeCrossingsCounter

end Elk.Alg.Layered.P3Order.Counting
