import Elk.Alg.Layered.Graph
import Elk.Alg.Layered.P3Order.CrossMinSnapshot
import Elk.Alg.Layered.P3Order.Counting.IInitializable
import Elk.Alg.Layered.P3Order.Counting.CrossingsCounter
import Elk.Alg.Layered.P3Order.Counting.HyperedgeCrossingsCounter
/-!
# `org.eclipse.elk.alg.layered.p3order.counting.AllCrossingsCounter`

Counts all crossings of a node order: in-layer crossings on the outer sides, between-layer
crossings (with the hyperedge approximation where a port carries several edges) and
north/south port crossings (elk-rs `all_crossings_counter.rs`). Must be initialised through
`Initializable.init #[counter.initializable, …] order` before counting; the initialisation
assigns `LPort.id`s in traversal order.

elk-rs hands the `GraphInfoHolder`'s counter a `CrossMinSnapshot`/`ArenaSync` (`set_snapshot`,
`set_arena_sync`); in Lean `setSnapshot` reaches the between-layer counting of the
`CrossingsCounter` (see there), everything else reads the arena. The
`ELK_TRACE` crossings breakdown output of elk-rs is not reproduced. Like Java (`initAfterTraversal`),
both counters share one port position array (elk-rs gave the hyperedge counter its own).
-/
namespace Elk.Alg.Layered.P3Order.Counting

open Elk.Core.Options Elk.Alg.Layered.Graph LayeredM

/-- `AllCrossingsCounter`. -/
structure AllCrossingsCounter where
  /-- `crossingCounter` (reset to fresh positions by `initAfterTraversal`; its position array is
  `portPos`, shared with `hyperedgeCrossingsCounter`). -/
  crossingCounter : CrossingsCounter
  /-- `hasHyperEdgesEastOfIndex`. -/
  hasHyperEdgesEastOfIndex : IO.Ref (Array Bool)
  /-- `hyperedgeCrossingsCounter`: Java's `initAfterTraversal` hands it the same `portPos` array as
  `crossingCounter`, so the in-layer counts read the positions it wrote for far ends they do not
  number themselves (elk-rs gave it an array of its own). -/
  hyperedgeCrossingsCounter : HyperedgeCrossingsCounter
  /-- `inLayerEdgeCounts`. -/
  inLayerEdgeCounts : IO.Ref (Array Int)
  /-- `hasNorthSouthPorts`. -/
  hasNorthSouthPorts : IO.Ref (Array Bool)
  /-- `nPorts`. -/
  nPorts : IO.Ref Int

namespace AllCrossingsCounter

/-- `new AllCrossingsCounter(graph)`: `order` is the current node order (Java's `graph`
argument); `_graph` identifies the `LGraph` and is not needed by the counter. -/
def new (_graph : LGraphId) (order : Array (Array LNodeId)) : LayeredM AllCrossingsCounter := do
  let length := order.size
  let portPos ← IO.mkRef (#[] : Array Int)
  return {
    crossingCounter := ← CrossingsCounter.new portPos
    hasHyperEdgesEastOfIndex := ← IO.mkRef (Array.replicate length false)
    hyperedgeCrossingsCounter := ← HyperedgeCrossingsCounter.shared portPos
    inLayerEdgeCounts := ← IO.mkRef (Array.replicate length 0)
    hasNorthSouthPorts := ← IO.mkRef (Array.replicate length false)
    nPorts := ← IO.mkRef 0 }

/-- elk-rs `set_snapshot(snapshot)`: hands the snapshot to the crossings counter. -/
def setSnapshot (c : AllCrossingsCounter) (s : CrossMinSnapshot) : BaseIO Unit := c.crossingCounter.setSnapshot s

/-- `countCrossingsAt(layerIndex, currentOrder)`. -/
private def countCrossingsAt (c : AllCrossingsCounter) (layerIndex : Nat) (currentOrder : Array (Array LNodeId)) :
    LayeredM Int := do
  let mut totalCrossings : Int := 0
  let leftLayer := currentOrder[layerIndex]!
  if layerIndex + 1 < currentOrder.size then
    let rightLayer := currentOrder[layerIndex + 1]!
    if (← c.hasHyperEdgesEastOfIndex.get)[layerIndex]?.getD false then
      let hyper ← c.hyperedgeCrossingsCounter.countCrossings leftLayer rightLayer
      let leftEast ← c.crossingCounter.countInLayerCrossingsOnSide leftLayer .east
      let rightWest ← c.crossingCounter.countInLayerCrossingsOnSide rightLayer .west
      totalCrossings := hyper + leftEast + rightWest
    else
      totalCrossings ← c.crossingCounter.countCrossingsBetweenLayers leftLayer rightLayer
  if (← c.hasNorthSouthPorts.get)[layerIndex]?.getD false then
    totalCrossings := totalCrossings + (← c.crossingCounter.countNorthSouthPortCrossingsInLayer leftLayer)
  return totalCrossings

/-- `countAllCrossings(currentOrder)`. -/
def countAllCrossings (c : AllCrossingsCounter) (currentOrder : Array (Array LNodeId)) : LayeredM Int := do
  if currentOrder.isEmpty then return 0
  let west ← c.crossingCounter.countInLayerCrossingsOnSide currentOrder[0]! .west
  let east ← c.crossingCounter.countInLayerCrossingsOnSide currentOrder[currentOrder.size - 1]! .east
  let mut crossings := west + east
  for layerIndex in [0:currentOrder.size] do
    crossings := crossings + (← c.countCrossingsAt layerIndex currentOrder)
  return crossings

/-- `initAtNodeLevel`: marks layers containing north/south port dummies. -/
private def initAtNodeLevel (c : AllCrossingsCounter) (l n : Nat) (nodeOrder : Array (Array LNodeId)) : LayeredM Unit := do
  let some node := (nodeOrder[l]?).bind (·[n]?) | return
  if (← getNode node).type == .northSouthPort then
    c.hasNorthSouthPorts.modify (·.setIfInBounds l true)

/-- The `p`-th port of the `n`-th node of layer `l`. -/
@[inline] private def portAt (l n p : Nat) (nodeOrder : Array (Array LNodeId)) : LayeredM (Option LPortId) := do
  let some node := (nodeOrder[l]?).bind (·[n]?) | return none
  return (← getNode node).ports[p]?

/-- `initAtPortLevel`: assigns `port.id = nPorts++` and marks hyperedge layers. -/
private def initAtPortLevel (c : AllCrossingsCounter) (l n p : Nat) (nodeOrder : Array (Array LNodeId)) : LayeredM Unit := do
  let some port ← portAt l n p nodeOrder | return
  let id ← c.nPorts.get
  modifyPort port fun x => { x with id := id }
  c.nPorts.set (id + 1)
  let pt ← getPort port
  if pt.outgoingEdges.size + pt.incomingEdges.size > 1 then
    if pt.side == .east then
      c.hasHyperEdgesEastOfIndex.modify (·.setIfInBounds l true)
    else if pt.side == .west && l > 0 then
      c.hasHyperEdgesEastOfIndex.modify (·.setIfInBounds (l - 1) true)

/-- `initAtEdgeLevel`: counts the in-layer edges leaving the layer's ports. -/
private def initAtEdgeLevel (c : AllCrossingsCounter) (l n p : Nat) (edge : LEdgeId) (nodeOrder : Array (Array LNodeId)) :
    LayeredM Unit := do
  let some port ← portAt l n p nodeOrder | return
  let a ← get
  let ed := a.edge edge
  if ed.source == some port then
    let layerOf (q : Option LPortId) : Option LayerId := q.bind fun q => (a.port q).owner.bind fun x => (a.node x).layer
    match layerOf ed.source, layerOf ed.target with
    | some sl, some tl =>
      if sl == tl then c.inLayerEdgeCounts.modify (·.modify l (· + 1))
    | _, _ => pure ()

/-- `initAfterTraversal`: a fresh position array `portPos` of `nPorts` entries, shared by both
counters. -/
private def initAfterTraversal (c : AllCrossingsCounter) : LayeredM Unit := do
  let n := (← c.nPorts.get).toNat
  c.crossingCounter.resetTo (Array.replicate n 0)

/-- The `IInitializable` implementation. `initAtEdgeLevel` only counts into `inLayerEdgeCounts`,
which nothing reads (Java hands it to the hyperedge counter, whose constructor ignores it; it cannot
throw), so the traversal skips the edge level for it (`usesEdgeLevel := false`; `initAtEdgeLevel` is
kept for the record). -/
def initializable (c : AllCrossingsCounter) : Initializable where
  initAtNodeLevel := c.initAtNodeLevel
  initAtPortLevel := c.initAtPortLevel
  initAtEdgeLevel := fun l n p _ edge order => c.initAtEdgeLevel l n p edge order
  initAfterTraversal := c.initAfterTraversal
  usesEdgeLevel := false

end AllCrossingsCounter

end Elk.Alg.Layered.P3Order.Counting
