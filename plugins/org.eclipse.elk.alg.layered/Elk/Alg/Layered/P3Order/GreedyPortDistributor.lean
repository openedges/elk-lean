import Elk.Alg.Layered.Graph
import Elk.Alg.Layered.Options.LayeredOptions
import Elk.Alg.Layered.P3Order.ISweepPortDistributor
import Elk.Alg.Layered.P3Order.Counting.CrossingsCounter
import Elk.Alg.Layered.Intermediate.GreedySwitch.BetweenLayerEdgeTwoNodeCrossingsCounter
/-!
# `org.eclipse.elk.alg.layered.p3order.GreedyPortDistributor`

Distributes the ports of the free layer's sweep side greedily: neighbouring ports are switched
as long as that decreases the crossings counted by a `CrossingsCounter` (plus, for a node with
a nested graph, the crossings inside it counted by a `BetweenLayerEdgeTwoNodeCrossingsCounter`
on the nested graph's border layer). elk-rs `greedy_port_distributor.rs`.

Rust semantics kept where they differ from Java:
- `initAtNodeLevel` sets `node.id := nodeIndex` and `initAtPortLevel` assigns `port.id :=
  nPorts++` (Java only counts the ports per node and relies on the other initialisables);
- a switch swaps the node's port list entries at the side's indices in `node.ports` (filtered by
  side) — Java writes through the `getPortSideView` sub-list view, which is the same list slot;
- a missing crossings counter (distribution before `initAfterTraversal`) throws
  `IllegalStateException: crossings counter not initialized` (Rust `expect`).
The `ELK_TRACE` greedy port output is not reproduced.
-/
namespace Elk.Alg.Layered.P3Order

open Elk.Core.Options Elk.Alg.Layered.Graph Elk.Alg.Layered.Options Elk.Alg.Layered.P3Order.Counting
open Elk.Alg.Layered.Intermediate.GreedySwitch LayeredM

/-- `GreedyPortDistributor`. -/
structure GreedyPortDistributor where
  /-- `crossings_counter` (created by `initAfterTraversal`). -/
  crossingsCounter : IO.Ref (Option CrossingsCounter)
  /-- `n_ports`. -/
  nPorts : IO.Ref Nat

namespace GreedyPortDistributor

/-- `GreedyPortDistributor::new()`. -/
def new : BaseIO GreedyPortDistributor := do
  return { crossingsCounter := ← IO.mkRef none, nPorts := ← IO.mkRef 0 }

/-- `crossings_counter_mut()`. -/
private def counter (d : GreedyPortDistributor) : LayeredM CrossingsCounter := do
  match ← d.crossingsCounter.get with
  | some c => return c
  | none => throw (IO.userError "java.lang.IllegalStateException: crossings counter not initialized")

/-- Rust `initialize(node_order, current_index, is_forward_sweep)` (`initialize` is a Lean keyword): positions for counting between
the free layer and its fixed neighbour, or for in-layer counting at the graph border. -/
def initializeCounting (d : GreedyPortDistributor) (order : Array (Array LNodeId)) (currentIndex : Nat) (isForwardSweep : Bool) :
    LayeredM Unit := do
  let c ← d.counter
  let layer (i : Nat) : Array LNodeId := order[i]?.getD #[]
  if isForwardSweep && currentIndex > 0 then
    c.initForCountingBetween (layer (currentIndex - 1)) (layer currentIndex)
  else if !isForwardSweep && currentIndex + 1 < order.size then
    c.initForCountingBetween (layer currentIndex) (layer (currentIndex + 1))
  else
    let side : PortSide := if isForwardSweep then .west else .east
    let _ ← c.initPortPositionsForInLayerCrossings (layer currentIndex) side

/-- `ports_for_side(node, side)`: the side's ports (`getPortSideView`) with their indices in
`node.ports`, reversed on the `SOUTH`/`WEST` sides. -/
def portsForSide (a : LGraphArena) (node : LNodeId) (side : PortSide) : Array LPortId × Array Nat := Id.run do
  let ports := a.nodePortSideView node side
  let mut indices : Array Nat := #[]
  let nodePorts := (a.node node).ports
  for h : index in [0:nodePorts.size] do
    if (a.port nodePorts[index]).side == side then indices := indices.push index
  if side == .south || side == .west then (ports.reverse, indices.reverse) else (ports, indices)

/-- `switching_decreases_crossings(upper_port, lower_port, hierarchical_counter)`. -/
def switchingDecreasesCrossings (d : GreedyPortDistributor) (upperPort lowerPort : LPortId)
    (hierarchicalCounter : Option BetweenLayerEdgeTwoNodeCrossingsCounter) : LayeredM Bool := do
  let (ul, lu) ← (← d.counter).countCrossingsBetweenPortsInBothOrders upperPort lowerPort
  let mut upperLowerCrossings := ul
  let mut lowerUpperCrossings := lu
  if let some hc := hierarchicalCounter then
    let upperNode := (← getPort upperPort).internal.portDummy
    let lowerNode := (← getPort lowerPort).internal.portDummy
    if let (some un, some ln) := (upperNode, lowerNode) then
      hc.countBothSideCrossings un ln
      upperLowerCrossings := upperLowerCrossings + (← hc.upperLowerCrossings)
      lowerUpperCrossings := lowerUpperCrossings + (← hc.lowerUpperCrossings)
  return upperLowerCrossings > lowerUpperCrossings

/-- `switch_ports(node, ports, indices, top_index, bottom_index)`: switches the positions in the
counter, the local lists and the node's port list. -/
def switchPorts (d : GreedyPortDistributor) (node : LNodeId) (ports : Array LPortId) (indices : Array Nat)
    (topIndex bottomIndex : Nat) : LayeredM (Array LPortId × Array Nat) := do
  if topIndex >= ports.size || bottomIndex >= ports.size then return (ports, indices)
  (← d.counter).switchPorts ports[topIndex]! ports[bottomIndex]!
  let topPos := indices[topIndex]?
  let bottomPos := indices[bottomIndex]?
  let ports := ports.swapIfInBounds topIndex bottomIndex
  let indices := indices.swapIfInBounds topIndex bottomIndex
  if let (some tp, some bp) := (topPos, bottomPos) then
    modifyNode node fun x =>
      if tp < x.ports.size && bp < x.ports.size then { x with ports := x.ports.swapIfInBounds tp bp } else x
  return (ports, indices)

/-- `distribute_ports_on_node(node, side, hierarchical_counter)`: bubble passes over the side's
ports until no switch improves; whether any switch was made. -/
def distributePortsOnNode (d : GreedyPortDistributor) (node : LNodeId) (side : PortSide)
    (hierarchicalCounter : Option BetweenLayerEdgeTwoNodeCrossingsCounter) : LayeredM Bool := do
  let (ports0, indices0) := portsForSide (← get) node side
  if ports0.isEmpty then return false
  let mut ports := ports0
  let mut indices := indices0
  let mut improved := false
  while true do
    let mut continueSwitching := false
    for i in [0:ports.size - 1] do
      let upperPort := ports[i]!
      let lowerPort := ports[i + 1]!
      if ← d.switchingDecreasesCrossings upperPort lowerPort hierarchicalCounter then
        improved := true
        (ports, indices) ← d.switchPorts node ports indices i (i + 1)
        continueSwitching := true
    if !continueSwitching then break
  return improved

/-- The hierarchical counter of a node with a nested graph and ports on `side`. -/
private def hierarchicalCounterFor (node : LNodeId) (side : PortSide) (isForwardSweep : Bool) :
    LayeredM (Option BetweenLayerEdgeTwoNodeCrossingsCounter) := do
  let a ← get
  let portsOnSide := a.nodePortSideView node side
  match (a.node node).nestedGraph with
  | some nested =>
    if portsOnSide.isEmpty then return none
    let innerGraph := a.graphToNodeArray nested
    let freeLayerIndex := if isForwardSweep then 0 else innerGraph.size - 1
    return some (← BetweenLayerEdgeTwoNodeCrossingsCounter.new innerGraph freeLayerIndex)
  | none => return none

/-- `distribute_ports_in_layer(node_order, current_index, is_forward_sweep)`. -/
def distributePortsInLayer (d : GreedyPortDistributor) (order : Array (Array LNodeId)) (currentIndex : Nat)
    (isForwardSweep : Bool) : LayeredM Bool := do
  let side : PortSide := if isForwardSweep then .west else .east
  let mut improved := false
  for node in order[currentIndex]?.getD #[] do
    let constraints ← getNodePropD node LayeredOptions.PORT_CONSTRAINTS PortConstraints.undefined
    if constraints.isOrderFixed then continue
    let hierarchicalCounter ← hierarchicalCounterFor node side isForwardSweep
    let nodeImproved ← d.distributePortsOnNode node side hierarchicalCounter
    improved := improved || nodeImproved
  return improved

/-- `distribute_ports_while_sweeping(node_order, current_index, is_forward_sweep)`: whether a
port order changed. -/
def distributePortsWhileSweeping (d : GreedyPortDistributor) (order : Array (Array LNodeId)) (currentIndex : Nat)
    (isForwardSweep : Bool) : LayeredM Bool := do
  d.initializeCounting order currentIndex isForwardSweep
  d.distributePortsInLayer order currentIndex isForwardSweep

/-- `init_at_node_level`: `node.id := nodeIndex`. -/
def initAtNodeLevel (_d : GreedyPortDistributor) (l n : Nat) (order : Array (Array LNodeId)) : LayeredM Unit := do
  let some node := (order[l]?).bind (·[n]?) | return
  modifyNode node fun x => { x with id := n }

/-- `init_at_port_level`: `port.id := nPorts++`. -/
def initAtPortLevel (d : GreedyPortDistributor) (l n p : Nat) (order : Array (Array LNodeId)) : LayeredM Unit := do
  let some node := (order[l]?).bind (·[n]?) | return
  let some port := (← getNode node).ports[p]? | return
  let id := (← d.nPorts.get)
  modifyPort port fun x => { x with id := id }
  d.nPorts.set (id + 1)

/-- `init_after_traversal`: a crossings counter over `nPorts` zeroed positions. -/
def initAfterTraversal (d : GreedyPortDistributor) : LayeredM Unit := do
  let n ← d.nPorts.get
  d.crossingsCounter.set (some (← CrossingsCounter.ofPositions (Array.replicate n 0)))

/-- The `IInitializable` implementation. -/
def initializable (d : GreedyPortDistributor) : Initializable where
  initAtNodeLevel := d.initAtNodeLevel
  initAtPortLevel := d.initAtPortLevel
  initAfterTraversal := d.initAfterTraversal

/-- The `ISweepPortDistributor` implementation. -/
def toSweepPortDistributor (d : GreedyPortDistributor) : SweepPortDistributor where
  initializable := d.initializable
  distributePortsWhileSweeping := d.distributePortsWhileSweeping

end GreedyPortDistributor

end Elk.Alg.Layered.P3Order
