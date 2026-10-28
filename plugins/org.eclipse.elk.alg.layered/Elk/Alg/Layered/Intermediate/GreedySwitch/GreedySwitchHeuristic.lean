import Elk.Alg.Layered.Graph
import Elk.Alg.Layered.P3Order.CrossMinType
import Elk.Alg.Layered.P3Order.ICrossingMinimizationHeuristic
import Elk.Alg.Layered.Intermediate.GreedySwitch.SwitchDecider
/-!
# `org.eclipse.elk.alg.layered.intermediate.greedyswitch.GreedySwitchHeuristic`

One- or two-sided greedy switch crossing minimisation (elk-rs `greedy_switch_heuristic.rs`):
neighbouring nodes of the free layer are switched while that reduces crossings.

elk-rs replaces Java's `GraphInfoHolder` back reference by two setters the holder calls
(`set_dont_sweep_into`, `update_parent_context` from `GraphInfoHolder.update_greedy_context`);
they are `setDontSweepInto`/`updateParentContext` on the `GreedySwitchHeuristic` object here,
which `toHeuristic` wraps into the `CrossingMinimizationHeuristic` record. The heuristic is
deterministic and draws no random numbers. The `ELK_TRACE` greedy switch output is not
reproduced.
-/
namespace Elk.Alg.Layered.Intermediate.GreedySwitch

open Elk.Alg.Layered.Graph Elk.Alg.Layered.P3Order Elk.Alg.Layered.P3Order.Counting LayeredM

/-- elk-rs `ParentContext`: the parent graph's current order, its (shared) port position array and
the parent node of the graph being swept. -/
structure ParentContext where
  parentNodeOrder : Array (Array LNodeId)
  parentPortPositions : IO.Ref (Array Int)
  parentNode : LNodeId

/-- `GreedySwitchHeuristic` (the mutable fields are `IO.Ref`s). -/
structure GreedySwitchHeuristic where
  /-- `greedySwitchType`. -/
  greedySwitchType : CrossMinType
  /-- The graph being swept. -/
  graph : LGraphId
  /-- `portPositions` (sized by `initAfterTraversal`): one array for the whole run, shared by the
  in-layer crossing counters of every `SwitchDecider` (Java; their positions survive from one free
  layer to the next). -/
  portPositions : IO.Ref (Array Int)
  /-- `nPorts`. -/
  nPorts : IO.Ref Nat
  /-- `graphData.hasParent()`. -/
  hasParent : Bool
  /-- `graphData.dontSweepInto()`. -/
  dontSweepInto : IO.Ref Bool
  /-- The parent data (`graphData.parentGraphData()`, `graphData.parent()`). -/
  parentContext : IO.Ref (Option ParentContext)

namespace GreedySwitchHeuristic

/-- `new GreedySwitchHeuristic(greedyType, graphData)` as the underlying object (elk-rs
`new(greedy_type, has_parent)`). -/
def create (greedyType : CrossMinType) (hasParent : Bool) (graph : LGraphId) : BaseIO GreedySwitchHeuristic := do
  return {
    greedySwitchType := greedyType, graph, hasParent
    portPositions := ← IO.mkRef #[], nPorts := ← IO.mkRef 0
    dontSweepInto := ← IO.mkRef false, parentContext := ← IO.mkRef none }

/-- elk-rs `set_dont_sweep_into`. -/
def setDontSweepInto (h : GreedySwitchHeuristic) (dontSweepInto : Bool) : BaseIO Unit := h.dontSweepInto.set dontSweepInto

/-- elk-rs `update_parent_context(parent_node_order, parent_port_positions, parent_node)`. -/
def updateParentContext (h : GreedySwitchHeuristic) (parentNodeOrder : Array (Array LNodeId))
    (parentPortPositions : IO.Ref (Array Int)) (parentNode : LNodeId) : BaseIO Unit :=
  h.parentContext.set (some { parentNodeOrder, parentPortPositions, parentNode })

/-- Rust `layer_index_of(node)`: the `id` of the node's layer (set by `initAtLayerLevel`). -/
private def layerIndexOf (node : LNodeId) : LayeredM (Option Nat) := do
  match (← getNode node).layer with
  | some l => return some (asUsize (← getLayer l).id)
  | none => return none

/-- `setUp(order, freeLayerIndex, forwardSweep)`: a fresh `SwitchDecider` for the free layer
(`none` when the index is out of range). -/
private def setUp (h : GreedySwitchHeuristic) (order : Array (Array LNodeId)) (freeLayerIndex : Nat) (forwardSweep : Bool) :
    LayeredM (Option SwitchDecider) := do
  if freeLayerIndex >= order.size then return none
  let side : CrossingCountSide := if forwardSweep then .west else .east
  let crossingMatrixFiller ← CrossingMatrixFiller.new h.greedySwitchType order freeLayerIndex side
  let oneSided := h.greedySwitchType == .oneSidedGreedySwitch
  let freeLayer := order[freeLayerIndex]!
  let freeLayerFirstIsExternalPort ← match freeLayer[0]? with
    | some n => pure ((← getNode n).type == .externalPort)
    | none => pure false
  let mut parentContext : Option ParentCrossingContext := none
  let mut countParentCrossings := !oneSided && h.hasParent && !(← h.dontSweepInto.get) && freeLayerFirstIsExternalPort
  if countParentCrossings then
    match ← h.parentContext.get with
    | some parent =>
      match ← layerIndexOf parent.parentNode with
      | some parentLayerIndex =>
        parentContext := some {
          parentNodeOrder := parent.parentNodeOrder, parentPortPositions := parent.parentPortPositions,
          parentLayerIndex, rightMostLayer := freeLayerIndex + 1 == order.size }
      | none => countParentCrossings := false
    | none => countParentCrossings := false
  some <$> SwitchDecider.new freeLayer crossingMatrixFiller h.portPositions parentContext countParentCrossings

/-- `exchangeNodes(indexOne, indexTwo, layerIndex)`. -/
private def exchangeNodes (order : Array (Array LNodeId)) (layerIndex indexOne indexTwo : Nat) (switchDecider : SwitchDecider) :
    LayeredM (Array (Array LNodeId)) := do
  let some layer := order[layerIndex]? | return order
  let (some upperNode, some lowerNode) := (layer[indexOne]?, layer[indexTwo]?) | return order
  switchDecider.notifyOfSwitch upperNode lowerNode
  return order.modify layerIndex (·.swapIfInBounds indexOne indexTwo)

/-- `switchIfImproves(layerIndex, upperNodeIndex, lowerNodeIndex)`: the order and whether it switched. -/
private def switchIfImproves (order : Array (Array LNodeId)) (layerIndex upperNodeIndex lowerNodeIndex : Nat)
    (switchDecider : SwitchDecider) : LayeredM (Array (Array LNodeId) × Bool) := do
  let some layer := order[layerIndex]? | return (order, false)
  let (some upperNode, some lowerNode) := (layer[upperNodeIndex]?, layer[lowerNodeIndex]?) | return (order, false)
  if ← switchDecider.doesSwitchReduceCrossings upperNode lowerNode then
    return (← exchangeNodes order layerIndex upperNodeIndex lowerNodeIndex switchDecider, true)
  return (order, false)

/-- `sweepDownwardInLayer(layerIndex)`: one pass over all neighbouring pairs. -/
private def sweepDownwardInLayer (order : Array (Array LNodeId)) (layerIndex : Nat) (switchDecider : SwitchDecider) :
    LayeredM (Array (Array LNodeId) × Bool) := do
  let mut order := order
  let mut continueSwitching := false
  let length := ((order[layerIndex]?).map (·.size)).getD 0
  for upperNodeIndex in [0:length - 1] do
    let (order', switched) ← switchIfImproves order layerIndex upperNodeIndex (upperNodeIndex + 1) switchDecider
    order := order'
    continueSwitching := continueSwitching || switched
  return (order, continueSwitching)

/-- `continueSwitchingUntilNoImprovementInLayer(freeLayerIndex)`. -/
private def continueSwitchingUntilNoImprovementInLayer (order : Array (Array LNodeId)) (freeLayerIndex : Nat)
    (switchDecider : SwitchDecider) : LayeredM (Array (Array LNodeId) × Bool) := do
  let mut order := order
  let mut improved := false
  repeat
    let (order', continueSwitching) ← sweepDownwardInLayer order freeLayerIndex switchDecider
    order := order'
    improved := improved || continueSwitching
    if !continueSwitching then break
  return (order, improved)

/-- `setFirstLayerOrder(currentOrder, isForwardSweep)`: one downward sweep in the first (forward)
or last layer. -/
def setFirstLayerOrder (h : GreedySwitchHeuristic) (order : Array (Array LNodeId)) (forwardSweep : Bool) :
    LayeredM (Array (Array LNodeId) × Bool) := do
  let startIndex := if forwardSweep then 0 else order.size - 1
  match ← h.setUp order startIndex forwardSweep with
  | some switchDecider => sweepDownwardInLayer order startIndex switchDecider
  | none => return (order, false)

/-- `minimizeCrossings(order, freeLayerIndex, forwardSweep, isFirstSweep)`. -/
def minimizeCrossings (h : GreedySwitchHeuristic) (order : Array (Array LNodeId)) (freeLayerIndex : Nat)
    (forwardSweep _isFirstSweep : Bool) : LayeredM (Array (Array LNodeId) × Bool) := do
  match ← h.setUp order freeLayerIndex forwardSweep with
  | some switchDecider => continueSwitchingUntilNoImprovementInLayer order freeLayerIndex switchDecider
  | none => return (order, false)

/-- `alwaysImproves()`: only the two-sided variant never makes things worse. -/
def alwaysImproves (h : GreedySwitchHeuristic) : Bool := h.greedySwitchType != .oneSidedGreedySwitch

/-- The `IInitializable` part: counts the ports, numbers the layers (`layer.id = l`) and sizes the
port position array. -/
def initializable (h : GreedySwitchHeuristic) : Initializable where
  initAtPortLevel := fun _ _ _ _ => h.nPorts.modify (· + 1)
  initAtLayerLevel := fun l nodeOrder => do
    let some node := (nodeOrder[l]?).bind (·[0]?) | return
    if let some layer := (← getNode node).layer then
      modifyLayer layer fun x => { x with id := l }
  initAfterTraversal := do h.portPositions.set (Array.replicate (← h.nPorts.get) 0)

/-- The `ICrossingMinimizationHeuristic` view of the object. -/
def toHeuristic (h : GreedySwitchHeuristic) : CrossingMinimizationHeuristic where
  initializable := h.initializable
  alwaysImproves := pure h.alwaysImproves
  setFirstLayerOrder := h.setFirstLayerOrder
  minimizeCrossings := h.minimizeCrossings
  isDeterministic := pure true

/-- `new GreedySwitchHeuristic(greedyType, graphData)` as the heuristic record; use `create` and
`toHeuristic` when the `setDontSweepInto`/`updateParentContext` setters are needed. -/
def new (greedyType : CrossMinType) (hasParent : Bool) (graph : LGraphId) : LayeredM CrossingMinimizationHeuristic := do
  return (← create greedyType hasParent graph).toHeuristic

end GreedySwitchHeuristic

end Elk.Alg.Layered.Intermediate.GreedySwitch
