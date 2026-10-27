import Elk.Alg.Layered.Graph
import Elk.Alg.Layered.P3Order.ICrossingMinimizationHeuristic
import Elk.Core.Util.Random
import Elk.Core.Util.Sort
import Elk.Core.Util.Java
/-!
# elk-rs `p3order/median_heuristic.rs` (no Java counterpart)

The median heuristic of `CrossingMinimizationStrategy.MEDIAN_LAYER_SWEEP` (`CrossMinType.MEDIAN`):
every node of the free layer gets the `WEIGHT` of the median of its neighbours in the reference
layer (the previous layer forward, the next one backward), nodes without such neighbours the mean
of the smallest and largest weight seen (which start at `f64::MIN_POSITIVE` and `f64::MAX`, so the
mean is about `f64::MAX / 2` and those nodes go last), and the layer is sorted stably by weight.
The first layer is ordered by random weights (`nextDouble()` per node) and then numbered
`1, 2, …`.

State: the weights are the node property `InternalProperties.WEIGHT` (`LNode.internal.weight`); the
heuristic itself is stateless and has no initialisation. The neighbours of a node are the end
nodes of its incoming then outgoing edges (port order), both ends of each edge being tested, in a
layer whose `Layer.id` equals the reference layer index (set by the other initialisables).

Random numbers: `setFirstLayerOrder` draws from the caller's generator (`IO.Ref Random`, captured
by `toHeuristic`); `minimizeCrossings` draws nothing. The heuristic reports itself deterministic
(Rust).

Sorting: Rust `stable_sort_by_weight` sorts `(index, node)` with `sort_by` and the comparator
"`None` weights greater, `partial_cmp`, then the index"; only its `Less` results matter to the
sort, so two nodes without weight keep their order. `stableSort` with the induced order gives the
same result.
-/
namespace Elk.Alg.Layered.P3Order

open Elk.Core.Util Elk.Alg.Layered.Graph Elk.Alg.Layered.Options Elk.Alg.Layered.P3Order.Counting LayeredM

/-- `MedianHeuristic` (a unit struct). -/
structure MedianHeuristic where
  deriving Inhabited

namespace MedianHeuristic

/-- `MedianHeuristic::new()`. -/
def new : MedianHeuristic := {}

/-- Rust `f64::MIN_POSITIVE` (the smallest positive normal double). -/
def F64_MIN_POSITIVE : Float := Float.ofBits 0x0010000000000000

/-- `weight_of(node)`. -/
@[inline] def weightOf (a : LGraphArena) (n : LNodeId) : Option Float := (a.node n).internal.weight

/-- Sets `WEIGHT`. -/
@[inline] def setWeight (n : LNodeId) (w : Float) : LayeredM Unit :=
  modifyNode n fun x => { x with internal := { x.internal with weight := some w } }

/-- The `is_less` of `stable_sort_by_weight` on `(index, weight)` entries: `weight_cmp` is `Less`
(a known weight before an unknown one, `partial_cmp`), or `Equal` and the index is smaller. -/
def entryIsLess (x y : Nat × Option Float) : Bool :=
  match x.2, y.2 with
  | none, _ => false
  | some _, none => true
  | some w1, some w2 =>
    match Float.comparePartial w1 w2 with
    | .lt => true
    | .gt => false
    | .eq => x.1 < y.1

/-- `stable_sort_by_weight(nodes)` with the weights read from the arena. -/
def stableSortByWeight (a : LGraphArena) (nodes : Array LNodeId) : Array LNodeId :=
  let entries := nodes.mapIdx fun i n => ((i, weightOf a n), n)
  let sorted := stableSort entries fun x y =>
    if entryIsLess x.1 y.1 then .lt else if entryIsLess y.1 x.1 then .gt else .eq
  sorted.map (·.2)

/-- Rust `layer_id(node)`: `Layer.id` of the node's layer (`as usize as isize`, i.e. the `i32` id). -/
@[inline] def layerIdOf (a : LGraphArena) (n : LNodeId) : Option Int :=
  (a.node n).layer.map fun l => (a.layer l).id

/-- The neighbours of `node` in the reference layer: for every incoming then outgoing edge the
source and the target node, if in a layer with id `referenceLayer`. -/
def connectedNodes (a : LGraphArena) (node : LNodeId) (referenceLayer : Int) : Array LNodeId := Id.run do
  let mut connected : Array LNodeId := #[]
  for edge in a.nodeIncomingEdges node ++ a.nodeOutgoingEdges node do
    let e := a.edge edge
    let source := e.source.bind fun p => (a.port p).owner
    let target := e.target.bind fun p => (a.port p).owner
    for candidate? in #[source, target] do
      if let some candidate := candidate? then
        if layerIdOf a candidate == some referenceLayer then
          connected := connected.push candidate
  return connected

/-- The median step of one node: `none` without neighbours in the reference layer (the node is
revisited), else the weight of the median `connected[len / 2]` of the neighbours sorted by weight
(`none` when the median has no weight). -/
def medianWeight (a : LGraphArena) (node : LNodeId) (referenceLayer : Int) : Option (Option Float) :=
  let connected := connectedNodes a node referenceLayer
  if connected.isEmpty then none
  else
    let sorted := stableSortByWeight a connected
    some (sorted[sorted.size / 2]?.bind (weightOf a))

/-- `calculate_medians(nodes, reference_layer)`. -/
def calculateMedians (nodes : Array LNodeId) (referenceLayer : Int) : LayeredM Unit := do
  let mut minWeight := F64_MIN_POSITIVE
  let mut maxWeight := Float.maxValue
  let mut toRevisit : Array LNodeId := #[]
  for node in nodes do
    match medianWeight (← get) node referenceLayer with
    | none => toRevisit := toRevisit.push node
    | some none => pure ()
    | some (some weight) =>
      setWeight node weight
      minWeight := fmin minWeight weight
      maxWeight := fmax maxWeight weight
  let avgWeight := (maxWeight + minWeight) / 2.0
  for node in toRevisit do
    setWeight node avgWeight

/-- Writes `sorted` into the layer slot (Rust `layer_slot[index] = node` for `index < len`). -/
def writeLayer (order : Array (Array LNodeId)) (layerIndex : Nat) (sorted : Array LNodeId) : Array (Array LNodeId) :=
  order.modify layerIndex fun slot => Id.run do
    let mut slot := slot
    for h : index in [0:sorted.size] do
      if index < slot.size then slot := slot.set! index sorted[index]
    return slot

/-- `set_first_layer_order(order, forward_sweep, random)`: random weights (`nextDouble()` per
node, in layer order), a stable sort by weight, then weights `1, 2, …` in the new order. -/
def setFirstLayerOrder (_h : MedianHeuristic) (order : Array (Array LNodeId)) (forwardSweep : Bool) (random : IO.Ref Random) :
    LayeredM (Array (Array LNodeId) × Bool) := do
  let firstIndex := if forwardSweep then 0 else order.size - 1
  let some layer := order[firstIndex]? | return (order, false)
  for node in layer do
    let weight ← random.modifyGet (·.nextDouble)
    setWeight node weight
  let sorted := stableSortByWeight (← get) layer
  let order := writeLayer order firstIndex sorted
  for h : index in [0:sorted.size] do
    setWeight sorted[index] (index + 1).toFloat
  return (order, false)

/-- `minimize_crossings(order, free_layer_index, forward_sweep, is_first_sweep, random)`: medians
with respect to the previous (forward) or next layer and a stable sort by weight; nothing happens
when that layer does not exist. Never reports an improvement. -/
def minimizeCrossings (_h : MedianHeuristic) (order : Array (Array LNodeId)) (freeLayerIndex : Nat)
    (forwardSweep _isFirstSweep : Bool) : LayeredM (Array (Array LNodeId) × Bool) := do
  let referenceLayer : Int := if forwardSweep then (freeLayerIndex : Int) - 1 else (freeLayerIndex : Int) + 1
  if referenceLayer < 0 || referenceLayer >= order.size then return (order, false)
  let freeLayer := order[freeLayerIndex]?.getD #[]
  calculateMedians freeLayer referenceLayer
  let sorted := stableSortByWeight (← get) freeLayer
  return (writeLayer order freeLayerIndex sorted, false)

/-- The `IInitializable` part (no initialisation). -/
def initializable (_h : MedianHeuristic) : Initializable := {}

/-- The `ICrossingMinimizationHeuristic` view; `random` is used by `setFirstLayerOrder` only.
Deterministic, never always improving. -/
def toHeuristic (h : MedianHeuristic) (random : IO.Ref Random) : CrossingMinimizationHeuristic where
  initializable := h.initializable
  alwaysImproves := pure false
  setFirstLayerOrder := fun order forwardSweep => h.setFirstLayerOrder order forwardSweep random
  minimizeCrossings := fun order freeLayerIndex forwardSweep isFirstSweep =>
    h.minimizeCrossings order freeLayerIndex forwardSweep isFirstSweep
  isDeterministic := pure true

end MedianHeuristic

end Elk.Alg.Layered.P3Order
