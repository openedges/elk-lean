import Std.Data.HashMap
import Std.Data.HashSet
import Elk.Alg.Layered.LayeredPhases
import Elk.Alg.Layered.Graph.LGraphUtil
import Elk.Core.Util.Sort
import Elk.Core.Util.JavaSort
/-!
# `org.eclipse.elk.alg.layered.intermediate.NodePromotion`

Port of elk-rs `intermediate/node_promotion.rs`. elk-rs implements only the model order strategies
`MODEL_ORDER_LEFT_TO_RIGHT` and `MODEL_ORDER_RIGHT_TO_LEFT`; for every other `NodePromotionStrategy`
(`NIKOLOV`, `NIKOLOV_PIXEL`, `NIKOLOV_IMPROVED`, `NIKOLOV_IMPROVED_PIXEL`, `DUMMYNODE_PERCENTAGE`,
`NODECOUNT_PERCENTAGE`, `NO_BOUNDARY`, `NONE`) the processor does nothing. **Java differs**: it runs the
Nikolov et al. promotion (`promotionMagic`, dummy-count bookkeeping) for those strategies. The Lean port
follows the oracle (elk-rs), so those strategies are no-ops here too.

Model order promotion (Java `modelOrderNodePromotion`; elk-rs `model_order_node_promotion` differs, see
below): every layer of the graph is sorted by `MODEL_ORDER` (descending for left-to-right, ascending
for right-to-left) and copied into a `BiLinkedHashMultiMap` (layer key → nodes, node → key; keys are
never removed, an emptied layer keeps its key). Passes run until nothing changes; a pass visits the
layer keys `keySet().size() - 2` down to `0` (left-to-right) or `1` up to `keySet().size() - 1`
(right-to-left), the bound re-read every step, and in each layer the live node list by index: a node
with a model order is promoted one layer towards the end (start) unless its layer key is the largest
(smallest) key of the map, when no node of its layer has a larger (smaller) model order and either the
next layer has a node with a smaller (larger) model order or the promotion can pass through an empty
layer or a layer of label dummies. After a promotion the same index is examined again (Java
`nodeIndex--`, then the loop's `++`). Promoting a node also promotes (`LinkedHashSet` work list) the
nodes connected to it that now share its key, where "share" is Java's `Integer ==`: equal values in
`[-128, 127]` (the `Integer` cache), else the same boxed object — the keys of one layer's initial
`putAll` share one box, every promotion boxes anew. Finally the new layering is applied (keys
ascending, empty layers dropped), also for graphs with fewer than two layers (whose single layer is
thus sorted). A node whose next-layer label check or label-layer check needs an edge it does not have
makes Java throw `java.util.NoSuchElementException` (reproduced).

elk-rs: it examines the previous index after a promotion, fixes the first/last key of a pass when the
pass starts, iterates the keys from the smallest to the largest key, compares keys by value, leaves
graphs with fewer than two layers untouched and skips missing edges. Existing `Layer` objects are
reused here (Java creates new ones; not observable).

The map is an `Array (Int × Array LNodeId)` kept sorted by key and a `Std.HashMap` node → (key, box).
Each layer is sorted like Java's `layer.getNodes().sort(MODEL_ORDER_NODE_COMPARATOR_DESC/ASC)`: JDK
`TimSort` (`javaSortBy`) with the model order difference (`int` subtraction) when both nodes have a
model order, else `0` — not a consistent order, so TimSort's comparison sequence decides the result
(elk-rs: Rust `sort_by`).
-/
namespace Elk.Alg.Layered.Intermediate

open Elk.Graph Elk.Core Elk.Core.Alg Elk.Core.Util Elk.Alg.Layered Elk.Alg.Layered.Graph
  Elk.Alg.Layered.Options LayeredM

namespace NodePromotion

/-- Java `BiLinkedHashMultiMap<Integer, LNode>`: layer key → nodes (sorted by key; keys are never
removed) and node → (key, the `Integer` box it was stored with). -/
structure LayerNodeMap where
  layers : Array (Int × Array LNodeId) := #[]
  reverse : Std.HashMap LNodeId (Int × Nat) := {}
  /-- The next fresh box id. -/
  nextBox : Nat := 0
  deriving Inhabited

namespace LayerNodeMap

/-- `keySet().size()`. -/
def keyCount (m : LayerNodeMap) : Nat := m.layers.size

/-- `getKey(node)` (value). -/
def keyOf (m : LayerNodeMap) (node : LNodeId) : Option Int := (m.reverse.get? node).map (·.1)

/-- `getValues(key)`: the nodes of a key (empty when absent). -/
def values (m : LayerNodeMap) (key : Int) : Array LNodeId :=
  match m.layers.find? (·.1 == key) with
  | some (_, nodes) => nodes
  | none => #[]

/-- `isMaximalKey(key)`: no key is larger. -/
def isMaximalKey (m : LayerNodeMap) (key : Int) : Bool := m.layers.all (·.1 <= key)

/-- `isMinimalKey(key)`: no key is smaller. -/
def isMinimalKey (m : LayerNodeMap) (key : Int) : Bool := m.layers.all (·.1 >= key)

/-- `put(key, node)` with the `Integer` box `box`: removes the node from its old key's list and appends
it to the list of `key` (created when missing; empty lists keep their key). -/
def putBoxed (m : LayerNodeMap) (key : Int) (box : Nat) (node : LNodeId) : LayerNodeMap := Id.run do
  let mut layers := m.layers
  if let some (oldKey, _) := m.reverse.get? node then
    if let some i := layers.findIdx? (·.1 == oldKey) then
      layers := layers.modify i fun (k, ns) => (k, ns.filter (· != node))
  match layers.findIdx? (·.1 == key) with
  | some i => layers := layers.modify i fun (k, ns) => (k, ns.push node)
  | none =>
    let pos := (layers.findIdx? (·.1 > key)).getD layers.size
    layers := layers.insertIdx! pos (key, #[node])
  return { m with layers := layers, reverse := m.reverse.insert node (key, box) }

/-- `put(key, node)` with a freshly boxed key (`Integer.valueOf`). -/
def put (m : LayerNodeMap) (key : Int) (node : LNodeId) : LayerNodeMap :=
  { m.putBoxed key m.nextBox node with nextBox := m.nextBox + 1 }

/-- `putAll(key, nodes)`: one box for all nodes (Java boxes the key once at the call). -/
def putAll (m : LayerNodeMap) (key : Int) (nodes : Array LNodeId) : LayerNodeMap :=
  let box := m.nextBox
  nodes.foldl (fun m n => m.putBoxed key box n) { m with nextBox := box + 1 }

/-- Java `getKey(a) == getKey(b)` on `Integer`s: both absent, or equal values that are cached
(`[-128, 127]`) or stored with the same box. -/
def keysIdentical (m : LayerNodeMap) (a b : LNodeId) : Bool :=
  match m.reverse.get? a, m.reverse.get? b with
  | none, none => true
  | some (k1, b1), some (k2, b2) => k1 == k2 && ((-128 <= k1 && k1 <= 127) || b1 == b2)
  | _, _ => false

end LayerNodeMap

/-- Java `MODEL_ORDER_NODE_COMPARATOR_DESC` (left-to-right: `o2 - o1`) / `_ASC` (`o1 - o2`) on the
model orders (Java `int` subtraction) when both nodes have one, else `0`. -/
def modelOrderCompare (left right : Option Int) (leftToRight : Bool) : Ordering :=
  match left, right with
  | some l, some r => compare (Int.wrap32 (if leftToRight then r - l else l - r)) 0
  | _, _ => .eq

/-- `precalculateAndSetInformationModelOrder()`: every layer sorted by model order and `putAll` into
the map under its index. -/
def fromGraph (graph : LGraphId) (leftToRight : Bool) : LayeredM LayerNodeMap := do
  let layers := (← getGraph graph).layers
  let mut m : LayerNodeMap := {}
  for h : layerId in [0:layers.size] do
    let mut withOrder : Array (LNodeId × Option Int) := #[]
    for node in (← getLayer layers[layerId]).nodes do
      withOrder := withOrder.push (node, (← getNode node).internal.modelOrder)
    -- Java `layer.getNodes().sort(comparator)`: the comparator is not a total order (nodes without
    -- a model order compare equal to all), so TimSort's comparison sequence decides the result
    let sorted ← match javaSortBy withOrder (fun a b => modelOrderCompare a.2 b.2 leftToRight) with
      | .ok r => pure (r.map (·.1))
      | .error _ => throw (IO.userError JavaSort.contractViolationError)
    m := m.putAll (layerId : Int) sorted
  return m

/-- `MODEL_ORDER` of a node. -/
def modelOrder (node : LNodeId) : LayeredM (Option Int) := do
  return (← getNode node).internal.modelOrder

/-- Java `node.getIncomingEdges().iterator().next().getSource().getNode()`
(`java.util.NoSuchElementException` without incoming edge). -/
def firstIncomingSourceNode (node : LNodeId) : LayeredM LNodeId := do
  let some edge := (← withArena (·.nodeIncomingEdges node))[0]?
    | throw (IO.userError "java.util.NoSuchElementException")
  let some port := (← getEdge edge).source | throw (IO.userError "java.lang.NullPointerException")
  let some owner := (← getPort port).owner | throw (IO.userError "java.lang.NullPointerException")
  return owner

/-- Java `node.getOutgoingEdges().iterator().next().getTarget().getNode()`
(`java.util.NoSuchElementException` without outgoing edge). -/
def firstOutgoingTargetNode (node : LNodeId) : LayeredM LNodeId := do
  let some edge := (← withArena (·.nodeOutgoingEdges node))[0]?
    | throw (IO.userError "java.util.NoSuchElementException")
  let some port := (← getEdge edge).target | throw (IO.userError "java.lang.NullPointerException")
  let some owner := (← getPort port).owner | throw (IO.userError "java.lang.NullPointerException")
  return owner

/-- Whether no node of the current layer blocks the promotion (has a larger model order for
left-to-right, a smaller one for right-to-left). -/
def notBlockedInLayer (currentLayer : Array LNodeId) (nodeModelOrder : Int) (leftToRight : Bool) :
    LayeredM Bool := do
  let mut shallBePromoted := true
  for other in currentLayer do
    if let some otherModelOrder ← modelOrder other then
      if (leftToRight && nodeModelOrder < otherModelOrder) || (!leftToRight && nodeModelOrder > otherModelOrder) then
        shallBePromoted := false
  return shallBePromoted

/-- `biLayerMap.getKey(n)` unboxed (Java would throw a `NullPointerException` for a node outside the
map; every node reached here is in it). -/
def keyValue (layerMap : LayerNodeMap) (n : LNodeId) : LayeredM Int := do
  match layerMap.keyOf n with
  | some k => return k
  | none => throw (IO.userError "java.lang.NullPointerException")

/-- The label dummy check of the next-layer scan: a label dummy whose edge comes from (goes to) `node`
blocks the promotion through the label layer when its other end is at most two layers away. -/
def labelDummyBlocks (layerMap : LayerNodeMap) (node labelDummy : LNodeId) (leftToRight : Bool) :
    LayeredM Bool := do
  let nodeConnectedToNextLayer ← if leftToRight then firstIncomingSourceNode labelDummy
    else firstOutgoingTargetNode labelDummy
  if nodeConnectedToNextLayer != node then return false
  let connectedNode ← if leftToRight then firstOutgoingTargetNode labelDummy else firstIncomingSourceNode labelDummy
  let connectedLayer ← keyValue layerMap connectedNode
  let sourceLayer ← keyValue layerMap nodeConnectedToNextLayer
  let layerDistance := if leftToRight then connectedLayer - sourceLayer else sourceLayer - connectedLayer
  return layerDistance <= 2

/-- Scan of the next layer: `(modelOrderAllowsPromotion, promoteThroughDummyLayer, containsLabels)`. -/
def scanNextLayer (layerMap : LayerNodeMap) (node : LNodeId) (nodeModelOrder nextLayerId : Int)
    (leftToRight : Bool) : LayeredM (Bool × Bool × Bool) := do
  let mut modelOrderAllowsPromotion := false
  let mut promoteThroughDummyLayer := true
  let mut containsLabels := false
  for nextLayerNode in layerMap.values nextLayerId do
    let nn ← getNode nextLayerNode
    match nn.internal.modelOrder with
    | some nextModelOrder =>
      if nextLayerNode != node then
        let allows := if leftToRight then nextModelOrder < nodeModelOrder else nextModelOrder > nodeModelOrder
        modelOrderAllowsPromotion := modelOrderAllowsPromotion || allows
        promoteThroughDummyLayer := false
    | none =>
      if !modelOrderAllowsPromotion && promoteThroughDummyLayer && nn.type == .label then
        containsLabels := true
        if ← labelDummyBlocks layerMap node nextLayerNode leftToRight then
          promoteThroughDummyLayer := false
  return (modelOrderAllowsPromotion, promoteThroughDummyLayer, containsLabels)

/-- Whether the node at the current index shall be promoted (Java's loop body up to the promotion;
every `continue` returns `false`). -/
def shallPromote (layerMap : LayerNodeMap) (node : LNodeId) (currentLayer : Array LNodeId)
    (currentLayerId : Int) (leftToRight : Bool) : LayeredM Bool := do
  let some nodeModelOrder ← modelOrder node | return false
  if (leftToRight && layerMap.isMaximalKey currentLayerId) || (!leftToRight && layerMap.isMinimalKey currentLayerId) then
    return false
  if !(← notBlockedInLayer currentLayer nodeModelOrder leftToRight) then return false
  let nextLayerId := if leftToRight then currentLayerId + 1 else currentLayerId - 1
  let (modelOrderAllowsPromotion, promoteThroughDummyLayer, containsLabels) ←
    scanNextLayer layerMap node nodeModelOrder nextLayerId leftToRight
  let mut promoteThroughDummyLayer := promoteThroughDummyLayer
  if containsLabels && promoteThroughDummyLayer then
    let connectedNode ← if leftToRight then firstOutgoingTargetNode node else firstIncomingSourceNode node
    let connectedLayer ← keyValue layerMap connectedNode
    let nodeLayer ← keyValue layerMap node
    let layerDistance := if leftToRight then connectedLayer - nodeLayer else nodeLayer - connectedLayer
    if layerDistance <= 2 && (← getNode connectedNode).type == .normal then
      promoteThroughDummyLayer := false
  return modelOrderAllowsPromotion || promoteThroughDummyLayer

/-- `promoteNodeByModelOrder(node, leftToRight)`: moves the node one layer and returns the connected nodes
(over outgoing edges for left-to-right, incoming for right-to-left; `LinkedHashSet` order) whose key is
now Java-identical (`Integer ==`, `LayerNodeMap.keysIdentical`) to the node's. -/
def promoteNodeByModelOrder (node : LNodeId) (leftToRight : Bool) (layerMap : LayerNodeMap) :
    LayeredM (LayerNodeMap × Array LNodeId) := do
  let oldLayer ← keyValue layerMap node
  let newLayer := if leftToRight then oldLayer + 1 else oldLayer - 1
  let layerMap := layerMap.put newLayer node
  let edges ← withArena fun a => if leftToRight then a.nodeOutgoingEdges node else a.nodeIncomingEdges node
  let mut nodesToPromote : Array LNodeId := #[]
  let mut seen : Std.HashSet LNodeId := {}
  for edge in edges do
    let ed ← getEdge edge
    let some port := (if leftToRight then ed.target else ed.source) | continue
    let some nextNode := (← getPort port).owner | continue
    if layerMap.keysIdentical nextNode node && !seen.contains nextNode then
      seen := seen.insert nextNode
      nodesToPromote := nodesToPromote.push nextNode
  return (layerMap, nodesToPromote)

/-- Promotes a node and every node pushed into the same layer as a neighbour (Java `LinkedHashSet`
work list: take the first, remove it, add the nodes its promotion returns that are not queued). -/
def promoteWithDependents (node : LNodeId) (leftToRight : Bool) (layerMap : LayerNodeMap) :
    LayeredM LayerNodeMap := do
  let (layerMap, first) ← promoteNodeByModelOrder node leftToRight layerMap
  let mut layerMap := layerMap
  let mut queue : Array LNodeId := #[]
  let mut queued : Std.HashSet LNodeId := {}
  for promoted in first do
    if !queued.contains promoted then
      queued := queued.insert promoted
      queue := queue.push promoted
  let mut head := 0
  while head < queue.size do
    let nodeToPromote := queue[head]!
    head := head + 1
    queued := queued.erase nodeToPromote
    let (next, promotedNodes) ← promoteNodeByModelOrder nodeToPromote leftToRight layerMap
    layerMap := next
    for promoted in promotedNodes do
      if !queued.contains promoted then
        queued := queued.insert promoted
        queue := queue.push promoted
  return layerMap

/-- The node loop of one layer key (Java inner `for` over the live `LinkedList`); returns the map and
whether something was promoted. After a promotion the same index is examined again. -/
def promoteInLayer (layerMap : LayerNodeMap) (currentLayerId : Int) (leftToRight : Bool) :
    LayeredM (LayerNodeMap × Bool) := do
  let mut layerMap := layerMap
  let mut somethingChanged := false
  let mut nodeIndex := 0
  while true do
    let currentLayer := layerMap.values currentLayerId
    if nodeIndex >= currentLayer.size then break
    let node := currentLayer[nodeIndex]!
    if ← shallPromote layerMap node currentLayer currentLayerId leftToRight then
      layerMap ← promoteWithDependents node leftToRight layerMap
      somethingChanged := true
    else
      nodeIndex := nodeIndex + 1
  return (layerMap, somethingChanged)

/-- `applyModelOrderLayers(graph, layerMap)`: writes the map back (existing layers by index, new layers
for new keys; all cleared, then filled in key order; empty keys dropped). -/
def applyModelOrderLayers (graph : LGraphId) (layerMap : LayerNodeMap) : LayeredM Unit := do
  let existingLayers := (← getGraph graph).layers
  let graphRef ← (do
    match existingLayers[0]? with
    | some l => pure (some (← getLayer l).owner)
    | none => pure none)
  let mut layerRefsByKey : Array (Int × LayerId) := #[]
  for h : idx in [0:existingLayers.size] do
    layerRefsByKey := layerRefsByKey.push ((idx : Int), existingLayers[idx])
  for (key, _) in layerMap.layers do
    if layerRefsByKey.any (·.1 == key) then continue
    let some g := graphRef | continue
    let newLayer ← createLayer g
    let pos := (layerRefsByKey.findIdx? (·.1 > key)).getD layerRefsByKey.size
    layerRefsByKey := layerRefsByKey.insertIdx! pos (key, newLayer)
  for (_, layer) in layerRefsByKey do
    modifyLayer layer fun l => { l with nodes := #[] }
  let mut orderedNonEmptyLayers : Array LayerId := #[]
  for (key, nodes) in layerMap.layers do
    if nodes.isEmpty then continue
    let some (_, targetLayer) := layerRefsByKey.find? (·.1 == key) | continue
    for h : idx in [0:nodes.size] do
      setNodeLayerAtIndex nodes[idx] idx (some targetLayer)
    orderedNonEmptyLayers := orderedNonEmptyLayers.push targetLayer
  let layers := orderedNonEmptyLayers
  modifyGraph graph fun g => { g with layers := layers }

/-- `modelOrderNodePromotion(leftToRight)` with `precalculateAndSetInformationModelOrder()` before and
`setNewLayeringModelOrder(graph)` after. The layer loop bound `keySet().size()` is re-read every step. -/
def modelOrderNodePromotion (graph : LGraphId) (leftToRight : Bool) : LayeredM Unit := do
  let mut layerMap ← fromGraph graph leftToRight
  while true do
    let mut somethingChanged := false
    let mut currentLayerId : Int := if leftToRight then (layerMap.keyCount : Int) - 2 else 1
    while (if leftToRight then currentLayerId >= 0 else currentLayerId < (layerMap.keyCount : Int)) do
      let (next, changed) ← promoteInLayer layerMap currentLayerId leftToRight
      layerMap := next
      somethingChanged := somethingChanged || changed
      currentLayerId := currentLayerId + (if leftToRight then -1 else 1)
    if !somethingChanged then break
  applyModelOrderLayers graph layerMap

/-- `process(graph, monitor)` body: only the model order strategies do something (see the module doc). -/
def run (graph : LGraphId) : LayeredM Unit := do
  match (← getGraph graph).props.getD LayeredOptions.LAYERING_NODE_PROMOTION_STRATEGY NodePromotionStrategy.none with
  | .modelOrderLeftToRight => modelOrderNodePromotion graph true
  | .modelOrderRightToLeft => modelOrderNodePromotion graph false
  | _ => pure ()

/-- The `NodePromotion` processor. -/
def processor : LayeredProcessor :=
  { name := "NodePromotion"
    process := fun graph monitor => do
      let _ ← monitor.begin "Node promotion heuristic" 1.0
      run graph
      monitor.done }

end NodePromotion

builtin_initialize registerNodePromotion : Unit ←
  IntermediateProcessorStrategy.register .nodePromotion NodePromotion.processor

end Elk.Alg.Layered.Intermediate
