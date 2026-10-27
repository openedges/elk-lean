import Std.Data.HashMap
import Std.Data.HashSet
import Elk.Alg.Layered.LayeredPhases
import Elk.Alg.Layered.Graph.LGraphUtil
import Elk.Core.Util.Sort
/-!
# `org.eclipse.elk.alg.layered.intermediate.NodePromotion`

Port of elk-rs `intermediate/node_promotion.rs`. elk-rs implements only the model order strategies
`MODEL_ORDER_LEFT_TO_RIGHT` and `MODEL_ORDER_RIGHT_TO_LEFT`; for every other `NodePromotionStrategy`
(`NIKOLOV`, `NIKOLOV_PIXEL`, `NIKOLOV_IMPROVED`, `NIKOLOV_IMPROVED_PIXEL`, `DUMMYNODE_PERCENTAGE`,
`NODECOUNT_PERCENTAGE`, `NO_BOUNDARY`, `NONE`) the processor does nothing. **Java differs**: it runs the
Nikolov et al. promotion (`promotionMagic`, dummy-count bookkeeping) for those strategies. The Lean port
follows the oracle (elk-rs), so those strategies are no-ops here too.

Model order promotion (`model_order_node_promotion`): the layers are copied into a `LayerNodeMap` (layer
index → nodes, each layer stably sorted by `MODEL_ORDER`, descending for left-to-right, ascending for
right-to-left; nodes without model order compare equal). Passes run until nothing changes: from the
second-to-last layer backwards (left-to-right) or from the second layer forwards (right-to-left), a node
with a model order is promoted one layer towards the end (start) when no node of its layer has a larger
(smaller) model order and either the next layer has a node with a smaller (larger) model order or the
promotion can pass through a layer of label dummies. Promoting a node also promotes (breadth-first,
insertion-ordered set) the nodes that would end up in the same layer as a node they are connected to.
Finally the new layering is applied, reusing the existing layer objects by index and creating layers for
new indices; empty layers are dropped.

Rust/Java differences (follows Rust):
- after a promotion the node index steps back by one (`saturating_sub(1)`, revisiting the previous node);
  Java re-examines the same index;
- the first/last layer keys of a pass are fixed when the pass starts (Java checks them dynamically);
- graphs with fewer than two layers are left untouched (Java still re-sorts and rebuilds the layers);
- existing `Layer` objects are reused (Java creates new ones).

The Rust `BTreeMap<i32, Vec<LNodeRef>>` is an `Array (Int × Array LNodeId)` kept sorted by key; the reverse
map (node → key) is a `Std.HashMap` (lookups only). Sorting uses `stableSort` (Rust `sort_by`).
-/
namespace Elk.Alg.Layered.Intermediate

open Elk.Graph Elk.Core Elk.Core.Alg Elk.Core.Util Elk.Alg.Layered Elk.Alg.Layered.Graph
  Elk.Alg.Layered.Options LayeredM

namespace NodePromotion

/-- Rust `LayerNodeMap`: layer key → nodes (sorted by key) and node → key. -/
structure LayerNodeMap where
  layers : Array (Int × Array LNodeId) := #[]
  reverse : Std.HashMap LNodeId Int := {}
  deriving Inhabited

namespace LayerNodeMap

/-- `min_key`. -/
def minKey (m : LayerNodeMap) : Option Int := m.layers[0]?.map (·.1)

/-- `max_key`. -/
def maxKey (m : LayerNodeMap) : Option Int := m.layers.back?.map (·.1)

/-- `key_count`. -/
def keyCount (m : LayerNodeMap) : Nat := m.layers.size

/-- `key_of(node)`. -/
def keyOf (m : LayerNodeMap) (node : LNodeId) : Option Int := m.reverse.get? node

/-- `values(key)`: the nodes of a key (empty when absent). -/
def values (m : LayerNodeMap) (key : Int) : Array LNodeId :=
  match m.layers.find? (·.1 == key) with
  | some (_, nodes) => nodes
  | none => #[]

/-- `put(key, node)`: removes the node from its old key's list and appends it to the list of `key`
(created in key order when missing). -/
def put (m : LayerNodeMap) (key : Int) (node : LNodeId) : LayerNodeMap := Id.run do
  let mut layers := m.layers
  if let some oldKey := m.reverse.get? node then
    if let some i := layers.findIdx? (·.1 == oldKey) then
      layers := layers.modify i fun (k, ns) => (k, ns.filter (· != node))
  match layers.findIdx? (·.1 == key) with
  | some i => layers := layers.modify i fun (k, ns) => (k, ns.push node)
  | none =>
    let pos := (layers.findIdx? (·.1 > key)).getD layers.size
    layers := layers.insertIdx! pos (key, #[node])
  return { layers := layers, reverse := m.reverse.insert node key }

end LayerNodeMap

/-- Rust `model_order_compare(left, right, leftToRight)`: descending (left-to-right) or ascending model
order when both nodes have one, else equal. -/
def modelOrderCompare (left right : Option Int) (leftToRight : Bool) : Ordering :=
  match left, right with
  | some l, some r => if leftToRight then compare r l else compare l r
  | _, _ => .eq

/-- `LayerNodeMap::from_graph(graph, leftToRight)`. -/
def fromGraph (graph : LGraphId) (leftToRight : Bool) : LayeredM LayerNodeMap := do
  let layers := (← getGraph graph).layers
  let mut m : LayerNodeMap := {}
  for h : layerId in [0:layers.size] do
    let mut withOrder : Array (LNodeId × Option Int) := #[]
    for node in (← getLayer layers[layerId]).nodes do
      withOrder := withOrder.push (node, (← getNode node).internal.modelOrder)
    let sorted := (stableSort withOrder fun a b => modelOrderCompare a.2 b.2 leftToRight).map (·.1)
    let mut reverse := m.reverse
    for node in sorted do
      reverse := reverse.insert node (layerId : Int)
    m := { layers := m.layers.push ((layerId : Int), sorted), reverse := reverse }
  return m

/-- `MODEL_ORDER` of a node. -/
def modelOrder (node : LNodeId) : LayeredM (Option Int) := do
  return (← getNode node).internal.modelOrder

/-- Rust `first_incoming_source_node(node)`. -/
def firstIncomingSourceNode (node : LNodeId) : LayeredM (Option LNodeId) := do
  let some edge := (← withArena (·.nodeIncomingEdges node))[0]? | return none
  let some port := (← getEdge edge).source | return none
  return (← getPort port).owner

/-- Rust `first_outgoing_target_node(node)`. -/
def firstOutgoingTargetNode (node : LNodeId) : LayeredM (Option LNodeId) := do
  let some edge := (← withArena (·.nodeOutgoingEdges node))[0]? | return none
  let some port := (← getEdge edge).target | return none
  return (← getPort port).owner

/-- Whether no node of the current layer blocks the promotion (has a larger model order for
left-to-right, a smaller one for right-to-left). -/
def notBlockedInLayer (currentLayer : Array LNodeId) (nodeModelOrder : Int) (leftToRight : Bool) :
    LayeredM Bool := do
  for other in currentLayer do
    if let some otherModelOrder ← modelOrder other then
      if (leftToRight && nodeModelOrder < otherModelOrder) || (!leftToRight && nodeModelOrder > otherModelOrder) then
        return false
  return true

/-- The label dummy check of the next-layer scan: a label dummy whose edge comes from (goes to) `node`
blocks the promotion through the label layer when its other end is at most two layers away. -/
def labelDummyBlocks (layerMap : LayerNodeMap) (node labelDummy : LNodeId) (currentLayerId nextLayerId : Int)
    (leftToRight : Bool) : LayeredM Bool := do
  let connectedToNext ← if leftToRight then firstIncomingSourceNode labelDummy else firstOutgoingTargetNode labelDummy
  let some nodeConnectedToNextLayer := connectedToNext | return false
  if nodeConnectedToNextLayer != node then return false
  let connected ← if leftToRight then firstOutgoingTargetNode labelDummy else firstIncomingSourceNode labelDummy
  let some connectedNode := connected | return false
  let connectedLayer := (layerMap.keyOf connectedNode).getD nextLayerId
  let sourceLayer := (layerMap.keyOf nodeConnectedToNextLayer).getD currentLayerId
  let layerDistance := if leftToRight then connectedLayer - sourceLayer else sourceLayer - connectedLayer
  return layerDistance <= 2

/-- Scan of the next layer: `(modelOrderAllowsPromotion, promoteThroughDummyLayer, containsLabels)`. -/
def scanNextLayer (layerMap : LayerNodeMap) (node : LNodeId) (nodeModelOrder currentLayerId nextLayerId : Int)
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
        if ← labelDummyBlocks layerMap node nextLayerNode currentLayerId nextLayerId leftToRight then
          promoteThroughDummyLayer := false
  return (modelOrderAllowsPromotion, promoteThroughDummyLayer, containsLabels)

/-- Whether the node at the current position shall be promoted (the Rust loop body up to the promotion;
every `node_index += 1; continue` case returns `false`). -/
def shallPromote (layerMap : LayerNodeMap) (node : LNodeId) (currentLayer : Array LNodeId)
    (currentLayerId minKey maxKey : Int) (leftToRight : Bool) : LayeredM Bool := do
  let some nodeModelOrder ← modelOrder node | return false
  if (leftToRight && currentLayerId == maxKey) || (!leftToRight && currentLayerId == minKey) then return false
  if !(← notBlockedInLayer currentLayer nodeModelOrder leftToRight) then return false
  let nextLayerId := if leftToRight then currentLayerId + 1 else currentLayerId - 1
  let (modelOrderAllowsPromotion, promoteThroughDummyLayer, containsLabels) ←
    scanNextLayer layerMap node nodeModelOrder currentLayerId nextLayerId leftToRight
  let mut promoteThroughDummyLayer := promoteThroughDummyLayer
  if containsLabels && promoteThroughDummyLayer then
    let connected ← if leftToRight then firstOutgoingTargetNode node else firstIncomingSourceNode node
    if let some connectedNode := connected then
      let connectedLayer := (layerMap.keyOf connectedNode).getD currentLayerId
      let nodeLayer := (layerMap.keyOf node).getD currentLayerId
      let layerDistance := if leftToRight then connectedLayer - nodeLayer else nodeLayer - connectedLayer
      if layerDistance <= 2 && (← getNode connectedNode).type == .normal then
        promoteThroughDummyLayer := false
  return modelOrderAllowsPromotion || promoteThroughDummyLayer

/-- `promoteNodeByModelOrder(node, leftToRight)`: moves the node one layer and returns the connected nodes
(over outgoing edges for left-to-right, incoming for right-to-left; first occurrence order) that now share
its layer. -/
def promoteNodeByModelOrder (node : LNodeId) (leftToRight : Bool) (layerMap : LayerNodeMap) :
    LayeredM (LayerNodeMap × Array LNodeId) := do
  let some oldLayer := layerMap.keyOf node | return (layerMap, #[])
  let newLayer := if leftToRight then oldLayer + 1 else oldLayer - 1
  let layerMap := layerMap.put newLayer node
  let edges ← withArena fun a => if leftToRight then a.nodeOutgoingEdges node else a.nodeIncomingEdges node
  let mut nodesToPromote : Array LNodeId := #[]
  let mut seen : Std.HashSet LNodeId := {}
  for edge in edges do
    let ed ← getEdge edge
    let some port := (if leftToRight then ed.target else ed.source) | continue
    let some nextNode := (← getPort port).owner | continue
    if layerMap.keyOf nextNode == layerMap.keyOf node && !seen.contains nextNode then
      seen := seen.insert nextNode
      nodesToPromote := nodesToPromote.push nextNode
  return (layerMap, nodesToPromote)

/-- Promotes a node and, breadth-first, every node pushed into the same layer as a neighbour (Rust
`VecDeque` + `HashSet` queue = Java `LinkedHashSet` iteration). -/
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

/-- One pass over one layer of the map (Rust inner `loop`); returns the map and whether something was
promoted. -/
def promoteInLayer (layerMap : LayerNodeMap) (currentLayerId minKey maxKey : Int) (leftToRight : Bool) :
    LayeredM (LayerNodeMap × Bool) := do
  let mut layerMap := layerMap
  let mut somethingChanged := false
  let mut nodeIndex := 0
  while true do
    let currentLayer := layerMap.values currentLayerId
    if nodeIndex >= currentLayer.size then break
    let node := currentLayer[nodeIndex]!
    if ← shallPromote layerMap node currentLayer currentLayerId minKey maxKey leftToRight then
      layerMap ← promoteWithDependents node leftToRight layerMap
      nodeIndex := nodeIndex - 1
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

/-- `modelOrderNodePromotion(graph, leftToRight)`. -/
def modelOrderNodePromotion (graph : LGraphId) (leftToRight : Bool) : LayeredM Unit := do
  let mut layerMap ← fromGraph graph leftToRight
  if layerMap.keyCount < 2 then return
  while true do
    let mut somethingChanged := false
    let minKey := layerMap.minKey.getD 0
    let maxKey := layerMap.maxKey.getD 0
    let mut currentLayerId : Int := if leftToRight then maxKey - 1 else minKey + 1
    while (if leftToRight then currentLayerId >= minKey else currentLayerId <= maxKey) do
      let (next, changed) ← promoteInLayer layerMap currentLayerId minKey maxKey leftToRight
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
