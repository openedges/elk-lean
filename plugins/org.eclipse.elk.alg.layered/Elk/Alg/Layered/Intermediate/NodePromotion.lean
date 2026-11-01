import Std.Data.HashMap
import Std.Data.HashSet
import Elk.Alg.Layered.LayeredPhases
import Elk.Alg.Layered.Graph.LGraphUtil
import Elk.Core.Util.Sort
import Elk.Core.Util.JavaSort
/-!
# `org.eclipse.elk.alg.layered.intermediate.NodePromotion`

Port of ELK Java's `NodePromotion` (elk-rs `intermediate/node_promotion.rs` implements only the model
order strategies and leaves the layering unchanged for every other strategy — an elk-rs difference that
elk-lean followed until the Java port).

Nikolov et al. (`NIKOLOV`, `NIKOLOV_PIXEL`, `NIKOLOV_IMPROVED`, `NIKOLOV_IMPROVED_PIXEL`,
`DUMMYNODE_PERCENTAGE`, `NODECOUNT_PERCENTAGE`, `NO_BOUNDARY`, and the switch's default case): Java's
`precalculateAndSetInformation()` (reversed layer ids, node ids, degrees, width estimates),
`promotionMagic` with `promoteNode` (see there, including Java's aliased width backups and its
`dummyBackup` arithmetic), the strategy switch (`nikolovStrategies`) and `setNewLayering`, line by line.
The Java arithmetic is kept: `int` widths and dummy counts, `double` pixel widths in Java's evaluation
order, `Math.max` for the pixel maxima, `(int) Math.ceil(n * promoteUntil / 100.0)` with the `int`
product for the percentage strategies, Java's array exceptions. Checked against the unmodified Java
processor on random layered graphs (`tests/fixtures/promotion/processor_cases.jsonl`).

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
  -- the fields are taken apart first so that the arrays are not shared with `m` while they are
  -- updated, and the lists are updated with `modifyIn` (PLAN 7.1 items 13, 16)
  let ⟨layers, reverse, nextBox⟩ := m
  let mut layers := layers
  if let some (oldKey, _) := reverse.get? node then
    if let some i := layers.findIdx? (·.1 == oldKey) then
      layers := layers.modifyIn i fun (k, ns) => (k, ns.filter (· != node))
  match layers.findIdx? (·.1 == key) with
  | some i => layers := layers.modifyIn i fun (k, ns) => (k, ns.push node)
  | none =>
    let pos := (layers.findIdx? (·.1 > key)).getD layers.size
    layers := layers.insertIdx! pos (key, #[node])
  return ⟨layers, reverse.insert node (key, box), nextBox⟩

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
  -- Java sets `layer.id` (index) and `node.id` (running, layer by layer); the later processors read
  -- stale layer ids (`ModelOrderNodeComparator`), see `applyModelOrderLayers`
  let mut nodeId : Int := 0
  for h : layerId in [0:layers.size] do
    let lid : Int := layerId
    modifyLayer layers[layerId] fun l => { l with id := lid }
    for node in (← getLayer layers[layerId]).nodes do
      let nid := nodeId
      modifyNode node fun n => { n with id := nid }
      nodeId := nodeId + 1
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

/-- `applyModelOrderLayers(graph, layerMap)` (Java `setNewLayeringModelOrder`): writes the map back
(existing layers by index, new layers for new keys; all cleared, then filled in key order; empty keys
dropped). Every non-empty layer gets Java's `newLayer.id = layerIndex`, the **key** (not the position:
keys of emptied layers are skipped) — `ModelOrderNodeComparator` (`SortByInputModelProcessor`) compares
the ids of layers it has not renumbered yet. -/
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
    modifyLayer targetLayer fun l => { l with id := key }
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

/-! ## Nikolov et al. (`promotionMagic`) -/

/-- The read-only data `precalculateAndSetInformation()` computes, indexed by the node id it assigns
(`node.id`, layer by layer in node order). -/
structure NikolovData where
  /-- `nodes` (index = id). -/
  nodes : Array LNodeId
  /-- `node.getSize().y + nodeSizeAffix`. -/
  nodeSize : Array Float
  /-- `degreeDiff[id][0]`: outgoing minus incoming edges. -/
  degreeDiff : Array Int
  /-- `degreeDiff[id][1]`: incoming edges. -/
  inDegree : Array Int
  /-- `degreeDiff[id][2]`: outgoing edges. -/
  outDegree : Array Int
  /-- `masterNode.id` of the source of every incoming edge (`node.getIncomingEdges()` order). -/
  incomingSources : Array (Array Int)
  /-- `nodesWithIncomingEdges` (ids, in `nodes` order). -/
  nodesWithIncomingEdges : Array Nat
  /-- `dummySize` (`SPACING_EDGE_NODE_BETWEEN_LAYERS`). -/
  dummySize : Float
  /-- `maxWidth`: the largest `currentWidth` before the promotion. -/
  maxWidth : Int
  /-- `maxWidthPixel`: the largest `currentWidthPixel` before the promotion (`Math.max`). -/
  maxWidthPixel : Float
  deriving Inhabited

/-- The mutable fields of `NodePromotion` the heuristic works on. -/
structure NikolovState where
  /-- `layers`: the reversed layer id of every node. -/
  layers : Array Int
  /-- `currentWidth` (`List<Integer>`; `promoteNode` appends a layer at the end of the list, which
  can be longer than `maxHeight`, see `promotionMagic`). -/
  currentWidth : Array Int
  /-- `currentWidthPixel` (`List<Double>`, like `currentWidth`). -/
  currentWidthPixel : Array Float
  /-- `maxHeight`: the number of layers. -/
  maxHeight : Nat
  /-- `dummyNodeCount`. -/
  dummyNodeCount : Int
  deriving Inhabited

/-- The heuristic's monad: the `NikolovState` fields (Java's exceptions as `IO.userError`). -/
abbrev NikolovM := StateRefT NikolovState IO

/-- Java `array[index]` (`ArrayIndexOutOfBoundsException`). -/
@[inline] def arrayGet {α : Type} [Inhabited α] (a : Array α) (index : Int) : NikolovM α :=
  if 0 <= index && index < a.size then pure a[index.toNat]!
  else throw (IO.userError s!"java.lang.ArrayIndexOutOfBoundsException: Index {index} out of bounds for length {a.size}")

/-- `layers[id]`. -/
@[inline] def layerOf (id : Int) : NikolovM Int := do arrayGet (← get).layers id

/-- `promoteNode(node)`: moves the node (id `node`) one layer up (reversed ids grow towards the first
layer), updating the widths of its old and new layer (`int`/`double` arithmetic in Java's order; a new
layer is appended to the width lists), checks the widths of both layers against `maxWidth`
(`NIKOLOV`) or `maxWidthPixel` (`NIKOLOV_PIXEL`), recursively promotes every source of an incoming
edge that is now in the node's layer (`layers[node]` is written only after the recursion, so a source
reached twice can be promoted twice) and returns the estimated dummy difference and whether the
maximal width was kept. -/
partial def promoteNode (d : NikolovData) (strategy : NodePromotionStrategy) (node : Nat) :
    NikolovM (Int × Bool) := do
  let mut maxWidthNotExceeded := true
  let mut dummydiff : Int := 0
  let mut nodeLayerPos ← layerOf node
  let nodeSize := d.nodeSize[node]!
  let dummiesBuilt := d.outDegree[node]!
  -- `currentWidth.set(nodeLayerPos, currentWidth.get(nodeLayerPos) - 1 + dummiesBuilt)`
  let pos := nodeLayerPos.toNat
  modify fun s => { s with
    currentWidth := s.currentWidth.modify pos (· - 1 + dummiesBuilt)
    currentWidthPixel := s.currentWidthPixel.modify pos (· - nodeSize + dummiesBuilt.toFloat * d.dummySize) }
  nodeLayerPos := nodeLayerPos + 1
  let pos := nodeLayerPos.toNat
  if pos >= (← get).maxHeight then
    modify fun s => { s with
      maxHeight := s.maxHeight + 1
      currentWidth := s.currentWidth.push 1
      currentWidthPixel := s.currentWidthPixel.push nodeSize }
  else
    let dummiesReduced := d.inDegree[node]!
    modify fun s => { s with
      currentWidth := s.currentWidth.modify pos (· + 1 - dummiesReduced)
      currentWidthPixel := s.currentWidthPixel.modify pos (· + nodeSize - dummiesReduced.toFloat * d.dummySize) }
  let exceeded ← match strategy with
    | .nikolov => do
      let w := (← get).currentWidth
      pure (w[pos]! > d.maxWidth || w[pos - 1]! > d.maxWidth)
    | .nikolovPixel => do
      let w := (← get).currentWidthPixel
      pure (w[pos]! > d.maxWidthPixel || w[pos - 1]! > d.maxWidthPixel)
    | _ => pure false
  if exceeded then maxWidthNotExceeded := false
  for masterNode in d.incomingSources[node]! do
    if (← layerOf masterNode) == nodeLayerPos then
      let (diff, kept) ← promoteNode d strategy masterNode.toNat
      dummydiff := dummydiff + diff
      maxWidthNotExceeded := maxWidthNotExceeded && kept
  modify fun s => { s with layers := s.layers.set! node nodeLayerPos }
  dummydiff := dummydiff + d.degreeDiff[node]!
  return (dummydiff, maxWidthNotExceeded)

/-- `promotionMagic(funky)`: Nikolov et al.'s outer loop. Every node with incoming edges is promoted;
the promotion is kept when it reduces the dummy count (and, for `NIKOLOV`/`NIKOLOV_PIXEL`, keeps the
width), otherwise the last kept state is restored. Iterations repeat while something was promoted and
`funky reducedDummies iterationCounter` holds.

Java's bookkeeping is reproduced exactly:
* `currentWidthBackup = currentWidth` (and the pixel list) starts as the **same list**, so until the
  first kept promotion or restore the "backup" follows every change; the first restore therefore keeps
  the widths of the rejected promotion (and the list stays longer than `maxHeight` if it appended a
  layer) and from then on the old list is the backup (`widthBackup`: `none` while aliased).
* A kept promotion sets `dummyBackup = dummyNodeCount + promotionPair.getFirst()` (the difference is
  counted twice) and adds `dummyBackup - dummyNodeCount` to `reducedDummies`. -/
def promotionMagic (d : NikolovData) (strategy : NodePromotionStrategy) (funky : Int → Int → Bool) :
    NikolovM Unit := do
  let mut iterationCounter : Int := 0
  let mut reducedDummies : Int := 0
  let mut layeringBackup := (← get).layers
  let mut dummyBackup := (← get).dummyNodeCount
  let mut heightBackup := (← get).maxHeight
  let mut widthBackup : Option (Array Int × Array Float) := none
  repeat
    let mut promotions : Int := 0
    for node in d.nodesWithIncomingEdges do
      let (first, second) ← promoteNode d strategy node
      let apply := if strategy == .nikolov || strategy == .nikolovPixel then second else true
      if first < 0 && apply then
        promotions := promotions + 1
        layeringBackup := (← get).layers
        let dummyNodeCount := (← get).dummyNodeCount + first
        modify fun s => { s with dummyNodeCount := dummyNodeCount }
        reducedDummies := reducedDummies + (dummyBackup - dummyNodeCount)
        dummyBackup := dummyNodeCount + first
        heightBackup := (← get).maxHeight
        widthBackup := some ((← get).currentWidth, (← get).currentWidthPixel)
      else
        match widthBackup with
        | some (w, wp) =>
          set ({ layers := layeringBackup, currentWidth := w, currentWidthPixel := wp, maxHeight := heightBackup
                 dummyNodeCount := dummyBackup } : NikolovState)
        | none =>
          -- the backup is the live list: the copy keeps the current widths, the old list becomes the backup
          widthBackup := some ((← get).currentWidth, (← get).currentWidthPixel)
          modify fun s => { s with layers := layeringBackup, dummyNodeCount := dummyBackup, maxHeight := heightBackup }
    iterationCounter := iterationCounter + 1
    if !(promotions != 0 && funky reducedDummies iterationCounter) then break

/-- `precalculateAndSetInformation()`: sets the layer ids (reversed: the first layer gets
`layerCount - 1`) and the node ids (layer by layer), and computes per node the degrees, the
approximated size (`size.y + SPACING_NODE_NODE`), and per layer the width in nodes plus dummies and
in pixels (dummies `SPACING_EDGE_NODE_BETWEEN_LAYERS` each), their maxima and the dummy count. -/
def precalculateAndSetInformation (graph : LGraphId) : LayeredM (NikolovData × NikolovState) := do
  let gr ← getGraph graph
  let nodeSizeAffix := gr.props.getD LayeredOptions.SPACING_NODE_NODE 20.0
  let dummySize := gr.props.getD LayeredOptions.SPACING_EDGE_NODE_BETWEEN_LAYERS 10.0
  let graphLayers := gr.layers
  let maxHeight := graphLayers.size
  let mut layerID : Int := (maxHeight : Int) - 1
  let mut nodeID : Int := 0
  let mut nodes : Array LNodeId := #[]
  for layer in graphLayers do
    let id := layerID
    modifyLayer layer fun l => { l with id := id }
    for node in (← getLayer layer).nodes do
      let nid := nodeID
      modifyNode node fun n => { n with id := nid }
      nodes := nodes.push node
      nodeID := nodeID + 1
    layerID := layerID - 1
  let mut layers : Array Int := Array.replicate nodes.size 0
  let mut nodeSize : Array Float := Array.replicate nodes.size 0.0
  let mut degreeDiff : Array Int := Array.replicate nodes.size 0
  let mut inDegrees : Array Int := Array.replicate nodes.size 0
  let mut outDegrees : Array Int := Array.replicate nodes.size 0
  let mut incomingSources : Array (Array Int) := Array.replicate nodes.size #[]
  let mut nodesWithIncomingEdges : Array Nat := #[]
  let mut currentWidth : Array Int := Array.replicate maxHeight 0
  let mut currentWidthPixel : Array Float := Array.replicate maxHeight 0.0
  let mut maxWidth : Int := 0
  let mut maxWidthPixel : Float := 0.0
  let mut dummyBaggage : Int := 0
  let mut dummyNodeCount : Int := 0
  for layer in graphLayers do
    let l ← getLayer layer
    let layerIdx := l.id.toNat
    let mut incoming : Int := 0
    let mut outcoming : Int := 0
    let layerSize : Int := l.nodes.size
    let mut layerSizePixel : Float := 0.0
    for node in l.nodes do
      let nd ← getNode node
      let id := nd.id.toNat
      layers := layers.set! id l.id
      layerSizePixel := layerSizePixel + (nd.size.y + nodeSizeAffix)
      nodeSize := nodeSize.set! id (nd.size.y + nodeSizeAffix)
      let inEdges ← withArena (·.nodeIncomingEdges node)
      let inDegree : Int := inEdges.size
      let outDegree : Int := (← withArena (·.nodeOutgoingEdges node)).size
      degreeDiff := degreeDiff.set! id (outDegree - inDegree)
      inDegrees := inDegrees.set! id inDegree
      outDegrees := outDegrees.set! id outDegree
      let mut sources : Array Int := #[]
      for edge in inEdges do
        let some port := (← getEdge edge).source | throw (IO.userError "java.lang.NullPointerException")
        let some source := (← getPort port).owner | throw (IO.userError "java.lang.NullPointerException")
        sources := sources.push (← getNode source).id
      incomingSources := incomingSources.set! id sources
      incoming := incoming + inDegree
      outcoming := outcoming + outDegree
      if inDegree > 0 then nodesWithIncomingEdges := nodesWithIncomingEdges.push id
    dummyBaggage := dummyBaggage - incoming
    let nodesNdummies := layerSize + dummyBaggage
    layerSizePixel := layerSizePixel + dummyBaggage.toFloat * dummySize
    currentWidth := currentWidth.set! layerIdx nodesNdummies
    currentWidthPixel := currentWidthPixel.set! layerIdx layerSizePixel
    maxWidth := max maxWidth nodesNdummies
    maxWidthPixel := javaMax maxWidthPixel layerSizePixel
    dummyNodeCount := dummyNodeCount + dummyBaggage
    dummyBaggage := dummyBaggage + outcoming
  let data : NikolovData := {
    nodes, nodeSize, degreeDiff, inDegree := inDegrees, outDegree := outDegrees, incomingSources
    nodesWithIncomingEdges, dummySize, maxWidth, maxWidthPixel }
  return (data, { layers, currentWidth, currentWidthPixel, maxHeight, dummyNodeCount })

/-- The strategy switch of `process` for the Nikolov family (`MAX_ITERATIONS` = `promoteUntil`):
`NIKOLOV`/`NIKOLOV_PIXEL` (and `NO_BOUNDARY`, the default case) run `promotionMagic` once without a
stop criterion; `NIKOLOV_IMPROVED(_PIXEL)` first as `NO_BOUNDARY` and, when the largest width (in nodes
or pixels, over the whole width list) then exceeds the initial maximum, once more as
`NIKOLOV(_PIXEL)` on the result; `NODECOUNT_PERCENTAGE` stops after
`(int) Math.ceil(nodeCount * promoteUntil / 100.0)` iterations and `DUMMYNODE_PERCENTAGE` once
`(int) Math.ceil(dummyNodeCount * promoteUntil / 100.0)` dummies are reduced (`int` products). -/
def nikolovStrategies (d : NikolovData) (strategy : NodePromotionStrategy) (promoteUntil : Int) : NikolovM Unit := do
  let funFunction : Int → Int → Bool := fun _ _ => true
  match strategy with
  | .nikolov | .nikolovPixel => promotionMagic d strategy funFunction
  | .nikolovImproved =>
    promotionMagic d .noBoundary funFunction
    let newMaxWidth := (← get).currentWidth.foldl (fun m w => max m w) 0
    if newMaxWidth > d.maxWidth then promotionMagic d .nikolov funFunction
  | .nikolovImprovedPixel =>
    promotionMagic d .noBoundary funFunction
    let newMaxWidthPixel := (← get).currentWidthPixel.foldl (fun m w => javaMax m w) 0.0
    if newMaxWidthPixel > d.maxWidthPixel then promotionMagic d .nikolovPixel funFunction
  | .nodecountPercentage =>
    let promoteUntilN := (Int.wrap32 ((d.nodes.size : Int) * promoteUntil)).toFloat / 100.0 |>.ceilToInt
    promotionMagic d strategy fun _ iterations => iterations < promoteUntilN
  | .dummynodePercentage =>
    let promoteUntilD := (Int.wrap32 ((← get).dummyNodeCount * promoteUntil)).toFloat / 100.0 |>.ceilToInt
    promotionMagic d strategy fun reduced _ => reduced < promoteUntilD
  | _ => promotionMagic d strategy funFunction

/-- `setNewLayering(graph)`: `maxHeight + 1` new layers with the reversed ids `maxHeight - i`, every
node (in `nodes` order) appended to layer `maxHeight - layers[id]`, empty layers dropped. -/
def setNewLayering (graph : LGraphId) (d : NikolovData) (st : NikolovState) : LayeredM Unit := do
  let maxHeight := st.maxHeight
  -- every node leaves its old layer (Java `setLayer` removes it there; those layers are dropped): empty
  -- them at once instead of one `remove` per node
  for layer in (← getGraph graph).layers do
    modifyLayer layer fun l => { l with nodes := #[] }
  let mut layList : Array LayerId := #[]
  for i in [0:maxHeight + 1] do
    let layer ← createLayer graph
    let id : Int := (maxHeight : Int) - i
    modifyLayer layer fun l => { l with id := id }
    layList := layList.push layer
  for h : i in [0:d.nodes.size] do
    let index := (maxHeight : Int) - st.layers[i]!
    let some layer := (if index >= 0 then layList[index.toNat]? else none)
      | throw (IO.userError s!"java.lang.IndexOutOfBoundsException: Index {index} out of bounds for length {layList.size}")
    setNodeLayer d.nodes[i] (some layer)
  let mut nonEmpty : Array LayerId := #[]
  for layer in layList do
    if !(← getLayer layer).nodes.isEmpty then nonEmpty := nonEmpty.push layer
  let layers := nonEmpty
  modifyGraph graph fun g => { g with layers := layers }

/-- `process` for the strategies other than the model order ones:
`precalculateAndSetInformation()`, the strategy switch, `setNewLayering(graph)`. -/
def nikolovNodePromotion (graph : LGraphId) (strategy : NodePromotionStrategy) : LayeredM Unit := do
  let (d, st) ← precalculateAndSetInformation graph
  let promoteUntil := (← getGraph graph).props.getD LayeredOptions.LAYERING_NODE_PROMOTION_MAX_ITERATIONS 0
  let ((), st) ← (nikolovStrategies d strategy promoteUntil).run st
  setNewLayering graph d st

/-- `process(graph, monitor)` body: the model order strategies or the Nikolov family. -/
def run (graph : LGraphId) : LayeredM Unit := do
  match (← getGraph graph).props.getD LayeredOptions.LAYERING_NODE_PROMOTION_STRATEGY NodePromotionStrategy.none with
  | .modelOrderLeftToRight => modelOrderNodePromotion graph true
  | .modelOrderRightToLeft => modelOrderNodePromotion graph false
  | strategy => nikolovNodePromotion graph strategy

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
