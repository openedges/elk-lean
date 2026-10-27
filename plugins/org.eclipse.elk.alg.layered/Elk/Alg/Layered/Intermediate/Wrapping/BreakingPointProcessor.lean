import Elk.Alg.Layered.Intermediate.Wrapping.BreakingPointInserter
/-!
# `org.eclipse.elk.alg.layered.intermediate.wrapping.BreakingPointProcessor`

Port of elk-rs `intermediate/breaking_point_processor.rs`. The second of the three breaking point
processors performs the actual wrapping: after the layer of breaking point start dummies, the
following layers are moved back to the first layers (an empty layer is prepended for the end
dummies); the `startEndEdge`s entering the end dummies are reversed and replaced by chains of
in-layer/long edge dummies (`CuttingUtils.insertDummies`), which are recorded in the `BPInfo`s.

With `WRAPPING_MULTI_EDGE_IMPROVE_WRAPPED_EDGES` (default `true`) two improvement steps follow:
chains of breaking points of edges spanning several cuts are merged
(`improveMultiCutIndexEdges`), and pairs of parallel long edge dummies next to breaking points
are dropped (`improveUnnecessarilyLongEdges`, backwards from the end dummies, then forwards from
the start dummies). These steps keep each node's index within its layer in `LNode.id` (Rust
`graph_element().id`).

Slots: after phase 3.

Rust deviations from Java (followed):
* `performWrapping` stops when the target layer index leaves the layer list;
* the merge step also relinks the neighbours (`prev.next`, `next.prev`) to the merged info;
* missing infos/dummies end the respective loop instead of throwing;
* `setLayer(index, layer)` clamps the index to `[0, size]` (Rust `set_layer_at_index_clamped`);
* `isAdjacentOrSeparatedByBreakingPoints` returns `false` for an index outside the layer.

TODO(long-edge-joiner): `joinAt` is a private copy of `LongEdgeJoiner.joinAt` (elk-rs
`LongEdgeJoiner::join_at`), which is ported in a parallel task; replace it by
`Elk.Alg.Layered.Intermediate.LongEdgeJoiner.joinAt` once that module is merged.
-/
namespace Elk.Alg.Layered.Intermediate.Wrapping

open Elk.Graph Elk.Core Elk.Core.Alg Elk.Core.Util Elk.Core.Math Elk.Core.Options Elk.Alg.Layered
  Elk.Alg.Layered.Graph Elk.Alg.Layered.Options Elk.Alg.Layered.Intermediate LayeredM

namespace BreakingPointProcessor

/-- Copy of `LongEdgeJoiner::join_at(long_edge_dummy, add_unnecessary_bendpoints)` (see the module
doc): the edges of the first `WEST` port's incoming list survive and take over the targets, bend
points, labels and junction points of the first `EAST` port's outgoing edges (paired by index). -/
private def joinAt (longEdgeDummy : LNodeId) (addUnnecessaryBendpoints : Bool) : LayeredM Unit := do
  let westPort := (← withArena (·.nodePortsBySide longEdgeDummy .west))[0]?
  let eastPort := (← withArena (·.nodePortsBySide longEdgeDummy .east))[0]?
  let (some westPort, some eastPort) := (westPort, eastPort) | return
  let inputEdges := (← getPort westPort).incomingEdges
  let outputEdges := (← getPort eastPort).outgoingEdges
  let edgeCount := min inputEdges.size outputEdges.size
  let unnecessaryBendpoint ← match (← getNode longEdgeDummy).ports[0]? with
    | some p => withArena (·.portAbsoluteAnchor p)
    | none => pure none
  for i in [0:edgeCount] do
    let survivingEdge := inputEdges[i]!
    let droppedEdge := outputEdges[i]!
    let some droppedTarget := (← getEdge droppedEdge).target | continue
    let droppedEdgeListIndex := ((← getPort droppedTarget).incomingEdges.findIdx? (· == droppedEdge)).getD 0
    setEdgeTargetAndInsertAtIndex survivingEdge (some droppedTarget) droppedEdgeListIndex
    setEdgeSource droppedEdge none
    setEdgeTarget droppedEdge none
    if addUnnecessaryBendpoints then
      if let some bp := unnecessaryBendpoint then
        modifyEdge survivingEdge fun e => { e with bendPoints := e.bendPoints.push bp }
    let dropped ← getEdge droppedEdge
    modifyEdge survivingEdge fun e => { e with bendPoints := e.bendPoints ++ dropped.bendPoints }
    modifyEdge droppedEdge fun e => { e with labels := #[] }
    modifyEdge survivingEdge fun e => { e with labels := e.labels ++ dropped.labels }
    let droppedJunctionPoints := if dropped.props.has LayeredOptions.JUNCTION_POINTS then
      dropped.props.get LayeredOptions.JUNCTION_POINTS else none
    if let some djp := droppedJunctionPoints then
      modifyEdge survivingEdge fun e =>
        let survivingJunctions := (if e.props.has LayeredOptions.JUNCTION_POINTS then
          e.props.get LayeredOptions.JUNCTION_POINTS else none).getD #[]
        { e with props := e.props.set LayeredOptions.JUNCTION_POINTS (survivingJunctions ++ djp) }

/-- `node.id` (the index within its layer during the improvement steps). -/
@[inline] private def nodeId (node : LNodeId) : LayeredM Int := do return (← getNode node).id

@[inline] private def setNodeId (node : LNodeId) (value : Int) : LayeredM Unit :=
  modifyNode node fun n => { n with id := value }

/-- `updateIndexesAfter(node)`: decrements the ids of the nodes after `node` in its layer. -/
def updateIndexesAfter (node : LNodeId) : LayeredM Unit := do
  let currentId ← nodeId node
  let some layer := (← getNode node).layer | return
  let nodes := (← getLayer layer).nodes
  let start := (max (currentId + 1) 0).toNat
  for i in [start:nodes.size] do
    let candidate := nodes[i]!
    setNodeId candidate ((← nodeId candidate) - 1)

/-- Rust `set_layer_at_index_clamped`: `setLayer(clamp(index, 0, size), layer)` with the size
taken before the node leaves its current layer; like Rust (`panic!`) an index beyond the layer
after that removal throws. -/
def setLayerAtIndexClamped (node : LNodeId) (index : Int) (layer : LayerId) : LayeredM Unit := do
  let maxLen := (← getLayer layer).nodes.size
  let clamped := (max 0 (min index (maxLen : Int))).toNat
  if (← getNode node).layer == some layer && clamped > maxLen - 1 then
    throw (IO.userError "java.lang.IllegalStateException: index must be >= 0 and <= layer node count")
  setNodeLayerAtIndex node clamped (some layer)

/-- `isInLayerDummy(node)`: a `LONG_EDGE` dummy with a non-self-loop edge to a node of its own
layer. -/
def isInLayerDummy (node : LNodeId) : LayeredM Bool := do
  let nd ← getNode node
  if nd.type != .longEdge then return false
  for edge in (← withArena (·.nodeConnectedEdges node)) do
    if (← withArena (·.edgeIsSelfLoop edge)) then continue
    let some other := (← withArena (·.edgeOtherNode edge node)) | continue
    let otherLayer := (← getNode other).layer
    if nd.layer.isSome && otherLayer.isSome && nd.layer == otherLayer then return true
  return false

/-- `nextLongEdgeDummy(start, forwards)`: the first `LONG_EDGE` neighbour over the outgoing
(`forwards`) or incoming edges that lies in a different layer. -/
def nextLongEdgeDummy (start : LNodeId) (forwards : Bool) : LayeredM (Option LNodeId) := do
  let edges ← if forwards then withArena (·.nodeOutgoingEdges start) else withArena (·.nodeIncomingEdges start)
  let startLayer := (← getNode start).layer
  for edge in edges do
    let some other := (← withArena (·.edgeOtherNode edge start)) | continue
    let o ← getNode other
    if o.type != .longEdge then continue
    if let (some sl, some ol) := (startLayer, o.layer) then
      if sl != ol then return some other
  return none

/-- `isAdjacentOrSeparatedByBreakingpoints(dummy1, dummy2, forwards)`: all nodes strictly between
the two dummies (by id) are breaking points or in-layer dummies. -/
def isAdjacentOrSeparatedByBreakingPoints (dummy1 dummy2 : LNodeId) (forwards : Bool) : LayeredM Bool := do
  let some layer := (← getNode dummy1).layer | return false
  let start := if forwards then dummy2 else dummy1
  let stop := if forwards then dummy1 else dummy2
  let startId ← nodeId start
  let endId ← nodeId stop
  if endId <= startId then return true
  let nodes := (← getLayer layer).nodes
  let mut i := startId + 1
  while i < endId do
    if i < 0 then return false
    let some node := nodes[i.toNat]? | return false
    let isBreaking := (← getNode node).type == .breakingPoint
    if !(isBreaking || (← isInLayerDummy node)) then return false
    i := i + 1
  return true

/-- Moves `bpNode`/`inLayerDummy` to the layer of the dropped pair (the `if let Some(new_layer)`
block of Rust `drop_dummies`). -/
private def moveIntoLayer (bpNode inLayerDummy predOne predTwo : LNodeId) (newLayer : LayerId)
    (forwards : Bool) : LayeredM Unit := do
  let predTwoId ← nodeId predTwo
  let predOneId ← nodeId predOne
  if forwards then
    setLayerAtIndexClamped inLayerDummy predTwoId newLayer
    setNodeId inLayerDummy predTwoId
    setLayerAtIndexClamped bpNode (predOneId + 1) newLayer
    setNodeId bpNode predOneId
  else
    setLayerAtIndexClamped bpNode predOneId newLayer
    setNodeId bpNode predOneId
    setLayerAtIndexClamped inLayerDummy (predTwoId + 1) newLayer
    setNodeId inLayerDummy predTwoId

/-- `dropDummies(bpNode, inLayerDummy, forwards, force)`: while the next long edge dummies of both
chains exist (and, unless `force`, are adjacent or only separated by breaking points / in-layer
dummies), joins them away and moves the two given nodes into their layer. Returns whether any
dummies were dropped. -/
def dropDummies (bpNode inLayerDummy : LNodeId) (forwards force : Bool) : LayeredM Bool := do
  let mut predOne ← nextLongEdgeDummy bpNode forwards
  let mut predTwo ← nextLongEdgeDummy inLayerDummy forwards
  let mut didsome := false
  while true do
    let (some p1, some p2) := (predOne, predTwo) | break
    if !(force || (← isAdjacentOrSeparatedByBreakingPoints p1 p2 forwards)) then break
    let nextOne ← nextLongEdgeDummy p1 forwards
    let nextTwo ← nextLongEdgeDummy p2 forwards
    updateIndexesAfter inLayerDummy
    updateIndexesAfter bpNode
    let newLayer := (← getNode p1).layer
    joinAt p1 false
    joinAt p2 false
    if let some nl := newLayer then
      moveIntoLayer bpNode inLayerDummy p1 p2 nl forwards
    setNodeLayer p1 none
    setNodeLayer p2 none
    predOne := nextOne
    predTwo := nextTwo
    didsome := true
  return didsome

/-- `performWrapping(graph)`: see the module doc. -/
def performWrapping (graph : LGraphId) : LayeredM Unit := do
  let first ← createLayer graph
  modifyGraph graph fun g => { g with layers := g.layers.insertIdxIfInBounds 0 first }
  let mut reverse := false
  let mut idx : Int := 1
  let mut layerItIndex : Nat := 1
  while layerItIndex < (← getGraph graph).layers.size do
    if idx < 0 then break
    let layers := (← getGraph graph).layers
    let newLayerIndex := idx.toNat
    if newLayerIndex >= layers.size then break
    let layer := layers[layerItIndex]!
    let newLayer := layers[newLayerIndex]!
    let nodesToMove := (← getLayer layer).nodes
    let offset := nodesToMove.size
    for node in nodesToMove do
      setNodeLayer node (some newLayer)
    if reverse then
      for node in nodesToMove.reverse do
        let incomingEdges ← withArena (·.nodeIncomingEdges node)
        for edge in incomingEdges do
          LGraphUtil.reverseEdge edge graph true
          modifyGraph graph fun g => { g with internal := { g.internal with cyclic := true } }
          let dummyEdges ← CuttingUtils.insertDummies graph edge offset
          let some _ ← BreakingPointInfo.get? node | continue
          let some startInLayerEdge := dummyEdges.back? | continue
          let startInLayerDummy ← match (← getEdge startInLayerEdge).source with
            | some p => pure (← getPort p).owner
            | none => pure none
          let endInLayerDummy ← match (← getEdge edge).target with
            | some p => pure (← getPort p).owner
            | none => pure none
          BreakingPointInfo.modifyAt node fun info => { info with
            startInLayerDummy, startInLayerEdge := some startInLayerEdge,
            endInLayerDummy, endInLayerEdge := some edge }
      reverse := false
    else if let some aNode := nodesToMove[0]? then
      if (← getNode aNode).type == .breakingPoint then
        reverse := true
        idx := -1
    idx := idx + 1
    layerItIndex := layerItIndex + 1
  let mut kept : Array LayerId := #[]
  for l in (← getGraph graph).layers do
    if !(← getLayer l).nodes.isEmpty then kept := kept.push l
  modifyGraph graph fun g => { g with layers := kept }

/-- One merge of `improveMultiCutIndexEdges`: `current` (start dummy `currentStart`) absorbs
`next`; returns the `next` link of the merged info, or `none` to stop (missing data). -/
private def mergeNext (currentStart nextStart : LNodeId) : LayeredM (Option (Option LNodeId)) := do
  let some next ← BreakingPointInfo.get? nextStart | return none
  let some nextStartInLayerDummy := next.startInLayerDummy | return none
  let _ ← dropDummies next.start nextStartInLayerDummy false true
  let some current ← BreakingPointInfo.get? currentStart | return none
  let some next ← BreakingPointInfo.get? nextStart | return none
  let (some curStartInLayerDummy, some curStartInLayerEdge, some curEndInLayerEdge,
       some nxtStartInLayerDummy, some nxtEndInLayerDummy, some nxtEndInLayerEdge) :=
      (current.startInLayerDummy, current.startInLayerEdge, current.endInLayerEdge,
       next.startInLayerDummy, next.endInLayerDummy, next.endInLayerEdge) | return none
  updateIndexesAfter current.endNode
  updateIndexesAfter next.start
  updateIndexesAfter nxtStartInLayerDummy
  updateIndexesAfter nxtEndInLayerDummy
  let reconnectTarget := (← getEdge curEndInLayerEdge).target
  setEdgeTarget nxtEndInLayerEdge reconnectTarget
  setEdgeTarget curEndInLayerEdge none
  setNodeLayer current.endNode none
  setNodeLayer next.start none
  setNodeLayer nxtStartInLayerDummy none
  setNodeLayer nxtEndInLayerDummy none
  let newInfo : BreakingPointInfo :=
    { BreakingPointInfo.new current.start next.endNode current.nodeStartEdge next.startEndEdge next.originalEdge with
      startInLayerDummy := some curStartInLayerDummy
      startInLayerEdge := some curStartInLayerEdge
      endInLayerDummy := current.endInLayerDummy
      endInLayerEdge := some nxtEndInLayerEdge
      prev := current.prev
      next := next.next }
  BreakingPointInfo.write newInfo
  if let some p := newInfo.prev then
    BreakingPointInfo.modifyAt p fun i => { i with next := some newInfo.start }
  if let some n := newInfo.next then
    BreakingPointInfo.modifyAt n fun i => { i with prev := some newInfo.start }
  return some newInfo.next

/-- `improveMultiCutIndexEdges(graph)`: for every chain head (a start dummy whose info has no
`prev` but a `next`) the chain is merged into one breaking point. -/
def improveMultiCutIndexEdges (graph : LGraphId) : LayeredM Unit := do
  for layer in (← getGraph graph).layers do
    let nodes := (← getLayer layer).nodes
    for node in nodes do
      if !(← BreakingPointInfo.isStart node) then continue
      let some info ← BreakingPointInfo.get? node | continue
      if info.prev.isSome || info.next.isNone then continue
      let current := info.start
      let mut next := info.next
      while true do
        let some nextStart := next | break
        match ← mergeNext current nextStart with
        | some n => next := n
        | none => break

/-- `improveUnneccesarilyLongEdges(graph, forwards)`: repeats sweeps (layers right to left for
`forwards`, nodes right to left otherwise) over the end (`forwards`) or start dummies until a
sweep's last `dropDummies` call drops nothing (Java/Rust overwrite `didsome` per call). -/
def improveUnnecessarilyLongEdges (graph : LGraphId) (forwards : Bool) : LayeredM Unit := do
  while true do
    let mut didsome := false
    let layers := (← getGraph graph).layers
    let layers := if forwards then layers.reverse else layers
    for layer in layers do
      let nodes := (← getLayer layer).nodes
      let nodes := if forwards then nodes else nodes.reverse
      for node in nodes do
        let ok ← if forwards then BreakingPointInfo.isEnd node else BreakingPointInfo.isStart node
        if !ok then continue
        let some bpInfo ← BreakingPointInfo.get? node | continue
        let inLayerDummy := if forwards then bpInfo.endInLayerDummy else bpInfo.startInLayerDummy
        if let some d := inLayerDummy then
          didsome ← dropDummies node d forwards false
    if !didsome then break

/-- `process(graph, monitor)`. -/
def process (graph : LGraphId) (monitor : ProgressMonitor) : LayeredM Unit := do
  let _ ← monitor.begin "Breaking Point Processor" 1.0
  performWrapping graph
  if ((← getGraph graph).props.get LayeredOptions.WRAPPING_MULTI_EDGE_IMPROVE_WRAPPED_EDGES).getD true then
    for layer in (← getGraph graph).layers do
      let nodes := (← getLayer layer).nodes
      for h : index in [0:nodes.size] do
        setNodeId nodes[index] index
    improveMultiCutIndexEdges graph
    improveUnnecessarilyLongEdges graph true
    improveUnnecessarilyLongEdges graph false
  monitor.done

/-- The `BreakingPointProcessor` processor. -/
def processor : LayeredProcessor := { name := "BreakingPointProcessor", process := process }

end BreakingPointProcessor

builtin_initialize registerBreakingPointProcessor : Unit ←
  IntermediateProcessorStrategy.register .breakingPointProcessor BreakingPointProcessor.processor

end Elk.Alg.Layered.Intermediate.Wrapping
