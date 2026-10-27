import Std.Data.HashMap
import Elk.Alg.Layered.LayeredPhases
import Elk.Alg.Layered.Options
/-!
# `org.eclipse.elk.alg.layered.p4nodes.LinearSegmentsNodePlacer` (elk-rs `p4nodes/linear_segments_node_placer.rs`)

Node placement following Sander's linear segments approach (G. Sander, *A fast heuristic
for hierarchical Manhattan layout*, GD'95): long edge dummies and north/south port dummies
form linear segments, the segments are ordered topologically by their in-layer order,
placed top-down without overlaps, balanced with the pendulum method and finally moved
towards straight incoming/outgoing edges where there is room.

Port notes (Rust is the oracle):

* node ids: like Rust, `LNode.id` of every layer node is overwritten (`-1`, then the
  segment index, finally the segment's rank); it is the segment index used by all steps;
* `layerIndex(node)` is the node's **layer id** (`Layer.id`, Rust
  `layer.graph_element().id as usize`, normally set to the layer index by the crossing
  minimizer), not `Layer.getIndex()` as in Java; a node without layer has index `0`, a
  negative id is out of range;
* the input/output priorities (Rust node properties `linearSegments.inputPrio` /
  `linearSegments.outputPrio`, only read by this placer) are kept in a local map from node
  to `(inputPrio, outputPrio)`; nodes without entry read `Integer.MIN_VALUE`;
* the Rust `ArenaSync` snapshot (sizes, margins, port positions/anchors) is replaced by
  live arena reads: the placer only writes node y positions and layer heights, which Rust
  reads live as well (`PORTING.md` §15.1);
* `createDependencyGraphEdges` follows Rust: `retain` removes every occurrence of the split
  segment from the predecessor's outgoing list (Java removes the first) and the incoming
  count is only decremented when positive;
* the unused `nodeCount` array of `createUnbalancedPlacement` is not ported.
-/
namespace Elk.Alg.Layered.P4Nodes

open Elk.Graph Elk.Core.Alg Elk.Core.Util Elk.Alg.Layered Elk.Alg.Layered.Graph
open Elk.Alg.Layered.Options Elk.Alg.Layered.Intermediate LayeredM

namespace LinearSegmentsNodePlacer

/-- `Integer.MIN_VALUE` / `i32::MIN`. -/
private def I32_MIN : Int := -2147483648

/-- `HIERARCHY_PROCESSING_ADDITIONS`: the hierarchical port position processor before edge routing. -/
def HIERARCHY_PROCESSING_ADDITIONS : LayeredProcessorConfiguration :=
  (LayoutProcessorConfiguration.create : LayeredProcessorConfiguration)
    |>.addBefore .p5EdgeRouting .hierarchicalPortPositionProcessor

/-- `getLayoutProcessorConfiguration(graph)`: the hierarchy additions if the graph has external ports. -/
def getLayoutProcessorConfiguration (graph : LGraphId) : LayeredM (Option LayeredProcessorConfiguration) := do
  if (← getGraph graph).internal.graphProperties.contains .externalPorts then
    return some (LayoutProcessorConfiguration.createFrom HIERARCHY_PROCESSING_ADDITIONS)
  else
    return none

/-- `LinearSegmentsNodePlacer.LinearSegment`: a set of nodes (one per layer) placed on the
same y coordinate as far as possible. -/
structure LinearSegment where
  /-- `nodes`: the nodes of the segment, in layer order. -/
  nodes : Array LNodeId := #[]
  /-- `id`: identifier (index in the segment list). -/
  id : Nat := 0
  /-- `indexInLastLayer`: index of the segment's node in the last layer it was seen in (`-1`). -/
  indexInLastLayer : Int := -1
  /-- `lastLayer`: the last layer the segment was seen in (`-1`). -/
  lastLayer : Int := -1
  /-- `deflection`: the accumulated force of the edges. -/
  deflection : Float := 0.0
  /-- `weight`: number of nodes contributing to the deflection. -/
  weight : Int := 0
  /-- `refSegment`: the segment this one has been merged into (region). -/
  refSegment : Option Nat := none
  /-- `nodeType`: the type of the segment's (last added) node. -/
  nodeType : NodeType := .normal
  deriving Inhabited

/-- `LinearSegment.split(node, newId)`: splits the segment before `node` (index `0` if not
contained), relabels the moved nodes with `newId` and returns `(shortened, new)`. -/
def LinearSegment.split (seg : LinearSegment) (node : LNodeId) (newId : Nat) :
    LayeredM (LinearSegment × LinearSegment) := do
  let nodeIndex := (seg.nodes.findIdx? (· == node)).getD 0
  let newNodes := seg.nodes.extract nodeIndex seg.nodes.size
  for moved in newNodes do
    modifyNode moved fun n => { n with id := (newId : Int) }
  return ({ seg with nodes := seg.nodes.extract 0 nodeIndex },
          { nodes := newNodes, id := newId, nodeType := seg.nodeType })

/-- Balancing mode (`Mode`). -/
inductive Mode where
  | forwPendulum
  | backwPendulum
  | rubber
  deriving BEq, Inhabited

/-- Input/output priority per node (Rust `INPUT_PRIO_PROPERTY` / `OUTPUT_PRIO_PROPERTY`). -/
abbrev PrioMap := Std.HashMap LNodeId (Int × Int)

/-- `max(inputPrio, outputPrio)`-style lookup: `(input, output)`, `Integer.MIN_VALUE` when unset. -/
@[inline] private def prioOf (prios : PrioMap) (n : LNodeId) : Int × Int :=
  prios.getD n (I32_MIN, I32_MIN)

/-- Rust `node_id(node).max(0) as usize`: the node's segment index. -/
@[inline] private def segIndexOf (n : LNodeId) : LayeredM Nat := do
  return (← getNode n).id.toNat

/-- Rust `layer_index(node)`: the id of the node's layer (`0` without layer). -/
private def layerIndexOf (n : LNodeId) : LayeredM Int := do
  match (← getNode n).layer with
  | some l => return (← getLayer l).id
  | none => return 0

/-- `Spacings.getVerticalSpacing(n1, n2)` for two arena nodes. -/
private def verticalSpacing (spacings : Spacings) (n1 n2 : LNodeId) : LayeredM Float := do
  let a ← getNode n1
  let b ← getNode n2
  spacings.getVerticalSpacing a.type a.props b.type b.props

/-- Rust `port_position_y_a(node, port)`: node y + port y + anchor y. -/
private def portPositionY (node : LNodeId) (port : LPortId) : LayeredM Float := do
  let nd ← getNode node
  let pt ← getPort port
  return nd.position.y + pt.position.y + pt.anchor.y

@[inline] private def isSegmentDummy (t : NodeType) : Bool :=
  t == .longEdge || t == .northSouthPort

/-- `fillSegment(node, segment)`: adds `node` (which must not be part of a segment yet) and,
for long edge / north-south port dummies, follows the first successor dummy in another layer
that is not part of a segment yet. The Rust recursion returns after the first successful
recursive call, so it is a chain walk; it is written as a loop. -/
def fillSegment (start : LNodeId) (segment : LinearSegment) : LayeredM LinearSegment := do
  let mut seg := segment
  let mut current := start
  while true do
    modifyNode current fun n => { n with id := (seg.id : Int) }
    seg := { seg with nodes := seg.nodes.push current }
    let nd ← getNode current
    seg := { seg with nodeType := nd.type }
    if !isSegmentDummy nd.type then
      break
    let currentLayer ← layerIndexOf current
    let mut next : Option LNodeId := none
    for sourcePort in nd.ports do
      for targetPort in (← withArena (·.portSuccessorPorts sourcePort)) do
        let some targetNode := (← getPort targetPort).owner | continue
        let tnd ← getNode targetNode
        if currentLayer != (← layerIndexOf targetNode) && isSegmentDummy tnd.type && tnd.id < 0 then
          next := some targetNode
          break
      if next.isSome then
        break
    match next with
    | some t => current := t
    | none => break
  return seg

/-- First part of `sortLinearSegments`: resets the node ids to `-1` and computes the
input/output priorities (maximum `PRIORITY_STRAIGHTNESS` of the incoming/outgoing edges). -/
private def initNodePriorities (layers : Array LayerId) : LayeredM PrioMap := do
  let mut prios : PrioMap := {}
  for layer in layers do
    for node in (← getLayer layer).nodes do
      modifyNode node fun n => { n with id := -1 }
      let mut inprio := I32_MIN
      let mut outprio := I32_MIN
      for port in (← getNode node).ports do
        let pt ← getPort port
        for edge in pt.incomingEdges do
          let prio := (← getEdge edge).props.get LayeredOptions.PRIORITY_STRAIGHTNESS |>.getD 0
          inprio := max inprio prio
        for edge in pt.outgoingEdges do
          let prio := (← getEdge edge).props.get LayeredOptions.PRIORITY_STRAIGHTNESS |>.getD 0
          outprio := max outprio prio
      prios := prios.insert node (inprio, outprio)
  return prios

/-- State of `createDependencyGraphEdges`: segments, outgoing dependencies and incoming counts. -/
private structure DependencyGraph where
  segments : Array LinearSegment
  outgoing : Array (Array Nat)
  incomingCount : Array Int

/-- Rust `create_dependency_graph_edges`: a dependency from the segment of every node to the
segment of the next node in its layer, splitting segments that would create cycles. -/
private def createDependencyGraphEdges (layers : Array LayerId) (dg : DependencyGraph) :
    LayeredM DependencyGraph := do
  let mut segments := dg.segments
  let mut outgoing := dg.outgoing
  let mut incomingCount := dg.incomingCount
  let mut nextId := segments.size
  let mut layerIndex : Int := 0
  for layer in layers do
    let nodes := (← getLayer layer).nodes
    if nodes.isEmpty then
      continue
    let mut indexInLayer : Nat := 0
    let mut previousNode : Option LNodeId := none
    for h : pos in [0:nodes.size] do
      let node := nodes[pos]
      let mut currentSegmentId ← segIndexOf node
      let seg := segments[currentSegmentId]!
      let mut cycleFound := false
      if seg.indexInLastLayer >= 0 then
        for cycleNode in nodes.extract (indexInLayer + 1) nodes.size do
          let cycleSeg := segments[(← segIndexOf cycleNode)]!
          if cycleSeg.lastLayer == seg.lastLayer && cycleSeg.indexInLastLayer < seg.indexInLastLayer then
            cycleFound := true
            break
      if cycleFound then
        if let some prev := previousNode then
          let prevId ← segIndexOf prev
          if incomingCount[currentSegmentId]! > 0 then
            incomingCount := incomingCount.modify currentSegmentId (· - 1)
          let cur := currentSegmentId
          outgoing := outgoing.modify prevId (·.filter (· != cur))
        let (shortened, newSegment) ← segments[currentSegmentId]!.split node nextId
        segments := segments.set! currentSegmentId shortened
        segments := segments.push newSegment
        outgoing := outgoing.push #[]
        incomingCount := incomingCount.push (if previousNode.isSome then 1 else 0)
        if let some prev := previousNode then
          let prevId ← segIndexOf prev
          let nid := nextId
          outgoing := outgoing.modify prevId (·.push nid)
        currentSegmentId := nextId
        nextId := nextId + 1
      if h' : pos + 1 < nodes.size then
        let nextSegmentId ← segIndexOf nodes[pos + 1]
        outgoing := outgoing.modify currentSegmentId (·.push nextSegmentId)
        incomingCount := incomingCount.modify nextSegmentId (· + 1)
      let li := layerIndex
      let il := indexInLayer
      segments := segments.modify currentSegmentId fun s => { s with lastLayer := li, indexInLastLayer := (il : Int) }
      previousNode := some node
      indexInLayer := indexInLayer + 1
    layerIndex := layerIndex + 1
  return { segments := segments, outgoing := outgoing, incomingCount := incomingCount }

/-- `sortLinearSegments(graph)`: builds the linear segments, orders them topologically
(queue of segments without incoming dependencies, in index order) and relabels segments and
node ids with the rank. Returns the ordered segments and the node priorities. -/
def sortLinearSegments (graph : LGraphId) : LayeredM (Array LinearSegment × PrioMap) := do
  let layers := (← getGraph graph).layers
  let prios ← initNodePriorities layers
  let mut initialSegments : Array LinearSegment := #[]
  let mut nextId : Nat := 0
  for layer in layers do
    for node in (← getLayer layer).nodes do
      if (← getNode node).id < 0 then
        let segment ← fillSegment node { id := nextId }
        nextId := nextId + 1
        initialSegments := initialSegments.push segment
  let dg ← createDependencyGraphEdges layers
    { segments := initialSegments, outgoing := Array.replicate initialSegments.size #[],
      incomingCount := Array.replicate initialSegments.size 0 }
  let segmentList := dg.segments
  let mut outgoing := dg.outgoing
  let mut incomingCount := dg.incomingCount
  let mut noIncoming : Array Nat := #[]
  for h : idx in [0:incomingCount.size] do
    if incomingCount[idx] == 0 then
      noIncoming := noIncoming.push idx
  let mut newRanks : Array Nat := Array.replicate segmentList.size 0
  let mut nextRank : Nat := 0
  let mut head := 0
  while head < noIncoming.size do
    let segIndex := noIncoming[head]!
    head := head + 1
    let segId := segmentList[segIndex]!.id
    newRanks := newRanks.set! segId nextRank
    nextRank := nextRank + 1
    let targets := outgoing[segId]!
    outgoing := outgoing.set! segId #[]
    for target in targets do
      if incomingCount[target]! > 0 then
        incomingCount := incomingCount.modify target (· - 1)
        if incomingCount[target]! == 0 then
          noIncoming := noIncoming.push target
  let mut linearSegments : Array LinearSegment := Array.replicate segmentList.size {}
  for segment in segmentList do
    let rank := newRanks[segment.id]!
    for node in segment.nodes do
      modifyNode node fun n => { n with id := (rank : Int) }
    linearSegments := linearSegments.set! rank { segment with id := rank }
  return (linearSegments, prios)

/-- `createUnbalancedPlacement(graph)`: places the segments in order, each as high as
possible below the nodes already placed in its layers (`layer.size.y` is the running
bottom of each layer). -/
def createUnbalancedPlacement (graph : LGraphId) (segments : Array LinearSegment) (spacings : Spacings) :
    LayeredM Unit := do
  let gr ← getGraph graph
  let layers := gr.layers
  let layerCount := layers.size
  let spacingEdgeEdge := gr.props.get LayeredOptions.SPACING_EDGE_EDGE |>.getD 0.0
  let mut recentNode : Array (Option LNodeId) := Array.replicate layerCount none
  for segment in segments do
    let mut uppermostPlace : Float := 0.0
    for node in segment.nodes do
      let li ← layerIndexOf node
      if li < 0 || li >= (layerCount : Int) then
        continue
      let i := li.toNat
      let spacing ← match recentNode[i]! with
        | some prev => verticalSpacing spacings prev node
        | none => pure spacingEdgeEdge
      let layerSize := (← getLayer layers[i]!).size.y
      uppermostPlace := fmax uppermostPlace (layerSize + spacing)
    for node in segment.nodes do
      let li ← layerIndexOf node
      let nd ← getNode node
      let up := uppermostPlace
      modifyNode node fun x => { x with position := { x.position with y := up + nd.margin.top } }
      if li >= 0 && li < (layerCount : Int) then
        let i := li.toNat
        modifyLayer layers[i]! fun l =>
          { l with size := { l.size with y := up + nd.margin.top + nd.size.y + nd.margin.bottom } }
        recentNode := recentNode.set! i (some node)

/-- Rust `region_index(segments, index)`: follows `refSegment` to the representative of the
region (merge chains are acyclic, so at most `segments.size` steps). -/
def regionIndex (segments : Array LinearSegment) (index : Nat) : Nat := Id.run do
  let mut current := index
  for _ in [0:segments.size + 1] do
    match segments[current]?.bind (·.refSegment) with
    | some next => current := next
    | none => break
  return current

/-- One direction of `calcDeflection`: adds the position differences of the edges of `edges`
whose other end is in another segment and whose priority is high enough to the running
`(nodeDeflection, edgeWeightSum)` (one running sum, as in Rust). -/
private def edgeDeflection (prios : PrioMap) (segmentIndex : Nat) (minPrio : Int) (portPos : Float)
    (edges : Array LEdgeId) (useTarget : Bool) (start : Float × Int) : LayeredM (Float × Int) := do
  let mut (nodeDeflection, edgeWeightSum) := start
  for edge in edges do
    let ed ← getEdge edge
    let some otherPort := (if useTarget then ed.target else ed.source) | continue
    let some otherNode := (← getPort otherPort).owner | continue
    let otherSegment ← segIndexOf otherNode
    if otherSegment != segmentIndex then
      let (oi, oo) := prioOf prios otherNode
      let otherPrio := max oi oo
      let prio := ed.props.get LayeredOptions.PRIORITY_STRAIGHTNESS |>.getD 0
      if prio >= minPrio && prio >= otherPrio then
        nodeDeflection := nodeDeflection + ((← portPositionY otherNode otherPort) - portPos)
        edgeWeightSum := edgeWeightSum + 1
  return (nodeDeflection, edgeWeightSum)

/-- `calcDeflection(segment, incoming, outgoing, deflectionDampening)` (Rust
`compute_deflection`): the dampened average position difference to the connected nodes of
other segments, and the number of contributing nodes. Per port: outgoing edges, then
incoming edges. -/
def computeDeflection (segments : Array LinearSegment) (prios : PrioMap) (segmentIndex : Nat)
    (incoming outgoing : Bool) (deflectionDampening : Float) : LayeredM (Float × Int) := do
  let mut segmentDeflection := 0.0
  let mut nodeWeightSum : Int := 0
  for node in segments[segmentIndex]!.nodes do
    let mut acc : Float × Int := (0.0, 0)
    let (ip, op) := prioOf prios node
    let inputPrio := if incoming then ip else I32_MIN
    let outputPrio := if outgoing then op else I32_MIN
    let minPrio := max inputPrio outputPrio
    for port in (← getNode node).ports do
      let portPos ← portPositionY node port
      let pt ← getPort port
      if outgoing then
        acc ← edgeDeflection prios segmentIndex minPrio portPos pt.outgoingEdges true acc
      if incoming then
        acc ← edgeDeflection prios segmentIndex minPrio portPos pt.incomingEdges false acc
    let (nodeDeflection, edgeWeightSum) := acc
    if edgeWeightSum > 0 then
      segmentDeflection := segmentDeflection + nodeDeflection / Float.ofInt edgeWeightSum
      nodeWeightSum := nodeWeightSum + 1
  if nodeWeightSum > 0 then
    return (deflectionDampening * segmentDeflection / Float.ofInt nodeWeightSum, nodeWeightSum)
  else
    return (0.0, 0)

/-- `mergeRegions(graph)`: merges touching regions of each layer (overlapping after applying
their deflections) into the lower one, averaging the deflections by weight. Returns whether
anything changed. -/
def mergeRegions (graph : LGraphId) (segments : Array LinearSegment) (spacings : Spacings) :
    LayeredM (Bool × Array LinearSegment) := do
  let gr ← getGraph graph
  let nodeSpacing := gr.props.get LayeredOptions.SPACING_NODE_NODE |>.getD 0.0
  let threshold := 0.0001 * nodeSpacing
  let mut segments := segments
  let mut changed := false
  for layer in gr.layers do
    let nodes := (← getLayer layer).nodes
    if nodes.isEmpty then
      continue
    let mut node1 := nodes[0]!
    let mut region1 := regionIndex segments (← segIndexOf node1)
    for node2 in nodes.extract 1 nodes.size do
      let region2 := regionIndex segments (← segIndexOf node2)
      if region1 != region2 then
        let spacing ← verticalSpacing spacings node1 node2
        let n1 ← getNode node1
        let n2 ← getNode node2
        let s1 := segments[region1]!
        let s2 := segments[region2]!
        let node1Extent := n1.position.y + n1.size.y + n1.margin.bottom + s1.deflection + spacing
        let node2Extent := n2.position.y - n2.margin.top + s2.deflection
        if node1Extent > node2Extent + threshold then
          let weightSum := s1.weight + s2.weight
          if weightSum > 0 then
            let newDeflection := (Float.ofInt s2.weight * s2.deflection + Float.ofInt s1.weight * s1.deflection) /
              Float.ofInt weightSum
            segments := segments.modify region2 fun s => { s with deflection := newDeflection, weight := weightSum }
            let r2 := region2
            segments := segments.modify region1 fun s => { s with refSegment := some r2 }
            changed := true
      node1 := node2
      region1 := region2
  return (changed, segments)

/-- `balancePlacement(graph)`: pendulum iterations (alternating incoming/outgoing forces) until
the total deflection stops decreasing, then rubber iterations (both directions) until it
converges. -/
def balancePlacement (graph : LGraphId) (segments : Array LinearSegment) (prios : PrioMap)
    (spacings : Spacings) : LayeredM (Array LinearSegment) := do
  let gr ← getGraph graph
  let deflectionDampening :=
    gr.props.get LayeredOptions.NODE_PLACEMENT_LINEAR_SEGMENTS_DEFLECTION_DAMPENING |>.getD 0.0
  let thoroughness := gr.props.get LayeredOptions.THOROUGHNESS |>.getD 1
  let mut segments := segments
  let mut pendulumIters : Int := 4
  let mut finalIters : Int := 3
  let threshold := 20.0 / Float.ofInt thoroughness
  let mut ready := false
  let mut mode := Mode.forwPendulum
  let mut lastTotalDeflection := Float.maxValue
  while true do
    let incoming := mode != .backwPendulum
    let outgoing := mode != .forwPendulum
    let mut totalDeflection := 0.0
    for index in [0:segments.size] do
      segments := segments.modify index fun s => { s with refSegment := none }
      let (deflection, weight) ← computeDeflection segments prios index incoming outgoing deflectionDampening
      segments := segments.modify index fun s => { s with deflection := deflection, weight := weight }
      totalDeflection := totalDeflection + deflection.abs
    while true do
      let (changed, segs) ← mergeRegions graph segments spacings
      segments := segs
      if !changed then
        break
    for index in [0:segments.size] do
      let deflection := segments[regionIndex segments index]!.deflection
      if deflection != 0.0 then
        for node in segments[index]!.nodes do
          modifyNode node fun x => { x with position := { x.position with y := x.position.y + deflection } }
    match mode with
    | .forwPendulum | .backwPendulum =>
      pendulumIters := pendulumIters - 1
      if pendulumIters <= 0 && (totalDeflection < lastTotalDeflection || -pendulumIters > thoroughness) then
        mode := .rubber
        lastTotalDeflection := Float.maxValue
      else if mode == .forwPendulum then
        mode := .backwPendulum
        lastTotalDeflection := totalDeflection
      else
        mode := .forwPendulum
        lastTotalDeflection := totalDeflection
    | .rubber =>
      ready := totalDeflection >= lastTotalDeflection || lastTotalDeflection - totalDeflection < threshold
      lastTotalDeflection := totalDeflection
      if ready then
        finalIters := finalIters - 1
    if ready && finalIters <= 0 then
      break
  return segments

/-- Room above (`true`) or below (`false`) a node of a segment in `postProcess`. -/
private def roomAround (spacings : Spacings) (node : LNodeId) (above : Bool) : LayeredM Float := do
  let index := (← withArena (·.nodeIndex node)).getD 0
  let nd ← getNode node
  let layerNodes ← match nd.layer with
    | some l => pure (← getLayer l).nodes
    | none => pure #[]
  if above then
    if index > 0 && index <= layerNodes.size then
      let neighbor := layerNodes[index - 1]!
      let spacing ← verticalSpacing spacings node neighbor
      let nb ← getNode neighbor
      return nd.position.y - nd.margin.top - (nb.position.y + nb.size.y + nb.margin.bottom + spacing)
    else
      return nd.position.y - nd.margin.top
  else
    if index + 1 < layerNodes.size then
      let neighbor := layerNodes[index + 1]!
      let spacing ← verticalSpacing spacings node neighbor
      let nb ← getNode neighbor
      return nb.position.y - nb.margin.top - (nd.position.y + nd.size.y + nd.margin.bottom + spacing)
    else
      return 2.0 * nd.position.y

/-- The displacement search of `postProcess` over the edges of one end node: incoming edges of
the first node (`incoming = true`) or outgoing edges of the last node. -/
private def searchDisplacement (node : LNodeId) (incoming : Bool) (minRoomAbove minRoomBelow : Float)
    (start : Float × Bool) : LayeredM (Float × Bool) := do
  let mut (minDisplacement, foundPlace) := start
  for port in (← getNode node).ports do
    let pos ← portPositionY node port
    let pt ← getPort port
    let edges := if incoming then pt.incomingEdges else pt.outgoingEdges
    for edge in edges do
      let ed ← getEdge edge
      let some otherPort := (if incoming then ed.source else ed.target) | continue
      let some otherNode := (← getPort otherPort).owner | continue
      let d := (← portPositionY otherNode otherPort) - pos
      if d.abs < minDisplacement.abs && d.abs < (if d < 0.0 then minRoomAbove else minRoomBelow) then
        minDisplacement := d
        foundPlace := true
  return (minDisplacement, foundPlace)

/-- `postProcess()`: moves each segment towards the closest connected port position (incoming
edges of its first node, outgoing edges of its last node) if there is room. -/
def postProcess (segments : Array LinearSegment) (spacings : Spacings) : LayeredM Unit := do
  for segment in segments do
    let mut minRoomAbove := Float.maxValue
    let mut minRoomBelow := Float.maxValue
    for node in segment.nodes do
      minRoomAbove := fmin minRoomAbove (← roomAround spacings node true)
      minRoomBelow := fmin minRoomBelow (← roomAround spacings node false)
    let mut result : Float × Bool := (Float.maxValue, false)
    if let some first := segment.nodes[0]? then
      result ← searchDisplacement first true minRoomAbove minRoomBelow result
    if let some last := segment.nodes.back? then
      result ← searchDisplacement last false minRoomAbove minRoomBelow result
    let (minDisplacement, foundPlace) := result
    if foundPlace && minDisplacement != 0.0 then
      for node in segment.nodes do
        modifyNode node fun x => { x with position := { x.position with y := x.position.y + minDisplacement } }

/-- `process(graph, monitor)` (Rust `LinearSegmentsNodePlacer::process`). -/
def process (graph : LGraphId) (monitor : ProgressMonitor) : LayeredM Unit := do
  let _ ← monitor.begin "Linear segments node placement" 1.0
  let some spacings := (← getGraph graph).internal.spacings
    | throw (IO.userError "java.lang.IllegalStateException: Missing spacings configuration for linear segments")
  let (segments, prios) ← sortLinearSegments graph
  createUnbalancedPlacement graph segments spacings
  let segments ← balancePlacement graph segments prios spacings
  postProcess segments spacings
  monitor.done

/-- The `LinearSegmentsNodePlacer` phase. -/
def phase : LayeredPhase :=
  { name := "LinearSegmentsNodePlacer"
    process := process
    getLayoutProcessorConfiguration := getLayoutProcessorConfiguration }

end LinearSegmentsNodePlacer

/-- Registers `NodePlacementStrategy.LINEAR_SEGMENTS` → `LinearSegmentsNodePlacer`. -/
builtin_initialize registerLinearSegmentsNodePlacer : Unit ←
  LayeredPhases.registerPhase .p4NodePlacement (ElkEnum.ordinal NodePlacementStrategy.linearSegments)
    (pure LinearSegmentsNodePlacer.phase)

end Elk.Alg.Layered.P4Nodes
