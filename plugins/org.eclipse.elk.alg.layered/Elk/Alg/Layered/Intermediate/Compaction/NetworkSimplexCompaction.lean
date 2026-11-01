import Std.Data.HashMap
import Std.Data.HashSet
import Elk.Alg.Common.NetworkSimplex
import Elk.Alg.Common.Compaction.OneD.ICompactionAlgorithm
import Elk.Alg.Layered.Intermediate.Compaction.CompactionMetadata
import Elk.Core.Util.FloatConst
open Elk.Core.Util.FloatConst
/-!
# `org.eclipse.elk.alg.layered.intermediate.compaction.NetworkSimplexCompaction`

Compaction strategy for the `OneDimensionalCompactor` based on the network simplex algorithm
(elk-rs `NetworkSimplexCompaction` of `intermediate/horizontal_graph_compactor.rs`). Not the
width is minimized but the edge length of the network simplex graph, which is modelled such that
the edge lengths of the original `LGraph` are minimized: one `NNode` per `CGroup`, separation
edges for the constraints (weight `1`, or `2` between a node and a segment), helper nodes for
constraints between segments of the same edge, edge-length edges (weight `100`) for the `LEdge`s,
and an artificial source connecting all sources.

Ported from Rust; differences to Java: `add_nnode_edge` skips self loops (also for the main
edge-length edge) and clamps `delta` at `0`; edges whose target node has no `CNode` (comment
boxes) are skipped instead of failing.

Lean specifics:
* the `NNode`s carry no origin (`NGraph Unit`); `group_to_nnode` is an array indexed by
  `CGroupId.idx` (the group nodes are created first, in group order);
* `add_edge_constraints` reads the outgoing edges of the represented `LNode`s from a snapshot
  taken when the strategy is created (`OutgoingEdgeInfo`): the strategy runs in `CompactM`,
  which has no access to the layered arena, and the edges do not change during compaction;
* Rust moves the port of a joined north/south segment by `adjust` (`port.position.x -= adjust`)
  during compaction. The strategy records these moves in `portAdjustments` (in order) and
  `applyPortAdjustments` replays them on the arena after the compactor finished; nothing reads
  port positions in between;
* `x as i32` saturates like Rust (`toI32`).
-/

namespace Elk.Alg.Layered.Intermediate.Compaction

open Elk.Core.Util Elk.Core.Options Elk.Alg.Common.NetworkSimplex Elk.Alg.Common.Compaction.OneD
open Elk.Alg.Layered.Graph LayeredM CompactM

/-- The network simplex graph of the compaction (no origins). -/
abbrev CompactionNGraph := NGraph Unit

/-- Snapshot of an outgoing `LEdge` of a node `CNode` (Rust reads these from the `LNode` in
`add_edge_constraints`). -/
structure OutgoingEdgeInfo where
  /-- The edge. -/
  edge : LEdgeId
  /-- `is_self_loop()`. -/
  isSelfLoop : Bool
  /-- Side of the source port (`none` if the edge has no source port). -/
  sourceSide : Option PortSide
  /-- Side of the target port (`none` if the edge has no target port). -/
  targetSide : Option PortSide
  /-- Owner of the target port. -/
  targetNode : Option LNodeId
  /-- The source port has outgoing edges (Java `LPort.OUTPUT_PREDICATE`). -/
  sourceHasOutgoing : Bool
  /-- The target port has incoming edges (Java `LPort.INPUT_PREDICATE`). -/
  targetHasIncoming : Bool
  deriving Inhabited

/-- Rust `NetworkSimplexCompaction`. -/
structure NetworkSimplexCompaction where
  /-- The CNode origins (Rust `metadata`). -/
  metadata : CompactionMetadata
  /-- Outgoing edges of the represented `LNode` per `CNodeId.idx` (empty for segments). -/
  outgoingEdges : Array (Array OutgoingEdgeInfo)
  /-- Port moves `(port, adjust)` made during compaction (`port.position.x -= adjust`). -/
  portAdjustments : IO.Ref (Array (LPortId × Float))

namespace NetworkSimplexCompaction

/-- `SEPARATION_WEIGHT` (Rust `NETWORK_SIMPLEX_SEPARATION_WEIGHT`). -/
def SEPARATION_WEIGHT : Float := 1.0

/-- `EDGE_WEIGHT` (Rust `NETWORK_SIMPLEX_EDGE_WEIGHT`). -/
def EDGE_WEIGHT : Float := 100.0

/-- Rust `x as i32`: truncation toward zero, saturating at the `i32` range, NaN → `0`. -/
def toI32 (x : Float) : Int :=
  if x.isNaN then 0
  else
    let t := Float.toIntTrunc x
    if t > I32_MAX then I32_MAX else if t < I32_MIN then I32_MIN else t

/-- Rust `is_north_south_side(side)`. -/
@[inline] def isNorthSouthSide (side : PortSide) : Bool := side == .north || side == .south

private def outgoingEdgeInfo (e : LEdgeId) : LayeredM OutgoingEdgeInfo := do
  let a ← get
  let ed := a.edge e
  let sourcePort := ed.source.map a.port
  let targetPort := ed.target.map a.port
  return { edge := e
           isSelfLoop := a.edgeIsSelfLoop e
           sourceSide := sourcePort.map (·.side)
           targetSide := targetPort.map (·.side)
           targetNode := targetPort.bind (·.owner)
           sourceHasOutgoing := (sourcePort.map fun p => !p.outgoingEdges.isEmpty).getD false
           targetHasIncoming := (targetPort.map fun p => !p.incomingEdges.isEmpty).getD false }

/-- `new NetworkSimplexCompaction()` with the metadata (Rust `NetworkSimplexCompaction::new`) and
the outgoing edge snapshot of the node `CNode`s. -/
def new (metadata : CompactionMetadata) : LayeredM NetworkSimplexCompaction := do
  let mut outgoingEdges : Array (Array OutgoingEdgeInfo) := Array.replicate metadata.nodeOrigins.size #[]
  for h : i in [0:metadata.nodeOrigins.size] do
    let some node := metadata.nodeOrigins[i] | continue
    let edges ← withArena (·.nodeOutgoingEdges node)
    let mut infos : Array OutgoingEdgeInfo := #[]
    for e in edges do
      infos := infos.push (← outgoingEdgeInfo e)
    outgoingEdges := outgoingEdges.set! i infos
  let portAdjustments ← IO.mkRef #[]
  return { metadata, outgoingEdges, portAdjustments }

/-- Rust `add_nnode_edge(source, target, delta, weight)`: no self loops, `delta` clamped at `0`. -/
def addNNodeEdge (g : CompactionNGraph) (source target : NNodeId) (delta : Int) (weight : Float) :
    IO CompactionNGraph := do
  if source == target then return g
  let builder : NEdgeBuilder Unit := NEdge.of
  let (g, _) ← (builder.delta (max delta 0) |>.weight weight |>.source source |>.target target).create g
  return g

/-- Rust `add_group_edge(group_to_nnode, source_group, target_group, delta, weight)`. -/
def addGroupEdge (g : CompactionNGraph) (groupToNNode : Array NNodeId) (sourceGroup targetGroup : CGroupId)
    (delta : Int) (weight : Float) : IO CompactionNGraph := do
  let some source := groupToNNode[sourceGroup.idx]? | return g
  let some target := groupToNNode[targetGroup.idx]? | return g
  addNNodeEdge g source target delta weight

/-- The joined-segments case of `add_separation_constraints`: a helper node keeps the two
segments of the same edge aligned (possibly moving a north/south port by the rounding
difference). -/
private def addSegmentPairConstraint (self : NetworkSimplexCompaction) (g : CompactionNGraph)
    (groupToNNode : Array NNodeId) (cNode incNode : CNodeId) (sourceGroup targetGroup : CGroupId) :
    CompactM CompactionNGraph := do
  let md := self.metadata
  let (g, helper) := (NNode.of : NNodeBuilder Unit).create g
  let incOffset := (← getCNode incNode).cGroupOffset.x
  let cOffset := (← getCNode cNode).cGroupOffset.x
  let offsetDelta := toI32 (incOffset - cOffset).ceil
  let mut adjust := Int.toFloat offsetDelta - (incOffset - cOffset)
  let mut alterOffsetNode := cNode
  let mut port := md.segmentPort cNode
  if port.isNone then
    port := md.segmentPort incNode
    adjust := -adjust
    alterOffsetNode := incNode
  if let some movedPort := port then
    let adj := adjust
    modifyCNode alterOffsetNode fun c => { c with cGroupOffset := { c.cGroupOffset with x := c.cGroupOffset.x - adj } }
    self.portAdjustments.modify (·.push (movedPort, adj))
  let some sourceNNode := groupToNNode[sourceGroup.idx]? | return g
  let some targetNNode := groupToNNode[targetGroup.idx]? | return g
  let g ← addNNodeEdge g helper sourceNNode (max offsetDelta 0) SEPARATION_WEIGHT
  addNNodeEdge g helper targetNNode (max (-offsetDelta) 0) SEPARATION_WEIGHT

/-- Rust `add_separation_constraints` (Java `addSeparationConstraints`): edges guaranteeing the
spacing and order between all groups. -/
def addSeparationConstraints (self : NetworkSimplexCompaction) (g : CompactionNGraph)
    (groupToNNode : Array NNodeId) : CompactM CompactionNGraph := do
  let md := self.metadata
  let mut g := g
  for cNode in (← cNodeIds) do
    let constraints := (← getCNode cNode).constraints
    for incNode in constraints do
      let some sourceGroup := (← getCNode cNode).cGroup | continue
      let some targetGroup := (← getCNode incNode).cGroup | continue
      if sourceGroup == targetGroup then continue
      let spacing ←
        if (← direction).isHorizontal then horizontalSpacing cNode incNode else verticalSpacing cNode incNode
      let c ← getCNode cNode
      let inc ← getCNode incNode
      let delta := toI32 (fmax (c.cGroupOffset.x + c.hitbox.width + spacing - inc.cGroupOffset.x).ceil fl0p0)
      if !md.segmentsShareEdge cNode incNode then
        let sourceIsSegment := md.isSegment cNode
        let targetIsSegment := md.isSegment incNode
        let sourceIsNode := (md.nodeOrigin cNode).isSome
        let targetIsNode := (md.nodeOrigin incNode).isSome
        let weight :=
          if (sourceIsSegment && targetIsNode) || (targetIsSegment && sourceIsNode) then fl2p0
          else SEPARATION_WEIGHT
        g ← addGroupEdge g groupToNNode sourceGroup targetGroup delta weight
        continue
      g ← self.addSegmentPairConstraint g groupToNNode cNode incNode sourceGroup targetGroup
  return g

/-- The inverted-port part of `add_edge_constraints`: keeps the segments of `edge` close to the
node `cNode` (`west`: segments left of the node, else segments right of it). -/
private def addInvertedPortEdges (g : CompactionNGraph) (groupToNNode : Array NNodeId) (cNode : CNodeId)
    (sourceGroup : CGroupId) (segmentNodes : Array CNodeId) (west : Bool) : CompactM CompactionNGraph := do
  let mut g := g
  for segmentNode in segmentNodes do
    let segmentX := (← getCNode segmentNode).hitbox.x
    let nodeX := (← getCNode cNode).hitbox.x
    let isCandidate : Bool := if west then segmentX < nodeX else segmentX > nodeX
    if isCandidate then
      let some segmentGroup := (← getCNode segmentNode).cGroup | continue
      if west then
        g ← addGroupEdge g groupToNNode segmentGroup sourceGroup 1 EDGE_WEIGHT
      else
        g ← addGroupEdge g groupToNNode sourceGroup segmentGroup 1 EDGE_WEIGHT
  return g

/-- Rust `add_edge_constraints` (Java `addEdgeConstraints`): heavy edges for the original
`LEdge`s (except directly connected north/south ports and self loops), plus edges keeping the
segments of inverted ports close to their node. -/
def addEdgeConstraints (self : NetworkSimplexCompaction) (g : CompactionNGraph)
    (groupToNNode : Array NNodeId) : CompactM CompactionNGraph := do
  let md := self.metadata
  let cNodes ← cNodeIds
  let mut lnodeMap : Std.HashMap LNodeId CNodeId := {}
  let mut ledgeMap : Std.HashMap LEdgeId (Array CNodeId) := {}
  for cNode in cNodes do
    if let some node := md.nodeOrigin cNode then
      lnodeMap := lnodeMap.insert node cNode
    else if let some segment := md.segmentInfo cNode then
      let mut seen : Std.HashSet LEdgeId := {}
      for edge in segment.representedEdges do
        if !seen.contains edge then
          seen := seen.insert edge
          ledgeMap := ledgeMap.insert edge ((ledgeMap.getD edge #[]).push cNode)
  let mut g := g
  for cNode in cNodes do
    if (md.nodeOrigin cNode).isNone then continue
    for info in self.outgoingEdges[cNode.idx]?.getD #[] do
      if info.isSelfLoop then continue
      let (some sourceSide, some targetSide) := (info.sourceSide, info.targetSide) | continue
      if isNorthSouthSide sourceSide && isNorthSouthSide targetSide then continue
      let some targetNode := info.targetNode | continue
      let some targetCNode := lnodeMap.get? targetNode | continue
      let some sourceGroup := (← getCNode cNode).cGroup | continue
      let some targetGroup := (← getCNode targetCNode).cGroup | continue
      g ← addGroupEdge g groupToNNode sourceGroup targetGroup 0 EDGE_WEIGHT
      if sourceSide == .west && info.sourceHasOutgoing then
        if let some segmentNodes := ledgeMap.get? info.edge then
          g ← addInvertedPortEdges g groupToNNode cNode sourceGroup segmentNodes true
      if targetSide == .east && info.targetHasIncoming then
        if let some segmentNodes := ledgeMap.get? info.edge then
          g ← addInvertedPortEdges g groupToNNode cNode sourceGroup segmentNodes false
  return g

/-- Rust `add_artificial_source_node(graph, next_id)` (Java `addArtificialSourceNode`): if there
is more than one source, a new node (id `nextId`) gets an edge (`delta 1`, `weight 0`) to each. -/
def addArtificialSourceNode (g : CompactionNGraph) (nextId : Int) : IO (CompactionNGraph × Int) := do
  let mut sources : Array NNodeId := #[]
  for node in g.nodeList do
    if (g.node node).incomingEdges.isEmpty then
      sources := sources.push node
  if sources.size <= 1 then return (g, nextId)
  let (g, dummySource) := ((NNode.of : NNodeBuilder Unit).id nextId).create g
  let mut g := g
  for source in sources do
    g ← addNNodeEdge g dummySource source 1 fl0p0
  return (g, nextId + 1)

/-- `compact(compactor)`: builds the network simplex graph, runs the network simplex and places
every `CNode` at its group's layer plus its group offset. -/
def compact (self : NetworkSimplexCompaction) : CompactM Unit := do
  let cGroups ← cGroupIds
  let mut g : CompactionNGraph := NGraph.new
  let mut groupToNNode : Array NNodeId := #[]
  let mut nextId : Int := 0
  for group in cGroups do
    let id := nextId
    modifyCGroup group fun grp => { grp with id := id }
    let (g', nNode) := ((NNode.of : NNodeBuilder Unit).id id).create g
    g := g'
    groupToNNode := groupToNNode.push nNode
    nextId := nextId + 1
  g ← self.addSeparationConstraints g groupToNNode
  g ← self.addEdgeConstraints g groupToNNode
  let (g', _) ← addArtificialSourceNode g nextId
  let layered ← NetworkSimplex.execute' (NetworkSimplex.forGraph g')
  for cNode in (← cNodeIds) do
    let some group := (← getCNode cNode).cGroup | continue
    let some nNode := groupToNNode[group.idx]? | continue
    let layer := (layered.node nNode).layer
    modifyCNode cNode fun c => { c with hitbox := { c.hitbox with x := Int.toFloat layer + c.cGroupOffset.x } }

/-- The strategy as an alg.common `CompactionAlgorithm`. -/
def toAlgorithm (self : NetworkSimplexCompaction) : CompactionAlgorithm := ⟨self.compact⟩

/-- Replays the recorded port moves on the arena (`port.position.x -= adjust`, in order). -/
def applyPortAdjustments (self : NetworkSimplexCompaction) : LayeredM Unit := do
  for (port, adjust) in (← self.portAdjustments.get) do
    modifyPort port fun p => { p with position := { p.position with x := p.position.x - adjust } }

end NetworkSimplexCompaction

end Elk.Alg.Layered.Intermediate.Compaction
