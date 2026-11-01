import Std.Data.HashMap
import Std.Data.HashSet
import Elk.Alg.Common.Compaction.OneD.CGraph
import Elk.Alg.Layered.Graph
import Elk.Alg.Layered.Options.LayeredOptions
import Elk.Alg.Layered.Intermediate.Compaction.CompactionMetadata
import Elk.Core.Util.Sort
import Elk.Core.Util.JavaSort
import Elk.Core.Util.FloatConst
open Elk.Core.Util.FloatConst
/-!
# `org.eclipse.elk.alg.layered.intermediate.compaction.LGraphToCGraphTransformer`

Transformation of the `LNode`s and `LEdge`s of a routed `LGraph` into the `CNode`s and `CGroup`s
of a `CGraph`, and the application of the compacted positions back to the `LGraph` (elk-rs
`CompactionContext` of `intermediate/horizontal_graph_compactor.rs`; `compact` is in
`HorizontalGraphCompactor`).

## Construction (Rust `new`, `transform_nodes`, `transform_edges_*`, `register_segments`)
* `nodes` are the nodes of all layers in layer order; the graph supports `LEFT`, `RIGHT` and,
  if no node has an edge, also `UP` and `DOWN`;
* every node except connected comment boxes becomes a `CNode` (hitbox = node box plus margins)
  in its own `CGroup`; connected comment boxes keep their offset to the first connected node
  (`commentOffsets`, in node order) and are re-positioned afterwards;
* orthogonal routing: the vertical segments of all edges are collected per node (outgoing edges:
  the north/south source segment, then the regular segments between bend points; incoming
  edges: the north/south target segment), in this creation order (= `segmentId` order);
* spline routing: every non-straight spline segment of an edge's `SPLINE_ROUTE_START` chain is a
  segment, with a predefined constraint to the next non-straight segment of the chain;
* the segments are sorted like Java's `Collections.sort(verticalSegments)` (JDK `TimSort`,
  `javaSortBy`, with `VerticalSegment.compareTo`: fuzzy x, then y — not transitive, so TimSort's
  comparison sequence matters; elk-rs: a stable sort), merged when they intersect and turned into
  `CNode`s (after the node `CNode`s, in merged order); north/south segments join the group of
  their (first) parent node;
* connection locks (`LEFT_RIGHT_CONNECTION_LOCKING`): a node is locked to the left if it has
  fewer incoming than outgoing edges (to the right if more; external port dummies are never
  locked), a segment by the number of distinct source vs. target ports of its edges.

## Lean representation
* The Rust pointer-keyed maps are arrays indexed by `CNodeId.idx` (`cnodeOrigin`,
  `connectionLocks`; Rust `cnode_to_segment` is the `.segment` case of `cnodeOrigin`) or a
  `Std.HashMap LNodeId CNodeId` (`nodeToCNode`, lookups only). Loops that iterate a Rust
  `HashMap` with order-independent effects (`apply_self_loop_label_offsets`,
  `apply_external_port_positions`) iterate the `CNode`s in arena order.
* Spline segments belong to the `p5edges.splines` package (which imports the layered phases, so
  this module stays independent of it). The transformer reads them through `SplineRouteAccess`
  (segment handles are `Nat`s: the `SplineSegmentId.idx` of the graph's segment table);
  `HorizontalGraphCompactor.splineRouteAccess` is the real access used by the processor,
  `SplineRouteAccess.unavailable` reports no routes.

## Differences to Java (Rust followed)
* the last regular segment of an outgoing edge compares the *last* bend point with the target
  hitbox (Java: the second to last one);
* junction points are not moved; comment offsets are kept in node order (Java `HashMap`);
* predefined constraints are deduplicated and never connect a `CNode` to itself;
* `adjustSplineControlPoints` advances past straight segments (the Java loop does not);
* the node groups have no `master` (Rust `CGroup::create`); `EdgeAwareScanlineConstraintCalculation`
  falls back to the first group node, which is the node `CNode`.
-/

namespace Elk.Alg.Layered.Intermediate.Compaction

open Elk.Graph Elk.Core Elk.Core.Math Elk.Core.Util Elk.Core.Options Elk.Alg.Common.Compaction.OneD
open Elk.Alg.Layered.Graph Elk.Alg.Layered.Options LayeredM

/-- Rust `CommentOffset`: a comment box positioned relative to `anchor` after compaction. -/
structure CommentOffset where
  comment : LNodeId
  anchor : LNodeId
  offset : KVector
  deriving Inhabited

/-- Rust `DirectionLocks` (Java lock map `Quadruplet`, only `LEFT`/`RIGHT` are used). -/
structure DirectionLocks where
  left : Bool := false
  right : Bool := false
  deriving Inhabited, BEq, Repr

/-- The fields of a `p5edges.splines.SplineSegment` read by the compactor. -/
structure SplineSegmentView where
  /-- `edges` (the first one represents the segment). -/
  edges : Array LEdgeId := #[]
  /-- `isStraight`. -/
  isStraight : Bool := false
  /-- `boundingBox`. -/
  boundingBox : ElkRectangle := {}
  /-- `initialSegment`. -/
  initialSegment : Bool := false
  /-- `lastSegment`. -/
  lastSegment : Bool := false
  /-- `sourceNode`. -/
  sourceNode : Option LNodeId := none
  /-- `targetNode`. -/
  targetNode : Option LNodeId := none
  deriving Inhabited

/-- Access to the spline routes of the graph (see the module doc). -/
structure SplineRouteAccess where
  /-- `edge.getProperty(InternalProperties.SPLINE_ROUTE_START)`: the segment handles of the
  edge's spline chain. -/
  routeStart : LEdgeId → LayeredM (Option (Array Nat))
  /-- Reads a spline segment. -/
  segment : Nat → LayeredM SplineSegmentView
  /-- Updates the bounding box of a spline segment. -/
  modifyBoundingBox : Nat → (ElkRectangle → ElkRectangle) → LayeredM Unit

namespace SplineRouteAccess

/-- No spline routes. -/
def unavailable : SplineRouteAccess :=
  { routeStart := fun _ => pure none, segment := fun _ => pure {}, modifyBoundingBox := fun _ _ => pure () }

instance : Inhabited SplineRouteAccess := ⟨unavailable⟩

end SplineRouteAccess

/-- Rust `CompactionContext` (Java `LGraphToCGraphTransformer` state). -/
structure CompactionContext where
  /-- `edgeRouting` of the graph (`ORTHOGONAL` or `SPLINES`). -/
  edgeRouting : EdgeRouting
  /-- The compaction graph (Rust `c_graph`); replaced by the compacted graph after `compact`. -/
  cGraph : CGraph
  /-- `nodes`: the nodes of all layers, in layer order. -/
  nodes : Array LNodeId
  /-- `node_to_cnode` (Java `nodesMap`). -/
  nodeToCNode : Std.HashMap LNodeId CNodeId := {}
  /-- `cnode_origin` by `CNodeId.idx`. -/
  cnodeOrigin : Array CNodeOrigin := #[]
  /-- `segments`: the merged vertical segments (index = `CNodeOrigin.segment` index). -/
  segments : Array VerticalSegment := #[]
  /-- `connection_locks` by `CNodeId.idx` (Java `lockMap`). -/
  connectionLocks : Array DirectionLocks := #[]
  /-- `comment_offsets` (in node order). -/
  commentOffsets : Array CommentOffset := #[]
  /-- `next_segment_id`. -/
  nextSegmentId : Nat := 0
  /-- Access to the spline routes. -/
  splines : SplineRouteAccess := SplineRouteAccess.unavailable
  deriving Inhabited

/-- The transformation monad: the context on top of the layered arena. -/
abbrev TransformM := StateT CompactionContext LayeredM

namespace CompactionContext

/-- Rust `CompactionContext::new(graph, edge_routing)` (Java `init`). -/
def new (graph : LGraphId) (edgeRouting : EdgeRouting) (splines : SplineRouteAccess := .unavailable) :
    LayeredM CompactionContext := do
  let mut hasEdges := false
  let mut nodes : Array LNodeId := #[]
  for layer in (← getGraph graph).layers do
    for node in (← getLayer layer).nodes do
      if !hasEdges then
        if !(← withArena (·.nodeConnectedEdges node)).isEmpty then
          hasEdges := true
      nodes := nodes.push node
  let mut directions : Array Direction := #[.left, .right]
  if !hasEdges then
    directions := directions ++ #[.up, .down]
  return { edgeRouting, cGraph := CGraph.new directions, nodes, splines }

/-- Moves the compaction graph out of the context (so that it is updated in place). -/
private def takeCGraph : TransformM CGraph :=
  modifyGet fun ctx => (ctx.cGraph, { ctx with cGraph := {} })

/-- Puts the compaction graph back. -/
private def putCGraph (g : CGraph) : TransformM Unit :=
  modify fun ctx => { ctx with cGraph := g }

/-- Rust `allocate_segment_id`. -/
def allocateSegmentId : TransformM Nat :=
  modifyGet fun ctx => (ctx.nextSegmentId, { ctx with nextSegmentId := ctx.nextSegmentId + 1 })

/-- Rust `new_vertical_segment(bend1, bend2, edge, bend_indices, potential_parent)`. -/
def newVerticalSegment (bend1 bend2 : KVector) (edge : LEdgeId) (bendIndices : Array Nat)
    (potentialParent : Option CNodeId) : TransformM VerticalSegment := do
  let segmentId ← allocateSegmentId
  return VerticalSegment.new segmentId bend1 bend2 edge bendIndices potentialParent

/-- Rust `capture_comment_offset_if_needed(node)`: a comment box with edges is not compacted but
remembered with its offset to the other end of its first connected edge. -/
def captureCommentOffsetIfNeeded (node : LNodeId) : TransformM Bool := do
  let isComment := ((← getNode node).props.get LayeredOptions.COMMENT_BOX).getD false
  let connected ← withArena (·.nodeConnectedEdges node)
  if !isComment || connected.isEmpty then return false
  let some edge := connected[0]? | return false
  let (sourceNode, targetNode) ← withArena fun a =>
    let ed := a.edge edge
    (ed.source.bind fun p => (a.port p).owner, ed.target.bind fun p => (a.port p).owner)
  let other : Option LNodeId := match sourceNode, targetNode with
    | some s, some t => if s == node then some t else if t == node then some s else some s
    | some s, none => some s
    | none, some t => some t
    | none, none => none
  let some other := other | return false
  let commentPos := (← getNode node).position
  let otherPos := (← getNode other).position
  let item : CommentOffset :=
    { comment := node, anchor := other, offset := ⟨commentPos.x - otherPos.x, commentPos.y - otherPos.y⟩ }
  modify fun ctx => { ctx with commentOffsets := ctx.commentOffsets.push item }
  return true

/-- Rust `transform_nodes` (Java `transformNodes`). -/
def transformNodes : TransformM Unit := do
  for node in (← get).nodes do
    if ← captureCommentOffsetIfNeeded node then continue
    let nd ← getNode node
    let margin := nd.margin
    let hitbox := ElkRectangle.ofValues (nd.position.x - margin.left) (nd.position.y - margin.top)
      (nd.size.x + margin.left + margin.right) (nd.size.y + margin.top + margin.bottom)
    let incomingCount := (← withArena (·.nodeIncomingEdges node)).size
    let outgoingCount := (← withArena (·.nodeOutgoingEdges node)).size
    let g ← takeCGraph
    let (g, cNode) := CNode.create g hitbox
    let (g, _) ← CGroup.createIO g #[cNode]
    putCGraph g
    let mut locks : DirectionLocks := {}
    if nd.type != .externalPort then
      let difference : Int := (incomingCount : Int) - (outgoingCount : Int)
      if difference < 0 then
        locks := { locks with left := true }
      else if difference > 0 then
        locks := { locks with right := true }
    modify fun ctx => { ctx with
      nodeToCNode := ctx.nodeToCNode.insert node cNode
      cnodeOrigin := ctx.cnodeOrigin.push (.node node)
      connectionLocks := ctx.connectionLocks.push locks }

/-- The hitbox of the `CNode` of the target port's node (Rust `target_hitbox` lookup). -/
private def targetHitbox (targetPort : Option LPortId) : TransformM (Option ElkRectangle) := do
  let some port := targetPort | return none
  let some targetNode := (← getPort port).owner | return none
  let some targetCNode := (← get).nodeToCNode.get? targetNode | return none
  return some ((← get).cGraph.cNode targetCNode).hitbox

/-- Spacing flags of a segment relative to a node hitbox `box` at height `y` (above: ignore
down; below: ignore up; inside: both). -/
private def ignoreFlags (s : VerticalSegment) (y : Float) (box : ElkRectangle) : VerticalSegment :=
  if y < box.y then { s with ignoreSpacingDown := true }
  else if y > box.y + box.height then { s with ignoreSpacingUp := true }
  else { s with ignoreSpacingUp := true, ignoreSpacingDown := true }

/-- The segments of one outgoing edge (body of the first inner loop of Rust
`collect_vertical_segments_orthogonal`). -/
private def outgoingEdgeSegments (cNode : CNodeId) (nodeHitbox : ElkRectangle) (edge : LEdgeId)
    (segments : Array VerticalSegment) : TransformM (Array VerticalSegment) := do
  let ed ← getEdge edge
  let bendPoints := ed.bendPoints
  let some firstBend := bendPoints[0]? | return segments
  let sourcePort := ed.source
  let sourceSide ← match sourcePort with
    | some p => pure (← getPort p).side
    | none => pure PortSide.undefined
  let mut segments := segments
  match sourceSide with
  | .north =>
    let s ← newVerticalSegment firstBend ⟨firstBend.x, nodeHitbox.y⟩ edge #[0] (some cNode)
    segments := segments.push { s with ignoreSpacingDown := true, port := sourcePort }
  | .south =>
    let s ← newVerticalSegment firstBend ⟨firstBend.x, nodeHitbox.y + nodeHitbox.height⟩ edge #[0] (some cNode)
    segments := segments.push { s with ignoreSpacingUp := true, port := sourcePort }
  | _ => pure ()
  let mut bend1 := firstBend
  let mut firstRegularSegment := true
  let mut lastRegularSegmentIndex : Option Nat := none
  for h : i in [1:bendPoints.size] do
    let bend2 := bendPoints[i]
    if !CompareFuzzy.eq bend1.y bend2.y then
      let mut s ← newVerticalSegment bend1 bend2 edge #[i - 1, i] none
      if firstRegularSegment then
        firstRegularSegment := false
        s := ignoreFlags s bend2.y nodeHitbox
      segments := segments.push s
      lastRegularSegmentIndex := some (segments.size - 1)
    bend1 := bend2
  if let some index := lastRegularSegmentIndex then
    if let some box ← targetHitbox ed.target then
      let y := bend1.y
      segments := segments.modifyIn index fun s => ignoreFlags s y box
  return segments

/-- The north/south target segment of one incoming edge (body of the second inner loop of Rust
`collect_vertical_segments_orthogonal`). -/
private def incomingEdgeSegments (cNode : CNodeId) (nodeHitbox : ElkRectangle) (edge : LEdgeId)
    (segments : Array VerticalSegment) : TransformM (Array VerticalSegment) := do
  let ed ← getEdge edge
  let bendPoints := ed.bendPoints
  if bendPoints.isEmpty then return segments
  let targetPort := ed.target
  let targetSide ← match targetPort with
    | some p => pure (← getPort p).side
    | none => pure PortSide.undefined
  let lastIdx := bendPoints.size - 1
  let bend := bendPoints[lastIdx]!
  match targetSide with
  | .north =>
    let s ← newVerticalSegment bend ⟨bend.x, nodeHitbox.y⟩ edge #[lastIdx] (some cNode)
    return segments.push { s with ignoreSpacingDown := true, port := targetPort }
  | .south =>
    let s ← newVerticalSegment bend ⟨bend.x, nodeHitbox.y + nodeHitbox.height⟩ edge #[lastIdx] (some cNode)
    return segments.push { s with ignoreSpacingUp := true, port := targetPort }
  | _ => return segments

/-- Rust `collect_vertical_segments_orthogonal` (Java `collectVerticalSegmentsOrthogonal`). -/
def collectVerticalSegmentsOrthogonal : TransformM (Array VerticalSegment) := do
  let mut segments : Array VerticalSegment := #[]
  for node in (← get).nodes do
    let some cNode := (← get).nodeToCNode.get? node | continue
    let outgoing ← withArena (·.nodeOutgoingEdges node)
    let incoming ← withArena (·.nodeIncomingEdges node)
    let nodeHitbox := ((← get).cGraph.cNode cNode).hitbox
    for edge in outgoing do
      segments ← outgoingEdgeSegments cNode nodeHitbox edge segments
    for edge in incoming do
      segments ← incomingEdgeSegments cNode nodeHitbox edge segments
  return segments

/-- Rust `collect_vertical_segments_splines` (Java `collectVerticalSegmentsSplines`): one segment
per non-straight spline segment (with at least one edge) of the outgoing edges of all nodes;
consecutive ones of a chain get a predefined constraint. -/
def collectVerticalSegmentsSplines : TransformM (Array VerticalSegment) := do
  let splines := (← get).splines
  let mut segments : Array VerticalSegment := #[]
  let mut segmentIdToIndex : Std.HashMap Nat Nat := {}
  for node in (← get).nodes do
    let outgoing ← withArena (·.nodeOutgoingEdges node)
    for edge in outgoing do
      let some chain ← splines.routeStart edge | continue
      let mut lastNonStraightSegmentId : Option Nat := none
      for splineSegment in chain do
        let view ← splines.segment splineSegment
        let some representative := view.edges[0]? | continue
        if view.isStraight then continue
        let segmentId ← allocateSegmentId
        let segment := VerticalSegment.newSpline segmentId view.boundingBox representative splineSegment
        if let some lastId := lastNonStraightSegmentId then
          if let some index := segmentIdToIndex.get? lastId then
            segments := segments.modifyIn index fun s =>
              { s with constraintTargetIds := pushUnique s.constraintTargetIds segmentId }
        segmentIdToIndex := segmentIdToIndex.insert segmentId segments.size
        lastNonStraightSegmentId := some segmentId
        segments := segments.push segment
  return segments

/-- Rust `merge_segments` (Java `mergeVerticalSegments`): joins consecutive intersecting segments
of the sorted list. -/
def mergeSegments (segments : Array VerticalSegment) : Array VerticalSegment := Id.run do
  let some first := segments[0]? | return #[]
  let mut merged : Array VerticalSegment := #[]
  let mut survivor := first
  for h : i in [1:segments.size] do
    let next := segments[i]
    if survivor.intersects next then
      survivor := survivor.joinWith next
    else
      merged := merged.push survivor
      survivor := next
  return merged.push survivor

/-- Rust `add_predefined_constraints(segment_id_to_cnode)` (Java `transformEdges`): the
constraints between consecutive non-straight spline segments, deduplicated, without self pairs. -/
def addPredefinedConstraints (segmentIdToCNode : Std.HashMap Nat CNodeId) : TransformM Unit := do
  let mut uniquePairs : Std.HashSet (CNodeId × CNodeId) := {}
  let mut constraints : Array (CNodeId × CNodeId) := #[]
  for segment in (← get).segments do
    let some sourceCNode := segmentIdToCNode.get? segment.segmentId | continue
    for targetSegmentId in segment.constraintTargetIds do
      let some targetCNode := segmentIdToCNode.get? targetSegmentId | continue
      if sourceCNode == targetCNode then continue
      if !uniquePairs.contains (sourceCNode, targetCNode) then
        uniquePairs := uniquePairs.insert (sourceCNode, targetCNode)
        constraints := constraints.push (sourceCNode, targetCNode)
  if !constraints.isEmpty then
    let g ← takeCGraph
    putCGraph { g with predefinedHorizontalConstraints := g.predefinedHorizontalConstraints ++ constraints }

/-- Rust connection locks of a segment: by the number of distinct source vs. target ports. -/
private def segmentLocks (segment : VerticalSegment) : LayeredM DirectionLocks := do
  let mut incomingPorts : Std.HashSet LPortId := {}
  let mut outgoingPorts : Std.HashSet LPortId := {}
  for edge in segment.representedEdges do
    let ed ← getEdge edge
    if let some source := ed.source then incomingPorts := incomingPorts.insert source
    if let some target := ed.target then outgoingPorts := outgoingPorts.insert target
  let difference : Int := (incomingPorts.size : Int) - (outgoingPorts.size : Int)
  if difference < 0 then return { left := true }
  else if difference > 0 then return { right := true }
  else return {}

/-- Adds a `CNode` to the group of a parent `CNode` (Rust `CGroup::add_c_node`, panics if the
node already has a group). -/
private def addToParentGroup (g : CGraph) (parent : Option CNodeId) (cNode : CNodeId) : IO CGraph := do
  let some parent := parent | return g
  let some group := g.groupOf parent | return g
  match CGroup.addCNode g group cNode with
  | .ok g => return g
  | .error e => throw (IO.userError e)

/-- Rust `register_segments(segments)` (Java `mergeVerticalSegments` + `verticalSegmentToCNode`):
sorts, merges and registers the segments as `CNode`s, then adds the predefined constraints. -/
def registerSegments (segments : Array VerticalSegment) : TransformM Unit := do
  if segments.isEmpty then return
  let sorted ← match javaSortBy segments VerticalSegment.compareTo with
    | .ok sorted => pure sorted
    | .error _ => throw (IO.userError JavaSort.contractViolationError)
  let merged := mergeSegments sorted
  modify fun ctx => { ctx with segments := merged }
  let mut segmentIdToCNode : Std.HashMap Nat CNodeId := {}
  for h : segmentIndex in [0:merged.size] do
    let segment := merged[segmentIndex]
    let g ← takeCGraph
    let (g, cNode) := CNode.create g segment.hitbox
    let g ← addToParentGroup g segment.potentialGroupParents[0]? cNode
    putCGraph g
    for segmentId in segment.joinedSegmentIds do
      segmentIdToCNode := segmentIdToCNode.insert segmentId cNode
    let locks ← segmentLocks segment
    modify fun ctx => { ctx with
      cnodeOrigin := ctx.cnodeOrigin.push (.segment segmentIndex)
      connectionLocks := ctx.connectionLocks.push locks }
  addPredefinedConstraints segmentIdToCNode

/-- Rust `transform_edges_orthogonal`. -/
def transformEdgesOrthogonal : TransformM Unit := do
  registerSegments (← collectVerticalSegmentsOrthogonal)

/-- Rust `transform_edges_splines`. -/
def transformEdgesSplines : TransformM Unit := do
  registerSegments (← collectVerticalSegmentsSplines)

/-- Java `transform(graph)`: `new`, `transformNodes` and the edge transformation of the routing
style (other styles transform no edges). -/
def transform (graph : LGraphId) (edgeRouting : EdgeRouting) (splines : SplineRouteAccess := .unavailable) :
    LayeredM CompactionContext := do
  let ctx ← CompactionContext.new graph edgeRouting splines
  let ((), ctx) ← (do
      transformNodes
      match edgeRouting with
      | .orthogonal => transformEdgesOrthogonal
      | .splines => transformEdgesSplines
      | _ => pure () : TransformM Unit).run ctx
  return ctx

/-! ### Applying the layout (Rust `apply_layout` and helpers) -/

/-- The x movement of a `CNode` during compaction (`hitbox.x - hitboxPreCompaction.x`). -/
def deltaX (ctx : CompactionContext) (c : CNodeId) : Option Float :=
  let n := ctx.cGraph.cNode c
  n.hitboxPreCompaction.map fun pre => n.hitbox.x - pre.x

/-- Rust apply step 1: node positions (`x = hitbox.x + margin.left`), in `CNode` order. -/
def applyNodePositions (ctx : CompactionContext) : LayeredM Unit := do
  for h : i in [0:ctx.cGraph.cNodes.size] do
    let .node node := ctx.cnodeOrigin[i]?.getD (.segment 0) | continue
    let x := ctx.cGraph.cNodes[i].hitbox.x
    modifyNode node fun nd => { nd with position := { nd.position with x := x + nd.margin.left } }

/-- Rust `apply_comment_positions`: comment box = anchor position + stored offset. -/
def applyCommentPositions (ctx : CompactionContext) : LayeredM Unit := do
  for item in ctx.commentOffsets do
    let anchor := (← getNode item.anchor).position
    modifyNode item.comment fun nd =>
      { nd with position := ⟨anchor.x + item.offset.x, anchor.y + item.offset.y⟩ }

/-- Rust `apply_segment_positions`: moves the affected bend points and spline segments of every
moved segment by its x movement (each bend point / spline segment once per segment). -/
def applySegmentPositions (ctx : CompactionContext) : LayeredM Unit := do
  for i in [0:ctx.cGraph.cNodes.size] do
    let .segment segmentIndex := ctx.cnodeOrigin[i]?.getD (.node ⟨0⟩) | continue
    let some delta := ctx.deltaX ⟨i⟩ | continue
    if CompareFuzzy.eq delta fl0p0 then continue
    let some segment := ctx.segments[segmentIndex]? | continue
    let mut adjusted : Std.HashSet (LEdgeId × Nat) := {}
    for (edge, bendIndex) in segment.affectedBends do
      if adjusted.contains (edge, bendIndex) then continue
      adjusted := adjusted.insert (edge, bendIndex)
      modifyEdge edge fun ed =>
        if bendIndex < ed.bendPoints.size then
          { ed with bendPoints := ed.bendPoints.modifyIn bendIndex fun p => { p with x := p.x + delta } }
        else ed
    let mut adjustedSplineSegments : Std.HashSet Nat := {}
    for splineSegment in segment.affectedSplineSegments do
      if adjustedSplineSegments.contains splineSegment then continue
      adjustedSplineSegments := adjustedSplineSegments.insert splineSegment
      ctx.splines.modifyBoundingBox splineSegment fun bb => { bb with x := bb.x + delta }

/-- Rust `apply_spline_self_loop_offsets`: the bend points of self loops of moved nodes move along. -/
def applySplineSelfLoopOffsets (ctx : CompactionContext) : LayeredM Unit := do
  for i in [0:ctx.cGraph.cNodes.size] do
    let .node node := ctx.cnodeOrigin[i]?.getD (.segment 0) | continue
    let some delta := ctx.deltaX ⟨i⟩ | continue
    if CompareFuzzy.eq delta fl0p0 then continue
    for edge in (← withArena (·.nodeOutgoingEdges node)) do
      if !(← withArena (·.edgeIsSelfLoop edge)) then continue
      modifyEdge edge fun ed => { ed with bendPoints := ed.bendPoints.offsetValues delta fl0p0 }

/-- Rust `first_non_straight_segment(spline, index)`: the first non-straight segment at or after
`index`, or the last segment; `(index, handle)`. -/
def firstNonStraightSegment (ctx : CompactionContext) (spline : Array Nat) (index : Nat) :
    LayeredM (Option (Nat × Nat)) := do
  if index >= spline.size then return none
  for h : i in [index:spline.size] do
    let segment := spline[i]
    let view ← ctx.splines.segment segment
    if i == spline.size - 1 || !view.isStraight then
      return some (i, segment)
  return none

/-- Rust `adjust_control_point_between_segments(left, right, left_idx, right_idx, spline)` (Java
`adjustControlPointBetweenSegments`): distributes the straight segments between `left` and
`right` equidistantly. -/
def adjustControlPointBetweenSegments (ctx : CompactionContext) (left right : Nat) (leftIdx rightIdx : Nat)
    (spline : Array Nat) : LayeredM Unit := do
  let l ← ctx.splines.segment left
  let (startX, idx1) : Float × Nat :=
    if l.initialSegment && l.isStraight then
      let sourceX := match l.sourceNode.bind ctx.nodeToCNode.get? with
        | some c =>
          let hitbox := (ctx.cGraph.cNode c).hitbox
          hitbox.x + hitbox.width
        | none => l.boundingBox.x + l.boundingBox.width
      (sourceX, leftIdx - 1)
    else (l.boundingBox.x + l.boundingBox.width, leftIdx)
  let r ← ctx.splines.segment right
  let (endX, idx2) : Float × Nat :=
    if r.lastSegment && r.isStraight then
      let targetX := match r.targetNode.bind ctx.nodeToCNode.get? with
        | some c => (ctx.cGraph.cNode c).hitbox.x
        | none => r.boundingBox.x
      (targetX, rightIdx + 1)
    else (r.boundingBox.x, rightIdx)
  let strip := endX - startX
  let chunks := (max 2 (idx2 - idx1)).toFloat
  let chunk := strip / chunks
  let mut pos := startX + chunk
  for idx in [idx1:idx2] do
    if let some segment := spline[idx]? then
      let x := pos
      ctx.splines.modifyBoundingBox segment fun bb => { bb with x := x - bb.width / fl2p0 }
      pos := pos + chunk

/-- Rust `adjust_spline_control_points(spline)` (Java `adjustSplineControlPoints`). -/
def adjustSplineControlPoints (ctx : CompactionContext) (spline : Array Nat) : LayeredM Unit := do
  let some first := spline[0]? | return
  let mut lastSegment := first
  if spline.size == 1 then
    ctx.adjustControlPointBetweenSegments lastSegment lastSegment 1 0 spline
    return
  let mut index := 1
  while index < spline.size do
    let view ← ctx.splines.segment lastSegment
    if view.initialSegment || !view.isStraight then
      if let some (nextIndex, nextSegment) ← ctx.firstNonStraightSegment spline index then
        ctx.adjustControlPointBetweenSegments lastSegment nextSegment index nextIndex spline
        index := nextIndex + 1
        lastSegment := nextSegment
        continue
    index := index + 1

/-- Rust `adjust_straight_spline_segments`: the spline chains of the outgoing edges of all nodes. -/
def adjustStraightSplineSegments (ctx : CompactionContext) : LayeredM Unit := do
  for node in ctx.nodes do
    for edge in (← withArena (·.nodeOutgoingEdges node)) do
      if let some spline ← ctx.splines.routeStart edge then
        ctx.adjustSplineControlPoints spline

/-- Rust `apply_self_loop_label_offsets`: the labels of self loops of moved nodes move along. -/
def applySelfLoopLabelOffsets (ctx : CompactionContext) : LayeredM Unit := do
  for i in [0:ctx.cGraph.cNodes.size] do
    let .node node := ctx.cnodeOrigin[i]?.getD (.segment 0) | continue
    let some delta := ctx.deltaX ⟨i⟩ | continue
    if CompareFuzzy.eq delta fl0p0 then continue
    for edge in (← withArena (·.nodeOutgoingEdges node)) do
      if !(← withArena (·.edgeIsSelfLoop edge)) then continue
      for label in (← getEdge edge).labels do
        modifyLabel label fun lb => { lb with position := { lb.position with x := lb.position.x + delta } }

/-- Rust `apply_external_port_positions(top_left, bottom_right)`: external port dummies are put
back to the border of the compacted drawing. -/
def applyExternalPortPositions (ctx : CompactionContext) (topLeft bottomRight : KVector) : LayeredM Unit := do
  for origin in ctx.cnodeOrigin do
    let .node node := origin | continue
    let nd ← getNode node
    if nd.type != .externalPort then continue
    match nd.internal.extPortSide with
    | .west => modifyNode node fun n => { n with position := { n.position with x := topLeft.x } }
    | .east => modifyNode node fun n =>
        { n with position := { n.position with x := bottomRight.x - (n.size.x + n.margin.right) } }
    | .north => modifyNode node fun n => { n with position := { n.position with y := topLeft.y } }
    | .south => modifyNode node fun n =>
        { n with position := { n.position with y := bottomRight.y - (n.size.y + n.margin.bottom) } }
    | .undefined => pure ()

/-- Rust `update_graph_bounds(graph)`: graph offset and size from the bounding box of all
hitboxes, then the external port dummies. -/
def updateGraphBounds (ctx : CompactionContext) (graph : LGraphId) : LayeredM Unit := do
  if ctx.cGraph.cNodes.isEmpty then return
  let mut topLeft : KVector := ⟨Float.posInf, Float.posInf⟩
  let mut bottomRight : KVector := ⟨Float.negInf, Float.negInf⟩
  for c in ctx.cGraph.cNodes do
    let hitbox := c.hitbox
    topLeft := ⟨fmin topLeft.x hitbox.x, fmin topLeft.y hitbox.y⟩
    bottomRight := ⟨fmax bottomRight.x (hitbox.x + hitbox.width), fmax bottomRight.y (hitbox.y + hitbox.height)⟩
  let tl := topLeft
  let br := bottomRight
  modifyGraph graph fun g =>
    { g with offset := ⟨0.0 + -tl.x, 0.0 + -tl.y⟩, size := ⟨br.x - tl.x, br.y - tl.y⟩ }
  ctx.applyExternalPortPositions topLeft bottomRight

/-- Rust `apply_layout(graph)` (Java `applyLayout`). -/
def applyLayout (ctx : CompactionContext) (graph : LGraphId) : LayeredM Unit := do
  ctx.applyNodePositions
  ctx.applyCommentPositions
  ctx.applySegmentPositions
  if ctx.edgeRouting == .splines then
    ctx.applySplineSelfLoopOffsets
    ctx.adjustStraightSplineSegments
  ctx.applySelfLoopLabelOffsets
  ctx.updateGraphBounds graph

end CompactionContext

end Elk.Alg.Layered.Intermediate.Compaction
