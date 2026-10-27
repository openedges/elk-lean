import Elk.Alg.Layered.Graph
import Elk.Alg.Layered.Intermediate.Compaction.VerticalSegment
/-!
# `CNodeOrigin` and `CompactionMetadata` (elk-rs only)

Java stores the represented object in `CNode.origin` (an `LNode` or a `VerticalSegment`) and
tests it with `instanceof` (`HorizontalGraphCompactor.getLNodeOrNull` /
`getVerticalSegmentOrNull`). elk-rs keeps the origins in pointer-keyed side tables of the
`CompactionContext` (`cnode_origin: HashMap<usize, CNodeOrigin>`) and hands the compaction
strategies a `CompactionMetadata` snapshot of them. The Lean port follows Rust: the `CGraph` of
`alg.common` has no origin payload, and the side tables are arrays indexed by `CNodeId.idx`
(every `CNode` of the compaction graph has an origin, so the arrays are dense).

The metadata also snapshots the node types (Rust `is_external_port_node` locks the `LNode` at
call time); node types do not change while the compactor runs, so the snapshot is equivalent.
-/
namespace Elk.Alg.Layered.Intermediate.Compaction

open Elk.Graph Elk.Core.Math Elk.Core.Options Elk.Alg.Common.Compaction.OneD
open Elk.Alg.Layered.Graph Elk.Alg.Layered.Options LayeredM

/-- Rust `CNodeOrigin`: the element a `CNode` represents. -/
inductive CNodeOrigin where
  /-- An `LNode` (Java `cNode.origin instanceof LNode`). -/
  | node (n : LNodeId)
  /-- The vertical segment with this index in `CompactionContext.segments` (Java
  `cNode.origin instanceof VerticalSegment`). -/
  | segment (index : Nat)
  deriving BEq, Repr, Inhabited

/-- Rust `SegmentCompactionInfo`: the parts of a `VerticalSegment` the strategies need. -/
structure SegmentCompactionInfo where
  /-- `represented_edges`. -/
  representedEdges : Array LEdgeId
  /-- `represented_edge_keys` (set of `representedEdges`). -/
  representedEdgeKeys : Array LEdgeId
  /-- `ignore_spacing_up`. -/
  ignoreSpacingUp : Bool
  /-- `ignore_spacing_down`. -/
  ignoreSpacingDown : Bool
  /-- `port` (Java `aPort`). -/
  port : Option LPortId
  deriving Inhabited

/-- Rust `CompactionMetadata`, indexed by `CNodeId.idx`. -/
structure CompactionMetadata where
  /-- `node_origins`: the represented `LNode` of node `CNode`s. -/
  nodeOrigins : Array (Option LNodeId) := #[]
  /-- Type of the represented `LNode` (snapshot, see the module doc). -/
  nodeTypes : Array (Option NodeType) := #[]
  /-- `segment_infos`: the represented segment of segment `CNode`s. -/
  segmentInfos : Array (Option SegmentCompactionInfo) := #[]
  /-- `node_spacing_node_node`: `Spacings.getIndividualOrDefault(graph, node, SPACING_NODE_NODE)`. -/
  nodeSpacingNodeNode : Array (Option Float) := #[]
  /-- `node_spacing_edge_edge`: `Spacings.getIndividualOrDefault(graph, node, SPACING_EDGE_EDGE)`. -/
  nodeSpacingEdgeEdge : Array (Option Float) := #[]
  deriving Inhabited

namespace CompactionMetadata

/-- Rust `Spacings::get_individual_or_default_with_graph` (panics with
`UnspecifiedSpacingException` when neither node, graph nor option provide a value). -/
def individualOrDefault (graphProps nodeProps : PropertyMap) (p : Property Float) : IO Float :=
  match Spacings.getIndividualOrDefaultWithGraph? graphProps nodeProps p with
  | some v => pure v
  | none => throw (unspecifiedSpacing)

/-- Rust `CompactionMetadata::from_context(origins, segments, graph)`. -/
def fromContext (origins : Array CNodeOrigin) (segments : Array VerticalSegment) (graph : LGraphId) :
    LayeredM CompactionMetadata := do
  let graphProps := (← getGraph graph).props
  let n := origins.size
  let mut md : CompactionMetadata :=
    { nodeOrigins := Array.replicate n none, nodeTypes := Array.replicate n none
      segmentInfos := Array.replicate n none, nodeSpacingNodeNode := Array.replicate n none
      nodeSpacingEdgeEdge := Array.replicate n none }
  for h : i in [0:n] do
    match origins[i] with
    | .node node =>
      let nd ← getNode node
      let nodeNode ← individualOrDefault graphProps nd.props LayeredOptions.SPACING_NODE_NODE
      let edgeEdge ← individualOrDefault graphProps nd.props LayeredOptions.SPACING_EDGE_EDGE
      md := { md with
        nodeOrigins := md.nodeOrigins.set! i (some node)
        nodeTypes := md.nodeTypes.set! i (some nd.type)
        nodeSpacingNodeNode := md.nodeSpacingNodeNode.set! i (some nodeNode)
        nodeSpacingEdgeEdge := md.nodeSpacingEdgeEdge.set! i (some edgeEdge) }
    | .segment index =>
      if let some segment := segments[index]? then
        let info : SegmentCompactionInfo :=
          { representedEdges := segment.representedEdges
            representedEdgeKeys := segment.representedEdgeKeys
            ignoreSpacingUp := segment.ignoreSpacingUp
            ignoreSpacingDown := segment.ignoreSpacingDown
            port := segment.port }
        md := { md with segmentInfos := md.segmentInfos.set! i (some info) }
  return md

/-- Rust `node_origin(c_node)` (Java `HorizontalGraphCompactor.getLNodeOrNull`). -/
@[inline] def nodeOrigin (md : CompactionMetadata) (c : CNodeId) : Option LNodeId :=
  (md.nodeOrigins[c.idx]?).join

/-- Rust `segment_info(c_node)` (Java `HorizontalGraphCompactor.getVerticalSegmentOrNull`). -/
@[inline] def segmentInfo (md : CompactionMetadata) (c : CNodeId) : Option SegmentCompactionInfo :=
  (md.segmentInfos[c.idx]?).join

/-- Rust `is_segment(c_node)`. -/
@[inline] def isSegment (md : CompactionMetadata) (c : CNodeId) : Bool := (md.segmentInfo c).isSome

/-- Rust `is_external_port_node(c_node)`: represents an `EXTERNAL_PORT` dummy. -/
def isExternalPortNode (md : CompactionMetadata) (c : CNodeId) : Bool :=
  match (md.nodeTypes[c.idx]?).join with
  | some t => t == .externalPort
  | none => false

/-- Rust `node_node_spacing(c_node)`. -/
@[inline] def nodeNodeSpacing (md : CompactionMetadata) (c : CNodeId) : Option Float :=
  (md.nodeSpacingNodeNode[c.idx]?).join

/-- Rust `node_edge_spacing(c_node)` (the node's `SPACING_EDGE_EDGE`). -/
@[inline] def nodeEdgeSpacing (md : CompactionMetadata) (c : CNodeId) : Option Float :=
  (md.nodeSpacingEdgeEdge[c.idx]?).join

/-- Rust `segment_port(c_node)` (Java `VerticalSegment.aPort`). -/
@[inline] def segmentPort (md : CompactionMetadata) (c : CNodeId) : Option LPortId :=
  (md.segmentInfo c).bind (·.port)

/-- Rust `segments_share_edge(c_node1, c_node2)` (Java
`HorizontalGraphCompactor.isVerticalSegmentsOfSameEdge`): both are segments and represent a
common edge. -/
def segmentsShareEdge (md : CompactionMetadata) (c1 c2 : CNodeId) : Bool :=
  match md.segmentInfo c1, md.segmentInfo c2 with
  | some s1, some s2 => s1.representedEdgeKeys.any s2.representedEdgeKeys.contains
  | _, _ => false

end CompactionMetadata

end Elk.Alg.Layered.Intermediate.Compaction
