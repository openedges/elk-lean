import Elk.Alg.Common.Compaction.OneD.ISpacingsHandler
import Elk.Alg.Layered.Intermediate.Compaction.CompactionMetadata
/-!
# `HorizontalGraphCompactor.specialSpacingsHandler`

The `ISpacingsHandler` of the horizontal graph compactor (Java anonymous inner class
`HorizontalGraphCompactor.specialSpacingsHandler`, elk-rs `SpecialSpacingsHandler` of
`intermediate/horizontal_graph_compactor.rs`). It copes with the special requirements of
`LGraph`s: vertical segments of the same edge get the horizontal spacing `0` (they are joined)
and the vertical spacing `1` (they overlap and get a constraint), external port dummies get `0`,
everything else is looked up in the graph's `Spacings` by node type (segments count as
`LONG_EDGE`).

The Rust pointer-keyed maps `node_origins` and `segment_edge_keys` are arrays indexed by
`CNodeId.idx`; `node_origins` is reduced to the node types (snapshot taken when the handler is
built, see `CompactionMetadata`).

Deviation: Rust panics with `UnspecifiedSpacingException` when the `Spacings` table has no entry
for a pair of node types. The alg.common `SpacingsHandler` closures are pure and cannot throw,
so such a pair yields `0.0` here. The case is unreachable in the layered pipeline: when this
processor runs, the remaining node types are `NORMAL`, `LABEL` and `EXTERNAL_PORT` (short-cut to
`0`) plus segments (`LONG_EDGE`), and every pair of them has an entry in both tables.
-/
namespace Elk.Alg.Layered.Intermediate.Compaction

open Elk.Alg.Common.Compaction.OneD Elk.Alg.Layered.Graph Elk.Alg.Layered.Options LayeredM

/-- Rust `SpecialSpacingsHandler`. -/
structure SpecialSpacingsHandler where
  /-- Type of the represented `LNode` per `CNode` (Rust `node_origins`). -/
  nodeTypes : Array (Option NodeType) := #[]
  /-- Rust `segment_edge_keys`: represented edges of segment `CNode`s. -/
  segmentEdgeKeys : Array (Option (Array LEdgeId)) := #[]
  /-- The graph's `InternalProperties.SPACINGS`. -/
  spacings : Option Spacings := none
  deriving Inhabited

namespace SpecialSpacingsHandler

/-- Rust `SpecialSpacingsHandler::new(origins, segments, spacings)`. -/
def new (origins : Array CNodeOrigin) (segments : Array VerticalSegment) (spacings : Option Spacings) :
    LayeredM SpecialSpacingsHandler := do
  let mut nodeTypes : Array (Option NodeType) := Array.replicate origins.size none
  let mut segmentEdgeKeys : Array (Option (Array LEdgeId)) := Array.replicate origins.size none
  for h : i in [0:origins.size] do
    match origins[i] with
    | .node node => nodeTypes := nodeTypes.set! i (some (← getNode node).type)
    | .segment index =>
      if let some segment := segments[index]? then
        segmentEdgeKeys := segmentEdgeKeys.set! i (some segment.representedEdgeKeys)
  return { nodeTypes, segmentEdgeKeys, spacings }

/-- Rust `node_type_or_long_edge(c_node)`: the node's type, `LONG_EDGE` for segments. -/
def nodeTypeOrLongEdge (h : SpecialSpacingsHandler) (c : CNodeId) : NodeType :=
  (h.nodeTypes[c.idx]?).join.getD .longEdge

/-- Rust `is_external_port_node(c_node)`. -/
def isExternalPortNode (h : SpecialSpacingsHandler) (c : CNodeId) : Bool :=
  match (h.nodeTypes[c.idx]?).join with
  | some t => t == .externalPort
  | none => false

/-- Rust `segments_share_edge(c_node1, c_node2)` (Java `isVerticalSegmentsOfSameEdge`). -/
def segmentsShareEdge (h : SpecialSpacingsHandler) (c1 c2 : CNodeId) : Bool :=
  match (h.segmentEdgeKeys[c1.idx]?).join, (h.segmentEdgeKeys[c2.idx]?).join with
  | some e1, some e2 => e1.any e2.contains
  | _, _ => false

/-- `getHorizontalSpacing(cNode1, cNode2)`. -/
def horizontalSpacing (h : SpecialSpacingsHandler) (c1 c2 : CNodeId) : Float :=
  if h.segmentsShareEdge c1 c2 then 0.0
  else if h.isExternalPortNode c1 || h.isExternalPortNode c2 then 0.0
  else match h.spacings with
    | some s => (s.getHorizontalSpacingForTypes? (h.nodeTypeOrLongEdge c1) (h.nodeTypeOrLongEdge c2)).getD 0.0
    | none => 0.0

/-- `getVerticalSpacing(cNode1, cNode2)` (only used by the quadratic constraint calculation).
Like Rust, external port dummies get `0` (the Java method has no such case). -/
def verticalSpacing (h : SpecialSpacingsHandler) (c1 c2 : CNodeId) : Float :=
  if h.segmentsShareEdge c1 c2 then 1.0
  else if h.isExternalPortNode c1 || h.isExternalPortNode c2 then 0.0
  else match h.spacings with
    | some s => (s.getVerticalSpacingForTypes? (h.nodeTypeOrLongEdge c1) (h.nodeTypeOrLongEdge c2)).getD 0.0
    | none => 0.0

/-- The handler as an alg.common `SpacingsHandler` (Rust `Box<dyn ISpacingsHandler>`). -/
def toSpacingsHandler (h : SpecialSpacingsHandler) : SpacingsHandler :=
  ⟨fun _ c1 c2 => h.horizontalSpacing c1 c2, fun _ c1 c2 => h.verticalSpacing c1 c2⟩

end SpecialSpacingsHandler

end Elk.Alg.Layered.Intermediate.Compaction
