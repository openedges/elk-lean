import Elk.Alg.Layered.Graph
import Elk.Alg.Layered.Options
import Elk.Core.Util.Java
/-!
# Shared helpers of the Brandes & Köpf node placer (elk-rs `p4nodes/bk/util.rs`)

elk-rs keeps these helpers in `util.rs` (Java: the static `BKNodePlacer.getEdge` and the
fields `layeredGraph`/`spacings` of `BKAlignedLayout`). The Rust code reads node sizes,
margins and port positions through an `ArenaSync` CSR copy of the graph; the Lean port reads
them from a snapshot of the `LGraphArena` taken after `NeighborhoodInformation.buildFor` has
assigned the node ids (nothing the placer reads changes before the final positions are
written back, see `PORTING.md` §15.1).

**Local node ids.** All per-node arrays of the placer are indexed by the node's `id` field as
assigned by `NeighborhoodInformation.buildFor` (Rust `node_id`: `graph_element().id as usize`):
the nodes of `graph.layers` in layer order, then in-layer order (`0 … nodeCount-1`).
`nodesById` is the inverse map (Rust `build_nodes_by_id`). The arena ids of elk-rs
(`node_element_id`) equal these ids because the `ArenaSync` is built after the ids are assigned.

**Edge lists.** The Rust BK code reads *all* edge lists from the live `LGraph`
(`LNode::incoming_edges/outgoing_edges/connected_edges`: ports in order, each port's
`incoming_edges`/`outgoing_edges` in list order), never `ArenaSync::port_incoming_edges`; only
node sizes/margins, port positions/anchors/owners and element ids come from the arena. The Lean
port therefore uses `LPort.incomingEdges`/`outgoingEdges` order (`nodeIncomingEdges`,
`nodeOutgoingEdges`, `nodeConnectedEdges`).

**Layer ids.** `NeighborhoodInformation.buildFor` sets `Layer.id` to the layer index (like
Java/Rust); `incidentToInnerSegment` reads `Layer.id` afterwards.
-/
namespace Elk.Alg.Layered.P4Nodes.BK

open Elk.Graph Elk.Core.Math Elk.Core.Util Elk.Alg.Layered.Graph Elk.Alg.Layered.Options

/-- Read-only data shared by all layouts of one placement run (Rust: the `layers`,
`nodes_by_id`, `spacings` and `sync: Arc<ArenaSync>` fields of `BKAlignedLayout`). -/
structure BKContext where
  /-- Snapshot of the layered arena (Rust `ArenaSync`); never written during the placement. -/
  arena : LGraphArena
  /-- `graph.layers()` of the placed graph. -/
  layers : Array LayerId
  /-- `nodes_by_id`: local node id → node. -/
  nodesById : Array LNodeId
  /-- `InternalProperties.SPACINGS` of the graph. -/
  spacings : Spacings
  deriving Inhabited

namespace BKContext

/-- Number of nodes in the layers (`NeighborhoodInformation.node_count`). -/
@[inline] def nodeCount (c : BKContext) : Nat := c.nodesById.size

/-- Rust `id as usize` of an `i32` id: negative ids wrap around (they are out of range of every
per-node array). -/
@[inline] def idAsUsize (id : Int) : Nat :=
  if id < 0 then (id + 18446744073709551616).toNat else id.toNat

/-- `util::node_id(node)`: the node's `id` field as a `usize`. -/
@[inline] def nodeId (c : BKContext) (n : LNodeId) : Nat := idAsUsize (c.arena.node n).id

/-- `bal.nodes_by_id[id]`. -/
@[inline] def nodeOf (c : BKContext) (id : Nat) : LNodeId := c.nodesById[id]!

/-- `util::node_type(node)`. -/
@[inline] def nodeType (c : BKContext) (n : LNodeId) : NodeType := (c.arena.node n).type

/-- `util::node_margin_top_a`. -/
@[inline] def marginTop (c : BKContext) (n : LNodeId) : Float := (c.arena.node n).margin.top

/-- `util::node_margin_bottom_a`. -/
@[inline] def marginBottom (c : BKContext) (n : LNodeId) : Float := (c.arena.node n).margin.bottom

/-- `util::node_size_y_a`. -/
@[inline] def sizeY (c : BKContext) (n : LNodeId) : Float := (c.arena.node n).size.y

/-- `util::port_offset_y_a`: `port.position.y + port.anchor.y`. -/
@[inline] def portOffsetY (c : BKContext) (p : LPortId) : Float :=
  let pt := c.arena.port p
  pt.position.y + pt.anchor.y

/-- `util::port_node_id_a`: the local id of the port's owner (out of range without owner). -/
@[inline] def portNodeId (c : BKContext) (p : LPortId) : Nat :=
  match (c.arena.port p).owner with
  | some n => c.nodeId n
  | none => 18446744073709551615

/-- `util::node_to_string` (`LNode.toString()`). -/
def nodeToString (c : BKContext) (n : LNodeId) : String := c.arena.nodeToString n

/-- `LNode.getDesignation()`. -/
def designation (c : BKContext) (n : LNodeId) : String := c.arena.nodeDesignation n

/-- `Spacings.getVerticalSpacing(n1, n2)` (throws `UnspecifiedSpacingException`). -/
def verticalSpacing (c : BKContext) (n1 n2 : LNodeId) : IO Float :=
  let a := c.arena
  let x := a.node n1
  let y := a.node n2
  c.spacings.getVerticalSpacing x.type x.props y.type y.props

/-- Whether `e` connects the nodes with local ids `sourceId` and `targetId` in either
direction (`util::edge_between::edge_matches`). -/
private def edgeMatches (c : BKContext) (e : LEdgeId) (sourceId targetId : Nat) : Bool :=
  let a := c.arena
  let ed := a.edge e
  match ed.source.bind (fun p => (a.port p).owner), ed.target.bind (fun p => (a.port p).owner) with
  | some s, some t =>
    let sId := c.nodeId s
    let tId := c.nodeId t
    (sId == sourceId && tId == targetId) || (sId == targetId && tId == sourceId)
  | _, _ => false

/-- `util::edge_between(source, target)` (Java `BKNodePlacer.getEdge`): the first connected
edge of `source` (ports in order, each port's incoming then outgoing edges) between the two
nodes, else the first such edge of `target`. -/
def edgeBetween (c : BKContext) (source target : LNodeId) : Option LEdgeId :=
  let sourceId := c.nodeId source
  let targetId := c.nodeId target
  match (c.arena.nodeConnectedEdges source).find? (c.edgeMatches · sourceId targetId) with
  | some e => some e
  | none => (c.arena.nodeConnectedEdges target).find? (c.edgeMatches · sourceId targetId)

end BKContext

/-- Rust `format!("{:.3}", x)` for the `ELK_TRACE_BK_*` diagnostics (fixed three decimals;
ties round away from zero, which may differ from Rust in the last digit). -/
def fmt3 (x : Float) : String :=
  if x.isNaN then "NaN"
  else if x.isInf then (if x > 0.0 then "inf" else "-inf")
  else
    let neg := x < 0.0
    let n := (x.abs * 1000.0).round.toUInt64.toNat
    let fracStr := toString (n % 1000)
    let fracStr := String.ofList (List.replicate (3 - fracStr.length) '0') ++ fracStr
    (if neg && n != 0 then "-" else "") ++ s!"{n / 1000}.{fracStr}"

end Elk.Alg.Layered.P4Nodes.BK
