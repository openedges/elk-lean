import Std.Data.HashSet
import Elk.Core.Util.FastFloat
import Elk.Alg.Layered.Graph
import Elk.Alg.Layered.Options.LayeredOptions
import Elk.Alg.Layered.P5Edges.Orthogonal.HyperEdgeSegmentDependency
/-!
# `org.eclipse.elk.alg.layered.p5edges.orthogonal.direction.BaseRoutingDirectionStrategy`

Port of elk-rs `p5edges/orthogonal/direction/base_routing_direction_strategy.rs`. The abstract Java
class (Rust: the `RoutingDirectionStrategy` enum over the three strategies) is a structure of the
direction-specific functions; the three implementations live in `WestToEastRoutingStrategy`,
`NorthToSouthRoutingStrategy` and `SouthToNorthRoutingStrategy`, and the factory
`forRoutingDirection` in the package aggregator `Orthogonal.Direction`.

The strategy's `created_junction_points` set is not stored in the strategy: `calculateBendPoints`
threads it explicitly (`Std.HashSet KVector`; `KVector`'s `BEq`/`Hashable` are the Rust `PartialEq`
(`x == x && y == y`) and bit hash). `OrthogonalRoutingGenerator.routeEdges` starts each call with an
empty set, which is Rust's `clear_created_junction_points()` at the end of every call.

This module also holds two helpers shared by the routers:
* `OrthogonalRoutingGenerator.TOLERANCE` (Java/Rust constant of the generator; defined here because the
  strategies, which the generator imports, need it);
* `ArenaScope`: the membership test of elk-rs `ArenaSync` (see `PORTING.md` §15.1).
-/
namespace Elk.Alg.Layered.P5Edges

open Elk.Graph Elk.Core.Math Elk.Core.Options Elk.Core.Util Elk.Alg.Layered.Graph Elk.Alg.Layered.Options LayeredM

/-- `OrthogonalRoutingGenerator.TOLERANCE`: differences below this are considered equal. -/
def Orthogonal.OrthogonalRoutingGenerator.TOLERANCE : Float := 1e-3

/-- The nodes elk-rs `ArenaSync::from_lgraph(graph)` copied into its CSR arena: the nodes of all
layers and the layerless nodes of the graph at the time of the snapshot. A port is in the arena when
its owner is; an edge when both end ports are (`ArenaSync` pass 2 skips edges leaving the graph).
Rust code that branches on `sync.port_id(port)` / `sync.edge_id(edge)` uses this test. -/
structure ArenaScope where
  nodes : Std.HashSet LNodeId := {}

namespace ArenaScope

/-- `ArenaSync::from_lgraph(graph)` membership (layers' nodes, then layerless nodes). -/
def ofGraph (a : LGraphArena) (graph : LGraphId) : ArenaScope := Id.run do
  let gr := a.graph graph
  let mut nodes : Std.HashSet LNodeId := {}
  for l in gr.layers do
    for n in (a.layer l).nodes do
      nodes := nodes.insert n
  for n in gr.layerlessNodes do
    nodes := nodes.insert n
  return { nodes := nodes }

/-- `sync.port_id(port).is_some()`. -/
def containsPort (s : ArenaScope) (a : LGraphArena) (p : LPortId) : Bool :=
  match (a.port p).owner with
  | some n => s.nodes.contains n
  | none => false

/-- `arena.port_outgoing_edges(pid)`: the port's outgoing edges whose target port is in the arena
(original order). -/
def portOutgoingEdges (s : ArenaScope) (a : LGraphArena) (p : LPortId) : Array LEdgeId :=
  (a.port p).outgoingEdges.filter fun e =>
    match (a.edge e).target with
    | some t => s.containsPort a t
    | none => false

end ArenaScope

namespace Orthogonal.Direction

open Elk.Alg.Layered.P5Edges.Orthogonal

/-- `BaseRoutingDirectionStrategy` (Rust `RoutingDirectionStrategy`): the direction-specific parts of
the orthogonal routing. -/
structure BaseRoutingDirectionStrategy where
  /-- `direction()`. -/
  direction : RoutingDirection
  /-- `getSourcePortSide()`: side of the ports whose edges leave the routing area's source side. -/
  sourcePortSide : PortSide
  /-- `getTargetPortSide()`. -/
  targetPortSide : PortSide
  /-- `getPortPositionOnHyperNode(port)`. -/
  portPositionOnHyperNode : LGraphArena → LPortId → Float
  /-- `calculateBendPoints(segment, startPos, edgeSpacing)` for the segment with the given index of the
  arena; threads the created junction points. -/
  calculateBendPoints : SegmentGraph → Nat → Float → Float → ArenaScope → Std.HashSet KVector →
    LayeredM (Std.HashSet KVector)

namespace BaseRoutingDirectionStrategy

/-- The test of `addJunctionPointIfNecessary(edge, segment, pos, vertical)` (Rust
`add_junction_point_with_guard`): `pos` becomes a junction point if it was not created yet and lies
strictly inside the segment's extent or on a boundary shared by an incoming and an outgoing
connection. -/
def isJunctionPoint (created : Std.HashSet KVector) (segment : HyperEdgeSegment) (pos : KVector) (vertical : Bool) :
    Bool :=
  if created.contains pos then false
  else
    let p := if vertical then pos.y else pos.x
    let pointInsideEdgeSegment := p > segment.startPosition && p < segment.endPosition
    let incoming := segment.incomingConnectionCoordinates
    let outgoing := segment.outgoingConnectionCoordinates
    let tol := OrthogonalRoutingGenerator.TOLERANCE
    let pointAtSegmentBoundary := !incoming.isEmpty && !outgoing.isEmpty &&
      (((p - incoming[0]!).abs < tol && (p - outgoing[0]!).abs < tol) ||
        ((p - incoming.back!).abs < tol && (p - outgoing.back!).abs < tol))
    pointInsideEdgeSegment || pointAtSegmentBoundary

/-- The bend points and junction points one edge receives from `calculateBendPoints`, and the created
junction points so far. Rust adds them to the edge one by one; neither is read back while routing,
so they are written in one update (`applyRoute`). -/
structure EdgeRoute where
  /-- Bend points in order (`edge.getBendPoints().add(bend)`). -/
  bends : Array KVector := #[]
  /-- Junction points in order (`JUNCTION_POINTS` additions). -/
  junctions : Array KVector := #[]
  /-- `created_junction_points`. -/
  created : Std.HashSet KVector

/-- `edge.getBendPoints().add(pos)` followed by `addJunctionPointIfNecessary(edge, segment, pos,
vertical)`. -/
@[inline] def EdgeRoute.addPoint (r : EdgeRoute) (segment : HyperEdgeSegment) (pos : KVector) (vertical : Bool) :
    EdgeRoute :=
  match r with
  | ⟨bends, junctions, created⟩ =>
    if isJunctionPoint created segment pos vertical then ⟨bends.push pos, junctions.push pos, created.insert pos⟩
    else ⟨bends.push pos, junctions, created⟩

/-- Appends the collected points to the edge (bend points; junction points to `JUNCTION_POINTS`, which
is only touched when there are some). Not inlined, so the edge is updated in place. -/
@[noinline] def appendRoute (bends junctions : Array KVector) (ed : LEdge) : LEdge :=
  let ed := { ed with bendPoints := ed.bendPoints ++ bends }
  if junctions.isEmpty then ed
  else
    let junctionPoints := ed.props.getD LayeredOptions.JUNCTION_POINTS #[]
    { ed with props := ed.props.set LayeredOptions.JUNCTION_POINTS (junctionPoints ++ junctions) }

/-- Writes an edge's route; returns the created junction points. -/
@[inline] def applyRoute (edge : LEdgeId) (r : EdgeRoute) : LayeredM (Std.HashSet KVector) := do
  match r with
  | ⟨bends, junctions, created⟩ =>
    modifyEdge edge (appendRoute bends junctions)
    return created

/-- The source port data the Rust strategies read: from the arena when `sync.port_id(port)` exists
(absolute anchor, `port_outgoing_edges`), else from the live port (anchor or `(0, 0)`, all outgoing
edges). Also returns whether the port is in the arena. -/
def sourcePortData (a : LGraphArena) (scope : ArenaScope) (port : LPortId) : KVector × Array LEdgeId × Bool :=
  if scope.containsPort a port then
    ((a.portAbsoluteAnchor port).getD {}, scope.portOutgoingEdges a port, true)
  else
    ((a.portAbsoluteAnchor port).getD {}, (a.port port).outgoingEdges, false)

/-- The edge data the Rust strategies read: `(is self loop, target anchor)`. Edges of an arena port are
arena edges, whose self-loop test is `source port == target port`; other edges use
`LEdge.isSelfLoop()` (same node) and the live target anchor (or `(0, 0)`). -/
def edgeTargetData (a : LGraphArena) (portInArena : Bool) (port : LPortId) (edge : LEdgeId) : Bool × KVector :=
  let target := (a.edge edge).target
  if portInArena then
    if target == some port then (true, {})
    else (false, (target.bind a.portAbsoluteAnchor).getD {})
  else
    if a.edgeIsSelfLoop edge then (true, {})
    else (false, (target.bind a.portAbsoluteAnchor).getD {})

end BaseRoutingDirectionStrategy

end Orthogonal.Direction

end Elk.Alg.Layered.P5Edges
