import Elk.Alg.Layered.P5Edges.Orthogonal.Direction.BaseRoutingDirectionStrategy
/-!
# `org.eclipse.elk.alg.layered.p5edges.orthogonal.direction.NorthToSouthRoutingStrategy`

Port of elk-rs `p5edges/orthogonal/direction/north_to_south_routing_strategy.rs`: edges leave south
ports and enter north ports; a segment's horizontal piece is placed at
`startPos + routingSlot * edgeSpacing` (used by the hierarchical port router for southern external
ports). The Rust `ArenaSync` snapshot is taken right before routing, so live anchors are identical.
-/
namespace Elk.Alg.Layered.P5Edges.Orthogonal.Direction

open Elk.Graph Elk.Core.Math Elk.Core.Options Elk.Core.Util Elk.Alg.Layered.Graph Elk.Alg.Layered.P5Edges
  Elk.Alg.Layered.P5Edges.Orthogonal

namespace NorthToSouthRoutingStrategy

open BaseRoutingDirectionStrategy

/-- `getPortPositionOnHyperNode(port)`: absolute anchor `x`. -/
def portPositionOnHyperNode (a : LGraphArena) (port : LPortId) : Float :=
  HyperEdgeSegment.portPositionOnHyperNode a .northToSouth port

/-- The bend points of one edge leaving `segment` (Rust inner loop body of `calculate_bend_points`). -/
private def routeEdge (g : SegmentGraph) (segment : HyperEdgeSegment) (edge : LEdgeId) (sourceX targetX segmentY startPos
    edgeSpacing : Float) (created : Std.HashSet KVector) : LayeredM (Std.HashSet KVector) := do
  let mut created := created
  let mut currentY := segmentY
  let mut currentSegment : Option HyperEdgeSegment := none
  let bend : KVector := ⟨sourceX, currentY⟩
  addBendPoint edge bend
  created ← addJunctionPointIfNecessary created edge segment bend false
  if let some partnerIdx := segment.splitPartner then
    let splitPartner := g.segment partnerIdx
    let splitX := splitPartner.incomingConnectionCoordinates[0]?.getD sourceX
    let bend : KVector := ⟨splitX, currentY⟩
    addBendPoint edge bend
    created ← addJunctionPointIfNecessary created edge segment bend false
    currentY := startPos + splitPartner.routingSlot.toFloat * edgeSpacing
    currentSegment := some splitPartner
    let bend : KVector := ⟨splitX, currentY⟩
    addBendPoint edge bend
    created ← addJunctionPointIfNecessary created edge splitPartner bend false
  let bend : KVector := ⟨targetX, currentY⟩
  addBendPoint edge bend
  match currentSegment with
  | some splitPartner => created ← addJunctionPointIfNecessary created edge splitPartner bend false
  | none => created ← addJunctionPointIfNecessary created edge segment bend false
  return created

/-- `calculateBendPoints(segment, startPos, edgeSpacing)` (see `WestToEastRoutingStrategy`, with the
coordinates swapped). -/
def calculateBendPoints (g : SegmentGraph) (segmentIdx : Nat) (startPos edgeSpacing : Float) (scope : ArenaScope)
    (created : Std.HashSet KVector) : LayeredM (Std.HashSet KVector) := do
  let segment := g.segment segmentIdx
  if segment.isDummy then return created
  let mut created := created
  let segmentY := startPos + segment.routingSlot.toFloat * edgeSpacing
  for port in segment.ports do
    let (sourceAnchor, outgoingEdges, portInArena) ← sourcePortData scope port
    let sourceX := sourceAnchor.x
    for edge in outgoingEdges do
      let (isSelfLoop, targetAnchor) ← edgeTargetData portInArena port edge
      if isSelfLoop then continue
      let targetX := targetAnchor.x
      if (sourceX - targetX).abs > OrthogonalRoutingGenerator.TOLERANCE then
        created ← routeEdge g segment edge sourceX targetX segmentY startPos edgeSpacing created
  return created

/-- The strategy (`new NorthToSouthRoutingStrategy()`). -/
def strategy : BaseRoutingDirectionStrategy where
  direction := .northToSouth
  sourcePortSide := .south
  targetPortSide := .north
  portPositionOnHyperNode := portPositionOnHyperNode
  calculateBendPoints := calculateBendPoints

end NorthToSouthRoutingStrategy

end Elk.Alg.Layered.P5Edges.Orthogonal.Direction
