import Elk.Alg.Layered.P5Edges.Orthogonal.Direction.BaseRoutingDirectionStrategy
/-!
# `org.eclipse.elk.alg.layered.p5edges.orthogonal.direction.SouthToNorthRoutingStrategy`

Port of elk-rs `p5edges/orthogonal/direction/south_to_north_routing_strategy.rs`: edges leave north
ports and enter south ports; a segment's horizontal piece is placed at
`startPos - routingSlot * edgeSpacing` (used by the hierarchical port router for northern external
ports). The Rust `ArenaSync` snapshot is taken right before routing, so live anchors are identical.
-/
namespace Elk.Alg.Layered.P5Edges.Orthogonal.Direction

open Elk.Graph Elk.Core.Math Elk.Core.Options Elk.Core.Util Elk.Alg.Layered.Graph Elk.Alg.Layered.P5Edges
  Elk.Alg.Layered.P5Edges.Orthogonal

namespace SouthToNorthRoutingStrategy

open BaseRoutingDirectionStrategy

/-- `getPortPositionOnHyperNode(port)`: absolute anchor `x`. -/
def portPositionOnHyperNode (a : LGraphArena) (port : LPortId) : Float :=
  HyperEdgeSegment.portPositionOnHyperNode a .southToNorth port

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
    currentY := startPos - splitPartner.routingSlot.toFloat * edgeSpacing
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

/-- `calculateBendPoints(segment, startPos, edgeSpacing)` (see `NorthToSouthRoutingStrategy`; slots grow
upwards). -/
def calculateBendPoints (g : SegmentGraph) (segmentIdx : Nat) (startPos edgeSpacing : Float) (scope : ArenaScope)
    (created : Std.HashSet KVector) : LayeredM (Std.HashSet KVector) := do
  let segment := g.segment segmentIdx
  if segment.isDummy then return created
  let mut created := created
  let segmentY := startPos - segment.routingSlot.toFloat * edgeSpacing
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

/-- The strategy (`new SouthToNorthRoutingStrategy()`). -/
def strategy : BaseRoutingDirectionStrategy where
  direction := .southToNorth
  sourcePortSide := .north
  targetPortSide := .south
  portPositionOnHyperNode := portPositionOnHyperNode
  calculateBendPoints := calculateBendPoints

end SouthToNorthRoutingStrategy

end Elk.Alg.Layered.P5Edges.Orthogonal.Direction
