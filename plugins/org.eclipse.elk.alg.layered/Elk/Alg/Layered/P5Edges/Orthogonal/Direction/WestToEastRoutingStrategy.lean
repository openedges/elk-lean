import Elk.Alg.Layered.P5Edges.Orthogonal.Direction.BaseRoutingDirectionStrategy
/-!
# `org.eclipse.elk.alg.layered.p5edges.orthogonal.direction.WestToEastRoutingStrategy`

Port of elk-rs `p5edges/orthogonal/direction/west_to_east_routing_strategy.rs`: edges leave east ports
of the left layer and enter west ports of the right layer; a segment's vertical piece is placed at
`startPos + routingSlot * edgeSpacing`.

Arena reads: Rust takes source/target anchors from the `ArenaSync` snapshot made at the start of
`OrthogonalEdgeRouter.process`, whose node `x` coordinates are stale after `placeNodesHorizontally`;
only `y` is read here, which no step of the router changes, so the live arena gives the same values.
-/
namespace Elk.Alg.Layered.P5Edges.Orthogonal.Direction

open Elk.Graph Elk.Core.Math Elk.Core.Options Elk.Core.Util Elk.Alg.Layered.Graph Elk.Alg.Layered.P5Edges
  Elk.Alg.Layered.P5Edges.Orthogonal

namespace WestToEastRoutingStrategy

open BaseRoutingDirectionStrategy

/-- `getPortPositionOnHyperNode(port)`: absolute anchor `y` (`(0, 0)` node position without a node). -/
def portPositionOnHyperNode (a : LGraphArena) (port : LPortId) : Float :=
  HyperEdgeSegment.portPositionOnHyperNode a .westToEast port

/-- The bend points of one edge leaving `segment` (Rust inner loop body of `calculate_bend_points`). -/
private def routeEdge (g : SegmentGraph) (segment : HyperEdgeSegment) (edge : LEdgeId) (sourceY targetY segmentX startPos
    edgeSpacing : Float) (created : Std.HashSet KVector) : LayeredM (Std.HashSet KVector) := do
  let mut created := created
  let mut currentX := segmentX
  let mut currentSegment : Option HyperEdgeSegment := none
  let bend : KVector := ⟨currentX, sourceY⟩
  addBendPoint edge bend
  created ← addJunctionPointIfNecessary created edge segment bend true
  if let some partnerIdx := segment.splitPartner then
    let splitPartner := g.segment partnerIdx
    let splitY := splitPartner.incomingConnectionCoordinates[0]?.getD sourceY
    let bend : KVector := ⟨currentX, splitY⟩
    addBendPoint edge bend
    created ← addJunctionPointIfNecessary created edge segment bend true
    currentX := startPos + splitPartner.routingSlot.toFloat * edgeSpacing
    currentSegment := some splitPartner
    let bend : KVector := ⟨currentX, splitY⟩
    addBendPoint edge bend
    created ← addJunctionPointIfNecessary created edge splitPartner bend true
  let bend : KVector := ⟨currentX, targetY⟩
  addBendPoint edge bend
  match currentSegment with
  | some splitPartner => created ← addJunctionPointIfNecessary created edge splitPartner bend true
  | none => created ← addJunctionPointIfNecessary created edge segment bend true
  return created

/-- `calculateBendPoints(segment, startPos, edgeSpacing)`: for every port of the segment (in order) and
every outgoing edge whose end points differ by more than `TOLERANCE` in `y`: a bend point at the
segment's slot on the source `y`, the detour over the split partner's slot when the segment was split,
and a bend point on the target `y`. Dummy segments (split partners) add nothing. -/
def calculateBendPoints (g : SegmentGraph) (segmentIdx : Nat) (startPos edgeSpacing : Float) (scope : ArenaScope)
    (created : Std.HashSet KVector) : LayeredM (Std.HashSet KVector) := do
  let segment := g.segment segmentIdx
  if segment.isDummy then return created
  let mut created := created
  let segmentX := startPos + segment.routingSlot.toFloat * edgeSpacing
  for port in segment.ports do
    let (sourceAnchor, outgoingEdges, portInArena) ← sourcePortData scope port
    let sourceY := sourceAnchor.y
    for edge in outgoingEdges do
      let (isSelfLoop, targetAnchor) ← edgeTargetData portInArena port edge
      if isSelfLoop then continue
      let targetY := targetAnchor.y
      if (sourceY - targetY).abs > OrthogonalRoutingGenerator.TOLERANCE then
        created ← routeEdge g segment edge sourceY targetY segmentX startPos edgeSpacing created
  return created

/-- The strategy (`new WestToEastRoutingStrategy()`). -/
def strategy : BaseRoutingDirectionStrategy where
  direction := .westToEast
  sourcePortSide := .east
  targetPortSide := .west
  portPositionOnHyperNode := portPositionOnHyperNode
  calculateBendPoints := calculateBendPoints

end WestToEastRoutingStrategy

end Elk.Alg.Layered.P5Edges.Orthogonal.Direction
