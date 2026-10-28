import Elk.Graph.Enum
import Elk.Core.Math.ElkRectangle
import Elk.Core.Util.Java
import Elk.Alg.Layered.Graph.Ids
/-!
# `org.eclipse.elk.alg.layered.p5edges.splines.SplineSegment` (data part)

Port of the data of elk-rs `p5edges/splines/spline_segment.rs`. A spline segment represents one or
more `LEdge`s between a pair of adjacent layers (a hyperedge when it represents several); the
`FinalSplineBendpointsCalculator` later joins the segments of a spline route into control points.
The `EdgeInformation` of each represented edge keeps the values valid during edge routing, since
the long-edge dummy edges no longer exist when the final control points are computed.

Like `Compound.CrossHierarchyEdge`, this module only holds the data (it imports nothing that needs
the arena) so that the internal properties can store segment tables. The constructors that read
the graph (`SplineSegment(singlePort, edges, sourceSide)`, `SplineSegment(edge, sourceSide,
targetSide)`, `addEdge`, `anchorY`) live with the router in `SplineEdgeRouter.lean`.

## Arena mapping
- Rust `SplineSegmentRef` (`Arc<Mutex<SplineSegment>>`) → `SplineSegmentId` indexing a segment
  table (`Array SplineSegment`): the router's table while routing, persisted per graph for the
  later processors (see `SplineEdgeRouter`).
- Rust `DependencyRef` → `DependencyId` indexing the router-local `Array Dependency`; `outgoing`/
  `incoming` hold these ids (they are only meaningful while the router runs).
- Rust `Vec<LPortRef>`/`Vec<LEdgeRef>` with `insert_unique_port`/`add_edge` (Java `HashSet`s):
  insertion-ordered arrays without duplicates (Rust order).
- `edge_information: FxHashMap<edge, EdgeInformation>` (lookup only) → an insertion-ordered
  association array, see `edgeInformationOf`.
-/
namespace Elk.Alg.Layered.P5Edges.Splines

open Elk.Core.Math Elk.Core.Util Elk.Alg.Layered.Graph

/-- `SplineEdgeRouter.SideToProcess`: the layer (left or right of the gap) a port lies in. -/
elk_enum SideToProcess := left right

/-- `SplineSegment.EdgeInformation`: per-edge values captured during edge routing. -/
structure EdgeInformation where
  /-- `startY`: anchor y of the source port (`anchorY`). -/
  startY : Float := 0.0
  /-- `endY`: anchor y of the target port. -/
  endY : Float := 0.0
  /-- `normalSourceNode`: the source node is `NORMAL` or `BREAKING_POINT`. -/
  normalSourceNode : Bool := false
  /-- `normalTargetNode`. -/
  normalTargetNode : Bool := false
  /-- `invertedLeft`: the source port is a `WEST` port. -/
  invertedLeft : Bool := false
  /-- `invertedRight`: the target port is an `EAST` port. -/
  invertedRight : Bool := false
  deriving Inhabited, BEq, Repr

/-- Id of a `SplineSegment` in a segment table (Rust `SplineSegmentRef`). -/
structure SplineSegmentId where
  idx : Nat
  deriving BEq, Hashable, Repr, Inhabited, DecidableEq, Ord

instance : ToString SplineSegmentId := ⟨fun i => s!"S{i.idx}"⟩

/-- Id of a `Dependency` in the router's dependency table (Rust `DependencyRef`). -/
structure DependencyId where
  idx : Nat
  deriving BEq, Hashable, Repr, Inhabited, DecidableEq, Ord

/-- `SplineEdgeRouter.Dependency`: `source` must lie left of `target`; `weight` counts the crossings
saved by that order. -/
structure Dependency where
  source : SplineSegmentId
  target : SplineSegmentId
  weight : Int
  deriving Inhabited, BEq, Repr

/-- `SplineSegment`. Field names follow Java (`hyperEdgeTopYPos`, …). -/
structure SplineSegment where
  /-- `handled`: set by the `FinalSplineBendpointsCalculator` once the segment was processed. -/
  handled : Bool := false
  /-- `leftPorts`: ports of the segment in the left layer (insertion order, unique). -/
  leftPorts : Array LPortId := #[]
  /-- `rightPorts`: ports of the segment in the right layer. -/
  rightPorts : Array LPortId := #[]
  /-- `outgoing`: dependencies to segments that must lie right of this one. -/
  outgoing : Array DependencyId := #[]
  /-- `incoming`: dependencies to segments that must lie left of this one. -/
  incoming : Array DependencyId := #[]
  /-- `mark` (cycle breaker). -/
  mark : Int := 0
  /-- `inweight`. -/
  inweight : Int := 0
  /-- `outweight`. -/
  outweight : Int := 0
  /-- `rank`: horizontal slot between the layers. -/
  rank : Int := 0
  /-- `edges`: the represented edges (insertion order, unique). -/
  edges : Array LEdgeId := #[]
  /-- `isStraight`: no vertical segment (source and target at the same height). -/
  isStraight : Bool := false
  /-- `boundingBox`: the imaginary box the segment should reside in. -/
  boundingBox : ElkRectangle := {}
  /-- `isWestOfInitialLayer`. -/
  isWestOfInitialLayer : Bool := false
  /-- `xDelta`: offset of the vertical segments when the layer gap exceeds the required spacing. -/
  xDelta : Float := 0.0
  /-- `sourcePort` (set by `getSplinePath`). -/
  sourcePort : Option LPortId := none
  /-- `targetPort` (set by `getSplinePath`). -/
  targetPort : Option LPortId := none
  /-- `initialSegment`. -/
  initialSegment : Bool := false
  /-- `lastSegment`. -/
  lastSegment : Bool := false
  /-- `sourceNode`: source node of the spline if this is its initial segment. -/
  sourceNode : Option LNodeId := none
  /-- `targetNode`: target node of the spline if this is its last segment. -/
  targetNode : Option LNodeId := none
  /-- `inverseOrder`: control points must be read backwards (wrapping). -/
  inverseOrder : Bool := false
  /-- `hyperEdgeTopYPos`. -/
  hyperEdgeTopYPos : Float := 0.0
  /-- `hyperEdgeBottomYPos`. -/
  hyperEdgeBottomYPos : Float := 0.0
  /-- `centerControlPointY`. -/
  centerControlPointY : Float := 0.0
  /-- `edgeInformation`: per represented edge, in insertion order. -/
  edgeInformation : Array (LEdgeId × EdgeInformation) := #[]
  deriving Inhabited, Repr

namespace SplineSegment

/-- `HYPEREDGE_POS_OUTER_RATE` (`0.9`). -/
def HYPEREDGE_POS_OUTER_RATE : Float := 0.9
/-- `HYPEREDGE_POS_MID_RATE` (`1 - HYPEREDGE_POS_OUTER_RATE`). -/
def HYPEREDGE_POS_MID_RATE : Float := 1.0 - HYPEREDGE_POS_OUTER_RATE
/-- `ONE_HALF`. -/
def ONE_HALF : Float := 0.5

/-- `isHyperEdge()`: represents more than one edge. -/
@[inline] def isHyperEdge (s : SplineSegment) : Bool := s.edges.size > 1

/-- `edgeInformation.get(edge)`. -/
def edgeInformationOf (s : SplineSegment) (edge : LEdgeId) : Option EdgeInformation :=
  (s.edgeInformation.find? (·.1 == edge)).map (·.2)

/-- Rust `insert_unique_port`: appends unless already present. -/
def insertUniquePort (ports : Array LPortId) (port : LPortId) : Array LPortId :=
  if ports.contains port then ports else ports.push port

/-- `setRelevantPositions(sourceY, targetYMin, targetYMax)`: bounding box y-range, center control
point and the hyperedge top/bottom positions used for the dependency graph. -/
def setRelevantPositions (s : SplineSegment) (sourceY targetYMin targetYMax : Float) : SplineSegment :=
  let boxY := fmin sourceY targetYMin
  let boxHeight := fmax sourceY targetYMax - boxY
  let s := { s with boundingBox := { s.boundingBox with y := boxY, height := boxHeight } }
  if sourceY < targetYMin then
    let center := ONE_HALF * (sourceY + targetYMin)
    { s with centerControlPointY := center,
             hyperEdgeTopYPos := HYPEREDGE_POS_MID_RATE * center + HYPEREDGE_POS_OUTER_RATE * sourceY,
             hyperEdgeBottomYPos := HYPEREDGE_POS_MID_RATE * center + HYPEREDGE_POS_OUTER_RATE * targetYMin }
  else
    let center := ONE_HALF * (sourceY + targetYMax)
    { s with centerControlPointY := center,
             hyperEdgeTopYPos := HYPEREDGE_POS_MID_RATE * center + HYPEREDGE_POS_OUTER_RATE * targetYMax,
             hyperEdgeBottomYPos := HYPEREDGE_POS_MID_RATE * center + HYPEREDGE_POS_OUTER_RATE * sourceY }

end SplineSegment

end Elk.Alg.Layered.P5Edges.Splines
