import Std.Data.HashMap
import Elk.Alg.Layered.Graph
import Elk.Alg.Layered.P5Edges.Orthogonal.Direction.RoutingDirection
import Elk.Core.Util.Java
/-!
# `org.eclipse.elk.alg.layered.p5edges.orthogonal.HyperEdgeSegment`

Port of elk-rs `p5edges/orthogonal/hyper_edge_segment.rs`. A hyperedge segment is the vertical
(for west-to-east routing) part of a set of edges connected through common ports, routed in one
routing slot between two layers.

Representation: Rust shares segments as `Rc<RefCell<HyperEdgeSegment>>` and links them through
`Weak` split partner / split-by pointers and `Rc` dependency objects. Here the segments of one
`OrthogonalRoutingGenerator.routeEdges` call live in a local arena (`SegmentGraph`, defined in
`HyperEdgeSegmentDependency` together with the dependencies); a segment refers to other segments
and to its dependencies by their **indices** in that arena (`Rc::ptr_eq` → index equality). The
index of a segment equals its position in Rust's `edge_segments` list, because every segment Rust
appends to that list is pushed to the arena at the same moment.

The pure operations on one segment live here; `splitAt` (which removes dependencies) lives in
`HyperEdgeSegmentDependency` as `SegmentGraph.splitAt`.
-/
namespace Elk.Alg.Layered.P5Edges.Orthogonal

open Elk.Graph Elk.Core.Math Elk.Core.Options Elk.Core.Util Elk.Alg.Layered.Graph
  Elk.Alg.Layered.P5Edges.Orthogonal.Direction

/-- `HyperEdgeSegment`. The connection coordinates are kept sorted ascending (`insertSorted`).
Dependency lists hold dependency indices of the owning `SegmentGraph`; `splitPartner`/`splitBy`
hold segment indices. -/
structure HyperEdgeSegment where
  /-- `routing_direction` (Java: the routing strategy; only its direction is needed). -/
  routingDirection : RoutingDirection := .westToEast
  /-- `ports`: the ports of the hyperedge in the order they were added. -/
  ports : Array LPortId := #[]
  /-- `mark` (used by `HyperEdgeCycleDetector`). -/
  mark : Int := 0
  /-- `routing_slot`. -/
  routingSlot : Int := 0
  /-- `start_position` (`NaN` until coordinates exist). -/
  startPosition : Float := Float.nan
  /-- `end_position` (`NaN` until coordinates exist). -/
  endPosition : Float := Float.nan
  /-- `incoming_connection_coordinates` (ports on the source side; sorted). -/
  incomingConnectionCoordinates : Array Float := #[]
  /-- `outgoing_connection_coordinates` (ports on the target side; sorted). -/
  outgoingConnectionCoordinates : Array Float := #[]
  /-- `outgoing_segment_dependencies` (dependency indices). -/
  outgoingSegmentDependencies : Array Nat := #[]
  /-- `incoming_segment_dependencies` (dependency indices). -/
  incomingSegmentDependencies : Array Nat := #[]
  /-- `out_dep_weight`. -/
  outDepWeight : Int := 0
  /-- `critical_out_dep_weight`. -/
  criticalOutDepWeight : Int := 0
  /-- `in_dep_weight`. -/
  inDepWeight : Int := 0
  /-- `critical_in_dep_weight`. -/
  criticalInDepWeight : Int := 0
  /-- `split_partner` (segment index). -/
  splitPartner : Option Nat := none
  /-- `split_by` (segment index). -/
  splitBy : Option Nat := none
  deriving Inhabited

namespace HyperEdgeSegment

/-- `HyperEdgeSegment::new(direction)` (Java `new HyperEdgeSegment(routingStrategy)`). -/
def new (direction : RoutingDirection) : HyperEdgeSegment := { routingDirection := direction }

/-- `source_port_side()` (Java `routingStrategy.getSourcePortSide()`): the side of the ports whose
coordinates are incoming connections. -/
def sourcePortSide (s : HyperEdgeSegment) : PortSide :=
  match s.routingDirection with
  | .westToEast => .east
  | .northToSouth => .south
  | .southToNorth => .north

/-- `getStartCoordinate()`. -/
@[inline] def startCoordinate (s : HyperEdgeSegment) : Float := s.startPosition

/-- `getEndCoordinate()`. -/
@[inline] def endCoordinate (s : HyperEdgeSegment) : Float := s.endPosition

/-- `getLength()`: end minus start coordinate. -/
def length (s : HyperEdgeSegment) : Float := s.endPosition - s.startPosition

/-- `representsHyperedge()`: more than two connection coordinates. -/
def representsHyperedge (s : HyperEdgeSegment) : Bool :=
  s.incomingConnectionCoordinates.size + s.outgoingConnectionCoordinates.size > 2

/-- `isDummy()`: the split partner created by `splitAt` (it has a partner but was not split by
another segment). -/
def isDummy (s : HyperEdgeSegment) : Bool := s.splitPartner.isSome && s.splitBy.isNone

/-- `compareTo(other)` (Java `this.mark - other.mark`): the ordering by `mark` used to sort the
unprocessed segments in `HyperEdgeCycleDetector` (Rust `sort_by_key(mark)`). -/
def compareByMark (a b : HyperEdgeSegment) : Ordering := compare a.mark b.mark

/-- Loop of `insertSorted` from index `idx` (tail recursive). -/
private partial def insertSortedFrom (list : Array Float) (value : Float) (idx : Nat) : Array Float :=
  if h : idx < list.size then
    let existing := list[idx]
    if (existing - value).abs < Float.epsilon then list
    else if existing > value then list.insertIdx! idx value
    else insertSortedFrom list value (idx + 1)
  else list.push value

/-- Rust `insert_sorted(list, value)`: inserts `value` before the first larger element; nothing is
inserted when an element differs from `value` by less than `f64::EPSILON`. (Java compares the
`float` value of the elements with `==`; elk-rs uses this `f64` epsilon test.) -/
def insertSorted (list : Array Float) (value : Float) : Array Float :=
  insertSortedFrom list value 0

/-- Start half of Rust `recompute_extent_list(start, end, positions)`: `start` (NaN = unset) widened by
the first element of the sorted `positions` (`f64::min`). -/
@[inline] def extentStart (start : Float) (positions : Array Float) : Float :=
  if h : 0 < positions.size then
    let first := positions[0]
    if start.isNaN then first else fmin start first
  else start

/-- End half of Rust `recompute_extent_list(start, end, positions)`: `stop` (NaN = unset) widened by the
last element of the sorted `positions` (`f64::max`). -/
@[inline] def extentEnd (stop : Float) (positions : Array Float) : Float :=
  if h : 0 < positions.size then
    let last := positions[positions.size - 1]
    if stop.isNaN then last else fmax stop last
  else stop

/-- Rust `recompute_extent_list(start, end, positions)`: widens `[start, stop]` (NaN = unset) by the
first and last element of the sorted `positions` (`f64::min`/`f64::max`). -/
def recomputeExtentList (start stop : Float) (positions : Array Float) : Float × Float :=
  (extentStart start positions, extentEnd stop positions)

/-- `recomputeExtent()`: start/end coordinate from the incoming and outgoing coordinates. -/
def recomputeExtent (s : HyperEdgeSegment) : HyperEdgeSegment :=
  let start := extentStart (extentStart Float.nan s.incomingConnectionCoordinates) s.outgoingConnectionCoordinates
  let stop := extentEnd (extentEnd Float.nan s.incomingConnectionCoordinates) s.outgoingConnectionCoordinates
  { s with startPosition := start, endPosition := stop }

/-! ### In-place updaters

The functions below are the element updates of `SegmentGraph.modifySegment`. They are deliberately
`@[noinline]`: when the update `fun s => { s with … }` is inlined into `Array.modify`, the Lean 4.35
compiler tests the element for exclusivity *before* `Array.modify` swaps it out of the array, so the
reuse always fails and every update allocates a fresh 17-field segment (and frees the old one). A
non-inlined updater receives the swapped-out, unshared element and updates it in place. -/

/-- `add_outgoing_dependency(dep)`: appends dependency `d` to the outgoing list. -/
@[noinline] def pushOutgoingDependency (d : Nat) (s : HyperEdgeSegment) : HyperEdgeSegment :=
  { s with outgoingSegmentDependencies := s.outgoingSegmentDependencies.push d }

/-- `add_incoming_dependency(dep)`: appends dependency `d` to the incoming list. -/
@[noinline] def pushIncomingDependency (d : Nat) (s : HyperEdgeSegment) : HyperEdgeSegment :=
  { s with incomingSegmentDependencies := s.incomingSegmentDependencies.push d }

/-- Rust `Vec::swap_remove(pos)` (`pos` in bounds): the last element moves into position `pos`. -/
@[inline] def swapRemoveAt (list : Array Nat) (pos : Nat) : Array Nat :=
  (list.set! pos list[list.size - 1]!).pop

/-- `swap_remove(pos)` on the outgoing dependency list. -/
@[noinline] def swapRemoveOutgoingAt (pos : Nat) (s : HyperEdgeSegment) : HyperEdgeSegment :=
  { s with outgoingSegmentDependencies := swapRemoveAt s.outgoingSegmentDependencies pos }

/-- `swap_remove(pos)` on the incoming dependency list. -/
@[noinline] def swapRemoveIncomingAt (pos : Nat) (s : HyperEdgeSegment) : HyperEdgeSegment :=
  { s with incomingSegmentDependencies := swapRemoveAt s.incomingSegmentDependencies pos }

/-- Stores the results of a `HyperEdgeCycleDetector` run (mark and the four weights). -/
@[noinline] def setCycleData (mark inWeight criticalInWeight outWeight criticalOutWeight : Int) (s : HyperEdgeSegment) :
    HyperEdgeSegment :=
  { s with mark := mark, inDepWeight := inWeight, criticalInDepWeight := criticalInWeight,
           outDepWeight := outWeight, criticalOutDepWeight := criticalOutWeight }

/-- Stores the results of `topologicalNumbering` (routing slot and the in/out weights). -/
@[noinline] def setNumberingData (routingSlot inWeight outWeight : Int) (s : HyperEdgeSegment) : HyperEdgeSegment :=
  { s with routingSlot := routingSlot, inDepWeight := inWeight, outDepWeight := outWeight }

/-- Rust `get_port_position_on_hyper_node_arena` / `get_port_position_on_hyper_node`
(Java `routingStrategy.getPortPositionOnHyperNode(port)`): the port's absolute anchor coordinate
across the routing direction (`y` for west-to-east, `x` otherwise); a port without a node counts
its node position as `(0, 0)`. Both Rust variants compute `node + port position + anchor`. -/
def portPositionOnHyperNode (a : LGraphArena) (direction : RoutingDirection) (port : LPortId) : Float :=
  let pt := a.port port
  let nodePos : KVector := match pt.owner with
    | some n => (a.node n).position
    | none => {}
  match direction with
  | .westToEast => nodePos.y + pt.position.y + pt.anchor.y
  | .northToSouth | .southToNorth => nodePos.x + pt.position.x + pt.anchor.x

/-- `addPortPositions(port, hyperEdgeSegmentMap)` (Rust `add_port_positions`): maps `port` to the
segment (index `segmentIndex`), records its coordinate as incoming (source side) or outgoing
connection, and recurses depth-first into the connected ports (predecessors, then successors) not
mapped yet. Pure: the arena is only read. -/
partial def addPortPositions (a : LGraphArena) (segmentIndex : Nat) (segment : HyperEdgeSegment) (port : LPortId)
    (map : Std.HashMap LPortId Nat) : HyperEdgeSegment × Std.HashMap LPortId Nat := Id.run do
  let mut map := map.insert port segmentIndex
  let mut segment := { segment with ports := segment.ports.push port }
  let portPos := portPositionOnHyperNode a segment.routingDirection port
  if (a.port port).side == segment.sourcePortSide then
    segment := { segment with
      incomingConnectionCoordinates := insertSorted segment.incomingConnectionCoordinates portPos }
  else
    segment := { segment with
      outgoingConnectionCoordinates := insertSorted segment.outgoingConnectionCoordinates portPos }
  segment := segment.recomputeExtent
  for otherPort in a.portConnectedPorts port do
    if !map.contains otherPort then
      let (s, m) := addPortPositions a segmentIndex segment otherPort map
      segment := s
      map := m
  return (segment, map)

/-- `simulateSplit()`: the two segments a split would produce (the first with this segment's
incoming coordinates and `splitBy`, the second with its outgoing coordinates), not added to any
arena. Rust also links the two through `split_partner`; the rating code never reads that link, so
the values here leave it unset. -/
def simulateSplit (s : HyperEdgeSegment) : HyperEdgeSegment × HyperEdgeSegment :=
  let newSplit : HyperEdgeSegment :=
    { routingDirection := s.routingDirection
      incomingConnectionCoordinates := s.incomingConnectionCoordinates
      splitBy := s.splitBy }
  let newSplitPartner : HyperEdgeSegment :=
    { routingDirection := s.routingDirection
      outgoingConnectionCoordinates := s.outgoingConnectionCoordinates }
  (newSplit.recomputeExtent, newSplitPartner.recomputeExtent)

end HyperEdgeSegment

end Elk.Alg.Layered.P5Edges.Orthogonal
