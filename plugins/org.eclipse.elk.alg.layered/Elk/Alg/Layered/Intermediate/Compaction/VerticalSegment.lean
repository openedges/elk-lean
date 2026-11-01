import Elk.Alg.Layered.Graph.Ids
import Elk.Alg.Common.Compaction.OneD.CNode
import Elk.Alg.Common.Compaction.OneD.CompareFuzzy
import Elk.Core.Math
import Elk.Core.Util.Java
/-!
# `org.eclipse.elk.alg.layered.intermediate.compaction.VerticalSegment`

A vertical segment of one or more `LEdge`s (elk-rs `VerticalSegment` of
`intermediate/horizontal_graph_compactor.rs`). Intersecting segments are merged
(`joinWith`) before they become `CNode`s of the compaction graph.

There are two kinds of segments: the usual segment stems from a step of an orthogonal edge
(or a non-straight spline segment) and has no parent node; the vertical part of an edge that is
connected to the north or south side of a node has that node's `CNode` as a potential group
parent, so node and segment are compacted as one `CGroup`.

The Rust struct is ported field by field (Java fields in parentheses):
* `affectedBends` (Java `affectedBends`, the `KVector` objects) are `(edge, bend point index)`
  pairs, since bend points are values here;
* `affectedSplineSegments` (Java `affectedBoundingBoxes`) are handles of spline segments, see
  `SplineRouteAccess` in `LGraphToCGraphTransformer`;
* the Rust `HashSet<usize>` fields `joinedSegmentIds`, `constraintTargetIds` and
  `representedEdgeKeys` are duplicate-free arrays in insertion order. `joinedSegmentIds` and
  `representedEdgeKeys` are only used for lookups; `constraintTargetIds` is iterated when the
  predefined constraints are created, where Rust's iteration order is the unspecified
  `RandomState` order — insertion order is used here;
* `junctionPoints` (Java `junctionPoints`, the `KVector` objects of the edge's `JUNCTION_POINTS`) are
  `(edge, junction point index)` pairs: the junction points whose x equals the first bend point's x
  (fuzzy), moved with the segment like Java (elk-rs does not move junction points). Like Java's lists,
  `affectedBends`, `affectedSplineSegments` and `junctionPoints` keep duplicates when segments are
  joined (a north/south segment and the regular segment starting at the same bend point both hold
  it), and every occurrence is moved.
-/
namespace Elk.Alg.Layered.Intermediate.Compaction

open Elk.Core.Math Elk.Core.Util Elk.Alg.Common.Compaction.OneD Elk.Alg.Layered.Graph

/-- Appends `x` unless it is already contained (Rust `HashSet::insert` on an insertion-ordered
array). -/
@[inline] def pushUnique {α : Type} [BEq α] (as : Array α) (x : α) : Array α :=
  if as.contains x then as else as.push x

/-- Rust `HashSet::extend` on an insertion-ordered array. -/
def extendUnique {α : Type} [BEq α] (as bs : Array α) : Array α :=
  bs.foldl pushUnique as

/-- `VerticalSegment` (Rust struct of the same name). -/
structure VerticalSegment where
  /-- Rust `segment_id`: creation index (`allocate_segment_id`). -/
  segmentId : Nat
  /-- Rust `joined_segment_ids` (Java `joined` plus the segment itself). -/
  joinedSegmentIds : Array Nat
  /-- Rust `constraint_target_ids` (Java `constraints`): segments that have to be placed right
  of this one (consecutive non-straight spline segments). -/
  constraintTargetIds : Array Nat := #[]
  /-- `hitbox`: the area occupied by this segment. -/
  hitbox : ElkRectangle
  /-- `representedLEdges`: the edges contributing to this segment (may contain duplicates). -/
  representedEdges : Array LEdgeId
  /-- Rust `represented_edge_keys`: the set of `representedEdges`. -/
  representedEdgeKeys : Array LEdgeId
  /-- `ignoreSpacing.up`. -/
  ignoreSpacingUp : Bool := false
  /-- `ignoreSpacing.down`. -/
  ignoreSpacingDown : Bool := false
  /-- `aPort`: the north/south port the segment leaves or enters. -/
  port : Option LPortId := none
  /-- `affectedBends`: `(edge, bend point index)` of the bend points to move after compaction. -/
  affectedBends : Array (LEdgeId × Nat) := #[]
  /-- Rust `affected_spline_segments` (Java `affectedBoundingBoxes`): spline segment handles. -/
  affectedSplineSegments : Array Nat := #[]
  /-- `junctionPoints`: `(edge, junction point index)` of the junction points to move. -/
  junctionPoints : Array (LEdgeId × Nat) := #[]
  /-- `potentialGroupParents`: node `CNode`s whose group may receive this segment. -/
  potentialGroupParents : Array CNodeId := #[]
  deriving Inhabited

namespace VerticalSegment

/-- The junction points of `edge` (its `JUNCTION_POINTS` `jps`) whose x equals `x` (`CompareFuzzy.eq`),
as `(edge, index)` in list order (Java constructor of `VerticalSegment`). -/
def junctionPointsAt (edge : LEdgeId) (jps : KVectorChain) (x : Float) : Array (LEdgeId × Nat) := Id.run do
  let mut out : Array (LEdgeId × Nat) := #[]
  for h : i in [0:jps.size] do
    if CompareFuzzy.eq jps[i].x x then out := out.push (edge, i)
  return out

/-- Rust `CompactionContext::new_vertical_segment` (Java `new VerticalSegment(bend1, bend2, cNode,
lEdge)`) for an already allocated `segmentId`: the hitbox spans both bend points; `jps` are the
edge's `JUNCTION_POINTS` (those at `bend1.x`, fuzzy, are recorded). -/
def new (segmentId : Nat) (bend1 bend2 : KVector) (edge : LEdgeId) (bendIndices : Array Nat)
    (potentialParent : Option CNodeId) (jps : KVectorChain := #[]) : VerticalSegment :=
  { segmentId
    joinedSegmentIds := #[segmentId]
    hitbox := ElkRectangle.ofValues (fmin bend1.x bend2.x) (fmin bend1.y bend2.y)
      (bend1.x - bend2.x).abs (bend1.y - bend2.y).abs
    representedEdges := #[edge]
    representedEdgeKeys := #[edge]
    affectedBends := bendIndices.map (edge, ·)
    junctionPoints := junctionPointsAt edge jps bend1.x
    potentialGroupParents := match potentialParent with
      | some p => #[p]
      | none => #[] }

/-- Rust `CompactionContext::new_spline_vertical_segment` (Java `collectVerticalSegmentsSplines`)
for a non-straight spline segment with handle `splineSegment`, its bounding box and its first
edge. -/
def newSpline (segmentId : Nat) (hitbox : ElkRectangle) (edge : LEdgeId) (splineSegment : Nat)
    (jps : KVectorChain := #[]) : VerticalSegment :=
  { segmentId
    joinedSegmentIds := #[segmentId]
    junctionPoints := junctionPointsAt edge jps hitbox.x
    hitbox
    representedEdges := #[edge]
    representedEdgeKeys := #[edge]
    affectedSplineSegments := #[splineSegment] }

/-- `VerticalSegment.intersects(o)` (Rust `segments_intersect`): same x (fuzzy) and overlapping y
ranges (fuzzy). -/
def intersects (a b : VerticalSegment) : Bool :=
  CompareFuzzy.eq a.hitbox.x b.hitbox.x &&
    !(CompareFuzzy.lt (a.hitbox.y + a.hitbox.height) b.hitbox.y ||
      CompareFuzzy.lt (b.hitbox.y + b.hitbox.height) a.hitbox.y)

/-- `VerticalSegment.joinWith(other)` (Rust `join_segments(left, right)`): `left` becomes the union
of both segments. -/
def joinWith (left right : VerticalSegment) : VerticalSegment :=
  let x := fmin left.hitbox.x right.hitbox.x
  let y := fmin left.hitbox.y right.hitbox.y
  let maxX := fmax (left.hitbox.x + left.hitbox.width) (right.hitbox.x + right.hitbox.width)
  let maxY := fmax (left.hitbox.y + left.hitbox.height) (right.hitbox.y + right.hitbox.height)
  { left with
    joinedSegmentIds := extendUnique left.joinedSegmentIds right.joinedSegmentIds
    constraintTargetIds := extendUnique left.constraintTargetIds right.constraintTargetIds
    representedEdges := left.representedEdges ++ right.representedEdges
    representedEdgeKeys := extendUnique left.representedEdgeKeys right.representedEdgeKeys
    ignoreSpacingUp := left.ignoreSpacingUp || right.ignoreSpacingUp
    ignoreSpacingDown := left.ignoreSpacingDown || right.ignoreSpacingDown
    port := if left.port.isNone then right.port else left.port
    affectedBends := left.affectedBends ++ right.affectedBends
    affectedSplineSegments := left.affectedSplineSegments ++ right.affectedSplineSegments
    junctionPoints := left.junctionPoints ++ right.junctionPoints
    potentialGroupParents := left.potentialGroupParents ++ right.potentialGroupParents
    hitbox := ElkRectangle.ofValues x y (maxX - x) (maxY - y) }

/-- Guava `DoubleMath.fuzzyCompare(a, b, tolerance)`: `0` when `|a - b| <= tolerance`, `a == b` or
both are NaN; else `a < b`, `a > b`, and finally a NaN is larger than a number. -/
def fuzzyCmp (left right : Float) : Ordering :=
  if (left - right).abs <= CompareFuzzy.TOLERANCE || left == right || (left != left && right != right) then .eq
  else if left < right then .lt
  else if left > right then .gt
  else if left != left then .gt else .lt

/-- `VerticalSegment.compareTo(o)`: `DoubleMath.fuzzyCompare` of the x coordinates (tolerance
`CompareFuzzy.TOLERANCE`), on `0` `Double.compare` of the y coordinates. Fuzzy equality is not
transitive, so this is not a consistent order (elk-rs: `partial_cmp` for both). -/
def compareTo (a b : VerticalSegment) : Ordering :=
  let xCmp := fuzzyCmp a.hitbox.x b.hitbox.x
  if xCmp != .eq then xCmp else Float.compareJava a.hitbox.y b.hitbox.y

end VerticalSegment

end Elk.Alg.Layered.Intermediate.Compaction
