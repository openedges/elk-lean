import Elk.Alg.Layered.P5Edges.Orthogonal.HyperEdgeSegment
import Elk.Graph.ArrayModify
/-!
# `org.eclipse.elk.alg.layered.p5edges.orthogonal.HyperEdgeSegmentDependency`

Port of elk-rs `p5edges/orthogonal/hyper_edge_segment_dependency.rs`: a weighted, regular or
critical dependency `source → target` between two hyperedge segments (the source must be routed
left of the target).

`SegmentGraph` is the local arena replacing Rust's `Rc<RefCell<…>>` object graph: the segments of
one routing run (`edge_segments`, in list order) plus every dependency ever created (a removed
dependency keeps its index with `source`/`target` cleared, exactly like the detached Rust object).
Segments list their dependencies by index. Like Rust (`swap_remove`, not Java's order-preserving
`List.remove`), removing a dependency from a segment's list moves the list's last element into the
freed position.

Representation: the dependencies are stored column-wise (`depSources`, `depTargets`, `depWeights`,
`depCritical`), so creating one allocates nothing; `dependency d` assembles the
`HyperEdgeSegmentDependency` value on demand. Every dependency also remembers its position in its
source's outgoing and its target's incoming list (`depSourcePos`, `depTargetPos`), which turns the
Rust `position` scan of `swap_remove` into a constant-time lookup (the list contents and order are
those of the scan: a dependency occurs at most once in a list).

`SegmentGraph.splitAt` is Java/Rust `HyperEdgeSegment.splitAt`; it is defined here because it removes
dependencies.
-/
namespace Elk.Alg.Layered.P5Edges.Orthogonal

open Elk.Graph Elk.Core.Util Elk.Alg.Layered.P5Edges.Orthogonal.Direction

/-- `HyperEdgeSegmentDependency.DependencyType`. -/
elk_enum DependencyType := regular critical

/-- `CRITICAL_DEPENDENCY_WEIGHT`. -/
def CRITICAL_DEPENDENCY_WEIGHT : Int := 1

/-- `HyperEdgeSegmentDependency`: `source`/`target` are segment indices (`none` once removed). -/
structure HyperEdgeSegmentDependency where
  /-- `dependency_type`. -/
  dependencyType : DependencyType := .regular
  /-- `source` (segment index). -/
  source : Option Nat := none
  /-- `target` (segment index). -/
  target : Option Nat := none
  /-- `weight`. -/
  weight : Int := 0
  deriving Inhabited

/-- The hyperedge segments of one routing run and their dependencies (see the module doc). -/
structure SegmentGraph where
  /-- Rust `edge_segments` (index = position in the list). -/
  segments : Array HyperEdgeSegment := #[]
  /-- Dependency `source` per dependency index (creation order): segment index `+ 1`, `0` = none. -/
  depSources : Array Nat := #[]
  /-- Dependency `target`: segment index `+ 1`, `0` = none. -/
  depTargets : Array Nat := #[]
  /-- Dependency `weight`. -/
  depWeights : Array Int := #[]
  /-- Whether the dependency is `CRITICAL`. -/
  depCritical : Array Bool := #[]
  /-- Position of the dependency in its source's outgoing list (meaningful while it has a source). -/
  depSourcePos : Array Nat := #[]
  /-- Position of the dependency in its target's incoming list (meaningful while it has a target). -/
  depTargetPos : Array Nat := #[]
  deriving Inhabited

namespace SegmentGraph

/-- The segment with index `i`. -/
@[inline] def segment (g : SegmentGraph) (i : Nat) : HyperEdgeSegment := g.segments[i]!

/-- Number of dependencies created so far. -/
@[inline] def dependencyCount (g : SegmentGraph) : Nat := g.depWeights.size

/-- Encoded source of dependency `d` (segment index `+ 1`, `0` = none). -/
@[inline] def depSourceCode (g : SegmentGraph) (d : Nat) : Nat := g.depSources[d]!

/-- Encoded target of dependency `d` (segment index `+ 1`, `0` = none). -/
@[inline] def depTargetCode (g : SegmentGraph) (d : Nat) : Nat := g.depTargets[d]!

/-- Weight of dependency `d`. -/
@[inline] def depWeight (g : SegmentGraph) (d : Nat) : Int := g.depWeights[d]!

/-- Whether dependency `d` is critical. -/
@[inline] def depIsCritical (g : SegmentGraph) (d : Nat) : Bool := g.depCritical[d]!

/-- Decodes a `depSources`/`depTargets` entry. -/
@[inline] def decodeSegment (code : Nat) : Option Nat :=
  match code with
  | 0 => none
  | i + 1 => some i

/-- The dependency with index `d`. -/
def dependency (g : SegmentGraph) (d : Nat) : HyperEdgeSegmentDependency :=
  { dependencyType := if g.depIsCritical d then .critical else .regular
    source := decodeSegment (g.depSourceCode d)
    target := decodeSegment (g.depTargetCode d)
    weight := g.depWeight d }

/-- All dependencies created so far (index = creation order). -/
def dependencies (g : SegmentGraph) : Array HyperEdgeSegmentDependency :=
  (Array.range g.dependencyCount).map g.dependency

/-- Updates segment `i` in place (a no-op for an invalid index). The update is only performed in
place when `f` is not inlined (see `HyperEdgeSegment.pushOutgoingDependency`). -/
@[inline] def modifySegment (g : SegmentGraph) (i : Nat) (f : HyperEdgeSegment → HyperEdgeSegment) : SegmentGraph :=
  { g with segments := g.segments.modifyIn i f }

/-- Appends a segment (Rust `edge_segments.push(segment)`); its index is the previous number of
segments. -/
def pushSegment (g : SegmentGraph) (s : HyperEdgeSegment) : SegmentGraph :=
  match g with
  | ⟨segments, sources, targets, weights, criticals, sourcePositions, targetPositions⟩ =>
    ⟨segments.push s, sources, targets, weights, criticals, sourcePositions, targetPositions⟩

/-- Appends a segment (Rust `edge_segments.push(segment)`), returning its index. -/
def addSegment (g : SegmentGraph) (s : HyperEdgeSegment) : SegmentGraph × Nat :=
  (g.pushSegment s, g.segments.size)

/-- Size of the outgoing dependency list of segment `i` (`0` for an invalid index). -/
@[inline] private def outgoingSize (g : SegmentGraph) (i : Nat) : Nat :=
  if h : i < g.segments.size then g.segments[i].outgoingSegmentDependencies.size else 0

/-- Size of the incoming dependency list of segment `i` (`0` for an invalid index). -/
@[inline] private def incomingSize (g : SegmentGraph) (i : Nat) : Nat :=
  if h : i < g.segments.size then g.segments[i].incomingSegmentDependencies.size else 0

/-- Position of `d` in `list`, Rust `iter().position(…)`: `hint` when it holds `d` (the recorded
position), else the first occurrence; `list.size` when absent. -/
@[inline] private def positionOf (list : Array Nat) (d hint : Nat) : Nat :=
  if h : hint < list.size then
    if list[hint] == d then hint else (list.findIdx? (· == d)).getD list.size
  else (list.findIdx? (· == d)).getD list.size

/-- Position of dependency `d` in the outgoing list of segment `i` (its size when absent). -/
@[inline] private def outgoingPosition (g : SegmentGraph) (i d : Nat) : Nat :=
  if h : i < g.segments.size then positionOf g.segments[i].outgoingSegmentDependencies d g.depSourcePos[d]!
  else 0

/-- Position of dependency `d` in the incoming list of segment `i` (its size when absent). -/
@[inline] private def incomingPosition (g : SegmentGraph) (i d : Nat) : Nat :=
  if h : i < g.segments.size then positionOf g.segments[i].incomingSegmentDependencies d g.depTargetPos[d]!
  else 0

/-- The dependency at position `pos` of segment `i`'s outgoing list (`0` past the end). -/
@[inline] private def outgoingAt (g : SegmentGraph) (i pos : Nat) : Nat :=
  if h : i < g.segments.size then g.segments[i].outgoingSegmentDependencies.getD pos 0 else 0

/-- The dependency at position `pos` of segment `i`'s incoming list (`0` past the end). -/
@[inline] private def incomingAt (g : SegmentGraph) (i pos : Nat) : Nat :=
  if h : i < g.segments.size then g.segments[i].incomingSegmentDependencies.getD pos 0 else 0

/-! The mutators below destructure the graph (`match g with ⟨…⟩ => ⟨…⟩`), rebuild it once and update
the segment array through the non-inlined helpers `pushOutgoingIn` …: after reads of the graph, an
inlined (branching) `Array.modify` makes the compiler copy the fields out and allocate a new graph
cell instead of reusing the unshared one. -/

/-- `segments[i].add_outgoing_dependency(d)` (in place). -/
@[noinline] private def pushOutgoingIn (segments : Array HyperEdgeSegment) (i d : Nat) : Array HyperEdgeSegment :=
  segments.modify i (HyperEdgeSegment.pushOutgoingDependency d)

/-- `segments[i].add_incoming_dependency(d)` (in place). -/
@[noinline] private def pushIncomingIn (segments : Array HyperEdgeSegment) (i d : Nat) : Array HyperEdgeSegment :=
  segments.modify i (HyperEdgeSegment.pushIncomingDependency d)

/-- `swap_remove(pos)` on the outgoing list of `segments[i]` (in place). -/
@[noinline] private def swapRemoveOutgoingIn (segments : Array HyperEdgeSegment) (i pos : Nat) : Array HyperEdgeSegment :=
  segments.modify i (HyperEdgeSegment.swapRemoveOutgoingAt pos)

/-- `swap_remove(pos)` on the incoming list of `segments[i]` (in place). -/
@[noinline] private def swapRemoveIncomingIn (segments : Array HyperEdgeSegment) (i pos : Nat) : Array HyperEdgeSegment :=
  segments.modify i (HyperEdgeSegment.swapRemoveIncomingAt pos)

/-- Swap-removes position `pos` of segment `i`'s outgoing list; `moved` (the last element) takes
position `pos`. -/
private def swapRemoveOutgoing (g : SegmentGraph) (i pos moved : Nat) : SegmentGraph :=
  match g with
  | ⟨segments, sources, targets, weights, criticals, sourcePositions, targetPositions⟩ =>
    ⟨swapRemoveOutgoingIn segments i pos, sources, targets, weights, criticals, sourcePositions.set! moved pos,
      targetPositions⟩

/-- Swap-removes position `pos` of segment `i`'s incoming list; `moved` (the last element) takes
position `pos`. -/
private def swapRemoveIncoming (g : SegmentGraph) (i pos moved : Nat) : SegmentGraph :=
  match g with
  | ⟨segments, sources, targets, weights, criticals, sourcePositions, targetPositions⟩ =>
    ⟨swapRemoveIncomingIn segments i pos, sources, targets, weights, criticals, sourcePositions,
      targetPositions.set! moved pos⟩

/-- `remove_outgoing_dependency(dep)` on segment `i`: Rust `swap_remove` of the first occurrence of `d`
(no-op when absent); the dependency moved into the hole (the former last one) gets its new position.
When `d` itself was last, its own recorded position is rewritten, which is harmless: the callers detach
or re-attach `d`. -/
def removeOutgoingDependency (g : SegmentGraph) (i d : Nat) : SegmentGraph :=
  let size := g.outgoingSize i
  let pos := g.outgoingPosition i d
  if pos < size then g.swapRemoveOutgoing i pos (g.outgoingAt i (size - 1)) else g

/-- `remove_incoming_dependency(dep)` on segment `i` (see `removeOutgoingDependency`). -/
def removeIncomingDependency (g : SegmentGraph) (i d : Nat) : SegmentGraph :=
  let size := g.incomingSize i
  let pos := g.incomingPosition i d
  if pos < size then g.swapRemoveIncoming i pos (g.incomingAt i (size - 1)) else g

/-- Sets the encoded source of `d` (no lists touched). -/
private def setSourceCode (g : SegmentGraph) (d code : Nat) : SegmentGraph :=
  match g with
  | ⟨segments, sources, targets, weights, criticals, sourcePositions, targetPositions⟩ =>
    ⟨segments, sources.set! d code, targets, weights, criticals, sourcePositions, targetPositions⟩

/-- Sets the encoded target of `d` (no lists touched). -/
private def setTargetCode (g : SegmentGraph) (d code : Nat) : SegmentGraph :=
  match g with
  | ⟨segments, sources, targets, weights, criticals, sourcePositions, targetPositions⟩ =>
    ⟨segments, sources, targets.set! d code, weights, criticals, sourcePositions, targetPositions⟩

/-- Appends `d` to the outgoing list of segment `s` and makes `s` its source. -/
private def attachSource (g : SegmentGraph) (d s : Nat) : SegmentGraph :=
  let pos := g.outgoingSize s
  match g with
  | ⟨segments, sources, targets, weights, criticals, sourcePositions, targetPositions⟩ =>
    ⟨pushOutgoingIn segments s d, sources.set! d (s + 1), targets, weights, criticals,
      sourcePositions.set! d pos, targetPositions⟩

/-- Appends `d` to the incoming list of segment `t` and makes `t` its target. -/
private def attachTarget (g : SegmentGraph) (d t : Nat) : SegmentGraph :=
  let pos := g.incomingSize t
  match g with
  | ⟨segments, sources, targets, weights, criticals, sourcePositions, targetPositions⟩ =>
    ⟨pushIncomingIn segments t d, sources, targets.set! d (t + 1), weights, criticals,
      sourcePositions, targetPositions.set! d pos⟩

/-- `HyperEdgeSegmentDependency::new(type, weight)` followed by `set_source(source)` and
`set_target(target)`: appends the dependency to the outgoing list of `source`, then to the incoming
list of `target`. Its index is the previous `dependencyCount`. -/
def addDependency (g : SegmentGraph) (critical : Bool) (source target : Nat) (weight : Int) : SegmentGraph :=
  let d := g.dependencyCount
  -- (both sizes can be read up front: even a self dependency goes to two different lists)
  let sourcePos := g.outgoingSize source
  let targetPos := g.incomingSize target
  match g with
  | ⟨segments, sources, targets, weights, criticals, sourcePositions, targetPositions⟩ =>
    let segments := pushOutgoingIn segments source d
    let segments := pushIncomingIn segments target d
    ⟨segments, sources.push (source + 1), targets.push (target + 1), weights.push weight, criticals.push critical,
      sourcePositions.push sourcePos, targetPositions.push targetPos⟩

/-- `createAndAddRegular(source, target, weight)`: a regular dependency (index returned). -/
def createAndAddRegular (g : SegmentGraph) (source target : Nat) (weight : Int) : SegmentGraph × Nat :=
  (g.addDependency false source target weight, g.dependencyCount)

/-- `createAndAddCritical(source, target)`: a critical dependency of weight `CRITICAL_DEPENDENCY_WEIGHT`
(index returned). -/
def createAndAddCritical (g : SegmentGraph) (source target : Nat) : SegmentGraph × Nat :=
  (g.addDependency true source target CRITICAL_DEPENDENCY_WEIGHT, g.dependencyCount)

/-- `HyperEdgeSegmentDependency.remove()`: detaches the dependency from both segments. -/
def removeDependency (g : SegmentGraph) (d : Nat) : SegmentGraph :=
  let sourceCode := g.depSourceCode d
  let targetCode := g.depTargetCode d
  let g := if sourceCode != 0 then g.removeOutgoingDependency (sourceCode - 1) d else g
  let g := if targetCode != 0 then g.removeIncomingDependency (targetCode - 1) d else g
  (g.setSourceCode d 0).setTargetCode d 0

/-- `HyperEdgeSegmentDependency.reverse()`: swaps source and target (removed from the old lists,
appended to the new ones: first the old target's outgoing, then the old source's incoming list). -/
def reverseDependency (g : SegmentGraph) (d : Nat) : SegmentGraph :=
  let sourceCode := g.depSourceCode d
  let targetCode := g.depTargetCode d
  let g := if sourceCode != 0 then g.removeOutgoingDependency (sourceCode - 1) d else g
  let g := if targetCode != 0 then g.removeIncomingDependency (targetCode - 1) d else g
  let g := (g.setSourceCode d targetCode).setTargetCode d sourceCode
  let g := if targetCode != 0 then g.attachSource d (targetCode - 1) else g
  if sourceCode != 0 then g.attachTarget d (sourceCode - 1) else g

/-- `HyperEdgeSegment.splitAt(splitPosition)` (Rust `HyperEdgeSegment::split_at`): segment `i` keeps its
incoming coordinates and gets the single outgoing coordinate `splitPosition`; the new split partner
(appended to the arena, index returned) gets `splitPosition` as incoming and the old outgoing
coordinates. All dependencies of segment `i` are removed (incoming first, then outgoing, in list
order of the copies taken before the removal). -/
def splitAt (g : SegmentGraph) (i : Nat) (splitPosition : Float) : SegmentGraph × Nat :=
  let seg := g.segment i
  let partnerIdx := g.segments.size
  let partner : HyperEdgeSegment :=
    { routingDirection := seg.routingDirection
      splitPartner := some i
      outgoingConnectionCoordinates := seg.outgoingConnectionCoordinates
      incomingConnectionCoordinates := #[splitPosition] }
  let incomingDeps := seg.incomingSegmentDependencies
  let outgoingDeps := seg.outgoingSegmentDependencies
  let g := { g with segments := g.segments.push partner.recomputeExtent }
  let g := g.modifySegment i fun s =>
    ({ s with splitPartner := some partnerIdx, outgoingConnectionCoordinates := #[splitPosition] } : HyperEdgeSegment).recomputeExtent
  let g := incomingDeps.foldl (fun g d => g.removeDependency d) g
  let g := outgoingDeps.foldl (fun g d => g.removeDependency d) g
  (g, partnerIdx)

end SegmentGraph

end Elk.Alg.Layered.P5Edges.Orthogonal
