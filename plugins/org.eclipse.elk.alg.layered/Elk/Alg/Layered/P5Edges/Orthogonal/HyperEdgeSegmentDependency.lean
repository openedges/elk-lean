import Elk.Alg.Layered.P5Edges.Orthogonal.HyperEdgeSegment
/-!
# `org.eclipse.elk.alg.layered.p5edges.orthogonal.HyperEdgeSegmentDependency`

Port of elk-rs `p5edges/orthogonal/hyper_edge_segment_dependency.rs`: a weighted, regular or
critical dependency `source → target` between two hyperedge segments (the source must be routed
left of the target).

`SegmentGraph` is the local arena replacing Rust's `Rc<RefCell<…>>` object graph: the segments of
one routing run (`edge_segments`, in list order) plus every dependency ever created (a removed
dependency stays in `dependencies` with `source`/`target` cleared, exactly like the detached Rust
object). Segments list their dependencies by index. Like Rust (`swap_remove`, not Java's
order-preserving `List.remove`), removing a dependency from a segment's list moves the list's last
element into the freed position.

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
  /-- All dependencies created so far (index = creation order). -/
  dependencies : Array HyperEdgeSegmentDependency := #[]
  deriving Inhabited

namespace SegmentGraph

/-- The segment with index `i`. -/
@[inline] def segment (g : SegmentGraph) (i : Nat) : HyperEdgeSegment := g.segments[i]!

/-- The dependency with index `d`. -/
@[inline] def dependency (g : SegmentGraph) (d : Nat) : HyperEdgeSegmentDependency := g.dependencies[d]!

/-- Updates segment `i` in place. -/
@[inline] def modifySegment (g : SegmentGraph) (i : Nat) (f : HyperEdgeSegment → HyperEdgeSegment) : SegmentGraph :=
  { g with segments := g.segments.modify i f }

/-- Updates dependency `d` in place. -/
@[inline] def modifyDependency (g : SegmentGraph) (d : Nat) (f : HyperEdgeSegmentDependency → HyperEdgeSegmentDependency) :
    SegmentGraph :=
  { g with dependencies := g.dependencies.modify d f }

/-- Appends a segment (Rust `edge_segments.push(segment)`), returning its index. -/
def addSegment (g : SegmentGraph) (s : HyperEdgeSegment) : SegmentGraph × Nat :=
  ({ g with segments := g.segments.push s }, g.segments.size)

/-- Rust `Vec::swap_remove` of the first occurrence of `d` (no-op when absent). -/
private def swapRemove (deps : Array Nat) (d : Nat) : Array Nat :=
  match deps.findIdx? (· == d) with
  | some pos =>
    let last := deps.size - 1
    (deps.set! pos deps[last]!).pop
  | none => deps

/-- `remove_outgoing_dependency(dep)` on segment `i`. -/
def removeOutgoingDependency (g : SegmentGraph) (i d : Nat) : SegmentGraph :=
  g.modifySegment i fun s => { s with outgoingSegmentDependencies := swapRemove s.outgoingSegmentDependencies d }

/-- `remove_incoming_dependency(dep)` on segment `i`. -/
def removeIncomingDependency (g : SegmentGraph) (i d : Nat) : SegmentGraph :=
  g.modifySegment i fun s => { s with incomingSegmentDependencies := swapRemove s.incomingSegmentDependencies d }

/-- `set_source(dep, new_source)`: detaches from the old source's outgoing list, attaches to the new one. -/
private def setSource (g : SegmentGraph) (d : Nat) (newSource : Option Nat) : SegmentGraph :=
  let g := match (g.dependency d).source with
    | some old => g.removeOutgoingDependency old d
    | none => g
  let g := g.modifyDependency d fun x => { x with source := newSource }
  match newSource with
  | some s => g.modifySegment s fun x => { x with outgoingSegmentDependencies := x.outgoingSegmentDependencies.push d }
  | none => g

/-- `set_target(dep, new_target)`. -/
private def setTarget (g : SegmentGraph) (d : Nat) (newTarget : Option Nat) : SegmentGraph :=
  let g := match (g.dependency d).target with
    | some old => g.removeIncomingDependency old d
    | none => g
  let g := g.modifyDependency d fun x => { x with target := newTarget }
  match newTarget with
  | some t => g.modifySegment t fun x => { x with incomingSegmentDependencies := x.incomingSegmentDependencies.push d }
  | none => g

/-- `HyperEdgeSegmentDependency::new(type, weight)` followed by `set_source`/`set_target`. -/
private def createAndAdd (g : SegmentGraph) (type : DependencyType) (source target : Nat) (weight : Int) :
    SegmentGraph × Nat :=
  let d := g.dependencies.size
  let g := { g with dependencies := g.dependencies.push { dependencyType := type, weight := weight } }
  let g := g.setSource d (some source)
  (g.setTarget d (some target), d)

/-- `createAndAddRegular(source, target, weight)`: a regular dependency. -/
def createAndAddRegular (g : SegmentGraph) (source target : Nat) (weight : Int) : SegmentGraph × Nat :=
  g.createAndAdd .regular source target weight

/-- `createAndAddCritical(source, target)`: a critical dependency of weight `CRITICAL_DEPENDENCY_WEIGHT`. -/
def createAndAddCritical (g : SegmentGraph) (source target : Nat) : SegmentGraph × Nat :=
  g.createAndAdd .critical source target CRITICAL_DEPENDENCY_WEIGHT

/-- `HyperEdgeSegmentDependency.remove()`: detaches the dependency from both segments. -/
def removeDependency (g : SegmentGraph) (d : Nat) : SegmentGraph :=
  let dep := g.dependency d
  let g := match dep.source with
    | some s => g.removeOutgoingDependency s d
    | none => g
  let g := match dep.target with
    | some t => g.removeIncomingDependency t d
    | none => g
  g.modifyDependency d fun x => { x with source := none, target := none }

/-- `HyperEdgeSegmentDependency.reverse()`: swaps source and target (removed from the old lists,
appended to the new ones). -/
def reverseDependency (g : SegmentGraph) (d : Nat) : SegmentGraph :=
  let dep := g.dependency d
  let oldSource := dep.source
  let oldTarget := dep.target
  let g := match oldSource with
    | some s => g.removeOutgoingDependency s d
    | none => g
  let g := match oldTarget with
    | some t => g.removeIncomingDependency t d
    | none => g
  let g := g.modifyDependency d fun x => { x with source := oldTarget, target := oldSource }
  let g := match oldTarget with
    | some s => g.modifySegment s fun x => { x with outgoingSegmentDependencies := x.outgoingSegmentDependencies.push d }
    | none => g
  match oldSource with
  | some t => g.modifySegment t fun x => { x with incomingSegmentDependencies := x.incomingSegmentDependencies.push d }
  | none => g

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
  let g := { g with segments := g.segments.push partner.recomputeExtent }
  let g := g.modifySegment i fun s =>
    ({ s with splitPartner := some partnerIdx, outgoingConnectionCoordinates := #[splitPosition] } : HyperEdgeSegment).recomputeExtent
  let incomingDeps := seg.incomingSegmentDependencies
  let outgoingDeps := seg.outgoingSegmentDependencies
  let g := incomingDeps.foldl (fun g d => g.removeDependency d) g
  let g := outgoingDeps.foldl (fun g d => g.removeDependency d) g
  (g, partnerIdx)

end SegmentGraph

end Elk.Alg.Layered.P5Edges.Orthogonal
