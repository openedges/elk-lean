import Elk.Alg.Layered.P5Edges.Orthogonal.HyperEdgeSegmentDependency
import Elk.Core.Util.Random
import Elk.Core.Util.Sort
/-!
# `org.eclipse.elk.alg.layered.p5edges.orthogonal.HyperEdgeCycleDetector`

Port of elk-rs `p5edges/orthogonal/hyper_edge_cycle_detector.rs`: finds the dependencies that close
cycles in the segment dependency graph with the Eades–Lin–Smyth linear ordering heuristic (sinks get
marks counting down from `n - 1`, sources and max-outflow segments marks counting up from `n + 1`;
ties of the max-outflow choice are broken with the given `Random`). Every dependency pointing from a
higher to a lower mark is returned.

The source/sink queues (`VecDeque`) are arrays with a head index; like Rust they may contain a
segment more than once. Segment identity (`Rc::ptr_eq`) is the arena index.
-/
namespace Elk.Alg.Layered.P5Edges.Orthogonal

open Elk.Graph Elk.Core.Util

namespace HyperEdgeCycleDetector

/-- Working state of one detection run. -/
private structure State where
  g : SegmentGraph
  sources : Array Nat := #[]
  sourcesHead : Nat := 0
  sinks : Array Nat := #[]
  sinksHead : Nat := 0

/-- Sum of the weights of the dependencies `deps` (only critical ones when `criticalOnly`). -/
private def sumWeights (g : SegmentGraph) (deps : Array Nat) (criticalOnly : Bool) : Int :=
  deps.foldl (init := 0) fun acc d =>
    let dep := g.dependency d
    if !criticalOnly || dep.dependencyType == .critical then acc + dep.weight else acc

/-- `initialize(segments, sources, sinks, criticalOnly)`: marks `-1, -2, …`, (critical) in/out
weights, and the initial sinks (no outgoing weight) and sources (else no incoming weight). -/
private def initializeState (g : SegmentGraph) (criticalOnly : Bool) : State := Id.run do
  let mut st : State := { g := g }
  let mut nextMark : Int := -1
  for i in [0:g.segments.size] do
    let seg := st.g.segment i
    let criticalInWeight := sumWeights st.g seg.incomingSegmentDependencies true
    let criticalOutWeight := sumWeights st.g seg.outgoingSegmentDependencies true
    let mut inWeight := criticalInWeight
    let mut outWeight := criticalOutWeight
    if !criticalOnly then
      inWeight := sumWeights st.g seg.incomingSegmentDependencies false
      outWeight := sumWeights st.g seg.outgoingSegmentDependencies false
    let mark := nextMark
    nextMark := nextMark - 1
    let (inW, outW) := (inWeight, outWeight)
    st := { st with g := st.g.modifySegment i fun s => { s with
      mark := mark, inDepWeight := inW, criticalInDepWeight := criticalInWeight,
      outDepWeight := outW, criticalOutDepWeight := criticalOutWeight } }
    if outWeight == 0 then
      st := { st with sinks := st.sinks.push i }
    else if inWeight == 0 then
      st := { st with sources := st.sources.push i }
  return st

/-- `updateNeighbors(node, sources, sinks, criticalOnly)`: removes the node's (critical) dependency
weights from its unmarked neighbours and queues neighbours that became sources or sinks. -/
private def updateNeighbors (st : State) (node : Nat) (criticalOnly : Bool) : State := Id.run do
  let mut st := st
  let nodeSeg := st.g.segment node
  for d in nodeSeg.outgoingSegmentDependencies do
    let dep := st.g.dependency d
    if !criticalOnly || dep.dependencyType == .critical then
      if let some target := dep.target then
        let tgt := st.g.segment target
        if tgt.mark < 0 && dep.weight > 0 then
          let newInWeight := tgt.inDepWeight - dep.weight
          let newCritical := if dep.dependencyType == .critical then tgt.criticalInDepWeight - dep.weight
            else tgt.criticalInDepWeight
          st := { st with g := st.g.modifySegment target fun s =>
            { s with inDepWeight := newInWeight, criticalInDepWeight := newCritical } }
          if newInWeight <= 0 && tgt.outDepWeight > 0 then
            st := { st with sources := st.sources.push target }
  for d in nodeSeg.incomingSegmentDependencies do
    let dep := st.g.dependency d
    if !criticalOnly || dep.dependencyType == .critical then
      if let some source := dep.source then
        let src := st.g.segment source
        if src.mark < 0 && dep.weight > 0 then
          let newOutWeight := src.outDepWeight - dep.weight
          let newCritical := if dep.dependencyType == .critical then src.criticalOutDepWeight - dep.weight
            else src.criticalOutDepWeight
          st := { st with g := st.g.modifySegment source fun s =>
            { s with outDepWeight := newOutWeight, criticalOutDepWeight := newCritical } }
          if newOutWeight <= 0 && src.inDepWeight > 0 then
            st := { st with sinks := st.sinks.push source }
  return st

/-- Rust `remove_segment(list, segment)`: removes the first occurrence (order preserving). -/
private def removeSegment (list : Array Nat) (segment : Nat) : Array Nat :=
  match list.findIdx? (· == segment) with
  | some pos => list.eraseIdx! pos
  | none => list

/-- Sets the mark of segment `i`. -/
private def setMark (st : State) (i : Nat) (mark : Int) : State :=
  { st with g := st.g.modifySegment i fun s => { s with mark := mark } }

/-- `computeLinearOrderingMarks(segments, sources, sinks, criticalOnly, random)`. -/
private def computeLinearOrderingMarks (st : State) (criticalOnly : Bool) (random : Random) : State × Random := Id.run do
  let mut st := st
  let mut random := random
  let n := st.g.segments.size
  let mut unprocessed : Array Nat := stableSort (Array.range n) fun a b =>
    HyperEdgeSegment.compareByMark (st.g.segment a) (st.g.segment b)
  let markBase : Int := n
  let mut nextSinkMark : Int := markBase - 1
  let mut nextSourceMark : Int := markBase + 1
  while !unprocessed.isEmpty do
    while st.sinksHead < st.sinks.size do
      let sink := st.sinks[st.sinksHead]!
      st := { st with sinksHead := st.sinksHead + 1 }
      unprocessed := removeSegment unprocessed sink
      st := setMark st sink nextSinkMark
      nextSinkMark := nextSinkMark - 1
      st := updateNeighbors st sink criticalOnly
    while st.sourcesHead < st.sources.size do
      let source := st.sources[st.sourcesHead]!
      st := { st with sourcesHead := st.sourcesHead + 1 }
      unprocessed := removeSegment unprocessed source
      st := setMark st source nextSourceMark
      nextSourceMark := nextSourceMark + 1
      st := updateNeighbors st source criticalOnly
    let mut maxOutflow : Int := -2147483648
    let mut maxSegments : Array Nat := #[]
    for i in unprocessed do
      let seg := st.g.segment i
      if !criticalOnly && seg.criticalOutDepWeight > 0 && seg.criticalInDepWeight <= 0 then
        maxSegments := #[i]
        break
      let outflow := seg.outDepWeight - seg.inDepWeight
      if outflow >= maxOutflow then
        if outflow > maxOutflow then
          maxSegments := #[]
          maxOutflow := outflow
        maxSegments := maxSegments.push i
    if !maxSegments.isEmpty then
      let (pick, r) := random.nextInt (maxSegments.size : Int)
      random := r
      let maxNode := maxSegments[pick.toNat]!
      unprocessed := removeSegment unprocessed maxNode
      st := setMark st maxNode nextSourceMark
      nextSourceMark := nextSourceMark + 1
      st := updateNeighbors st maxNode criticalOnly
  let shiftBase : Int := (n : Int) + 1
  for i in [0:n] do
    if (st.g.segment i).mark < markBase then
      st := { st with g := st.g.modifySegment i fun s => { s with mark := s.mark + shiftBase } }
  return (st, random)

/-- `detectCycles(segments, criticalOnly, random)`: the dependencies (indices, in segment order and
then outgoing-list order) that point from a higher to a lower linear-ordering mark. Returns them with
the updated arena (marks, weights) and the advanced generator. -/
def detectCycles (g : SegmentGraph) (criticalOnly : Bool) (random : Random) : Array Nat × SegmentGraph × Random := Id.run do
  let st := initializeState g criticalOnly
  let (st, random) := computeLinearOrderingMarks st criticalOnly random
  let g := st.g
  let mut result : Array Nat := #[]
  for source in g.segments do
    for d in source.outgoingSegmentDependencies do
      let dep := g.dependency d
      if !criticalOnly || dep.dependencyType == .critical then
        if let some target := dep.target then
          if source.mark > (g.segment target).mark then
            result := result.push d
  return (result, g, random)

end HyperEdgeCycleDetector

end Elk.Alg.Layered.P5Edges.Orthogonal
