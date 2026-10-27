import Elk.Alg.Layered.P5Edges.Orthogonal.HyperEdgeSegmentDependency
import Elk.Core.Util.Random
/-!
# `org.eclipse.elk.alg.layered.p5edges.orthogonal.HyperEdgeCycleDetector`

Port of elk-rs `p5edges/orthogonal/hyper_edge_cycle_detector.rs`: finds the dependencies that close
cycles in the segment dependency graph with the Eades–Lin–Smyth linear ordering heuristic (sinks get
marks counting down from `n - 1`, sources and max-outflow segments marks counting up from `n + 1`;
ties of the max-outflow choice are broken with the given `Random`). Every dependency pointing from a
higher to a lower mark is returned.

The source/sink queues (`VecDeque`) are arrays with a head index; like Rust they may contain a
segment more than once. Segment identity (`Rc::ptr_eq`) is the arena index.

Representation: the run reads the dependency structure of the `SegmentGraph` (unchanged during the
run) and keeps the per-segment marks and weights in local arrays (`State`), which are written back
to the segments at the end (Rust stores them in the segments). Rust's `unprocessed` list (the
segments sorted by their initial marks `-1, -2, …`, i.e. in reverse index order, shrunk by the
order-preserving `remove_segment`) is the array `order` plus a membership flag per segment: removing
clears the flag, iterating skips cleared entries, so the iteration order is the list order.
-/
namespace Elk.Alg.Layered.P5Edges.Orthogonal

open Elk.Graph Elk.Core.Util

namespace HyperEdgeCycleDetector

/-- Working state of one detection run (per segment index). -/
private structure State where
  /-- `mark`. -/
  mark : Array Int
  /-- `in_weight`. -/
  inWeight : Array Int
  /-- `critical_in_weight`. -/
  criticalInWeight : Array Int
  /-- `out_weight`. -/
  outWeight : Array Int
  /-- `critical_out_weight`. -/
  criticalOutWeight : Array Int
  /-- `sources` queue (`sourcesHead` = front). -/
  sources : Array Nat := #[]
  sourcesHead : Nat := 0
  /-- `sinks` queue (`sinksHead` = front). -/
  sinks : Array Nat := #[]
  sinksHead : Nat := 0
  /-- Membership in Rust's `unprocessed` list. -/
  unprocessed : Array Bool
  /-- Number of segments in `unprocessed`. -/
  unprocessedCount : Nat
  /-- `unprocessed` in list order (may still hold removed segments). -/
  order : Array Nat
  /-- `next_sink_mark`. -/
  nextSinkMark : Int
  /-- `next_source_mark`. -/
  nextSourceMark : Int

/-- The dependency lists a run considers, per segment: the segments' outgoing and incoming lists, or
(critical-only runs) their critical entries in list order. Every function below visits the
dependencies in list order and skips the non-critical ones of a critical-only run, so iterating the
filtered lists is the same. -/
private structure Lists where
  outgoing : Array (Array Nat)
  incoming : Array (Array Nat)

/-- The lists of a run on `g`. -/
private def Lists.of (g : SegmentGraph) (criticalOnly : Bool) : Lists :=
  if criticalOnly then
    { outgoing := g.segments.map fun seg => seg.outgoingSegmentDependencies.filter g.depIsCritical
      incoming := g.segments.map fun seg => seg.incomingSegmentDependencies.filter g.depIsCritical }
  else
    { outgoing := g.segments.map (·.outgoingSegmentDependencies)
      incoming := g.segments.map (·.incomingSegmentDependencies) }

/-- Sums of the weights of all and of the critical dependencies among `deps[k:]` (one pass). -/
private partial def sumWeights (g : SegmentGraph) (deps : Array Nat) (k : Nat) (total critical : Int) : Int × Int :=
  if h : k < deps.size then
    let d := deps[k]
    let weight := g.depWeight d
    sumWeights g deps (k + 1) (total + weight) (if g.depIsCritical d then critical + weight else critical)
  else (total, critical)

/-- Per-segment weights of `initializeState`. -/
private structure Weights where
  inWeight : Array Int
  criticalInWeight : Array Int
  outWeight : Array Int
  criticalOutWeight : Array Int

/-- Appends the (critical) in/out weights of the segments `i, i + 1, …` (`in`/`out` = the critical
weights when `criticalOnly`). -/
private partial def collectWeights (g : SegmentGraph) (ls : Lists) (criticalOnly : Bool) (i : Nat) (w : Weights) :
    Weights :=
  if h : i < ls.outgoing.size then
    let (inTotal, inCritical) := sumWeights g ls.incoming[i]! 0 0 0
    let (outTotal, outCritical) := sumWeights g ls.outgoing[i] 0 0 0
    match w with
    | ⟨inWeight, criticalInWeight, outWeight, criticalOutWeight⟩ =>
      collectWeights g ls criticalOnly (i + 1)
        ⟨inWeight.push (if criticalOnly then inCritical else inTotal), criticalInWeight.push inCritical,
          outWeight.push (if criticalOnly then outCritical else outTotal), criticalOutWeight.push outCritical⟩
  else w

/-- `initialize(segments, sources, sinks, criticalOnly)`: marks `-1, -2, …`, (critical) in/out
weights, and the initial sinks (no outgoing weight) and sources (else no incoming weight), both in
segment order. -/
private def initializeState (g : SegmentGraph) (ls : Lists) (criticalOnly : Bool) : State :=
  let n := g.segments.size
  let ⟨inWeight, criticalInWeight, outWeight, criticalOutWeight⟩ := collectWeights g ls criticalOnly 0
    ⟨Array.emptyWithCapacity n, Array.emptyWithCapacity n, Array.emptyWithCapacity n, Array.emptyWithCapacity n⟩
  let sinks := (Array.range n).filter fun i => outWeight[i]! == 0
  let sources := (Array.range n).filter fun i => outWeight[i]! != 0 && inWeight[i]! == 0
  { mark := (Array.range n).map fun (i : Nat) => -1 - (i : Int), inWeight, criticalInWeight, outWeight, criticalOutWeight,
    sources, sinks, unprocessed := Array.replicate n true, unprocessedCount := n,
    -- Rust `unprocessed.sort_by_key(mark)` with the distinct marks `-1 - i`: reverse index order
    order := (Array.range n).reverse,
    nextSinkMark := (n : Int) - 1, nextSourceMark := (n : Int) + 1 }

/-- Outgoing half of `updateNeighbors`: for the dependencies `deps[k:]` of the processed node, removes
the (critical) weight from unmarked targets and queues those that became sources. -/
private partial def updateTargets (g : SegmentGraph) (deps : Array Nat) (criticalOnly : Bool) (k : Nat) (st : State) :
    State :=
  if h : k < deps.size then
    let d := deps[k]
    let critical := g.depIsCritical d
    let targetCode := g.depTargetCode d
    if (!criticalOnly || critical) && targetCode != 0 then
      let target := targetCode - 1
      let weight := g.depWeight d
      if st.mark[target]! < 0 && weight > 0 then
        let newInWeight := st.inWeight[target]! - weight
        let st := { st with inWeight := st.inWeight.set! target newInWeight }
        let st := if critical then
            { st with criticalInWeight := st.criticalInWeight.set! target (st.criticalInWeight[target]! - weight) }
          else st
        let st := if newInWeight <= 0 && st.outWeight[target]! > 0 then { st with sources := st.sources.push target }
          else st
        updateTargets g deps criticalOnly (k + 1) st
      else updateTargets g deps criticalOnly (k + 1) st
    else updateTargets g deps criticalOnly (k + 1) st
  else st

/-- Incoming half of `updateNeighbors`: removes the (critical) weight from unmarked sources of
`deps[k:]` and queues those that became sinks. -/
private partial def updateSources (g : SegmentGraph) (deps : Array Nat) (criticalOnly : Bool) (k : Nat) (st : State) :
    State :=
  if h : k < deps.size then
    let d := deps[k]
    let critical := g.depIsCritical d
    let sourceCode := g.depSourceCode d
    if (!criticalOnly || critical) && sourceCode != 0 then
      let source := sourceCode - 1
      let weight := g.depWeight d
      if st.mark[source]! < 0 && weight > 0 then
        let newOutWeight := st.outWeight[source]! - weight
        let st := { st with outWeight := st.outWeight.set! source newOutWeight }
        let st := if critical then
            { st with criticalOutWeight := st.criticalOutWeight.set! source (st.criticalOutWeight[source]! - weight) }
          else st
        let st := if newOutWeight <= 0 && st.inWeight[source]! > 0 then { st with sinks := st.sinks.push source }
          else st
        updateSources g deps criticalOnly (k + 1) st
      else updateSources g deps criticalOnly (k + 1) st
    else updateSources g deps criticalOnly (k + 1) st
  else st

/-- `updateNeighbors(node, sources, sinks, criticalOnly)`: removes the node's (critical) dependency
weights from its unmarked neighbours and queues neighbours that became sources or sinks. -/
private def updateNeighbors (g : SegmentGraph) (ls : Lists) (st : State) (node : Nat) (criticalOnly : Bool) : State :=
  if h : node < ls.outgoing.size then
    let st := updateTargets g ls.outgoing[node] criticalOnly 0 st
    updateSources g ls.incoming[node]! criticalOnly 0 st
  else st

/-- Rust `remove_segment(unprocessed, segment)` followed by `segment.mark = mark` and
`updateNeighbors(segment)`. -/
private def processSegment (g : SegmentGraph) (ls : Lists) (st : State) (segment : Nat) (mark : Int) (criticalOnly : Bool) :
    State :=
  let st := if st.unprocessed[segment]! then
      { st with unprocessed := st.unprocessed.set! segment false, unprocessedCount := st.unprocessedCount - 1 }
    else st
  let st := { st with mark := st.mark.set! segment mark }
  updateNeighbors g ls st segment criticalOnly

/-- `while let Some(sink) = sinks.pop_front()`: processes the queued sinks (marks counting down). -/
private partial def drainSinks (g : SegmentGraph) (ls : Lists) (criticalOnly : Bool) (st : State) : State :=
  if h : st.sinksHead < st.sinks.size then
    let sink := st.sinks[st.sinksHead]
    let mark := st.nextSinkMark
    let st := { st with sinksHead := st.sinksHead + 1, nextSinkMark := mark - 1 }
    drainSinks g ls criticalOnly (processSegment g ls st sink mark criticalOnly)
  else st

/-- `while let Some(source) = sources.pop_front()`: processes the queued sources (marks counting up). -/
private partial def drainSources (g : SegmentGraph) (ls : Lists) (criticalOnly : Bool) (st : State) : State :=
  if h : st.sourcesHead < st.sources.size then
    let source := st.sources[st.sourcesHead]
    let mark := st.nextSourceMark
    let st := { st with sourcesHead := st.sourcesHead + 1, nextSourceMark := mark + 1 }
    drainSources g ls criticalOnly (processSegment g ls st source mark criticalOnly)
  else st

/-- The max-outflow scan over `unprocessed` (entries `order[k:]`): the first segment with critical
outgoing but no critical incoming weight (when not `criticalOnly`), else every segment with the
maximal `out_weight - in_weight`, in list order. -/
private partial def maxOutflowSegments (st : State) (criticalOnly : Bool) (k : Nat) (maxOutflow : Int)
    (maxSegments : Array Nat) : Array Nat :=
  if h : k < st.order.size then
    let i := st.order[k]
    if st.unprocessed[i]! then
      if !criticalOnly && st.criticalOutWeight[i]! > 0 && st.criticalInWeight[i]! <= 0 then #[i]
      else
        let outflow := st.outWeight[i]! - st.inWeight[i]!
        if outflow > maxOutflow then maxOutflowSegments st criticalOnly (k + 1) outflow #[i]
        else if outflow == maxOutflow then maxOutflowSegments st criticalOnly (k + 1) maxOutflow (maxSegments.push i)
        else maxOutflowSegments st criticalOnly (k + 1) maxOutflow maxSegments
    else maxOutflowSegments st criticalOnly (k + 1) maxOutflow maxSegments
  else maxSegments

/-- Rust `i32::MIN`, the initial maximal outflow. -/
private def I32_MIN : Int := -2147483648

/-- Drops the removed entries of `order` (keeping the list order). -/
private def compactOrder (order : Array Nat) (unprocessed : Array Bool) : Array Nat :=
  order.filter fun i => unprocessed[i]!

/-- The main loop of `computeLinearOrderingMarks` (`while !unprocessed.is_empty()`). -/
private partial def linearOrderingLoop (g : SegmentGraph) (ls : Lists) (criticalOnly : Bool) (st : State)
    (random : Random) : State × Random :=
  if st.unprocessedCount == 0 then (st, random)
  else
    let st := drainSources g ls criticalOnly (drainSinks g ls criticalOnly st)
    -- drop the removed entries once they make up more than half of the scanned list
    let st := if st.order.size > 2 * st.unprocessedCount then
        { st with order := compactOrder st.order st.unprocessed }
      else st
    let maxSegments := maxOutflowSegments st criticalOnly 0 I32_MIN #[]
    if maxSegments.isEmpty then linearOrderingLoop g ls criticalOnly st random
    else
      let (pick, random) := random.nextInt (maxSegments.size : Int)
      let maxNode := maxSegments[pick.toNat]!
      let mark := st.nextSourceMark
      let st := processSegment g ls { st with nextSourceMark := mark + 1 } maxNode mark criticalOnly
      linearOrderingLoop g ls criticalOnly st random

/-- `computeLinearOrderingMarks(segments, sources, sinks, criticalOnly, random)`: the marks start at
`n - 1` (sinks, counting down) and `n + 1` (sources, counting up, see `initializeState`); finally the
marks below `n` are shifted by `n + 1`. -/
private def computeLinearOrderingMarks (g : SegmentGraph) (ls : Lists) (st : State) (criticalOnly : Bool)
    (random : Random) : State × Random :=
  let n := g.segments.size
  let markBase : Int := n
  let (st, random) := linearOrderingLoop g ls criticalOnly st random
  let shiftBase : Int := (n : Int) + 1
  let mark := st.mark.map fun m => if m < markBase then m + shiftBase else m
  ({ st with mark := mark }, random)

/-- The dependencies `deps[k:]` of `source` that point to a lower mark (critical ones only when
`criticalOnly`), appended to `result`. -/
private partial def collectBackward (g : SegmentGraph) (mark : Array Int) (sourceMark : Int) (deps : Array Nat)
    (criticalOnly : Bool) (k : Nat) (result : Array Nat) : Array Nat :=
  if h : k < deps.size then
    let d := deps[k]
    let targetCode := g.depTargetCode d
    if (!criticalOnly || g.depIsCritical d) && targetCode != 0 && sourceMark > mark[targetCode - 1]! then
      collectBackward g mark sourceMark deps criticalOnly (k + 1) (result.push d)
    else collectBackward g mark sourceMark deps criticalOnly (k + 1) result
  else result

/-- Writes the marks and weights of the run to the segments `i, i + 1, …`. -/
private partial def writeBack (segments : Array HyperEdgeSegment) (st : State) (i : Nat) : Array HyperEdgeSegment :=
  if i < segments.size then
    writeBack (segments.modify i (HyperEdgeSegment.setCycleData st.mark[i]! st.inWeight[i]! st.criticalInWeight[i]!
      st.outWeight[i]! st.criticalOutWeight[i]!)) st (i + 1)
  else segments

/-- `detectCycles(segments, criticalOnly, random)`: the dependencies (indices, in segment order and
then outgoing-list order) that point from a higher to a lower linear-ordering mark. Returns them with
the updated arena (marks, weights) and the advanced generator. -/
def detectCycles (g : SegmentGraph) (criticalOnly : Bool) (random : Random) : Array Nat × SegmentGraph × Random :=
  let ls := Lists.of g criticalOnly
  let st := initializeState g ls criticalOnly
  let (st, random) := computeLinearOrderingMarks g ls st criticalOnly random
  let result := ls.outgoing.size.fold (init := #[]) fun i h result =>
    collectBackward g st.mark st.mark[i]! ls.outgoing[i] criticalOnly 0 result
  (result, { g with segments := writeBack g.segments st 0 }, random)

end HyperEdgeCycleDetector

end Elk.Alg.Layered.P5Edges.Orthogonal
