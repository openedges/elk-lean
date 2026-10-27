import Std.Data.HashMap
import Elk.Alg.Layered.P5Edges.Orthogonal.HyperEdgeCycleDetector
import Elk.Alg.Layered.P5Edges.Orthogonal.HyperEdgeSegmentSplitter
import Elk.Alg.Layered.P5Edges.Orthogonal.Direction
import Elk.Core.Util.ElkTrace
/-!
# `org.eclipse.elk.alg.layered.p5edges.orthogonal.OrthogonalRoutingGenerator`

Port of elk-rs `p5edges/orthogonal/orthogonal_routing_generator.rs`: orthogonal routing of the edges
between two layers (or, for the hierarchical port router, between nodes and external port dummies).

`routeEdges`:
1. creates one hyperedge segment per set of connected output ports on the source side of the source
   layer, then of the target layer (`createHyperEdgeSegments`, depth-first over connected ports);
2. sets the critical conflict threshold to `0.2 ×` the minimum distance of distinct incoming
   (outgoing) connection coordinates and creates the pairwise dependencies (critical for coordinates
   closer than that threshold, else weighted by conflicts and crossings);
3. with at least two critical dependencies, breaks critical cycles by splitting segments
   (`HyperEdgeSegmentSplitter`), then reverses (weight > 0) or removes (weight 0) the dependencies
   closing non-critical cycles (`HyperEdgeCycleDetector`, with the graph's `RANDOM`);
4. assigns routing slots by topological numbering (segments with only outgoing connections and no
   outgoing dependencies are pulled to the right) and lets the routing strategy add bend and junction
   points; returns the number of slots used.

The segments live in a local `SegmentGraph` (see `HyperEdgeSegment`). Rust's `port_to_segment_map`
(`FxHashMap` keyed by port pointer) is only used for membership and lookup, so its iteration order is
irrelevant; it is a `Std.HashMap LPortId Nat`.

Random numbers: Rust clones the graph's `RANDOM` (an `Arc`-shared state, so the draws advance the
graph's generator) or uses a fresh `Random::default()` (seed 0, not stored) when it is missing; the
port does the same and writes the advanced generator back only in the first case.

Performance notes: the loops over segment pairs and dependencies are tail-recursive pure functions
that read the arena and thread only what they change (`SegmentGraph` updates are in place, see
`HyperEdgeSegmentDependency`); `topologicalNumbering` keeps slots and weights in local arrays;
`minimumDifference` sorts a `FloatArray` by the `total_cmp` key.
-/
namespace Elk.Alg.Layered.P5Edges.Orthogonal

open Elk.Graph Elk.Core.Math Elk.Core.Options Elk.Core.Util Elk.Alg.Layered.Graph Elk.Alg.Layered.Options
  Elk.Alg.Layered.P5Edges Elk.Alg.Layered.P5Edges.Orthogonal.Direction LayeredM

/-- `OrthogonalRoutingGenerator`. `criticalConflictThreshold` is recomputed by every `routeEdges` call. -/
structure OrthogonalRoutingGenerator where
  /-- `routing_direction`. -/
  routingDirection : RoutingDirection
  /-- `routing_strategy`. -/
  routingStrategy : BaseRoutingDirectionStrategy
  /-- `edge_spacing`. -/
  edgeSpacing : Float
  /-- `conflict_threshold` (`CONFLICT_THRESHOLD_FACTOR * edgeSpacing`). -/
  conflictThreshold : Float
  /-- `critical_conflict_threshold`. -/
  criticalConflictThreshold : Float := 0.0
  /-- `debug_prefix` (only used by the `ELK_TRACE_ORTHO` output). -/
  debugPrefix : Option String := none

namespace OrthogonalRoutingGenerator

/-- `CRITICAL_CONFLICTS_DETECTED`. -/
def CRITICAL_CONFLICTS_DETECTED : Int := -1
/-- `CONFLICT_THRESHOLD_FACTOR`. -/
def CONFLICT_THRESHOLD_FACTOR : Float := 0.5
/-- `CRITICAL_CONFLICT_THRESHOLD_FACTOR`. -/
def CRITICAL_CONFLICT_THRESHOLD_FACTOR : Float := 0.2
/-- `CONFLICT_PENALTY`. -/
def CONFLICT_PENALTY : Int := 1
/-- `CROSSING_PENALTY`. -/
def CROSSING_PENALTY : Int := 16

/-- `new OrthogonalRoutingGenerator(direction, edgeSpacing, debugPrefix)`. -/
def new (direction : RoutingDirection) (edgeSpacing : Float) (debugPrefix : Option String := none) :
    OrthogonalRoutingGenerator :=
  { routingDirection := direction
    routingStrategy := BaseRoutingDirectionStrategy.forRoutingDirection direction
    edgeSpacing := edgeSpacing
    conflictThreshold := CONFLICT_THRESHOLD_FACTOR * edgeSpacing
    criticalConflictThreshold := 0.0
    debugPrefix := debugPrefix }

/-- Loop of `countCrossings` from index `k` (tail recursive, no boxed loop state). -/
private partial def countCrossingsFrom (posis : Array Float) (start stop : Float) (k : Nat) (crossings : Int) : Int :=
  if h : k < posis.size then
    let pos := posis[k]
    if pos > stop then crossings
    else countCrossingsFrom posis start stop (k + 1) (if pos >= start then crossings + 1 else crossings)
  else crossings

/-- `countCrossings(posis, start, end)`: how many of the sorted `posis` lie in `[start, end]`. -/
def countCrossings (posis : Array Float) (start stop : Float) : Int :=
  countCrossingsFrom posis start stop 0 0

/-- Merge loop of `countConflicts` at indices `i`, `j` (values `pos1`, `pos2`); tail recursive with
unboxed `Float` parameters (a `while` loop would box its six-variable state on every step). -/
private partial def countConflictsFrom (posis1 posis2 : Array Float) (critical threshold : Float)
    (i j : Nat) (pos1 pos2 : Float) (conflicts : Int) : Int :=
  if pos1 > pos2 - critical && pos1 < pos2 + critical then CRITICAL_CONFLICTS_DETECTED
  else
    let conflicts := if pos1 > pos2 - threshold && pos1 < pos2 + threshold then conflicts + 1 else conflicts
    if pos1 <= pos2 && i + 1 < posis1.size then
      countConflictsFrom posis1 posis2 critical threshold (i + 1) j posis1[i + 1]! pos2 conflicts
    else if pos2 <= pos1 && j + 1 < posis2.size then
      countConflictsFrom posis1 posis2 critical threshold i (j + 1) pos1 posis2[j + 1]! conflicts
    else conflicts

/-- `countConflicts(posis1, posis2)`: merges the two sorted coordinate lists and counts pairs closer than
the conflict threshold; `CRITICAL_CONFLICTS_DETECTED` as soon as a pair is closer than the critical
threshold. Like Java/Rust, when one list is exhausted on equal values the other may still advance. -/
def countConflicts (gen : OrthogonalRoutingGenerator) (posis1 posis2 : Array Float) : Int :=
  if posis1.isEmpty || posis2.isEmpty then 0
  else countConflictsFrom posis1 posis2 gen.criticalConflictThreshold gen.conflictThreshold 0 0
    posis1[0]! posis2[0]! 0

/-- `countCrossings` loop with an unboxed count. -/
private partial def crossingCount (posis : Array Float) (start stop : Float) (k : Nat) (crossings : UInt64) : UInt64 :=
  if h : k < posis.size then
    let pos := posis[k]
    if pos > stop then crossings
    else crossingCount posis start stop (k + 1) (if pos >= start then crossings + 1 else crossings)
  else crossings

/-- `CRITICAL_CONFLICTS_DETECTED` of `conflictCount`. -/
private def CRITICAL_CONFLICTS : UInt64 := 0xFFFFFFFFFFFFFFFF

/-- `countConflictsFrom` with an unboxed count (`CRITICAL_CONFLICTS` for a critical conflict). -/
private partial def conflictCountFrom (posis1 posis2 : Array Float) (critical threshold : Float)
    (i j : Nat) (pos1 pos2 : Float) (conflicts : UInt64) : UInt64 :=
  if pos1 > pos2 - critical && pos1 < pos2 + critical then CRITICAL_CONFLICTS
  else
    let conflicts := if pos1 > pos2 - threshold && pos1 < pos2 + threshold then conflicts + 1 else conflicts
    if pos1 <= pos2 && i + 1 < posis1.size then
      conflictCountFrom posis1 posis2 critical threshold (i + 1) j posis1[i + 1]! pos2 conflicts
    else if pos2 <= pos1 && j + 1 < posis2.size then
      conflictCountFrom posis1 posis2 critical threshold i (j + 1) pos1 posis2[j + 1]! conflicts
    else conflicts

/-- `countConflicts` with an unboxed count (`CRITICAL_CONFLICTS` for a critical conflict). -/
@[inline] private def conflictCount (critical threshold : Float) (posis1 posis2 : Array Float) : UInt64 :=
  if h : 0 < posis1.size ∧ 0 < posis2.size then
    conflictCountFrom posis1 posis2 critical threshold 0 0 posis1[0] posis2[0] 0
  else 0

/-- `CONFLICT_PENALTY` as `UInt64`. -/
private def CONFLICT_PENALTY_U64 : UInt64 := CONFLICT_PENALTY.toNat.toUInt64
/-- `CROSSING_PENALTY` as `UInt64`. -/
private def CROSSING_PENALTY_U64 : UInt64 := CROSSING_PENALTY.toNat.toUInt64

/-- The regular dependency (or zero-weight pair) of two non-degenerate segments without critical
conflicts, from the orderings' penalties `CONFLICT_PENALTY * conflicts + CROSSING_PENALTY * crossings`
(non-negative, so computed in `UInt64`). -/
private def addRegularDependency (g : SegmentGraph) (i1 i2 : Nat) (depValue1 depValue2 : UInt64) : SegmentGraph :=
  if depValue1 < depValue2 then g.addDependency false i1 i2 (depValue2 - depValue1).toNat
  else if depValue1 > depValue2 then g.addDependency false i2 i1 (depValue1 - depValue2).toNat
  else if depValue1 > 0 && depValue2 > 0 then
    (g.addDependency false i1 i2 0).addDependency false i2 i1 0
  else g

/-- `createDependencyIfNecessary(he1, he2)` on segments `i1`, `i2`, without the critical dependency
count: critical dependencies for critical conflicts, otherwise a regular dependency weighted by the
difference of the two orderings' conflict and crossing penalties (two zero-weight dependencies on a
tie with positive values). Degenerate segments (extent below `TOLERANCE`) get none. The segments are
only read before the first dependency is added; the counts are unboxed `UInt64` values. -/
def createDependency (gen : OrthogonalRoutingGenerator) (g : SegmentGraph) (i1 i2 : Nat) : SegmentGraph :=
  let he1 := g.segment i1
  let he2 := g.segment i2
  let start1 := he1.startPosition
  let end1 := he1.endPosition
  let start2 := he2.startPosition
  let end2 := he2.endPosition
  if (start1 - end1).abs < TOLERANCE || (start2 - end2).abs < TOLERANCE then g
  else
    let critical := gen.criticalConflictThreshold
    let threshold := gen.conflictThreshold
    let conflicts1 := conflictCount critical threshold he1.outgoingConnectionCoordinates he2.incomingConnectionCoordinates
    let conflicts2 := conflictCount critical threshold he2.outgoingConnectionCoordinates he1.incomingConnectionCoordinates
    let critical1 := conflicts1 == CRITICAL_CONFLICTS
    let critical2 := conflicts2 == CRITICAL_CONFLICTS
    if critical1 || critical2 then
      let g := if critical1 then g.addDependency true i2 i1 CRITICAL_DEPENDENCY_WEIGHT else g
      if critical2 then g.addDependency true i1 i2 CRITICAL_DEPENDENCY_WEIGHT else g
    else
      let crossings1 := crossingCount he1.outgoingConnectionCoordinates start2 end2 0 0 +
        crossingCount he2.incomingConnectionCoordinates start1 end1 0 0
      let crossings2 := crossingCount he2.outgoingConnectionCoordinates start1 end1 0 0 +
        crossingCount he1.incomingConnectionCoordinates start2 end2 0 0
      addRegularDependency g i1 i2 (CONFLICT_PENALTY_U64 * conflicts1 + CROSSING_PENALTY_U64 * crossings1)
        (CONFLICT_PENALTY_U64 * conflicts2 + CROSSING_PENALTY_U64 * crossings2)

/-- Number of critical dependencies among the dependencies `d, d + 1, …` of `g`, plus `count`. -/
private partial def countCriticalFrom (g : SegmentGraph) (d : Nat) (count : Int) : Int :=
  if d < g.dependencyCount then countCriticalFrom g (d + 1) (if g.depIsCritical d then count + 1 else count)
  else count

/-- `createDependencyIfNecessary(he1, he2)` on segments `i1`, `i2` (see `createDependency`), also
returning the number of critical dependencies created. -/
def createDependencyIfNecessary (gen : OrthogonalRoutingGenerator) (g : SegmentGraph) (i1 i2 : Nat) : SegmentGraph × Int :=
  let before := g.dependencyCount
  let g := gen.createDependency g i1 i2
  (g, countCriticalFrom g before 0)

/-- The pairwise loop of `routeEdges` from the pair `(i, j)` on: `createDependencyIfNecessary` for every
pair of segments `i < j < n`, row by row. -/
private partial def createDependenciesFrom (gen : OrthogonalRoutingGenerator) (n i j : Nat) (g : SegmentGraph) :
    SegmentGraph :=
  if j < n then createDependenciesFrom gen n i (j + 1) (gen.createDependency g i j)
  else if i + 2 < n then createDependenciesFrom gen n (i + 1) (i + 2) g
  else g

/-- Rust `f64::total_cmp` as an unsigned key: the bit pattern with the sign bit flipped for
non-negative values and all bits flipped for negative ones (NaNs ordered by sign and payload). -/
@[inline] private def totalOrderKey (x : Float) : UInt64 :=
  let bits := x.toBits
  if bits >>> 63 != 0 then ~~~bits else bits ^^^ 0x8000000000000000

/-- Merges the sorted runs `src[i:mid]` and `src[j:hi]` into `dst[k:hi]` (by `totalOrderKey`, left run
first on ties). -/
private partial def mergeRuns (src dst : FloatArray) (i j k mid hi : Nat) : FloatArray :=
  if k < hi then
    if i < mid && (j >= hi || totalOrderKey src[i]! <= totalOrderKey src[j]!) then
      mergeRuns src (dst.set! k src[i]!) (i + 1) j (k + 1) mid hi
    else
      mergeRuns src (dst.set! k src[j]!) i (j + 1) (k + 1) mid hi
  else dst

/-- One bottom-up merge pass with run width `width`, from offset `lo` on. -/
private partial def mergePass (src dst : FloatArray) (width lo : Nat) : FloatArray :=
  if lo < src.size then
    let mid := min (lo + width) src.size
    let hi := min (lo + 2 * width) src.size
    mergePass src (mergeRuns src dst lo mid lo mid hi) width hi
  else dst

/-- Bottom-up merge sort; the two buffers alternate between passes. -/
private partial def mergeSortLoop (src dst : FloatArray) (width : Nat) : FloatArray :=
  if width < src.size then
    let dst := mergePass src dst width 0
    mergeSortLoop dst src (2 * width)
  else src

/-- Sorts by `f64::total_cmp` (stable merge sort; elements with equal keys have the same bit pattern
anyway, so every correct sort gives this array). -/
private def sortTotal (xs : FloatArray) : FloatArray :=
  mergeSortLoop xs (FloatArray.mk (Array.replicate xs.size 0.0)) 1

/-- Scan of `minimumDifference` over the sorted `sorted[k:]` (`prev` = last distinct value, `distinct`
= number of distinct values so far): skips bit-identical duplicates (Rust `dedup_by`), returns `NaN` at
the first `NaN` gap, else the minimum gap (`f64::MAX` with fewer than two distinct values). -/
private partial def minimumGapFrom (sorted : FloatArray) (k : Nat) (prev : Float) (distinct : Nat) (minDifference : Float) :
    Float :=
  if h : k < sorted.size then
    let x := sorted[k]
    if x.toBits == prev.toBits then minimumGapFrom sorted (k + 1) prev distinct minDifference
    else
      let diff := x - prev
      if diff != diff then Float.nan
      else minimumGapFrom sorted (k + 1) x (distinct + 1) (if diff < minDifference then diff else minDifference)
  else if distinct < 2 then Float.maxValue else minDifference

/-- `minimumDifference` of a `FloatArray`. -/
private def minimumDifferenceOf (numbers : FloatArray) : Float :=
  if numbers.size < 2 then Float.maxValue
  else
    let sorted := sortTotal numbers
    minimumGapFrom sorted 1 sorted[0]! 1 Float.maxValue

/-- `minimumDifference(numbers)`: the smallest gap between distinct values (sorted with `total_cmp`,
duplicates by bit pattern removed); `f64::MAX` for fewer than two values, `NaN` if a gap is `NaN`. -/
def minimumDifference (numbers : Array Float) : Float :=
  minimumDifferenceOf (numbers.foldl (·.push ·) (FloatArray.emptyWithCapacity numbers.size))

/-- All incoming (`incoming`) or outgoing connection coordinates of the segments. -/
private def collectCoordinates (g : SegmentGraph) (incoming : Bool) : FloatArray :=
  g.segments.foldl (init := FloatArray.emptyWithCapacity (2 * g.segments.size)) fun acc seg =>
    (if incoming then seg.incomingConnectionCoordinates else seg.outgoingConnectionCoordinates).foldl (·.push ·) acc

/-- `minimumHorizontalSegmentDistance(edgeSegments)`: the smaller of the minimum differences of all
incoming and of all outgoing connection coordinates (Rust `f64::min`). -/
def minimumHorizontalSegmentDistance (g : SegmentGraph) : Float :=
  fmin (minimumDifferenceOf (collectCoordinates g true)) (minimumDifferenceOf (collectCoordinates g false))

/-- `createHyperEdgeSegments(nodes, portSide, hyperEdges, portToHyperEdgeSegmentMap)`: a new segment for
every output port on `portSide` (node order, port order) that is not part of a segment yet. -/
def createHyperEdgeSegments (gen : OrthogonalRoutingGenerator) (a : LGraphArena) (nodes : Array LNodeId)
    (portSide : PortSide) (g : SegmentGraph) (portMap : Std.HashMap LPortId Nat) :
    SegmentGraph × Std.HashMap LPortId Nat := Id.run do
  let mut g := g
  let mut portMap := portMap
  for node in nodes do
    for port in a.nodePortsByTypeAndSide node .output portSide do
      if !portMap.contains port then
        let index := g.segments.size
        let (segment, m) := HyperEdgeSegment.addPortPositions a index (HyperEdgeSegment.new gen.routingDirection) port portMap
        g := (g.addSegment segment).1
        portMap := m
  return (g, portMap)

/-- The splitter with this generator's callbacks (Java `new HyperEdgeSegmentSplitter(this)`). -/
def splitter (gen : OrthogonalRoutingGenerator) : HyperEdgeSegmentSplitter :=
  { createDependency := gen.createDependency, countCrossings := countCrossings }

/-- `breakCriticalCycles(edgeSegments, random)`: splits segments to resolve the critical cycles. -/
def breakCriticalCycles (gen : OrthogonalRoutingGenerator) (g : SegmentGraph) (random : Random) : SegmentGraph × Random :=
  let (cycleDependencies, g, random) := HyperEdgeCycleDetector.detectCycles g true random
  (gen.splitter.splitSegments cycleDependencies g gen.criticalConflictThreshold, random)

/-- `breakNonCriticalCycles(edgeSegments, random)` (public static; also used by the self-loop
`RoutingSlotAssigner`): removes the zero-weight and reverses the other dependencies closing cycles. -/
def breakNonCriticalCycles (g : SegmentGraph) (random : Random) : SegmentGraph × Random :=
  let (cycleDependencies, g, random) := HyperEdgeCycleDetector.detectCycles g false random
  let g := cycleDependencies.foldl (init := g) fun g d =>
    if g.depWeight d == 0 then g.removeDependency d else g.reverseDependency d
  (g, random)

/-- Working arrays of `topologicalNumbering` (per segment index) and its FIFO queue. -/
private structure Numbering where
  /-- `routing_slot`. -/
  slot : Array Int
  /-- `in_weight`. -/
  inWeight : Array Int
  /-- `out_weight`. -/
  outWeight : Array Int
  /-- The queue (`head` = front). -/
  queue : Array Nat
  head : Nat := 0
  /-- `max_rank`. -/
  maxRank : Int := -1

/-- First pass over the outgoing dependencies `deps[k:]` of a dequeued source with slot `nodeSlot`:
every target gets at least slot `nodeSlot + 1` and becomes a source when its last incoming dependency
is processed. -/
private partial def numberTargets (g : SegmentGraph) (deps : Array Nat) (nodeSlot : Int) (k : Nat) (st : Numbering) :
    Numbering :=
  if h : k < deps.size then
    let targetCode := g.depTargetCode deps[k]
    if targetCode != 0 then
      let target := targetCode - 1
      let newSlot := nodeSlot + 1
      let current := st.slot[target]!
      let slot := if current < newSlot then newSlot else current
      let inWeight := st.inWeight[target]! - 1
      let st := { st with slot := st.slot.set! target slot, inWeight := st.inWeight.set! target inWeight,
                          maxRank := max st.maxRank slot }
      let st := if inWeight == 0 then { st with queue := st.queue.push target } else st
      numberTargets g deps nodeSlot (k + 1) st
    else numberTargets g deps nodeSlot (k + 1) st
  else st

/-- Longest-path numbering from the queued sources. -/
private partial def numberFromSources (g : SegmentGraph) (st : Numbering) : Numbering :=
  if h : st.head < st.queue.size then
    let node := st.queue[st.head]
    let st := { st with head := st.head + 1 }
    let nodeSlot := st.slot[node]!
    numberFromSources g (numberTargets g (g.segment node).outgoingSegmentDependencies nodeSlot 0 st)
  else st

/-- Second pass over the incoming dependencies `deps[k:]` of a dequeued rightward target with slot
`nodeSlot`: sources without incoming connections are pulled to at most slot `nodeSlot - 1` and queued
when their last outgoing dependency is processed. -/
private partial def pullSources (g : SegmentGraph) (deps : Array Nat) (nodeSlot : Int) (k : Nat) (st : Numbering) :
    Numbering :=
  if h : k < deps.size then
    let sourceCode := g.depSourceCode deps[k]
    if sourceCode != 0 && (g.segment (sourceCode - 1)).incomingConnectionCoordinates.isEmpty then
      let source := sourceCode - 1
      let newSlot := nodeSlot - 1
      let current := st.slot[source]!
      let slot := if current > newSlot then newSlot else current
      let outWeight := st.outWeight[source]! - 1
      let st := { st with slot := st.slot.set! source slot, outWeight := st.outWeight.set! source outWeight }
      let st := if outWeight == 0 then { st with queue := st.queue.push source } else st
      pullSources g deps nodeSlot (k + 1) st
    else pullSources g deps nodeSlot (k + 1) st
  else st

/-- Pulls the predecessors of the queued rightward targets. -/
private partial def pullFromTargets (g : SegmentGraph) (st : Numbering) : Numbering :=
  if h : st.head < st.queue.size then
    let node := st.queue[st.head]
    let st := { st with head := st.head + 1 }
    let nodeSlot := st.slot[node]!
    pullFromTargets g (pullSources g (g.segment node).incomingSegmentDependencies nodeSlot 0 st)
  else st

/-- Stores the routing slots and weights of `topologicalNumbering` in the segments `i, i + 1, …`. -/
private partial def writeNumbering (segments : Array HyperEdgeSegment) (st : Numbering) (i : Nat) :
    Array HyperEdgeSegment :=
  if i < segments.size then
    writeNumbering (segments.modify i (HyperEdgeSegment.setNumberingData st.slot[i]! st.inWeight[i]! st.outWeight[i]!))
      st (i + 1)
  else segments

/-- `topologicalNumbering(segments)`: routing slots by longest path from the sources; afterwards the
segments with only outgoing connections and no outgoing dependencies ("rightward targets") are moved to
the highest slot and their predecessors without incoming connections pulled after them. Slots and
in/out weights are computed in local arrays and stored in the segments at the end. -/
def topologicalNumbering (g : SegmentGraph) : SegmentGraph := Id.run do
  let n := g.segments.size
  let mut slots : Array Int := Array.emptyWithCapacity n
  let mut inWeights : Array Int := Array.emptyWithCapacity n
  let mut outWeights : Array Int := Array.emptyWithCapacity n
  let mut sources : Array Nat := #[]
  let mut rightwardTargets : Array Nat := #[]
  for h : i in [0:n] do
    let seg := g.segments[i]
    let inWeight : Int := seg.incomingSegmentDependencies.size
    let outWeight : Int := seg.outgoingSegmentDependencies.size
    slots := slots.push seg.routingSlot
    inWeights := inWeights.push inWeight
    outWeights := outWeights.push outWeight
    if inWeight == 0 then sources := sources.push i
    if outWeight == 0 && seg.incomingConnectionCoordinates.isEmpty then
      rightwardTargets := rightwardTargets.push i
  let st := numberFromSources g { slot := slots, inWeight := inWeights, outWeight := outWeights, queue := sources }
  let st := if st.maxRank > -1 then
      let maxRank := st.maxRank
      let slot := rightwardTargets.foldl (init := st.slot) fun slot node => slot.set! node maxRank
      pullFromTargets g { st with slot := slot, queue := rightwardTargets, head := 0 }
    else st
  return { g with segments := writeNumbering g.segments st 0 }

/-- Rust `{:?}` of a coordinate list (approximation used by the trace output only). -/
private def showCoords (cs : Array Float) : String :=
  "[" ++ ", ".intercalate (cs.toList.map Float.toRustDisplay) ++ "]"

/-- `trace_segments(label, edge_segments)` (`ELK_TRACE_ORTHO`; the `{:.1}` formatting of Rust is
approximated with `Float.toRustDisplay`). -/
def traceSegments (gen : OrthogonalRoutingGenerator) (label : String) (g : SegmentGraph) : LayeredM Unit := do
  if !ElkTrace.global.ortho then return
  let prefix_ := gen.debugPrefix.getD "?"
  IO.eprintln s!"[orthogonal:{prefix_}] {label} segments={g.segments.size}"
  let a ← get
  for idx in [0:g.segments.size] do
    let seg := g.segment idx
    let ports := seg.ports.toList.map fun p =>
      let pt := a.port p
      let nodeName := match pt.owner with
        | some n => a.nodeDesignation n
        | none => "?"
      let anchor := ((a.portAbsoluteAnchor p).map (·.y)).getD 0.0
      s!"{nodeName}:{pt.side}@{Float.toRustDisplay anchor}"
    IO.eprintln (s!"  seg#{idx} slot={seg.routingSlot} start={Float.toRustDisplay seg.startPosition} " ++
      s!"end={Float.toRustDisplay seg.endPosition} incoming={showCoords seg.incomingConnectionCoordinates} " ++
      s!"outgoing={showCoords seg.outgoingConnectionCoordinates} split_by={seg.splitBy.isSome} " ++
      s!"split_partner={seg.splitPartner.isSome} ports=[{", ".intercalate ports}]")

/-- `routeEdges(monitor, layeredGraph, sourceLayerNodes, sourceLayerIndex, targetLayerNodes, startPos)`:
routes the edges between the two node sets (Rust `None` layers are empty arrays) starting at
`startPos` and returns the number of routing slots used. `scope` is the `ArenaSync` membership of the
graph (computed from `graph` when not given; the orthogonal edge router passes the snapshot taken at
the start of its `process`). `sourceLayerIndex` is only used by Java's debug output (Rust ignores it). -/
def routeEdges (gen : OrthogonalRoutingGenerator) (graph : LGraphId) (sourceLayerNodes : Array LNodeId)
    (sourceLayerIndex : Int) (targetLayerNodes : Array LNodeId) (startPos : Float) (scope : Option ArenaScope := none) :
    LayeredM Nat := do
  let _ := sourceLayerIndex
  let scope ← match scope with
    | some s => pure s
    | none => withArena (ArenaScope.ofGraph · graph)
  let g ← withArena fun a =>
    let (g, portMap) := gen.createHyperEdgeSegments a sourceLayerNodes gen.routingStrategy.sourcePortSide {} {}
    (gen.createHyperEdgeSegments a targetLayerNodes gen.routingStrategy.targetPortSide g portMap).1
  gen.traceSegments "initial" g
  let gen := { gen with
    criticalConflictThreshold := CRITICAL_CONFLICT_THRESHOLD_FACTOR * minimumHorizontalSegmentDistance g }
  -- every dependency is created by this loop, so the critical ones are exactly those Rust counts
  let mut g := createDependenciesFrom gen g.segments.size 0 1 g
  let criticalDependencyCount := countCriticalFrom g 0 0
  let graphRandom ← LayeredM.graphRandom? graph
  let mut random := graphRandom.getD (Random.ofInt 0)
  if criticalDependencyCount >= 2 then
    let (g', r) := gen.breakCriticalCycles g random
    g := g'
    random := r
  gen.traceSegments "after_critical" g
  let (g', r) := breakNonCriticalCycles g random
  g := g'
  random := r
  gen.traceSegments "after_noncritical" g
  if graphRandom.isSome then
    LayeredM.setGraphRandom graph random
  g := topologicalNumbering g
  let mut rankCount : Int := -1
  let mut created : Std.HashSet KVector := {}
  for i in [0:g.segments.size] do
    let seg := g.segment i
    if (seg.startPosition - seg.endPosition).abs < TOLERANCE then continue
    rankCount := max rankCount seg.routingSlot
    created ← gen.routingStrategy.calculateBendPoints g i startPos gen.edgeSpacing scope created
  return (rankCount + 1).toNat

end OrthogonalRoutingGenerator

end Elk.Alg.Layered.P5Edges.Orthogonal
