import Std.Data.HashMap
import Elk.Alg.Layered.P5Edges.Orthogonal.HyperEdgeCycleDetector
import Elk.Alg.Layered.P5Edges.Orthogonal.HyperEdgeSegmentSplitter
import Elk.Alg.Layered.P5Edges.Orthogonal.Direction
import Elk.Core.Util.ElkTrace
import Elk.Core.Util.Sort
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

/-- `createDependencyIfNecessary(he1, he2)` on segments `i1`, `i2`: critical dependencies for critical
conflicts (returning their number), otherwise a regular dependency weighted by the difference of the
two orderings' conflict and crossing penalties (two zero-weight dependencies on a tie with positive
values). Degenerate segments (extent below `TOLERANCE`) get none. -/
def createDependencyIfNecessary (gen : OrthogonalRoutingGenerator) (g : SegmentGraph) (i1 i2 : Nat) : SegmentGraph × Int := Id.run do
  let he1 := g.segment i1
  let he2 := g.segment i2
  if (he1.startPosition - he1.endPosition).abs < TOLERANCE || (he2.startPosition - he2.endPosition).abs < TOLERANCE then
    return (g, 0)
  let conflicts1 := gen.countConflicts he1.outgoingConnectionCoordinates he2.incomingConnectionCoordinates
  let conflicts2 := gen.countConflicts he2.outgoingConnectionCoordinates he1.incomingConnectionCoordinates
  let criticalConflictsDetected := conflicts1 == CRITICAL_CONFLICTS_DETECTED || conflicts2 == CRITICAL_CONFLICTS_DETECTED
  let (depValue1, depValue2) : Int × Int :=
    if criticalConflictsDetected then (0, 0)
    else
      let crossings1 := countCrossings he1.outgoingConnectionCoordinates he2.startPosition he2.endPosition +
        countCrossings he2.incomingConnectionCoordinates he1.startPosition he1.endPosition
      let crossings2 := countCrossings he2.outgoingConnectionCoordinates he1.startPosition he1.endPosition +
        countCrossings he1.incomingConnectionCoordinates he2.startPosition he2.endPosition
      (CONFLICT_PENALTY * conflicts1 + CROSSING_PENALTY * crossings1,
        CONFLICT_PENALTY * conflicts2 + CROSSING_PENALTY * crossings2)
  let mut g := g
  let mut criticalDependencyCount : Int := 0
  if criticalConflictsDetected then
    if conflicts1 == CRITICAL_CONFLICTS_DETECTED then
      g := (g.createAndAddCritical i2 i1).1
      criticalDependencyCount := criticalDependencyCount + 1
    if conflicts2 == CRITICAL_CONFLICTS_DETECTED then
      g := (g.createAndAddCritical i1 i2).1
      criticalDependencyCount := criticalDependencyCount + 1
  else if depValue1 < depValue2 then
    g := (g.createAndAddRegular i1 i2 (depValue2 - depValue1)).1
  else if depValue1 > depValue2 then
    g := (g.createAndAddRegular i2 i1 (depValue1 - depValue2)).1
  else if depValue1 > 0 && depValue2 > 0 then
    g := (g.createAndAddRegular i1 i2 0).1
    g := (g.createAndAddRegular i2 i1 0).1
  return (g, criticalDependencyCount)

/-- `minimumDifference(numbers)`: the smallest gap between distinct values (sorted with `total_cmp`,
duplicates by bit pattern removed); `f64::MAX` for fewer than two values, `NaN` if a gap is `NaN`. -/
def minimumDifference (numbers : Array Float) : Float := Id.run do
  if numbers.size < 2 then return Float.maxValue
  let sorted := stableSort numbers Float.compareTotal
  let mut distinct : Array Float := #[]
  for x in sorted do
    let isDuplicate : Bool := match distinct.back? with
      | some y => y.toBits == x.toBits
      | none => false
    if !isDuplicate then distinct := distinct.push x
  if distinct.size < 2 then return Float.maxValue
  let mut minDifference := Float.maxValue
  for i in [1:distinct.size] do
    let diff := distinct[i]! - distinct[i - 1]!
    if diff.isNaN then return Float.nan
    if diff < minDifference then minDifference := diff
  return minDifference

/-- `minimumHorizontalSegmentDistance(edgeSegments)`: the smaller of the minimum differences of all
incoming and of all outgoing connection coordinates (Rust `f64::min`). -/
def minimumHorizontalSegmentDistance (g : SegmentGraph) : Float := Id.run do
  let mut incoming : Array Float := #[]
  let mut outgoing : Array Float := #[]
  for seg in g.segments do
    incoming := incoming ++ seg.incomingConnectionCoordinates
    outgoing := outgoing ++ seg.outgoingConnectionCoordinates
  return fmin (minimumDifference incoming) (minimumDifference outgoing)

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
  { createDependencyIfNecessary := gen.createDependencyIfNecessary, countCrossings := countCrossings }

/-- `breakCriticalCycles(edgeSegments, random)`: splits segments to resolve the critical cycles. -/
def breakCriticalCycles (gen : OrthogonalRoutingGenerator) (g : SegmentGraph) (random : Random) : SegmentGraph × Random :=
  let (cycleDependencies, g, random) := HyperEdgeCycleDetector.detectCycles g true random
  (gen.splitter.splitSegments cycleDependencies g gen.criticalConflictThreshold, random)

/-- `breakNonCriticalCycles(edgeSegments, random)` (public static; also used by the self-loop
`RoutingSlotAssigner`): removes the zero-weight and reverses the other dependencies closing cycles. -/
def breakNonCriticalCycles (g : SegmentGraph) (random : Random) : SegmentGraph × Random := Id.run do
  let (cycleDependencies, g', random) := HyperEdgeCycleDetector.detectCycles g false random
  let mut g := g'
  for d in cycleDependencies do
    if (g.dependency d).weight == 0 then g := g.removeDependency d
    else g := g.reverseDependency d
  return (g, random)

/-- `topologicalNumbering(segments)`: routing slots by longest path from the sources; afterwards the
segments with only outgoing connections and no outgoing dependencies ("rightward targets") are moved to
the highest slot and their predecessors without incoming connections pulled after them. -/
def topologicalNumbering (g : SegmentGraph) : SegmentGraph := Id.run do
  let mut g := g
  let mut sources : Array Nat := #[]
  let mut rightwardTargets : Array Nat := #[]
  for i in [0:g.segments.size] do
    let seg := g.segment i
    let inWeight : Int := seg.incomingSegmentDependencies.size
    let outWeight : Int := seg.outgoingSegmentDependencies.size
    g := g.modifySegment i fun s => { s with inDepWeight := inWeight, outDepWeight := outWeight }
    if inWeight == 0 then sources := sources.push i
    if outWeight == 0 && seg.incomingConnectionCoordinates.isEmpty then
      rightwardTargets := rightwardTargets.push i
  let mut maxRank : Int := -1
  let mut head := 0
  while head < sources.size do
    let node := sources[head]!
    head := head + 1
    let nodeSeg := g.segment node
    let nodeSlot := nodeSeg.routingSlot
    for d in nodeSeg.outgoingSegmentDependencies do
      if let some target := (g.dependency d).target then
        let newSlot := nodeSlot + 1
        let tgt := g.segment target
        let slot := if tgt.routingSlot < newSlot then newSlot else tgt.routingSlot
        maxRank := max maxRank slot
        let inWeight := tgt.inDepWeight - 1
        g := g.modifySegment target fun s => { s with routingSlot := slot, inDepWeight := inWeight }
        if inWeight == 0 then sources := sources.push target
  if maxRank > -1 then
    for node in rightwardTargets do
      let rank := maxRank
      g := g.modifySegment node fun s => { s with routingSlot := rank }
    let mut targetsHead := 0
    while targetsHead < rightwardTargets.size do
      let node := rightwardTargets[targetsHead]!
      targetsHead := targetsHead + 1
      let nodeSeg := g.segment node
      let nodeSlot := nodeSeg.routingSlot
      for d in nodeSeg.incomingSegmentDependencies do
        if let some source := (g.dependency d).source then
          let src := g.segment source
          if !src.incomingConnectionCoordinates.isEmpty then continue
          let newSlot := nodeSlot - 1
          let slot := if src.routingSlot > newSlot then newSlot else src.routingSlot
          let outWeight := src.outDepWeight - 1
          g := g.modifySegment source fun s => { s with routingSlot := slot, outDepWeight := outWeight }
          if outWeight == 0 then rightwardTargets := rightwardTargets.push source
  return g

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
  let mut g := g
  let mut criticalDependencyCount : Int := 0
  let n := g.segments.size
  for i in [0:n] do
    for j in [i + 1:n] do
      let (g', count) := gen.createDependencyIfNecessary g i j
      g := g'
      criticalDependencyCount := criticalDependencyCount + count
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
