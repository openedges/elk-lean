import Std.Data.HashSet
import Elk.Alg.Layered.LayeredPhases
import Elk.Alg.Layered.Graph.LGraphUtil
import Elk.Alg.Layered.Options.CycleBreakingStrategy
import Elk.Alg.Layered.P1Cycles.GroupModelOrderCalculator
import Elk.Core.Util.ElkTrace
import Elk.Core.Util.Sort
/-!
# `org.eclipse.elk.alg.layered.p1cycles.GreedyCycleBreaker` (+ `GreedyModelOrderCycleBreaker`)

Port of elk-rs `p1cycles/greedy_cycle_breaker.rs` (Eades, Lin, Smyth: *A fast and effective
heuristic for the feedback arc set problem*). Sinks get marks `-1, -2, …`, sources and the
max-outflow nodes `1, 2, …`; afterwards every edge pointing from a higher to a lower mark is
reversed. Ties of the max-outflow choice are broken with the graph's `RANDOM` generator (or, in
model-order mode, by the smallest constraint model order).

Like Rust, the Java subclass `GreedyModelOrderCycleBreaker` is the same phase with
`preferModelOrder := true`; its trace name is the Rust `type_name` `GreedyModelOrderCycleBreaker`.

Rust struct fields (`indeg`, `outdeg`, `mark`, `sources`, `sinks`, `random`) are the phase-local
`GreedyCycleBreaker.State`. Node indices are written to `LNode.id` (Rust `graph_element().id`) and
read back from there, exactly like Rust. The `VecDeque`s are arrays with a head index.

Debug hooks of elk-rs are ported: `ELK_DEBUG_CYCLE_RANDOM_PREFETCH` (discard `n` draws of
`nextInt(2)`), `ELK_DEBUG_CYCLE_FORCE_REVERSE_ORIGINS` (reverse exactly the edges whose ElkEdge
origin index is listed), `ELK_TRACE_CYCLE_CHOICES` / `ELK_TRACE_CYCLE_REVERSALS` (stderr lines).
-/
namespace Elk.Alg.Layered.P1Cycles

open Elk.Graph Elk.Core Elk.Core.Alg Elk.Core.Util Elk.Alg.Layered Elk.Alg.Layered.Graph
  Elk.Alg.Layered.Options Elk.Alg.Layered.Intermediate LayeredM

namespace GreedyCycleBreaker

/-- `INTERMEDIATE_PROCESSING_CONFIGURATION`: `REVERSED_EDGE_RESTORER` after P5. -/
def intermediateProcessingConfiguration : LayeredProcessorConfiguration :=
  (LayoutProcessorConfiguration.create : LayeredProcessorConfiguration).addAfter .p5EdgeRouting .reversedEdgeRestorer

/-- Rust `GreedyCycleBreaker` fields. -/
structure State where
  /-- `indeg`: weighted in-degree of each node (by node index). -/
  indeg : Array Int := #[]
  /-- `outdeg`: weighted out-degree of each node. -/
  outdeg : Array Int := #[]
  /-- `mark`: the node's position mark (`0` = unprocessed). -/
  mark : Array Int := #[]
  /-- `sources` (`VecDeque`): pending elements are `sources[sourcesHead:]`. -/
  sources : Array LNodeId := #[]
  sourcesHead : Nat := 0
  /-- `sinks` (`VecDeque`): pending elements are `sinks[sinksHead:]`. -/
  sinks : Array LNodeId := #[]
  sinksHead : Nat := 0
  /-- `random`: the graph's `RANDOM` (shared) or a local `Random::new(0)`. -/
  random : Random := Random.ofInt 0
  /-- Whether `random` is the graph's generator (Rust `Arc<Mutex<_>>` sharing): every draw is written back. -/
  sharedRandom : Bool := false
  /-- `prefer_model_order`. -/
  preferModelOrder : Bool := false

/-- Phase-local monad. -/
abbrev GreedyM := StateT State LayeredM

/-- Rust `node_index`: `graph_element().id as usize`. -/
private def nodeIndex (n : LNodeId) : LayeredM Int := do return (← getNode n).id

/-- `idx as usize < len`: a negative `i32` cast to `usize` is never in range. -/
@[inline] private def inRange (i : Int) (size : Nat) : Option Nat :=
  if i >= 0 && i < (size : Int) then some i.toNat else none

/-- `self.random.next_int(bound)`, writing the generator back to the graph when it is shared. -/
private def nextInt (graph : LGraphId) (bound : Int) : GreedyM Int := do
  let (v, r) := (← get).random.nextInt bound
  modify fun s => { s with random := r }
  if (← get).sharedRandom then
    modifyGraph graph fun g => { g with internal := { g.internal with random := some r } }
  return v

private def popSink : GreedyM (Option LNodeId) := do
  let s ← get
  match s.sinks[s.sinksHead]? with
  | some n => set { s with sinksHead := s.sinksHead + 1 }; return some n
  | none => return none

private def popSource : GreedyM (Option LNodeId) := do
  let s ← get
  match s.sources[s.sourcesHead]? with
  | some n => set { s with sourcesHead := s.sourcesHead + 1 }; return some n
  | none => return none

/-- `chooseNodeWithMaxOutflow(nodes)` (Rust `choose_node_with_max_outflow`): in model-order mode the
node with the smallest constraint (group) model order among those with a `MODEL_ORDER`, otherwise
(or if none has one) a random node. -/
def chooseNodeWithMaxOutflow (graph : LGraphId) (nodes : Array LNodeId) : GreedyM (Option LNodeId) := do
  if nodes.isEmpty then return none
  if (← get).preferModelOrder then
    let gr ← getGraph graph
    let offset : Int := max (gr.layerlessNodes.size : Int) gr.internal.maxModelOrderNodes
    let bigOffset := offset * gr.internal.cbNumModelOrderGroups
    let enforceGroupModelOrder :=
      gr.props.getD LayeredOptions.GROUP_MODEL_ORDER_CB_GROUP_ORDER_STRATEGY .onlyWithinGroup == .enforced
    let mut minimumModelOrder : Int := 2147483647
    let mut returnNode : Option LNodeId := none
    let mut calculator := GroupModelOrderCalculator.new
    for node in nodes do
      let nd ← getNode node
      if nd.internal.modelOrder.isNone then continue
      let (modelOrder, c) :=
        if enforceGroupModelOrder then calculator.computeConstraintGroupModelOrder nd bigOffset offset
        else calculator.computeConstraintModelOrder nd offset
      calculator := c
      if minimumModelOrder > modelOrder then
        minimumModelOrder := modelOrder
        returnNode := some node
    if returnNode.isSome then return returnNode
  let index ← nextInt graph (nodes.size : Int)
  if ElkTrace.global.cycleChoices then
    let mut candidates : Array String := #[]
    for n in nodes do candidates := candidates.push (toString (← nodeIndex n))
    let picked ← match nodes[index.toNat]? with
      | some n => nodeIndex n
      | none => pure 0
    IO.eprintln s!"[cycle-breaker-choice] candidates=[{",".intercalate candidates.toList}] picked_index={index} picked_node={picked}"
  return nodes[index.toNat]?

/-- `updateNeighbors(node)` (Rust `update_neighbors`): decrements the degrees of the unmarked
neighbours (per port: incoming then outgoing edges) and queues new sources/sinks. -/
def updateNeighbors (node : LNodeId) : GreedyM Unit := do
  let ports := (← getNode node).ports
  for port in ports do
    let edges := (← getPort port).connectedEdges
    for edge in edges do
      let ed ← getEdge edge
      let some sourcePort := ed.source | continue
      let some targetPort := ed.target | continue
      let connectedPort := if sourcePort == port then targetPort else sourcePort
      let isTarget := targetPort == connectedPort
      let priority := ed.props.getD LayeredOptions.PRIORITY_DIRECTION 0
      let some endpoint := (← getPort connectedPort).owner | continue
      if endpoint == node then continue
      let some index := inRange (← nodeIndex endpoint) (← get).mark.size | continue
      if (← get).mark[index]! != 0 then continue
      let priority := if priority < 0 then 0 else priority
      if isTarget then
        modify fun s => { s with indeg := s.indeg.modify index (· - (priority + 1)) }
        let s ← get
        if s.indeg[index]! <= 0 && s.outdeg[index]! > 0 then
          set { s with sources := s.sources.push endpoint }
      else
        modify fun s => { s with outdeg := s.outdeg.modify index (· - (priority + 1)) }
        let s ← get
        if s.outdeg[index]! <= 0 && s.indeg[index]! > 0 then
          set { s with sinks := s.sinks.push endpoint }

/-- `ElkEdge` origin index of an edge (Rust `edge_origin_id`). -/
private def edgeOriginId (edge : LEdgeId) : LayeredM (Option Nat) := do
  match (← getEdge edge).internal.origin with
  | some (.elkEdge id) => return some id.idx
  | _ => return none

/-- Rust `trace_port_origin`. -/
private def portOriginId (port : Option LPortId) : LayeredM (Option Nat) := do
  let some p := port | return none
  match (← getPort p).internal.origin with
  | some (.elkPort id) => return some id.idx
  | _ => return none

/-- Rust `{:?}` of an `Option<usize>`. -/
private def debugOption (o : Option Nat) : String :=
  match o with
  | some v => s!"Some({v})"
  | none => "None"

/-- Rust `trace_reversal_entry`. -/
private def traceReversalEntry (edge : LEdgeId) (sourceIdx targetIdx sourceMark targetMark : Int) : LayeredM String := do
  let ed ← getEdge edge
  let edgeOrigin ← edgeOriginId edge
  let sourcePortOrigin ← portOriginId ed.source
  let targetPortOrigin ← portOriginId ed.target
  return s!"edge_origin={debugOption edgeOrigin},source_port_origin={debugOption sourcePortOrigin},target_port_origin={debugOption targetPortOrigin},src_node={sourceIdx},tgt_node={targetIdx},src_mark={sourceMark},tgt_mark={targetMark}"

/-- The `ELK_DEBUG_CYCLE_FORCE_REVERSE_ORIGINS` set (`none` when unset or empty). -/
private def forcedReverseOrigins : Option (Std.HashSet Nat) := do
  let raw ← ElkTrace.global.debugCycleForceReverseOrigins
  let values := (raw.splitOn ",").foldl (fun (acc : Std.HashSet Nat) tok =>
    match tok.trimAscii.toString.toNat? with
    | some v => acc.insert v
    | none => acc) {}
  if values.isEmpty then none else some values

/-- Rust `reverse_edges`: reverses (with port adaptation) every outgoing edge whose source mark
exceeds its target mark, in node → port → outgoing edge order (port and edge lists are copied
when the loop reaches them, like `toPortArray`/`toEdgeArray`). -/
def reverseEdges (graph : LGraphId) (nodes : Array LNodeId) : GreedyM Unit := do
  let traceReversals := ElkTrace.global.cycleReversals
  let forced := forcedReverseOrigins
  let mut reversedEdges : Array String := #[]
  for node in nodes do
    let nd ← getNode node
    let nodeIdx := nd.id
    for port in nd.ports do
      let edges := (← getPort port).outgoingEdges
      for edge in edges do
        let some targetPort := (← getEdge edge).target | continue
        let some targetNode := (← getPort targetPort).owner | continue
        let targetIndex ← nodeIndex targetNode
        let mark := (← get).mark
        let reverseByMark := match inRange nodeIdx mark.size, inRange targetIndex mark.size with
          | some i, some j => mark[i]! > mark[j]!
          | _, _ => false
        let shouldReverse : Bool ← match forced with
          | some f => do
            let origin ← edgeOriginId edge
            pure (origin.any f.contains)
          | none => pure reverseByMark
        if shouldReverse then
          if traceReversals then
            let sm := (inRange nodeIdx mark.size).map (mark[·]!) |>.getD 0
            let tm := (inRange targetIndex mark.size).map (mark[·]!) |>.getD 0
            reversedEdges := reversedEdges.push (← traceReversalEntry edge nodeIdx targetIndex sm tm)
          LGraphUtil.reverseEdge edge graph true
          modifyGraph graph fun g => { g with internal := { g.internal with cyclic := true } }
  if traceReversals && !reversedEdges.isEmpty then
    let sorted := stableSort reversedEdges compare
    IO.eprintln s!"[cycle-breaker] reversed_count={sorted.size} edges={" | ".intercalate sorted.toList}"

/-- Computes the initial weighted degrees, assigns node indices and queues the initial sinks/sources. -/
private def initializeDegrees (nodes : Array LNodeId) : GreedyM Unit := do
  let mut index : Nat := 0
  for node in nodes do
    modifyNode node fun n => { n with id := (index : Int) }
    let ports := (← getNode node).ports
    for port in ports do
      let pt ← getPort port
      for edge in pt.incomingEdges do
        let ed ← getEdge edge
        let sourceNode ← match ed.source with
          | some p => pure (← getPort p).owner
          | none => pure none
        if sourceNode == some node then continue
        let priority := ed.props.getD LayeredOptions.PRIORITY_DIRECTION 0
        let w : Int := if priority > 0 then priority + 1 else 1
        modify fun s => { s with indeg := s.indeg.modify index (· + w) }
      for edge in pt.outgoingEdges do
        let ed ← getEdge edge
        let targetNode ← match ed.target with
          | some p => pure (← getPort p).owner
          | none => pure none
        if targetNode == some node then continue
        let priority := ed.props.getD LayeredOptions.PRIORITY_DIRECTION 0
        let w : Int := if priority > 0 then priority + 1 else 1
        modify fun s => { s with outdeg := s.outdeg.modify index (· + w) }
    let s ← get
    if s.outdeg[index]! == 0 then
      set { s with sinks := s.sinks.push node }
    else if s.indeg[index]! == 0 then
      set { s with sources := s.sources.push node }
    index := index + 1

/-- Marks `node` with `value` if its index is in range (returns whether it was marked). -/
private def markNode (node : LNodeId) (value : Int) : GreedyM Bool := do
  match inRange (← nodeIndex node) (← get).mark.size with
  | some i =>
    modify fun s => { s with mark := s.mark.set! i value }
    return true
  | none => return false

/-- `process(layeredGraph, monitor)` body on the phase-local state. -/
def run (graph : LGraphId) : GreedyM Unit := do
  let nodes := (← getGraph graph).layerlessNodes
  let total := nodes.size
  let graphRandom := (← getGraph graph).internal.random
  modify fun s => { s with
    indeg := Array.replicate total 0, outdeg := Array.replicate total 0, mark := Array.replicate total 0,
    sources := #[], sourcesHead := 0, sinks := #[], sinksHead := 0,
    random := graphRandom.getD (Random.ofInt 0), sharedRandom := graphRandom.isSome }
  if let some prefetch := ElkTrace.global.debugCycleRandomPrefetch.bind String.toNat? then
    for _ in [0:prefetch] do
      let _ ← nextInt graph 2
    if ElkTrace.global.cycleChoices then
      IO.eprintln s!"[cycle-breaker-choice] random_prefetch={prefetch}"
  initializeDegrees nodes
  let mut unprocessed := total
  let mut nextRight : Int := -1
  let mut nextLeft : Int := 1
  while unprocessed > 0 do
    while true do
      match ← popSink with
      | none => break
      | some sink =>
        if ← markNode sink nextRight then
          nextRight := nextRight - 1
          updateNeighbors sink
          unprocessed := unprocessed - 1
    while true do
      match ← popSource with
      | none => break
      | some source =>
        if ← markNode source nextLeft then
          nextLeft := nextLeft + 1
          updateNeighbors source
          unprocessed := unprocessed - 1
    if unprocessed > 0 then
      let mut maxOutflow : Int := -2147483648
      let mut maxNodes : Array LNodeId := #[]
      for node in nodes do
        let s ← get
        if let some index := inRange (← nodeIndex node) s.mark.size then
          if s.mark[index]! == 0 then
            let outflow := s.outdeg[index]! - s.indeg[index]!
            if outflow >= maxOutflow then
              if outflow > maxOutflow then
                maxNodes := #[]
                maxOutflow := outflow
              maxNodes := maxNodes.push node
      match ← chooseNodeWithMaxOutflow graph maxNodes with
      | some maxNode =>
        if ← markNode maxNode nextLeft then
          nextLeft := nextLeft + 1
          updateNeighbors maxNode
          unprocessed := unprocessed - 1
      -- unreachable for consistent node ids (Rust would loop forever here)
      | none => break
  let shiftBase : Int := (nodes.size : Int) + 1
  modify fun s => { s with mark := s.mark.map fun v => if v < 0 then v + shiftBase else v }
  reverseEdges graph nodes

/-- The phase (`GreedyCycleBreaker`, or `GreedyModelOrderCycleBreaker` when `preferModelOrder`). -/
def create (preferModelOrder : Bool) : LayeredPhase :=
  { name := if preferModelOrder then "GreedyModelOrderCycleBreaker" else "GreedyCycleBreaker"
    process := fun graph monitor => do
      let _ ← monitor.begin "Greedy cycle removal" 1.0
      let _ ← (run graph).run { preferModelOrder := preferModelOrder }
      monitor.done
    getLayoutProcessorConfiguration := fun _ => pure (some intermediateProcessingConfiguration) }

/-- `CycleBreakingStrategy.GREEDY` → `GreedyCycleBreaker::new()`. -/
def phase : LayeredPhase := create false

/-- `CycleBreakingStrategy.GREEDY_MODEL_ORDER` → `GreedyCycleBreaker::new_with_model_order(true)`
(Java `GreedyModelOrderCycleBreaker`). -/
def modelOrderPhase : LayeredPhase := create true

end GreedyCycleBreaker

builtin_initialize registerGreedyCycleBreaker : Unit ←
  LayeredPhases.registerPhase .p1CycleBreaking (ElkEnum.ordinal CycleBreakingStrategy.greedy)
    (pure GreedyCycleBreaker.phase)

builtin_initialize registerGreedyModelOrderCycleBreaker : Unit ←
  LayeredPhases.registerPhase .p1CycleBreaking (ElkEnum.ordinal CycleBreakingStrategy.greedyModelOrder)
    (pure GreedyCycleBreaker.modelOrderPhase)

end Elk.Alg.Layered.P1Cycles
