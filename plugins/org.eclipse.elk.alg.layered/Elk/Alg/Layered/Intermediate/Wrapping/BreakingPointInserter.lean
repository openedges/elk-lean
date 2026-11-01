import Elk.Alg.Layered.Intermediate.Wrapping.BreakingPointInfo
import Elk.Alg.Layered.Intermediate.Wrapping.SingleEdgeGraphWrapper
import Elk.Core.Util.Sort
/-!
# `org.eclipse.elk.alg.layered.intermediate.wrapping.BreakingPointInserter`

Port of elk-rs `intermediate/breaking_point_inserter.rs`. Calculates cut indexes (as the
`SingleEdgeGraphWrapper`), optionally improves them for multi edges
(`WRAPPING_MULTI_EDGE_IMPROVE_CUTS`), validifies them only if `WRAPPING_VALIDIFY_STRATEGY` is set
explicitly, and splits every edge spanning a cut:

```
u --nodeStartEdge--> startMarker --startEndEdge--> endMarker --e--> v
```

The original edge `e` is pushed "to the right" so it can be split again; consecutive breaking
points are chained (`BPInfo.prev`/`next`). Two new layers hold the start and end markers.

Slots: after phase 2; must run before `LongEdgeSplitter`.

Follows Java (agent COV): `applyCuts` walks the layers like Java's `ListIterator` — the two
inserted breaking point layers are skipped and `idx + 1 == cut` compares original layer indexes
(elk-rs walked the list by index, visited the new layers and applied every cut after the first two
layers earlier per preceding cut). `improveCuts` checks `bestCut != null` like Java (a `null` hit
cannot occur: `lCut` is `null` only while `rCut` is not); without cuts it returns no cuts like
Java's empty loop. The early return for an empty layering is unreachable from the layered pipeline
(a graph without nodes is never laid out by the phases; Java would fail in `GraphStats`).

This module also holds the `BPInfo` accessors (`BPInfo` is an inner class of the Java
`BreakingPointInserter`, `isStart`/`isEnd` are its static methods).
-/
namespace Elk.Alg.Layered.Intermediate.Wrapping

open Elk.Graph Elk.Core Elk.Core.Alg Elk.Core.Util Elk.Core.Options Elk.Alg.Layered Elk.Alg.Layered.Graph
  Elk.Alg.Layered.Options Elk.Alg.Layered.Intermediate LayeredM

namespace BreakingPointInfo

/-- `node.getProperty(InternalProperties.BREAKING_POINT_INFO)`. -/
def get? (node : LNodeId) : LayeredM (Option BreakingPointInfo) := do
  return (← getNode node).internal.breakingPointInfo

/-- Stores `info` on one node (`node.setProperty(BREAKING_POINT_INFO, info)`). -/
def setOn (node : LNodeId) (info : BreakingPointInfo) : LayeredM Unit :=
  modifyNode node fun n => { n with internal := { n.internal with breakingPointInfo := some info } }

/-- Writes the (mutated) shared info to both of its markers (see the module doc of
`BreakingPointInfo`). -/
def write (info : BreakingPointInfo) : LayeredM Unit := do
  setOn info.start info
  setOn info.endNode info

/-- Mutates the info whose `start` (or `end`) dummy is `node`: reads it from `node`, applies `f`
and writes it to both markers. -/
def modifyAt (node : LNodeId) (f : BreakingPointInfo → BreakingPointInfo) : LayeredM Unit := do
  if let some info ← get? node then write (f info)

/-- `BPInfo.isStart(n)`: `n` is the start dummy of its breaking point info. -/
def isStart (node : LNodeId) : LayeredM Bool := do
  match ← get? node with
  | some info => return info.start == node
  | none => return false

/-- `BPInfo.isEnd(n)`: `n` is the end dummy of its breaking point info. -/
def isEnd (node : LNodeId) : LayeredM Bool := do
  match ← get? node with
  | some info => return info.endNode == node
  | none => return false

end BreakingPointInfo

namespace BreakingPointInserter

/-- Rust `contains_edge` + push (insertion-ordered set, Java `LinkedHashSet.add`). -/
private def addEdge (edges : Array LEdgeId) (e : LEdgeId) : Array LEdgeId :=
  if edges.contains e then edges else edges.push e

/-- Rust `remove_edge` (first occurrence). -/
private def removeEdge (edges : Array LEdgeId) (e : LEdgeId) : Array LEdgeId :=
  match edges.findIdx? (· == e) with
  | some i => edges.eraseIdx! i
  | none => edges

/-- `computeEdgeSpans(graph)`: `spans[i]` is the number of edges spanning the gap before layer
`i` (outgoing edges of the layer's nodes are added after counting, incoming ones removed). -/
def computeEdgeSpans (graph : LGraphId) : LayeredM (Array Int) := do
  let layers := (← getGraph graph).layers
  let mut spans : Array Int := Array.replicate (layers.size + 1) 0
  let mut openEdges : Array LEdgeId := #[]
  for idx in [0:layers.size] do
    spans := spans.set! idx openEdges.size
    let nodes := (← getLayer layers[idx]!).nodes
    for node in nodes do
      for edge in (← withArena (·.nodeOutgoingEdges node)) do
        openEdges := addEdge openEdges edge
    for node in nodes do
      for edge in (← withArena (·.nodeIncomingEdges node)) do
        openEdges := removeEdge openEdges edge
  return spans

/-- Java inner class `Cut` (Rust `CutState`, linked by indexes into the cut array). -/
structure CutState where
  /-- The 'original' cut (offset by assigned neighbours). -/
  index : Int
  /-- A suggestion for a better cut. -/
  newIndex : Int
  /-- The numerically closest smaller cut. -/
  prev : Option Nat
  /-- The numerically closest larger cut. -/
  suc : Option Nat
  /-- Whether `newIndex` is final. -/
  assigned : Bool := false
  deriving Inhabited, Repr

/-- `Cut.selfOrNext()`: the first unassigned cut from `cut` on. -/
def cutSelfOrNext (cuts : Array CutState) (cut : Option Nat) : Option Nat := Id.run do
  let mut current := cut
  -- every step follows `suc`, which strictly increases the index
  for _ in [0:cuts.size + 1] do
    match current with
    | none => return none
    | some idx =>
      if !cuts[idx]!.assigned then return some idx
      current := cuts[idx]!.suc
  return none

/-- `Cut.next()`. -/
def cutNext (cuts : Array CutState) (cut : Nat) : Option Nat := cutSelfOrNext cuts cuts[cut]!.suc

/-- `Cut.offset()`: moves the assigned cut to its `newIndex` and the unassigned neighbours on both
sides (up to the next assigned cut) by the same offset. -/
def offsetAssignedCut (cuts : Array CutState) (cut : Nat) : Array CutState := Id.run do
  if !cuts[cut]!.assigned then return cuts
  let mut cuts := cuts
  let offset := cuts[cut]!.newIndex - cuts[cut]!.index
  cuts := cuts.modifyIn cut fun c => { c with index := c.index + offset }
  let mut prev := cuts[cut]!.prev
  for _ in [0:cuts.size] do
    match prev with
    | none => break
    | some p =>
      if cuts[p]!.assigned then break
      cuts := cuts.modifyIn p fun c => { c with index := c.index + offset }
      prev := cuts[p]!.prev
  let mut suc := cuts[cut]!.suc
  for _ in [0:cuts.size] do
    match suc with
    | none => break
    | some s =>
      if cuts[s]!.assigned then break
      cuts := cuts.modifyIn s fun c => { c with index := c.index + offset }
      suc := cuts[s]!.suc
  return cuts

/-- `computeScore(graph, index, spans, dist)`: `spans + dist ^ WRAPPING_MULTI_EDGE_DISTANCE_PENALTY`. -/
def computeScore (distancePenalty : Float) (spans dist : Int) : Float :=
  Float.ofInt spans + Float.pow (Float.ofInt dist) distancePenalty

/-- One round of `improveCuts`: the best `(cut, score)` over all gaps `1 ≤ idx < layers`. -/
private def bestCutRound (cutStates : Array CutState) (spans : Array Int) (layerCount : Nat)
    (distancePenalty : Float) : Array CutState × Option Nat := Id.run do
  let mut cutStates := cutStates
  let mut lCut : Option Nat := none
  let mut rCut := cutSelfOrNext cutStates (some 0)
  let mut bestCut : Option Nat := none
  let mut bestScore := Float.posInf
  for idx in [1:layerCount] do
    let i : Int := idx
    let rDist : Int := match rCut, lCut with
      | some r, _ => (cutStates[r]!.index - i).natAbs
      | none, some l => (i - cutStates[l]!.index).natAbs + 1
      | none, none => 1
    let lDist : Int := match lCut with
      | some l => (i - cutStates[l]!.index).natAbs
      | none => rDist + 1
    let (hit, dist) := if lDist < rDist then (lCut, lDist) else (rCut, rDist)
    let score := computeScore distancePenalty (spans.getD idx 0) dist
    if score < bestScore then
      bestScore := score
      bestCut := hit
      if let some b := bestCut then
        cutStates := cutStates.modifyIn b fun c => { c with newIndex := i }
    if let some r := rCut then
      if i == cutStates[r]!.index then
        lCut := rCut
        rCut := cutNext cutStates r
  return (cutStates, bestCut)

/-- `improveCuts(graph, cuts)`: repeatedly moves the cut with the best score (fewest spanning
edges plus distance penalty) and offsets its unassigned neighbours; the result is sorted. -/
def improveCuts (graph : LGraphId) (cuts : Array Int) : LayeredM (Array Int) := do
  if cuts.isEmpty then return #[]
  let mut improved : Array Int := #[]
  let mut cutStates : Array CutState := #[]
  for idx in [0:cuts.size] do
    let cut := cuts[idx]!
    let prev : Option Nat := if idx > 0 then some (idx - 1) else none
    let state : CutState := { index := cut, newIndex := cut, prev := prev, suc := none }
    cutStates := cutStates.push state
  for idx in [0:cutStates.size - 1] do
    cutStates := cutStates.modifyIn idx fun c => { c with suc := some (idx + 1) }
  let spans ← computeEdgeSpans graph
  let layerCount := (← getGraph graph).layers.size
  let distancePenalty :=
    ((← getGraph graph).props.get LayeredOptions.WRAPPING_MULTI_EDGE_DISTANCE_PENALTY).getD 2.0
  for _ in [0:cutStates.size] do
    let (states, bestCut) := bestCutRound cutStates spans layerCount distancePenalty
    cutStates := states
    if let some b := bestCut then
      improved := improved.push cutStates[b]!.newIndex
      cutStates := cutStates.modifyIn b fun c => { c with assigned := true }
      cutStates := offsetAssignedCut cutStates b
  return stableSort improved compare

/-- Rust `create_breaking_point_dummy(graph, layer)`: a `BREAKING_POINT` node with
`PORT_CONSTRAINTS = FIXED_SIDE` in `layer`, a `WEST` input and an `EAST` output port. -/
def createBreakingPointDummy (graph : LGraphId) (layer : LayerId) : LayeredM (LNodeId × LPortId × LPortId) := do
  let node ← createNode graph
  modifyNode node fun n => { n with
    props := n.props.set LayeredOptions.PORT_CONSTRAINTS PortConstraints.fixedSide,
    type := .breakingPoint }
  setNodeLayer node (some layer)
  let inPort ← createPort
  modifyPort inPort (·.setSide .west)
  setPortNode inPort (some node)
  let outPort ← createPort
  modifyPort outPort (·.setSide .east)
  setPortNode outPort (some node)
  return (node, inPort, outPort)

/-- Splits one open edge at a cut (the body of the Rust `for original_edge in open_edges`). -/
private def splitEdge (graph : LGraphId) (bpLayer1 bpLayer2 : LayerId) (originalEdge : LEdgeId) : LayeredM Unit := do
  let (bpStartMarker, inPortBp1, outPortBp1) ← createBreakingPointDummy graph bpLayer1
  let (bpEndMarker, inPortBp2, outPortBp2) ← createBreakingPointDummy graph bpLayer2
  let orig ← getEdge originalEdge
  let modelOrder := orig.internal.modelOrder
  let sourcePort := orig.source
  let nodeStartEdge ← createEdge
  setEdgeSource nodeStartEdge sourcePort
  setEdgeTarget nodeStartEdge (some inPortBp1)
  modifyEdge nodeStartEdge fun e => { e with internal := { e.internal with modelOrder := modelOrder } }
  let startEndEdge ← createEdge
  setEdgeSource startEndEdge (some outPortBp1)
  setEdgeTarget startEndEdge (some inPortBp2)
  modifyEdge startEndEdge fun e => { e with internal := { e.internal with modelOrder := modelOrder } }
  setEdgeSource originalEdge (some outPortBp2)
  let bpInfo := BreakingPointInfo.new bpStartMarker bpEndMarker nodeStartEdge startEndEdge originalEdge
  BreakingPointInfo.write bpInfo
  -- possibly link a chain of breaking point dummies
  let prevNode ← match (← getEdge nodeStartEdge).source with
    | some p => pure (← getPort p).owner
    | none => pure none
  if let some prevNode := prevNode then
    if (← getNode prevNode).type == .breakingPoint then
      if let some prevInfo ← BreakingPointInfo.get? prevNode then
        BreakingPointInfo.write { prevInfo with next := some bpStartMarker }
        BreakingPointInfo.write { bpInfo with prev := some prevInfo.start }

/-- `applyCuts(graph, cuts)`: inserts two layers after each cut position and splits the open
edges; returns the number of distinct split edges. As in Java, the layers are walked with a list
iterator: `idx` counts the original layers only, and the two layers inserted at a cut
(`ListIterator.add`) are skipped, so every cut refers to the original layer indexes. -/
def applyCuts (graph : LGraphId) (cuts : Array Int) : LayeredM Nat := do
  if cuts.isEmpty then return 0
  -- `idx`: Java's counter of visited original layers; `pos`: the list iterator's cursor
  let mut idx : Nat := 0
  let mut pos : Nat := 0
  let mut cutIndex : Nat := 0
  let mut nextCut : Int := cuts[0]!
  let mut noSplitEdges : Nat := 0
  let mut alreadySplit : Array LEdgeId := #[]
  let mut openEdges : Array LEdgeId := #[]
  while pos < (← getGraph graph).layers.size do
    let layer := (← getGraph graph).layers[pos]!
    pos := pos + 1
    let nodes := (← getLayer layer).nodes
    for node in nodes do
      for edge in (← withArena (·.nodeOutgoingEdges node)) do
        openEdges := addEdge openEdges edge
      for edge in (← withArena (·.nodeIncomingEdges node)) do
        openEdges := removeEdge openEdges edge
    if ((idx + 1 : Nat) : Int) == nextCut then
      let bpLayer1 ← createLayer graph
      modifyGraph graph fun g => { g with layers := g.layers.insertIdxIfInBounds pos bpLayer1 }
      let bpLayer2 ← createLayer graph
      modifyGraph graph fun g => { g with layers := g.layers.insertIdxIfInBounds (pos + 1) bpLayer2 }
      pos := pos + 2
      for originalEdge in openEdges do
        if !alreadySplit.contains originalEdge then
          noSplitEdges := noSplitEdges + 1
          alreadySplit := alreadySplit.push originalEdge
        splitEdge graph bpLayer1 bpLayer2 originalEdge
      cutIndex := cutIndex + 1
      if cutIndex >= cuts.size then break
      nextCut := cuts[cutIndex]!
    idx := idx + 1
  return noSplitEdges

/-- `process(graph, monitor)`. -/
def process (graph : LGraphId) (monitor : ProgressMonitor) : LayeredM Unit := do
  let _ ← monitor.begin "Breaking Point Insertion" 1.0
  if (← getGraph graph).layers.isEmpty then
    monitor.done
    return
  let gs ← GraphStats.new graph
  let gr ← getGraph graph
  let cuttingStrategy := (gr.props.get LayeredOptions.WRAPPING_CUTTING_STRATEGY).getD .msd
  let calculator := cutIndexCalculatorFor cuttingStrategy
  let mut cuts ← calculator.getCutIndexes graph gs
  if (gr.props.get LayeredOptions.WRAPPING_MULTI_EDGE_IMPROVE_CUTS).getD true then
    cuts ← improveCuts graph cuts
  if !calculator.guaranteeValid && gr.props.has LayeredOptions.WRAPPING_VALIDIFY_STRATEGY then
    match (gr.props.get LayeredOptions.WRAPPING_VALIDIFY_STRATEGY).getD .greedy with
    | .lookBack => cuts := SingleEdgeGraphWrapper.validifyIndexesLookingBack gs cuts
    | .greedy => cuts := SingleEdgeGraphWrapper.validifyIndexesGreedily gs cuts
    | .no => pure ()
  if cuts.isEmpty then
    monitor.done
    return
  let _ ← applyCuts graph cuts
  monitor.done

/-- The `BreakingPointInserter` processor. -/
def processor : LayeredProcessor := { name := "BreakingPointInserter", process := process }

end BreakingPointInserter

builtin_initialize registerBreakingPointInserter : Unit ←
  IntermediateProcessorStrategy.register .breakingPointInserter BreakingPointInserter.processor

end Elk.Alg.Layered.Intermediate.Wrapping
