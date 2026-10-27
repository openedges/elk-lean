import Elk.Alg.Layered.Graph
import Elk.Alg.Layered.Options.PortType
import Elk.Alg.Layered.P3Order.CrossMinSnapshot
import Elk.Alg.Layered.P3Order.ICrossingMinimizationHeuristic
import Elk.Alg.Layered.P3Order.BarycenterPortDistributor
import Elk.Alg.Layered.P3Order.ForsterConstraintResolver
import Elk.Alg.Layered.P3Order.RandomTrace
import Elk.Core.Util.Random
import Elk.Core.Util.Sort
import Elk.Core.Util.ElkTrace
import Std.Data.HashMap
/-!
# `org.eclipse.elk.alg.layered.p3order.BarycenterHeuristic`

Orders a free layer by the barycenters of its nodes with respect to the port ranks of the fixed
neighbour layer (elk-rs `barycenter_heuristic.rs`): in-layer edges and `BARYCENTER_ASSOCIATES`
merge the barycenter of other nodes of the free layer, nodes without neighbours get filled-in
barycenters, a small random perturbation is added, the layer is sorted stably by barycenter and
the in-layer constraints are resolved by the `ForsterConstraintResolver`.

## API (for `GraphInfoHolder`)
* `BarycenterHeuristic.new constraintResolver portDistributor : BaseIO BarycenterHeuristic`
  (Rust `new(constraint_resolver, port_distributor)`). The resolver and the distributor are the
  P3b1 objects; their state lives behind `IO.Ref`s and is shared, so the `SweepPortDistributor`
  view of the same distributor (initialised separately by the holder) and this heuristic see the
  same ranks, and the resolver's `barycenterStates` are this heuristic's barycenter states.
* Random numbers come from a generator owned by the caller (Rust passes `random: &mut Random` to
  every call; the `GraphInfoHolder` owns it): the methods take an `IO.Ref Random`, and
  `toHeuristic random` captures it in the `CrossingMinimizationHeuristic` closures.
* `initializable`: the resolver's layer/node initialisation, `Layer.id := layer index`, and in
  `initAfterTraversal` a copy of the distributor's ranks. The resolver must therefore *not* be
  added to the `IInitializable` list separately, and the distributor's own initialisable has to
  run before this one (the `GraphInfoHolder` order: counter, decider, port distributor, heuristic).
* `setSnapshot s`: hands the `CrossMinSnapshot` to the distributor, the resolver and the heuristic
  (Rust `set_snapshot`; the holder calls it after the initialisation).

## Two code paths (as in elk-rs)
* **snapshot path** (after `setSnapshot`): node ids, layer indices, port ids, the *captured* port
  order of a node and the edge end points are read from the snapshot (`calculate_barycenter_snap`);
  "same layer" is the equality of the captured layer indices.
* **lock path** (no snapshot, e.g. the elk-rs unit tests): live `LNode.id`, `Layer.id`, `LPort.id`,
  the current port order, `getPredecessorPorts`/`getSuccessorPorts` and layer identity
  (`calculate_barycenter_lock`).
`BARYCENTER_ASSOCIATES` and node types are read from the arena (elk-rs `ArenaSync` or lock).

## Numerics and order
The perturbation is `(nextFloat() as f32 * 0.07f - 0.07f / 2) as f64` in `f32` arithmetic (every
operation rounded with `Float.toF32`), the filled-in random value `nextFloat() * maxBary - 1` and
everything else is `f64`. Draws happen in the Rust order: per computed node with a positive degree
(after its in-layer/associate recursion), then per node without barycenter in
`fillInUnknownBarycenters`, or one `nextDouble()` per node in `randomizeBarycenters`, also for nodes
without a state. The sort is stable (Rust `sort_by`) with known barycenters ascending
(`partial_cmp`, NaN equal) before unknown ones.

## Deviations
* Java `minimizeCrossings(layer, …)` sorts with `ModelOrderBarycenterHeuristic.insertionSort` when
  the graph has `CROSSING_MINIMIZATION_FORCE_NODE_MODEL_ORDER`; Rust (followed) always sorts by
  barycenter here (the model order heuristic overrides `minimizeCrossings` only).
* Java's comparator uses `Double.compareTo` (NaN biggest, `-0.0 < 0.0`); Rust's `partial_cmp`
  (followed) treats NaN as equal and `-0.0 == 0.0`.
* An out-of-range layer index returns the order unchanged (Rust panics on `order[index]`).
* The `ELK_TRACE_CROSSMIN`, `_PORT_RANKS`, `_CROSSMIN_TIMING` and `BARYCENTER_LAYER_PATTERN` dumps are
  not reproduced; `CROSSMIN_RANDOM_TRACE` lines are (see `RandomTrace`), including the Rust quirk that
  the node label of `calculate_barycenter` is empty unless `ELK_TRACE_CROSSMIN` is set.
-/
namespace Elk.Alg.Layered.P3Order

open Elk.Core.Util Elk.Alg.Layered.Graph Elk.Alg.Layered.Options Elk.Alg.Layered.P3Order.Counting LayeredM

/-- Java `RANDOM_AMOUNT = 0.07f` (Rust `0.07_f32 as f64`): the amount of random perturbation. -/
def BarycenterHeuristic.RANDOM_AMOUNT : Float := Float.toF32 0.07

/-- `2^24`, the divisor of `Random.nextFloat` (a global: a literal in a loop is converted at run time). -/
def BarycenterHeuristic.TWO_POW_24 : Float := 16777216.0

/-! ## One barycenter computation -/

/-- Read-only inputs of one computation (Rust `&self` fields plus the call arguments). -/
structure BarycenterContext where
  /-- The arena (read only during the computation). -/
  arena : LGraphArena
  /-- `snapshot`. -/
  snapshot : Option CrossMinSnapshot := none
  /-- `port_ranks` (by port id). -/
  portRanks : FloatArray := FloatArray.empty
  /-- The sweep direction (`forward`). -/
  forward : Bool := true
  /-- `flat_to_node_buf`: flat index → node for the nodes of the current call (snapshot path), as
  `node.idx + 1` (`0`: none) at `flat - flatToNodeBase`. -/
  flatToNode : Array Nat := #[]
  /-- The smallest flat index of `flatToNode`. -/
  flatToNodeBase : Nat := 0
  /-- `random_trace::is_enabled()`. -/
  randomTrace : Bool := false
  /-- `ElkTrace::global().crossmin` (only changes trace labels). -/
  crossminTrace : Bool := false

namespace BarycenterContext

/-- `node_id_of(node)`: the snapshot's captured id, else `LNode.id as usize`. -/
@[inline] def nodeIdOf (c : BarycenterContext) (n : LNodeId) : Nat :=
  match c.snapshot with
  | some s => s.nodeId n
  | none => asUsize (c.arena.node n).id

/-- `layer_index_of(node)`: the snapshot's layer index, else `Layer.id as usize` (`0` without layer). -/
@[inline] def layerIndexOf (c : BarycenterContext) (n : LNodeId) : Nat :=
  match c.snapshot with
  | some s => s.nodeLayerIndex n
  | none => liveLayerIndex c.arena n

/-- `port_id_of(port)`: the snapshot's captured id, else `LPort.id as usize`. -/
@[inline] def portIdOf (c : BarycenterContext) (p : LPortId) : Nat :=
  match c.snapshot with
  | some s => s.portId p
  | none => asUsize (c.arena.port p).id

/-- `same_layer_check(a, b)`: equal snapshot layer indices, else both nodes in the same layer. -/
def sameLayerCheck (c : BarycenterContext) (a b : LNodeId) : Bool :=
  match c.snapshot with
  | some s => s.sameLayer a b
  | none =>
    match (c.arena.node a).layer, (c.arena.node b).layer with
    | some x, some y => x == y
    | _, _ => false

/-- `is_external_port_dummy(node)`. -/
def isExternalPortDummy (c : BarycenterContext) (n : LNodeId) : Bool :=
  match c.snapshot with
  | some s => s.nodeTypeOf (s.nodeFlatIndex n) == .externalPort
  | none => (c.arena.node n).type == .externalPort

/-- The trace label `id:<LNode.id>`. -/
@[inline] def nodeLabel (c : BarycenterContext) (n : LNodeId) : String := s!"id:{(c.arena.node n).id}"

/-- `flat_to_node_buf.get(flat)`. -/
@[inline] def nodeOfFlat? (c : BarycenterContext) (flat : Nat) : Option LNodeId :=
  if flat >= c.flatToNodeBase then
    let i := flat - c.flatToNodeBase
    if h : i < c.flatToNode.size then
      match c.flatToNode[i] with
      | 0 => none
      | k + 1 => some ⟨k⟩
    else none
  else none

end BarycenterContext

/-- The mutable data of one computation: the resolver's `barycenter_states[layer][node id]`, the
caller's generator and the pending `CROSSMIN_RANDOM_TRACE` lines `(method, value, location)`. -/
structure BarycenterData where
  /-- `constraint_resolver.barycenter_states`. -/
  states : Array (Array (Option BarycenterState)) := #[]
  /-- The generator. -/
  random : Random := {}
  /-- Pending trace lines. -/
  traces : Array (String × String × String) := #[]
  deriving Inhabited

namespace BarycenterData

/-- `bary_state(li, ni)`. -/
@[inline] def state? (d : BarycenterData) (li ni : Nat) : Option BarycenterState :=
  ((d.states[li]?).bind (·[ni]?)).bind id

/-- `bary_state_mut(li, ni)` with an update (no-op without a state). -/
@[inline] def modifyState (d : BarycenterData) (li ni : Nat) (f : BarycenterState → BarycenterState) : BarycenterData :=
  match d with
  | ⟨states, random, traces⟩ => ⟨BarycenterState.updateIn states li ni f, random, traces⟩

/-- The barycenter of a state (`none` without a state). -/
@[inline] def barycenter? (d : BarycenterData) (li ni : Nat) : Option Float :=
  (d.state? li ni).bind (·.barycenter)

/-- Whether state `(li, ni)` exists and has a barycenter (`barycenter?` is `some`), without an
`Option`. -/
@[inline] def hasBarycenterAt (d : BarycenterData) (li ni : Nat) : Bool := BarycenterState.knownIn d.states li ni

/-- The barycenter of state `(li, ni)` when `hasBarycenterAt` (else unspecified). -/
@[inline] def barycenterValueAt (d : BarycenterData) (li ni : Nat) : Float := BarycenterState.valueIn d.states li ni

/-- Adds the degree and summed weight of state `(fromLi, fromNi)` (or `(0, 0.0)`) to `(li, ni)`. -/
def addFrom (d : BarycenterData) (li ni fromLi fromNi : Nat) : BarycenterData :=
  let (degree, weight) := match d.state? fromLi fromNi with
    | some st => (st.degree, st.summedWeight)
    | none => (0, floatZero)
  d.modifyState li ni fun st => { st with degree := st.degree + degree, summedWeight := st.summedWeight + weight }

/-- Sets barycenter, summed weight (both `value`) and degree `1`. -/
@[inline] def assign (d : BarycenterData) (li ni : Nat) (value : Float) : BarycenterData :=
  d.modifyState li ni fun st => { st with barycenterValue := value, hasBarycenter := true, summedWeight := value, degree := 1 }

/-- `random.next_float()` with `random_trace::trace_next_float`. -/
def drawFloat (d : BarycenterData) (traceOn : Bool) (location : Unit → String) : Float × BarycenterData :=
  let (v, r) := d.random.nextFloat
  let d := { d with random := r }
  if traceOn then (v, { d with traces := d.traces.push ("next_float", RandomTrace.formatFixed 7 v, location ()) })
  else (v, d)

/-- `random.next_double()` with `random_trace::trace_next_double`. -/
def drawDouble (d : BarycenterData) (traceOn : Bool) (location : Unit → String) : Float × BarycenterData :=
  let (v, r) := d.random.nextDouble
  let d := { d with random := r }
  if traceOn then (v, { d with traces := d.traces.push ("next_double", RandomTrace.formatFixed 7 v, location ()) })
  else (v, d)

end BarycenterData

namespace BarycenterHeuristic

/-- The end of `calculate_barycenter_*`: for a positive degree the perturbation
`nextFloat() * RANDOM_AMOUNT - RANDOM_AMOUNT / 2` (`f32`) is added to the summed weight and the
barycenter becomes `summedWeight / degree`. -/
def finishBarycenter (c : BarycenterContext) (li ni : Nat) (nodeName : String) (d : BarycenterData) : BarycenterData :=
  match d.state? li ni with
  | some st =>
    if st.degree > 0 then
      let apply (raw : Float) (d : BarycenterData) : BarycenterData :=
        let ra := RANDOM_AMOUNT
        let perturbation := Float.toF32 (Float.toF32 (Float.toF32 raw * ra) - Float.toF32 (ra / floatTwo))
        d.modifyState li ni fun st =>
          let summedWeight := st.summedWeight + perturbation
          { st with summedWeight, barycenterValue := summedWeight / Float.ofInt st.degree, hasBarycenter := true }
      match d with
      | ⟨states, random, traces⟩ =>
        if random.mockDoubleSequence.isNone && !c.randomTrace then
          -- `Random.nextFloat` without mock and trace (`next(24) / 2^24` in `f32`), without its tuples
          let seed := (random.seed * Random.multiplier + Random.addend) &&& Random.mask
          let raw := Float.toF32 ((seed >>> 24).toUInt32.toNat.toFloat / TWO_POW_24)
          apply raw ⟨states, { random with seed }, traces⟩
        else
          let (raw, d) := (⟨states, random, traces⟩ : BarycenterData).drawFloat c.randomTrace
            fun _ => s!"barycenter::calculate_barycenter node={nodeName}"
          apply raw d
    else d
  | none => d

/-- Resets a state at the start of `calculate_barycenter_*`; `none` when it was already visited. -/
@[inline] def startVisit (d : BarycenterData) (li ni : Nat) : Option BarycenterData :=
  match d.state? li ni with
  | some st =>
    if st.visited then none
    else some (d.modifyState li ni fun st => { st with visited := true, degree := 0, summedWeight := floatZero, hasBarycenter := false })
  | none => some d

/-- Whether state `(li, ni)` exists and was already visited (`startVisit` returns `none`). -/
@[inline] def alreadyVisited (d : BarycenterData) (li ni : Nat) : Bool :=
  match d.state? li ni with
  | some st => st.visited
  | none => false

/-- `startVisit` of a state known not to be visited. -/
@[inline] def resetVisit (d : BarycenterData) (li ni : Nat) : BarycenterData :=
  d.modifyState li ni fun st => { st with visited := true, degree := 0, summedWeight := floatZero, hasBarycenter := false }

/-- The far ends of a captured port in the sweep direction. -/
@[inline] def farEnds (c : BarycenterContext) (s : CrossMinSnapshot) (pid : Nat) : Array Nat :=
  if c.forward then s.portPredecessors pid else s.portSuccessors pid

/-- Whether a far end of `ends[k:]` lies in captured layer `li`. -/
partial def anyEndInLayerOf (s : CrossMinSnapshot) (li : Nat) (ends : Array Nat) (k : Nat) : Bool :=
  if h : k < ends.size then
    s.nodeLayerOf (s.portOwnerFlat ends[k]) == li || anyEndInLayerOf s li ends (k + 1)
  else false

/-- Whether a far end of the captured ports `pids[i:]` lies in captured layer `li` (then `calcSnap`
recurses or skips self loops, otherwise every far end only adds its rank). -/
partial def anyPortEndInLayer (c : BarycenterContext) (s : CrossMinSnapshot) (li : Nat) (pids : Array Nat) (i : Nat) :
    Bool :=
  if h : i < pids.size then anyEndInLayerOf s li (farEnds c s pids[i]) 0 || anyPortEndInLayer c s li pids (i + 1)
  else false

/-- `acc + rank` over the far ends `ends[k:]` (in order). -/
partial def addEndRanks (c : BarycenterContext) (ends : Array Nat) (k : Nat) (acc : Float) : Float :=
  if h : k < ends.size then addEndRanks c ends (k + 1) (acc + c.portRanks.get! ends[k]) else acc

/-- `acc + rank` over the far ends `ends[k:hi]` (in order). -/
partial def addEndRanksRange (ranks : FloatArray) (ends : Array Nat) (k hi : Nat) (acc : Float) : Float :=
  if h : k < hi ∧ k < ends.size then addEndRanksRange ranks ends (k + 1) hi (acc + ranks.get! ends[k]) else acc

/-- `acc + rank` over the far ends of the captured ports `pids[i:]` (in order; the far ends in the
sweep direction are the predecessor or successor range of the snapshot's `endIds`). -/
partial def addPortEndRanks (c : BarycenterContext) (s : CrossMinSnapshot) (pids : Array Nat) (i : Nat) (acc : Float) :
    Float :=
  if h : i < pids.size then
    let pid := pids[i]
    let lo := if c.forward then s.endLo pid else s.endSplit pid
    let hi := if c.forward then s.endSplit pid else s.endHi pid
    addPortEndRanks c s pids (i + 1) (addEndRanksRange c.portRanks s.endIds lo hi acc)
  else acc

/-- The number of far ends of the captured ports `pids[i:]`. -/
partial def countPortEnds (c : BarycenterContext) (s : CrossMinSnapshot) (pids : Array Nat) (i acc : Nat) : Nat :=
  if h : i < pids.size then countPortEnds c s pids (i + 1) (acc + (farEnds c s pids[i]).size) else acc

mutual

/-- `calculate_barycenter_snap(snap, flat, …)`: the captured ports of the node and their captured
predecessors (forward) or successors; a far end in the same (captured) layer contributes its own
recursively computed degree and weight (self loops ignored), others their port rank; then the
associates of the node (if it is one of the current nodes) in the same layer. -/
partial def calcSnap (c : BarycenterContext) (s : CrossMinSnapshot) (flat : Nat) (d : BarycenterData) : BarycenterData :=
  let li := s.nodeLayerOf flat
  let ni := s.nodeGraphIdOf flat
  if alreadyVisited d li ni then d
  else
    let pids := s.nodePorts flat
    -- `anyPortEndInLayer c s li pids 0` and `countPortEnds c s pids 0 0`, precomputed by the snapshot
    let endsInLayer := s.nodeEndFlag flat &&& (if c.forward then 1 else 2) != 0
    let d := if endsInLayer then calcSnapPorts c s flat li ni pids 0 (resetVisit d li ni)
      else
        -- no recursion: the reset state accumulates the ranks of all far ends in order
        let sum := addPortEndRanks c s pids 0 floatZero
        let degree : Int := (if c.forward then s.nodePredCounts[flat]? else s.nodeSuccCounts[flat]?).getD 0
        d.modifyState li ni fun st =>
          { st with visited := true, degree := 0 + degree, summedWeight := sum, hasBarycenter := false }
    -- the associates (read only for a node that has any, `nodeEndFlags` bit `2`)
    let d := if s.nodeEndFlag flat &&& 4 == 0 then d
      else match c.nodeOfFlat? flat with
        | some node => calcSnapAssociates c s li ni (c.arena.node node).internal.barycenterAssociates 0 d
        | none => d
    let nodeName := if c.crossminTrace then ((c.nodeOfFlat? flat).map c.nodeLabel).getD "<unknown>" else ""
    finishBarycenter c li ni nodeName d

/-- The port loop of `calcSnap` over the captured ports `pids[i:]` of node `flat`. -/
partial def calcSnapPorts (c : BarycenterContext) (s : CrossMinSnapshot) (flat li ni : Nat) (pids : Array Nat) (i : Nat)
    (d : BarycenterData) : BarycenterData :=
  if h : i < pids.size then
    let pid := pids[i]
    let connected := if c.forward then s.portPredecessors pid else s.portSuccessors pid
    calcSnapPorts c s flat li ni pids (i + 1) (calcSnapConnected c s flat li ni connected 0 d)
  else d

/-- The far-end loop of `calcSnap` over the captured port ids `connected[k:]`. -/
partial def calcSnapConnected (c : BarycenterContext) (s : CrossMinSnapshot) (flat li ni : Nat) (connected : Array Nat)
    (k : Nat) (d : BarycenterData) : BarycenterData :=
  if h : k < connected.size then
    let fixedPid := connected[k]
    let fixedFlat := s.portOwnerFlat fixedPid
    let fixedLi := s.nodeLayerOf fixedFlat
    if fixedLi == li then
      if fixedFlat != flat then
        let d := (calcSnap c s fixedFlat d).addFrom li ni fixedLi (s.nodeGraphIdOf fixedFlat)
        calcSnapConnected c s flat li ni connected (k + 1) d
      else calcSnapConnected c s flat li ni connected (k + 1) d
    else
      let rank := c.portRanks.get! fixedPid
      let d := match d with
        | ⟨states, random, traces⟩ =>
          ⟨BarycenterState.updateIn states li ni fun st => { st with summedWeight := st.summedWeight + rank, degree := st.degree + 1 },
           random, traces⟩
      calcSnapConnected c s flat li ni connected (k + 1) d
  else d

/-- The associate loop of `calcSnap` (`BARYCENTER_ASSOCIATES` in the same captured layer). -/
partial def calcSnapAssociates (c : BarycenterContext) (s : CrossMinSnapshot) (li ni : Nat) (associates : Array LNodeId)
    (k : Nat) (d : BarycenterData) : BarycenterData :=
  if h : k < associates.size then
    let assocFlat := s.nodeFlatIndex associates[k]
    let assocLi := s.nodeLayerOf assocFlat
    if assocLi == li then
      let d := (calcSnap c s assocFlat d).addFrom li ni assocLi (s.nodeGraphIdOf assocFlat)
      calcSnapAssociates c s li ni associates (k + 1) d
    else calcSnapAssociates c s li ni associates (k + 1) d
  else d

end

/-- `calculate_barycenter_lock(node, …)`: like `calcSnap` on the live graph (current port order,
`getPredecessorPorts`/`getSuccessorPorts`, ports without owner skipped, layer identity). -/
partial def calcLock (c : BarycenterContext) (node : LNodeId) (d : BarycenterData) : BarycenterData := Id.run do
  let li := c.layerIndexOf node
  let ni := c.nodeIdOf node
  let some d0 := startVisit d li ni | return d
  let mut d := d0
  for freePort in (c.arena.node node).ports do
    let portIter := if c.forward then c.arena.portPredecessorPorts freePort else c.arena.portSuccessorPorts freePort
    for fixedPort in portIter do
      let some fixedNode := (c.arena.port fixedPort).owner | continue
      if c.sameLayerCheck fixedNode node then
        if fixedNode != node then
          d := calcLock c fixedNode d
          d := d.addFrom li ni (c.layerIndexOf fixedNode) (c.nodeIdOf fixedNode)
      else
        let rank := c.portRanks.get! (c.portIdOf fixedPort)
        d := d.modifyState li ni fun st => { st with summedWeight := st.summedWeight + rank, degree := st.degree + 1 }
  for associate in (c.arena.node node).internal.barycenterAssociates do
    if c.sameLayerCheck associate node then
      d := calcLock c associate d
      d := d.addFrom li ni (c.layerIndexOf associate) (c.nodeIdOf associate)
  let nodeName := if c.crossminTrace then c.nodeLabel node else ""
  return finishBarycenter c li ni nodeName d

/-- `flat_to_node_buf` entries of the nodes `nodes[i:]` with flat indices `flats`. -/
partial def fillFlatToNode (nodes : Array LNodeId) (flats : Array Nat) (base i : Nat) (out : Array Nat) : Array Nat :=
  if h : i < nodes.size then
    fillFlatToNode nodes flats base (i + 1) (out.setIfInBounds (flats[i]! - base) (nodes[i].idx + 1))
  else out

/-- Clears the `visited` flags of the flat nodes `flats[i:]`. -/
partial def clearVisitedSnap (s : CrossMinSnapshot) (flats : Array Nat) (i : Nat) (d : BarycenterData) : BarycenterData :=
  if h : i < flats.size then
    let flat := flats[i]
    clearVisitedSnap s flats (i + 1) (d.modifyState (s.nodeLayerOf flat) (s.nodeGraphIdOf flat) fun st => { st with visited := false })
  else d

/-- `calcSnap` of the nodes `flats[i:]`. -/
partial def calcSnapAll (c : BarycenterContext) (s : CrossMinSnapshot) (flats : Array Nat) (i : Nat) (d : BarycenterData) :
    BarycenterData :=
  if h : i < flats.size then calcSnapAll c s flats (i + 1) (calcSnap c s flats[i] d) else d

/-- `calculate_barycenters(nodes, forward, random)`: all `visited` flags of the nodes are cleared,
then every node's barycenter is computed (snapshot or lock path). -/
def calculateBarycenters (c : BarycenterContext) (nodes : Array LNodeId) (d : BarycenterData) : BarycenterData := Id.run do
  match c.snapshot with
  | some s =>
    let flats := nodes.map s.nodeFlatIndex
    let base := flats.foldl min (flats[0]?.getD 0)
    let top := flats.foldl max 0
    let flatToNode := fillFlatToNode nodes flats base 0
      (Array.replicate (if flats.isEmpty then 0 else top + 1 - base) 0)
    let d := clearVisitedSnap s flats 0 d
    calcSnapAll { c with flatToNode, flatToNodeBase := base } s flats 0 d
  | none =>
    let mut d := d
    for node in nodes do
      d := d.modifyState (c.layerIndexOf node) (c.nodeIdOf node) fun st => { st with visited := false }
    for node in nodes do
      d := calcLock c node d
    return d

/-- The first known barycenter of `nodes[j:]`, else `dflt`. -/
partial def nextKnownBarycenter (c : BarycenterContext) (d : BarycenterData) (nodes : Array LNodeId) (j : Nat)
    (dflt : Float) : Float :=
  if h : j < nodes.size then
    let n := nodes[j]
    let li := c.layerIndexOf n
    let ni := c.nodeIdOf n
    if d.hasBarycenterAt li ni then d.barycenterValueAt li ni else nextKnownBarycenter c d nodes (j + 1) dflt
  else dflt

/-- The pre-ordered branch of `fill_in_unknown_barycenters` from `nodes[index]` on (`lastValue`: the
previous node's value). -/
partial def fillPreOrdered (c : BarycenterContext) (nodes : Array LNodeId) (index : Nat) (lastValue : Float)
    (d : BarycenterData) : BarycenterData :=
  if h : index < nodes.size then
    let node := nodes[index]
    let li := c.layerIndexOf node
    let ni := c.nodeIdOf node
    if d.hasBarycenterAt li ni then fillPreOrdered c nodes (index + 1) (d.barycenterValueAt li ni) d
    else
      let nextValue := nextKnownBarycenter c d nodes (index + 1) (lastValue + floatOne)
      let computed := (lastValue + nextValue) / floatTwo
      fillPreOrdered c nodes (index + 1) computed (d.assign li ni computed)
  else d

/-- `fill_in_unknown_barycenters(nodes, pre_ordered, random)`. Pre-ordered: an unknown barycenter
becomes the mean of the previous value (initially `-1`) and the next known one (default previous
`+ 1`). Otherwise: `nextFloat() * (max(0, known barycenters) + 2) - 1`, one draw per node without
barycenter (also for nodes without a state). -/
def fillInUnknownBarycenters (c : BarycenterContext) (nodes : Array LNodeId) (preOrdered : Bool)
    (d : BarycenterData) : BarycenterData := Id.run do
  let mut d := d
  if preOrdered then
    return fillPreOrdered c nodes 0 floatMinusOne d
  else
    let mut maxBary : Float := floatZero
    for node in nodes do
      if let some bary := d.barycenter? (c.layerIndexOf node) (c.nodeIdOf node) then
        if bary > maxBary then maxBary := bary
    maxBary := maxBary + floatTwo
    for node in nodes do
      let li := c.layerIndexOf node
      let ni := c.nodeIdOf node
      if (d.barycenter? li ni).isNone then
        let (raw, d') := d.drawFloat c.randomTrace fun _ => s!"barycenter::fill_in_unknown_barycenters node={c.nodeLabel node}"
        d := d'.assign li ni (raw * maxBary - floatOne)
  return d

/-- `randomize_barycenters(nodes, random)`: barycenter = summed weight = `nextDouble()`, degree `1`
(one draw per node, also without a state). -/
def randomizeBarycenters (c : BarycenterContext) (nodes : Array LNodeId) (d : BarycenterData) : BarycenterData := Id.run do
  let mut d := d
  for node in nodes do
    let (value, d') := d.drawDouble c.randomTrace fun _ => s!"barycenter::randomize_barycenters node={c.nodeLabel node}"
    d := d'.assign (c.layerIndexOf node) (c.nodeIdOf node) value
  return d

/-- The Rust sort comparator of `minimize_crossings_layer`: known barycenters ascending
(`partial_cmp`, NaN equal), known before unknown, unknowns equal. -/
def compareBarycenters : Option Float → Option Float → Ordering
  | some l, some r => Float.comparePartial l r
  | some _, none => .lt
  | none, some _ => .gt
  | none, none => .eq

/-- The barycenter of state `(li, ni)` of a states table (`none` without a state). -/
@[inline] def stateBarycenter (states : Array (Array (Option BarycenterState))) (li ni : Nat) : Option Float :=
  if h : li < states.size then
    let row := states[li]
    if h2 : ni < row.size then
      match row[ni] with
      | some st => st.barycenter
      | none => none
    else none
  else none

/-- `get_barycenter(node)` on explicit states. -/
@[inline] def barycenterIn (c : BarycenterContext) (states : Array (Array (Option BarycenterState))) (n : LNodeId) :
    Option Float :=
  stateBarycenter states (c.layerIndexOf n) (c.nodeIdOf n)

/-- The barycenter keys of `layer[i:]`: value (`0.0` when unknown) and whether it is known. -/
partial def barycenterKeys (c : BarycenterContext) (states : Array (Array (Option BarycenterState))) (layer : Array LNodeId)
    (i : Nat) (values : FloatArray) (known : ByteArray) : FloatArray × ByteArray :=
  if h : i < layer.size then
    let n := layer[i]
    let li := c.layerIndexOf n
    let ni := c.nodeIdOf n
    if BarycenterState.knownIn states li ni then
      barycenterKeys c states layer (i + 1) (values.push (BarycenterState.valueIn states li ni)) (known.push 1)
    else barycenterKeys c states layer (i + 1) (values.push floatZero) (known.push 0)
  else (values, known)

/-- `compareBarycenters (key i) (key j) == .gt` of the comparator below (known before unknown,
known by `partial_cmp`). -/
@[inline] def keyGreater (values : FloatArray) (known : ByteArray) (i j : Nat) : Bool :=
  if known.get! i != 0 then known.get! j != 0 && values.get! i > values.get! j
  else known.get! j != 0

/-- The stable sort of `minimize_crossings_layer` (Rust sorts indices by the pre-extracted
barycenters with `sort_by`): positions sorted by the extracted keys (`compareBarycenters`) with
`keyedStableSort` (`stableSort`'s algorithm on the unboxed keys). -/
def sortByBarycenter (c : BarycenterContext) (states : Array (Array (Option BarycenterState))) (layer : Array LNodeId) :
    Array LNodeId :=
  if layer.size < 2 then layer
  else
    let (values, known) := barycenterKeys c states layer 0 (FloatArray.emptyWithCapacity layer.size)
      (ByteArray.emptyWithCapacity layer.size)
    let sorted := keyedStableSort layer.size (keyGreater values known)
    sorted.map fun i => layer[i]!

/-- `is_first_layer(node_order, current_index, forward_sweep)`: the start index is `0` forward and
`length - 1` (saturating) backward. -/
@[inline] def isFirstLayer (order : Array (Array LNodeId)) (currentIndex : Nat) (forwardSweep : Bool) : Bool :=
  currentIndex == (if forwardSweep then 0 else order.size - 1)

end BarycenterHeuristic

/-! ## The heuristic -/

/-- `BarycenterHeuristic` (the mutable Rust fields are `IO.Ref`s; the barycenter states are the
resolver's `barycenterStates`). -/
structure BarycenterHeuristic where
  /-- `port_ranks`: the copy of the distributor's ranks. -/
  portRanks : IO.Ref FloatArray
  /-- `constraint_resolver` (shares its state, including `barycenterStates`). -/
  constraintResolver : ForsterConstraintResolver
  /-- `port_distributor`. -/
  portDistributor : BarycenterPortDistributor
  /-- `sweep_iteration` (only used by the elk-rs port rank traces). -/
  sweepIteration : IO.Ref Nat
  /-- `snapshot` (`set_snapshot`). -/
  snapshot : IO.Ref (Option CrossMinSnapshot)

namespace BarycenterHeuristic

/-- `BarycenterHeuristic::new(constraint_resolver, port_distributor)` (Java additionally takes the
random generator and the node order). -/
def new (constraintResolver : ForsterConstraintResolver) (portDistributor : BarycenterPortDistributor) :
    BaseIO BarycenterHeuristic := do
  return {
    portRanks := ← IO.mkRef FloatArray.empty, constraintResolver, portDistributor
    sweepIteration := ← IO.mkRef 0, snapshot := ← IO.mkRef none }

/-- `set_snapshot(snapshot)`: also hands it to the port distributor and the constraint resolver. -/
def setSnapshot (h : BarycenterHeuristic) (s : CrossMinSnapshot) : BaseIO Unit := do
  h.portDistributor.setSnapshot s
  h.constraintResolver.setSnapshot s
  h.snapshot.set (some s)

/-- The context of one computation on the current arena. -/
def context (h : BarycenterHeuristic) (forward : Bool) : LayeredM BarycenterContext := do
  return {
    arena := ← get, snapshot := ← h.snapshot.get, portRanks := ← h.portRanks.get, forward
    randomTrace := RandomTrace.isEnabled, crossminTrace := ElkTrace.global.crossmin }

/-- Runs a pure step on the resolver's barycenter states and the caller's generator, then prints
the pending `CROSSMIN_RANDOM_TRACE` lines. -/
def runOnStates (h : BarycenterHeuristic) (random : IO.Ref Random) (f : BarycenterData → BarycenterData) : LayeredM Unit := do
  let states ← h.constraintResolver.barycenterStates.swap #[]
  let rnd ← random.get
  let d := f { states, random := rnd }
  h.constraintResolver.barycenterStates.set d.states
  random.set d.random
  for (method, value, location) in d.traces do
    RandomTrace.trace method value location

/-- `get_barycenter(node)`. -/
def getBarycenter (h : BarycenterHeuristic) (node : LNodeId) : LayeredM (Option Float) := do
  let c ← h.context true
  return barycenterIn c (← h.constraintResolver.barycenterStates.get) node

/-- The barycenter state of a node (`bary_state(layer_index_of(node), node_id_of(node))`). -/
def stateOf (h : BarycenterHeuristic) (node : LNodeId) : LayeredM (Option BarycenterState) := do
  let c ← h.context true
  return ({ states := ← h.constraintResolver.barycenterStates.get } : BarycenterData).state? (c.layerIndexOf node) (c.nodeIdOf node)

/-- `is_external_port_dummy(node)`. -/
def isExternalPortDummy (h : BarycenterHeuristic) (node : LNodeId) : LayeredM Bool := do
  return (← h.context true).isExternalPortDummy node

/-- `calculate_barycenters(nodes, forward, random)` on the heuristic's states. -/
def calculateBarycentersM (h : BarycenterHeuristic) (nodes : Array LNodeId) (forward : Bool) (random : IO.Ref Random) :
    LayeredM Unit := do
  let c ← h.context forward
  h.runOnStates random (calculateBarycenters c nodes)

/-- `fill_in_unknown_barycenters(nodes, pre_ordered, random)` on the heuristic's states. -/
def fillInUnknownBarycentersM (h : BarycenterHeuristic) (nodes : Array LNodeId) (preOrdered : Bool) (random : IO.Ref Random) :
    LayeredM Unit := do
  let c ← h.context true
  h.runOnStates random (fillInUnknownBarycenters c nodes preOrdered)

/-- `minimize_crossings_layer(layer, pre_ordered, randomize, forward, random)`: randomised or
computed and filled-in barycenters; a layer with more than one node is sorted stably by
barycenter and the constraints are resolved. Returns the new layer order. -/
def minimizeCrossingsLayer (h : BarycenterHeuristic) (layer : Array LNodeId) (preOrdered randomize forward : Bool)
    (random : IO.Ref Random) : LayeredM (Array LNodeId) := do
  let c ← h.context forward
  if randomize then
    h.runOnStates random (randomizeBarycenters c layer)
  else
    h.runOnStates random fun d => fillInUnknownBarycenters c layer preOrdered (calculateBarycenters c layer d)
  if layer.size > 1 then
    let sorted := sortByBarycenter c (← h.constraintResolver.barycenterStates.get) layer
    h.constraintResolver.processConstraints sorted
  else
    return layer

/-- The port rank step of `minimize_crossings`: unless the free layer is the first one, the ranks
of the fixed layer (`OUTPUT` ports forward, `INPUT` backward) are computed and copied. -/
def updatePortRanks (h : BarycenterHeuristic) (order : Array (Array LNodeId)) (freeLayerIndex : Nat) (forwardSweep : Bool) :
    LayeredM Unit := do
  if !isFirstLayer order freeLayerIndex forwardSweep then
    let fixedLayerIndex := if forwardSweep then freeLayerIndex - 1 else freeLayerIndex + 1
    let portType : PortType := if forwardSweep then .output else .input
    if let some layer := order[fixedLayerIndex]? then
      h.portDistributor.calculatePortRanks layer portType
      h.portRanks.set (← h.portDistributor.portRanksF)

/-- `pre_ordered` of `minimize_crossings`: not the first sweep, or the free layer starts with an
external port dummy. -/
def preOrderedFor (h : BarycenterHeuristic) (freeLayer : Array LNodeId) (isFirstSweep : Bool) : LayeredM Bool := do
  if !isFirstSweep then return true
  match freeLayer[0]? with
  | some n => h.isExternalPortDummy n
  | none => return false

/-- `set_first_layer_order(order, forward_sweep, random)`: randomised barycenters on the first
(forward) or last layer. Never reports an improvement. -/
def setFirstLayerOrder (h : BarycenterHeuristic) (order : Array (Array LNodeId)) (forwardSweep : Bool) (random : IO.Ref Random) :
    LayeredM (Array (Array LNodeId) × Bool) := do
  let startIndex := if forwardSweep then 0 else order.size - 1
  let some layer := order[startIndex]? | return (order, false)
  let layer ← h.minimizeCrossingsLayer layer false true forwardSweep random
  return (order.setIfInBounds startIndex layer, false)

/-- `minimize_crossings(order, free_layer_index, forward_sweep, is_first_sweep, random)`. Never
reports an improvement. -/
def minimizeCrossings (h : BarycenterHeuristic) (order : Array (Array LNodeId)) (freeLayerIndex : Nat)
    (forwardSweep isFirstSweep : Bool) (random : IO.Ref Random) : LayeredM (Array (Array LNodeId) × Bool) := do
  h.updatePortRanks order freeLayerIndex forwardSweep
  let some freeLayer := order[freeLayerIndex]? | return (order, false)
  let preOrdered ← h.preOrderedFor freeLayer isFirstSweep
  let layer ← h.minimizeCrossingsLayer freeLayer preOrdered false forwardSweep random
  return (order.setIfInBounds freeLayerIndex layer, false)

/-- `init_at_layer_level(layer_index, node_order)`: the resolver's, then `Layer.id := layer index`. -/
def initAtLayerLevel (h : BarycenterHeuristic) (l : Nat) (order : Array (Array LNodeId)) : LayeredM Unit := do
  h.constraintResolver.initAtLayerLevel l order
  if let some first := (order[l]?).bind (·[0]?) then
    if let some layer := (← getNode first).layer then
      modifyLayer layer fun x => { x with id := l }

/-- The `IInitializable` part: layer/node level delegate to the resolver (its port/edge levels are
no-ops), `initAfterTraversal` copies the distributor's ranks. -/
def initializable (h : BarycenterHeuristic) : Initializable where
  initAtLayerLevel := h.initAtLayerLevel
  initAtNodeLevel := h.constraintResolver.initAtNodeLevel
  initAfterTraversal := do h.portRanks.set (← h.portDistributor.portRanksF)
  usesPortLevel := false
  usesEdgeLevel := false

/-- The `ICrossingMinimizationHeuristic` view; `random` is the caller's generator used by
`setFirstLayerOrder`/`minimizeCrossings`. Not deterministic, never always improving. -/
def toHeuristic (h : BarycenterHeuristic) (random : IO.Ref Random) : CrossingMinimizationHeuristic where
  initializable := h.initializable
  alwaysImproves := pure false
  setFirstLayerOrder := fun order forwardSweep => h.setFirstLayerOrder order forwardSweep random
  minimizeCrossings := fun order freeLayerIndex forwardSweep isFirstSweep =>
    h.minimizeCrossings order freeLayerIndex forwardSweep isFirstSweep random
  isDeterministic := pure false
  resetSweepIteration := h.sweepIteration.set 0
  incrementSweepIteration := h.sweepIteration.modify (· + 1)
  setSnapshot := h.setSnapshot

end BarycenterHeuristic

end Elk.Alg.Layered.P3Order
