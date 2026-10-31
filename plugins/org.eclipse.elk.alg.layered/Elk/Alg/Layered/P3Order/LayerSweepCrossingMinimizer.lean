import Elk.Alg.Layered.LayeredPhases
import Elk.Alg.Layered.Options
import Elk.Alg.Layered.P3Order.GraphInfoHolder
import Elk.Alg.Layered.Intermediate.Preserveorder.ModelOrderNodeComparator
import Elk.Alg.Layered.Intermediate.SortByInputModelProcessor
import Elk.Core.Util.ElkTrace
/-!
# `org.eclipse.elk.alg.layered.p3order.LayerSweepCrossingMinimizer`

The layer sweep crossing minimiser (elk-rs `layer_sweep_crossing_minimizer.rs`, the oracle): one
`GraphInfoHolder` per (nested) graph, sweeps over the layers with the heuristic of the
`CrossMinType`, hierarchical sweeps into nested graphs whose `LayerSweepTypeDecider` decided against
a bottom-up layout, and the best node and port orders written back at the end. It is the
`CrossingMinimizationStrategy.LAYER_SWEEP` (`BARYCENTER`) and `MEDIAN_LAYER_SWEEP` (`MEDIAN`) phase
and the `ONE_SIDED_GREEDY_SWITCH`/`TWO_SIDED_GREEDY_SWITCH` intermediate processors (elk-rs
`LayerSweepAsProcessor`); all are named `LayerSweepCrossingMinimizer` (the elk-rs trace name).

## State
One `process` call runs on a fresh `LayerSweepCrossingMinimizer` value (Rust creates a new minimiser
per call) in `SweepM := StateRefT LayerSweepCrossingMinimizer LayeredM`. The holders are kept in an
array indexed like Rust's `graph_index` (BFS order from the root, also stored in `LGraph.id`); the
`BTreeSet<usize>`s are membership arrays iterated in ascending index order. Crossings are counted
again on every request like Java (elk-rs cached the count per graph until a sweep dirtied it; the
counters' shared position array makes a recount observable, see `countCurrentNumberOfCrossings`).

## Random numbers
elk-rs `Random` clones share their state (`Arc<Mutex<u64>>`). `initialize` takes the root graph's
`RANDOM` (`LayeredM.graphRandom?`, default `Random(0)`) into the minimiser's `IO.Ref Random` `random`;
it draws the seed (`nextLong`), is handed to the root holder (which draws the distributor's
`nextBoolean`, and whose heuristic draws all its numbers from it) and draws every sweep direction
(`next_boolean_for_graph`); `reset_random_for_all_graphs` reseeds it. A nested graph's holder gets the
nested graph's own `RANDOM` (a separate ref, or the same ref when the graph shares its generator with
an earlier one, see `LGraphInternals.randomOwner`; a fresh `Random(0)` without `RANDOM`). Nothing
else reads a `RANDOM` while the minimiser runs, so every shared state is written back with
`LayeredM.setGraphRandom` once, when `process` ends (also on the early returns after
`initialize`).

## Orders reproduced
* `initialize`: BFS from the root over `GraphInfoHolder.childGraphs` (nodes in layer order); a graph
  with `dontSweepInto` is *prepended* to the sweep list, so the deepest/last such graph comes first
  and decides the minimising method.
* `countCurrentNumberOfCrossings`: the graph, then recursively the child graphs that are swept into,
  in `childGraphs` order (Java). The model-order variant adds only the start graph's model order
  changes; `countModelOrderNodeChanges`/`…PortChanges` follow Java: layer `0` is its own previous
  layer, a fresh comparator per layer (per node for ports), every node's long edge targets are
  preprocessed.
* `sweep_reducing_crossings`: the first layer's ports are distributed, the hierarchical nodes of the
  first layer are swept into, then every further layer is minimised, its ports distributed and its
  hierarchical nodes swept into; `|=` always evaluates the right-hand side.
* `save_all_node_orders_of_changed_graphs`/`set_currently_best_node_orders`: ascending graph index.

## Rust semantics kept where they differ from Java
* The `FIRST_TRY_WITH_INITIAL_ORDER`/`SECOND_TRY_WITH_INITIAL_ORDER` flags are holder fields (Java:
  graph properties, which survive the call).
* `compare_different_randomized_layouts` resets the heuristic's sweep iteration and increments it
  after every iteration (tracing only).
* The greedy switch processors are not hierarchy aware (`LayerSweepAsProcessor` keeps the
  `ILayoutProcessor` default; Java's `LayerSweepCrossingMinimizer` is an
  `IHierarchyAwareLayoutProcessor`). The greedy switch is only configured on the root graph of a
  hierarchical layout, so this does not change which graphs it runs on.
* The progress monitor task is `Minimize Crossings <Rust Debug name>` (e.g. `Barycenter`).

## Deviations from Rust (no observable difference on valid input)
* Where Rust would panic on an index (`current_node_order()[start]` of an empty nested graph, the
  dummy index of `sort_ports_by_dummy_positions_in_last_layer`), the empty case is skipped and the
  index overrun throws `IndexOutOfBoundsException`; `sort_port_dummies_by_port_positions` throws
  `IllegalStateException` with the Rust panic message.
* Of the `ELK_TRACE_CROSSMIN*` diagnostics only the `crossmin: sweep layer=… order=[…]` and
  `crossmin: with_counter …` lines are reproduced (same format); `CROSSMIN_RANDOM_TRACE` lines are for the
  seed, the sweep directions and (in `GraphInfoHolder`) the distributor draw.
-/
namespace Elk.Alg.Layered.P3Order

open Elk.Core.Alg Elk.Core.Options Elk.Core.Util Elk.Alg.Layered Elk.Alg.Layered.Graph Elk.Alg.Layered.Options
open Elk.Alg.Layered.Intermediate Elk.Alg.Layered.Intermediate.Preserveorder Elk.Alg.Layered.P3Order.Counting
open LayeredM

/-- elk-rs `MinimizingMethod`. -/
inductive MinimizingMethod where
  | compareRandomized
  | noCounter
  | withCounter
  deriving BEq, Repr, Inhabited

/-- `LayerSweepCrossingMinimizer` (the state of one `process` run). -/
structure LayerSweepCrossingMinimizer where
  /-- `cross_min_type`. -/
  crossMinType : CrossMinType
  /-- `graph_info_holders`, indexed by graph index. -/
  graphInfoHolders : Array GraphInfoHolder := #[]
  /-- `graphs_whose_node_order_changed` (`BTreeSet<usize>` as membership by index). -/
  graphsWhoseNodeOrderChanged : Array Bool := #[]
  /-- `random`: the shared generator (see the module doc). -/
  random : IO.Ref Random
  /-- `random_seed` (`u64` in Rust; `setSeed` wraps). -/
  randomSeed : Int := 0
  /-- The shared generators to write back: the graph holding the `RANDOM` state and its ref. -/
  randomRefs : Array (LGraphId × IO.Ref Random) := #[]

/-- The minimiser monad. -/
abbrev SweepM := StateRefT LayerSweepCrossingMinimizer LayeredM

namespace LayerSweepCrossingMinimizer

/-! ## Small helpers (Rust free functions) -/

/-- `BTreeSet::insert` on a membership array. -/
@[inline] def setInsert (s : Array Bool) (i : Nat) : Array Bool :=
  if i < s.size then s.set! i true else (s ++ Array.replicate (i + 1 - s.size) false).set! i true

/-- `BTreeSet::contains`. -/
@[inline] def setContains (s : Array Bool) (i : Nat) : Bool := s[i]?.getD false

/-- The members in ascending order (`BTreeSet` iteration). -/
def setMembers (s : Array Bool) : Array Nat := Id.run do
  let mut out := #[]
  for h : i in [0:s.size] do
    if s[i] then out := out.push i
  return out

/-- `first_index(is_forward, length)`. -/
@[inline] def firstIndex (isForward : Bool) (length : Nat) : Nat := if isForward then 0 else length - 1

/-- `end_index(is_forward, length)`. -/
@[inline] def endIndex (isForward : Bool) (length : Nat) : Nat := if isForward then length - 1 else 0

/-- `first_free(is_forward, length)` (`isize`). -/
@[inline] def firstFree (isForward : Bool) (length : Nat) : Int := if isForward then 1 else (length : Int) - 2

/-- `next(is_forward)`. -/
@[inline] def next (isForward : Bool) : Int := if isForward then 1 else -1

/-- `is_not_end(length, index, is_forward)`. -/
@[inline] def isNotEnd (length : Nat) (index : Int) (isForward : Bool) : Bool :=
  if isForward then index < (length : Int) else index >= 0

/-- `side_opposed_sweep_direction(is_forward)`. -/
@[inline] def sideOpposedSweepDirection (isForward : Bool) : PortSide := if isForward then .west else .east

/-- `is_on_end_of_sweep_side(port, on_right_most_layer)`. -/
@[inline] def isOnEndOfSweepSide (side : PortSide) (onRightMostLayer : Bool) : Bool :=
  if onRightMostLayer then side == .east else side == .west

/-- Rust `Debug` name of a `CrossMinType` (progress monitor task name). -/
def crossMinTypeDebugName : CrossMinType → String
  | .barycenter => "Barycenter"
  | .oneSidedGreedySwitch => "OneSidedGreedySwitch"
  | .twoSidedGreedySwitch => "TwoSidedGreedySwitch"
  | .median => "Median"

/-- `graph_id(graph)`: `LGraph.id as usize` (the holder index set by `initialize`). -/
def graphIndexOf (g : LGraphId) : LayeredM Nat := do return asUsize (← getGraph g).id

/-- `collect_hierarchical_targets(layer)`: the nodes with a nested graph and the nested graph's index. -/
def collectHierarchicalTargets (layer : Array LNodeId) : LayeredM (Array (LNodeId × Nat)) := do
  let mut out := #[]
  for node in layer do
    let some nested := (← getNode node).nestedGraph | continue
    out := out.push (node, ← graphIndexOf nested)
  return out

/-- Java's `ClassCastException` of `(LPort) node.getProperty(ORIGIN)` (`originPort`) for an origin of
another class (JDK message for classes of the application class loader). -/
def originPortCastError (origin : Origin) : Option String :=
  let cls := match origin with
    | .elkNode _ => some "org.eclipse.elk.graph.impl.ElkNodeImpl"
    | .elkPort _ => some "org.eclipse.elk.graph.impl.ElkPortImpl"
    | .elkEdge _ => some "org.eclipse.elk.graph.impl.ElkEdgeImpl"
    | .elkLabel _ => some "org.eclipse.elk.graph.impl.ElkLabelImpl"
    | .lGraph _ => some "org.eclipse.elk.alg.layered.graph.LGraph"
    | .lNode _ => some "org.eclipse.elk.alg.layered.graph.LNode"
    | .lEdge _ => some "org.eclipse.elk.alg.layered.graph.LEdge"
    | .lLabel _ => some "org.eclipse.elk.alg.layered.graph.LLabel"
    | .lPort _ => none
  cls.map fun c =>
    s!"java.lang.ClassCastException: class {c} cannot be cast to class org.eclipse.elk.alg.layered.graph.LPort " ++
    s!"({c} and org.eclipse.elk.alg.layered.graph.LPort are in unnamed module of loader 'app')"

/-- The core of `sort_ports_by_dummy_positions_in_last_layer[_snap]`: walks the parent's ports and
replaces every hierarchical port (`INSIDE_CONNECTIONS`) on the end-of-sweep side by the `ORIGIN` port
of the next node of `lastLayer` (from the first index of the sweep direction onwards). Java assumes
that the layer holds one external port dummy per such port: running past the layer is its
`ArrayIndexOutOfBoundsException`, a node whose origin is no port (e.g. a normal node, `ElkNode`) its
`ClassCastException` of `originPort`. A node without origin is not consumed (elk-rs; Java would put
`null` into the port list). -/
def replaceHierarchicalPorts (lastLayer : Array LNodeId) (parent : LNodeId) (onRightMostLayer : Bool) :
    LayeredM Unit := do
  let mut j : Int := firstIndex onRightMostLayer lastLayer.size
  let mut ports := (← getNode parent).ports
  for i in [0:ports.size] do
    let some port := ports[i]? | continue
    let pt ← getPort port
    if isOnEndOfSweepSide pt.side onRightMostLayer && pt.internal.insideConnections then
      let some dummy := (if j < 0 then none else lastLayer[j.toNat]?)
        | throw (IO.userError s!"java.lang.ArrayIndexOutOfBoundsException: Index {j} out of bounds for length {lastLayer.size}")
      match (← getNode dummy).internal.origin with
      | some (.lPort origin) =>
        ports := ports.set! i origin
        j := j + next onRightMostLayer
      | some other =>
        if let some msg := originPortCastError other then throw (IO.userError msg)
      | none => pure ()
  modifyNode parent fun n => { n with ports := ports }

/-- `sort_ports_by_dummy_positions_in_last_layer(node_order, parent, on_right_most_layer)`: only when
the last (right-most) or first layer starts with an external port dummy. -/
def sortPortsByDummyPositionsInLastLayer (nodeOrder : Array (Array LNodeId)) (parent : LNodeId)
    (onRightMostLayer : Bool) : LayeredM Unit := do
  let some lastLayer := nodeOrder[endIndex onRightMostLayer nodeOrder.size]? | return
  let some first := lastLayer[firstIndex onRightMostLayer lastLayer.size]? | return
  if (← getNode first).type != .externalPort then return
  replaceHierarchicalPorts lastLayer parent onRightMostLayer

/-- `sort_ports_by_dummy_positions_in_last_layer_snap(node_order, parent, on_right_most_layer,
snapshot)`: the same on the flat node indices of a `SweepCopy` (`SweepCopy.nodes`, mapped to flat
indices here; the node type of the first dummy is the captured one). -/
def sortPortsByDummyPositionsInLastLayerSnap (nodeOrder : Array (Array LNodeId)) (parent : LNodeId)
    (onRightMostLayer : Bool) (snapshot : CrossMinSnapshot) : LayeredM Unit := do
  let some lastLayer := nodeOrder[endIndex onRightMostLayer nodeOrder.size]? | return
  let some first := lastLayer[firstIndex onRightMostLayer lastLayer.size]? | return
  if snapshot.nodeTypeOf (snapshot.nodeFlatIndex first) != .externalPort then return
  replaceHierarchicalPorts (lastLayer.map fun n => snapshot.nodeRef (snapshot.nodeFlatIndex n)) parent onRightMostLayer

/-- `sort_port_dummies_by_port_positions(parent_node, layer_close_to_edge, side)`: the `PORT_DUMMY`s of
the parent's hierarchical ports on `side` in north-south/east-west order. -/
def sortPortDummiesByPortPositions (parentNode : LNodeId) (layerCloseToEdge : Array LNodeId) (side : PortSide) :
    LayeredM (Array LNodeId) := do
  let a ← get
  let mut sortedDummies : Array LNodeId := #[]
  for port in CrossMinUtil.inNorthSouthEastWestOrder a parentNode side do
    let pt := a.port port
    if pt.internal.insideConnections then
      if let some dummy := pt.internal.portDummy then
        sortedDummies := sortedDummies.push dummy
  if sortedDummies.size < layerCloseToEdge.size then
    throw (IO.userError s!"java.lang.IllegalStateException: Expected {layerCloseToEdge.size} hierarchical ports, but found only {sortedDummies.size}.")
  return sortedDummies

/-! ## Model order counts -/

/-- The comparators' view of graph `g`: its own options (Java passes `currentGraph.lGraph()`; elk-rs
held the processed graph locked, so its `try_lock` fell back to the defaults there). -/
def graphContext (g : LGraphId) : LayeredM ModelOrderGraphContext :=
  ModelOrderGraphContext.ofGraph g

/-- The previous layer of `layerIndex`: Java's `previousLayer == -1 ? layers[0] : layers[previousLayer]`,
so layer `0` is its own previous layer (elk-rs: empty). -/
@[inline] def previousLayerOf (layers : Array (Array LNodeId)) (layerIndex : Nat) : Array LNodeId :=
  (if layerIndex == 0 then layers[0]? else layers[layerIndex - 1]?).getD #[]

/-- The pairs `(active[p], active[k])`, `k > p`, of `countModelOrderNodeChanges` from `(p, k)` on: the
comparator after them and `acc` plus the number of pairs ordered the other way round. -/
partial def nodeChangePairs (layer : Array LNodeId) (active : Array Nat) (p k : Nat) (comp : ModelOrderNodeComparator)
    (acc : Int) : LayeredM (ModelOrderNodeComparator × Int) := do
  if h : p < active.size then
    if h2 : k < active.size then
      let (value, comp) ← comp.compare layer[active[p]]! layer[active[k]]!
      nodeChangePairs layer active p (k + 1) comp (if value > 0 then acc + 1 else acc)
    else nodeChangePairs layer active (p + 1) (p + 2) comp acc
  else return (comp, acc)

/-- The indices of the nodes of `layer[i:]` with `MODEL_ORDER`, pushed onto `out`. -/
partial def modelOrderIndices (a : LGraphArena) (layer : Array LNodeId) (i : Nat) (out : Array Nat) : Array Nat :=
  if h : i < layer.size then
    modelOrderIndices a layer (i + 1) (if (a.node layer[i]).internal.modelOrder.isSome then out.push i else out)
  else out

/-- The layers `layers[li:]` of `countModelOrderNodeChanges`. -/
partial def nodeChangeLayers (layers : Array (Array LNodeId)) (li : Nat) (comp : ModelOrderNodeComparator) (acc : Int) :
    LayeredM Int := do
  if h : li < layers.size then
    let layer := layers[li]
    let comp := comp.resetForPreviousLayerSlice (previousLayerOf layers li)
    let active := modelOrderIndices (← get) layer 0 #[]
    let (comp, acc) ← nodeChangePairs layer active 0 1 comp acc
    nodeChangeLayers layers (li + 1) comp acc
  else return acc

/-- `countModelOrderNodeChanges(graph, layers, strategy, cmGroupOrderStrategy)` with the monadic
`ModelOrderNodeComparator.compare` (the reference of `countModelOrderNodeChanges`, differential test
`layered.p3.modelOrderChangeCounts`): pairs `i < j` of nodes with `MODEL_ORDER` of each layer that the
node comparator orders the other way round (a fresh comparator per layer, here: reset;
`previousLayerOf`). The loops are tail-recursive functions (`nodeChangeLayers`, `nodeChangePairs`)
with the same comparison sequence. -/
def countModelOrderNodeChangesRef (graph : ModelOrderGraphContext) (layers : Array (Array LNodeId))
    (strategy : OrderingStrategy) (groupStrategy : GroupOrderStrategy) : LayeredM Int :=
  nodeChangeLayers layers 0 (ModelOrderNodeComparator.new graph #[] strategy .equal groupStrategy false) 0

/-- `nodeChangePairs` with the pure `NodeCmpEnv.compareCore` (the number of pairs, or Java's exception
text). -/
partial def nodeChangePairsIn (a : LGraphArena) (env : NodeCmpEnv) (layer : Array LNodeId) (active : Array Nat)
    (p k : Nat) (rel : ModelOrderRelations LNodeId) (acc : Nat) : Except String Nat :=
  if h : p < active.size then
    if h2 : k < active.size then
      let (value, rel) := NodeCmpEnv.compareCore a env rel layer[active[p]]! layer[active[k]]!
      if NodeCmpEnv.isFailure value then .error (NodeCmpEnv.failureText value)
      else nodeChangePairsIn a env layer active p (k + 1) rel (if value > 0 then acc + 1 else acc)
    else nodeChangePairsIn a env layer active (p + 1) (p + 2) rel acc
  else .ok acc

/-- `nodeChangeLayers` with the pure comparator (fresh relations per layer). -/
partial def nodeChangeLayersIn (a : LGraphArena) (env : NodeCmpEnv) (layers : Array (Array LNodeId)) (li : Nat)
    (acc : Nat) : Except String Nat :=
  if h : li < layers.size then
    let layer := layers[li]
    let env := env.resetForPreviousLayer (previousLayerOf layers li)
    let active := modelOrderIndices a layer 0 #[]
    match nodeChangePairsIn a env layer active 0 1 (ModelOrderRelations.emptyWithCapacity active.size) acc with
    | .ok acc => nodeChangeLayersIn a env layers (li + 1) acc
    | .error msg => .error msg
  else .ok acc

/-- `countModelOrderNodeChanges(graph, layers, strategy, cmGroupOrderStrategy)`: `countModelOrderNodeChangesRef`
with the pure comparator on the arena (`NodeCmpEnv`; the comparator does not write the arena): the
same comparisons in the same order with the same relations, and the same exception. -/
def countModelOrderNodeChanges (graph : ModelOrderGraphContext) (layers : Array (Array LNodeId))
    (strategy : OrderingStrategy) (_groupStrategy : GroupOrderStrategy) : LayeredM Int := do
  match nodeChangeLayersIn (← get) (NodeCmpEnv.new graph #[] strategy .equal false) layers 0 0 with
  | .ok n => return n
  | .error msg => throw (IO.userError msg)

/-- The pairs `(ports[i], ports[j])`, `j > i`, of `countModelOrderPortChanges` from `(i, j)` on. -/
partial def portChangePairs (ports : Array LPortId) (i j : Nat) (comp : ModelOrderPortComparator) (acc : Int) :
    LayeredM (ModelOrderPortComparator × Int) := do
  if h : i < ports.size then
    if h2 : j < ports.size then
      let (value, comp) ← comp.compare ports[i] ports[j]
      portChangePairs ports i (j + 1) comp (if value > 0 then acc + 1 else acc)
    else portChangePairs ports (i + 1) (i + 2) comp acc
  else return (comp, acc)

/-- The nodes `nodes[k:]` of one layer of `countModelOrderPortChanges`. -/
partial def portChangeNodes (nodes : Array LNodeId) (k : Nat) (comp : ModelOrderPortComparator) (acc : Int) :
    LayeredM (ModelOrderPortComparator × Int) := do
  if h : k < nodes.size then
    let node := nodes[k]
    let longEdgeTargets ← SortByInputModelProcessor.longEdgeTargetNodePreprocessing node
    let ports := (← getNode node).ports
    if ports.size < 2 then portChangeNodes nodes (k + 1) comp acc
    else
      let (comp, acc) ← portChangePairs ports 0 1 (comp.resetForNodeTargetModelOrder (some longEdgeTargets)) acc
      portChangeNodes nodes (k + 1) comp acc
  else return (comp, acc)

/-- The layers `layers[li:]` of `countModelOrderPortChanges`. -/
partial def portChangeLayers (layers : Array (Array LNodeId)) (li : Nat) (comp : ModelOrderPortComparator) (acc : Int) :
    LayeredM Int := do
  if h : li < layers.size then
    let (comp, acc) ← portChangeNodes layers[li] 0 (comp.resetForPreviousLayerSlice (previousLayerOf layers li)) acc
    portChangeLayers layers (li + 1) comp acc
  else return acc

/-- `countModelOrderPortChanges(graph, layers, groupOrderStrategy)`: pairs `i < j` of ports of every
node that the port comparator orders the other way round. Like Java a fresh comparator per node
(here: reset), and `longEdgeTargetNodePreprocessing` for every node — it caches
`TARGET_NODE_MODEL_ORDER` and sets `LONG_EDGE_TARGET_NODE` also on nodes with fewer than two ports
(elk-rs skipped those first). The loops are tail-recursive functions (`portChangeLayers`,
`portChangeNodes`, `portChangePairs`) with the same calls in the same order. The monadic reference of
`countModelOrderPortChanges` (differential test `layered.p3.modelOrderChangeCounts`). -/
def countModelOrderPortChangesRef (graph : ModelOrderGraphContext) (layers : Array (Array LNodeId))
    (strategy : OrderingStrategy) (portModelOrder : Bool) : LayeredM Int :=
  portChangeLayers layers 0 (ModelOrderPortComparator.new graph #[] strategy none portModelOrder) 0

/-- `portChangePairs` with the pure `PortCmpEnv.compareCore` (the number of pairs, or Java's exception
text). -/
partial def portChangePairsIn (a : LGraphArena) (env : PortCmpEnv) (ports : Array LPortId) (i j : Nat)
    (rel : ModelOrderRelations LPortId) (acc : Nat) : Except String Nat :=
  if h : i < ports.size then
    if h2 : j < ports.size then
      let (value, rel) := PortCmpEnv.compareCore a env rel ports[i] ports[j]
      if value == PortCmpEnv.failed then .error maxModelOrderNodesNullError
      else portChangePairsIn a env ports i (j + 1) rel (if value > 0 then acc + 1 else acc)
    else portChangePairsIn a env ports (i + 1) (i + 2) rel acc
  else .ok acc

/-- `portChangeNodes` with the pure comparator: `longEdgeTargetNodePreprocessing` (which writes the
arena) for every node, then the pairs of its ports on the arena after it (fresh relations per node). -/
partial def portChangeNodesIn (nodes : Array LNodeId) (k : Nat) (env : PortCmpEnv) (acc : Nat) : LayeredM Nat := do
  if h : k < nodes.size then
    let node := nodes[k]
    let longEdgeTargets ← SortByInputModelProcessor.longEdgeTargetNodePreprocessing node
    let a ← get
    let ports := (a.node node).ports
    if ports.size < 2 then portChangeNodesIn nodes (k + 1) env acc
    else
      match portChangePairsIn a (env.resetForNodeTargetModelOrder (some longEdgeTargets)) ports 0 1
          (ModelOrderRelations.emptyWithCapacity ports.size) acc with
      | .ok acc => portChangeNodesIn nodes (k + 1) env acc
      | .error msg => throw (IO.userError msg)
  else return acc

/-- `portChangeLayers` with the pure comparator. -/
partial def portChangeLayersIn (layers : Array (Array LNodeId)) (li : Nat) (env : PortCmpEnv) (acc : Nat) :
    LayeredM Nat := do
  if h : li < layers.size then
    let acc ← portChangeNodesIn layers[li] 0 (env.resetForPreviousLayer (previousLayerOf layers li)) acc
    portChangeLayersIn layers (li + 1) env acc
  else return acc

/-- `countModelOrderPortChanges(graph, layers, groupOrderStrategy)`: `countModelOrderPortChangesRef` with
the pure comparator on the arena (`PortCmpEnv`): the same preprocessing, comparisons, relations and
exception in the same order. -/
def countModelOrderPortChanges (graph : ModelOrderGraphContext) (layers : Array (Array LNodeId))
    (strategy : OrderingStrategy) (portModelOrder : Bool) : LayeredM Int := do
  return ((← portChangeLayersIn layers 0 (PortCmpEnv.new graph #[] strategy none portModelOrder) 0 : Nat) : Int)

/-! ## Holder access -/

/-- The holder of a graph index (`graph_info_holders[index]`). -/
def holderAt (index : Nat) : SweepM GraphInfoHolder := do
  match (← get).graphInfoHolders[index]? with
  | some h => return h
  | none => throw (IO.userError s!"java.lang.IndexOutOfBoundsException: graph info holder {index}")

/-- Updates a holder in place. -/
@[inline] def modifyHolder (index : Nat) (f : GraphInfoHolder → GraphInfoHolder) : SweepM Unit :=
  modify fun s => { s with graphInfoHolders := s.graphInfoHolders.modify index f }

/-- Takes the current node order out of a holder (so the heuristics own it uniquely). -/
def takeOrder (index : Nat) : SweepM (Array (Array LNodeId)) := do
  let h ← holderAt index
  modifyHolder index fun h => { h with currentNodeOrder := #[] }
  return h.currentNodeOrder

/-- Puts a node order back. -/
@[inline] def putOrder (index : Nat) (order : Array (Array LNodeId)) : SweepM Unit :=
  modifyHolder index fun h => { h with currentNodeOrder := order }

/-- `GraphInfoHolder::set_first_layer_order(forward_sweep)`. -/
def setFirstLayerOrder (index : Nat) (forwardSweep : Bool) : SweepM Bool := do
  let order ← takeOrder index
  let h ← holderAt index
  let (order, improved) ← h.crossMinimizer.setFirstLayerOrder order forwardSweep
  putOrder index order
  return improved

/-- `GraphInfoHolder::minimize_crossings_on_layer(free_layer_index, forward_sweep, is_first_sweep)`. -/
def minimizeCrossingsOnLayer (index freeLayerIndex : Nat) (forwardSweep isFirstSweep : Bool) : SweepM Bool := do
  let order ← takeOrder index
  let h ← holderAt index
  let (order, improved) ← h.crossMinimizer.minimizeCrossings order freeLayerIndex forwardSweep isFirstSweep
  putOrder index order
  return improved

/-- `GraphInfoHolder::distribute_ports_while_sweeping(current_index, is_forward_sweep)`. -/
def distributePortsWhileSweeping (index currentIndex : Nat) (isForwardSweep : Bool) : SweepM Bool := do
  let h ← holderAt index
  h.portDistributor.distributePortsWhileSweeping h.currentNodeOrder currentIndex isForwardSweep

/-! ## Bookkeeping -/

/-- `graphs_whose_node_order_changed.insert(index)`. -/
@[inline] def markNodeOrderChanged (index : Nat) : SweepM Unit :=
  modify fun s => { s with graphsWhoseNodeOrderChanged := setInsert s.graphsWhoseNodeOrderChanged index }

/-- `choose_minimizing_method(root_index)`. -/
def chooseMinimizingMethod (rootIndex : Nat) : SweepM MinimizingMethod := do
  let parent ← holderAt rootIndex
  if !(← parent.crossMinimizer.isDeterministic) then return .compareRandomized
  else if ← parent.crossMinimizer.alwaysImproves then return .noCounter
  else return .withCounter

/-- `reset_random_for_all_graphs()`: reseeds the shared generator only (Java likewise). -/
def resetRandomForAllGraphs : SweepM Unit := do
  let s ← get
  s.random.modify (·.setSeed s.randomSeed)

/-- `next_boolean_for_graph(index)`: the sweep direction from the shared generator
(`ELK_DEBUG_CROSSMIN_FORCE_SWEEP=forward|backward` forces it). -/
def nextBooleanForGraph (_index : Nat) : SweepM Bool := do
  match ElkTrace.global.debugCrossminForceSweep with
  | some "forward" => return true
  | some "backward" => return false
  | _ => pure ()
  let v ← (← get).random.modifyGet (·.nextBoolean)
  RandomTrace.traceNextBoolean v "crossing_min::sweep_direction"

/-- `parent_snapshot_for(index)`: the parent holder's current order and port positions and the
parent node. -/
def parentSnapshotFor (s : LayerSweepCrossingMinimizer) (index : Nat) :
    Option (Array (Array LNodeId) × IO.Ref (Array Int) × LNodeId) := do
  let holder ← s.graphInfoHolders[index]?
  let parentIndex ← holder.parentGraphIndex
  let parent ← s.graphInfoHolders[parentIndex]?
  let parentNode ← holder.parentNode
  return (parent.currentNodeOrder, parent.portPositions, parentNode)

/-- `prepare_cross_minimizer(index)`: refreshes the greedy switch context (greedy types only). -/
def prepareCrossMinimizer (index : Nat) : SweepM Unit := do
  let s ← get
  if !(s.crossMinType == .oneSidedGreedySwitch || s.crossMinType == .twoSidedGreedySwitch) then return
  let some holder := s.graphInfoHolders[index]? | return
  let parentSnapshot := if holder.hasParent then parentSnapshotFor s index else none
  holder.updateGreedyContext parentSnapshot

/-- `collect_child_graph_indices(index)`: the graph indices of the holder's child graphs. -/
def collectChildGraphIndices (index : Nat) : SweepM (Array Nat) := do
  let h ← holderAt index
  h.childGraphs.mapM fun c => (graphIndexOf c : LayeredM Nat)

/-- `save_all_node_orders_of_changed_graphs()`. -/
def saveAllNodeOrdersOfChangedGraphs : SweepM Unit := do
  for index in setMembers (← get).graphsWhoseNodeOrderChanged do
    let h ← (← holderAt index).updateBestFromCurrentlyBestOrCurrent
    modifyHolder index fun _ => h

/-- `set_currently_best_node_orders()`. -/
def setCurrentlyBestNodeOrders : SweepM Unit := do
  for index in setMembers (← get).graphsWhoseNodeOrderChanged do
    let h ← (← holderAt index).updateCurrentlyBestFromCurrent
    modifyHolder index fun _ => h

/-! ## Crossing counts -/

/-- `countCurrentNumberOfCrossings(currentGraph)`: the crossings of the graph and, recursively in
`childGraphs` order, of every nested graph swept into. Like Java every call counts again (elk-rs
cached the count per graph until a sweep dirtied it): the counters' shared position array keeps the
positions of the last count, and the in-layer counts read them for far ends they do not number
themselves, so a recount of an unchanged order can differ (and fail) where the first did not. -/
partial def countCurrentNumberOfCrossings (index : Nat) : SweepM Int := do
  let mut totalCrossings ← (← holderAt index).countCurrentCrossings
  for childIndex in ← collectChildGraphIndices index do
    if !(← holderAt childIndex).dontSweepInto then
      totalCrossings := totalCrossings + (← countCurrentNumberOfCrossings childIndex)
  return totalCrossings

/-- `countCurrentNumberOfCrossingsNodePortOrder(currentGraph)`: the start graph's model order changes
weighted by its node and port influence (counted first), plus its crossings, plus the plain
crossings of the nested graphs swept into, summed in Java's `double` order. -/
def countCurrentNumberOfCrossingsNodePortOrder (startIndex : Nat) : SweepM Float := do
  let h ← holderAt startIndex
  let mut totalCrossings : Float := 0.0
  let mut modelOrderInfluence : Float := 0.0
  if h.considerModelOrderStrategy != .none then
    let order := h.currentNodeOrder
    let ctx ← graphContext h.lGraph
    let nodeChanges ← countModelOrderNodeChanges ctx order h.considerModelOrderStrategy h.groupOrderStrategy
    modelOrderInfluence := modelOrderInfluence + h.nodeInfluence * Float.ofInt nodeChanges
    let portChanges ← countModelOrderPortChanges ctx order h.considerModelOrderStrategy h.portModelOrder
    modelOrderInfluence := modelOrderInfluence + h.portInfluence * Float.ofInt portChanges
  let crossings ← (← holderAt startIndex).countCurrentCrossings
  totalCrossings := totalCrossings + (Float.ofInt crossings + modelOrderInfluence)
  for childIndex in ← collectChildGraphIndices startIndex do
    if !(← holderAt childIndex).dontSweepInto then
      totalCrossings := totalCrossings + Float.ofInt (← countCurrentNumberOfCrossings childIndex)
  return totalCrossings

/-! ## Sweeps -/

/-- `ELK_TRACE_CROSSMIN`: `crossmin: sweep layer=<i> order=[<nodes>]` after a layer was ordered
(elk-rs `format_layer_nodes`, `LNode.toString()`). -/
def traceSweepLayer (index layerIndex : Nat) : SweepM Unit := do
  if !ElkTrace.global.crossmin then return
  let a ← getThe LGraphArena
  let layer := ((← holderAt index).currentNodeOrder[layerIndex]?).getD #[]
  IO.eprintln s!"crossmin: sweep layer={layerIndex} order=[{", ".intercalate (layer.toList.map a.nodeToString)}]"

mutual

/-- `sweep_reducing_crossings(index, forward, first_sweep)`. -/
partial def sweepReducingCrossings (index : Nat) (forward firstSweep : Bool) : SweepM Bool := do
  let length := (← holderAt index).currentNodeOrder.size
  if length == 0 then return false
  prepareCrossMinimizer index
  let first := firstIndex forward length
  let mut improved ← distributePortsWhileSweeping index first forward
  traceSweepLayer index first
  let hasChildren := !(← holderAt index).childGraphs.isEmpty
  if hasChildren then
    let targets ← collectHierarchicalTargets (((← holderAt index).currentNodeOrder[first]?).getD #[])
    let r ← sweepInHierarchicalNodes targets forward firstSweep
    improved := improved || r
  let mut i := firstFree forward length
  while isNotEnd length i forward do
    let iN := i.toNat
    let allowFirstSweep ← do
      let h ← holderAt index
      pure (firstSweep && !h.firstTryWithInitialOrder)
    prepareCrossMinimizer index
    let r1 ← minimizeCrossingsOnLayer index iN forward allowFirstSweep
    improved := improved || r1
    let r2 ← distributePortsWhileSweeping index iN forward
    improved := improved || r2
    traceSweepLayer index iN
    if hasChildren then
      let targets ← collectHierarchicalTargets (((← holderAt index).currentNodeOrder[iN]?).getD #[])
      let r3 ← sweepInHierarchicalNodes targets forward firstSweep
      improved := improved || r3
    i := i + next forward
  markNodeOrderChanged index
  return improved

/-- `sweep_in_hierarchical_nodes(hierarchical_nodes, is_forward_sweep, is_first_sweep)`. -/
partial def sweepInHierarchicalNodes (hierarchicalNodes : Array (LNodeId × Nat)) (isForwardSweep isFirstSweep : Bool) :
    SweepM Bool := do
  let mut improved := false
  for (node, nestedIndex) in hierarchicalNodes do
    if !(← holderAt nestedIndex).dontSweepInto then
      let r ← sweepInHierarchicalNode isForwardSweep node nestedIndex isFirstSweep
      improved := improved || r
  return improved

/-- `sweep_in_hierarchical_node(is_forward_sweep, node, nested_index, is_first_sweep)`: the first
layer of the nested graph is ordered by the parent's port positions (external port dummies) or by
the heuristic, then the nested graph is swept and the parent's ports follow its last layer. Java
reads `nestedGraphNodeOrder[startIndex][0]` unguarded: a nested graph without layers (index `0`,
or `-1` backwards) or with an empty first layer fails with `ArrayIndexOutOfBoundsException`
(agent HMO; elk-rs skipped the first layer's ordering and swept the empty graph). -/
partial def sweepInHierarchicalNode (isForwardSweep : Bool) (node : LNodeId) (nestedIndex : Nat) (isFirstSweep : Bool) :
    SweepM Bool := do
  let order := (← holderAt nestedIndex).currentNodeOrder
  if order.isEmpty then
    let index : Int := if isForwardSweep then 0 else -1
    throw (IO.userError s!"java.lang.ArrayIndexOutOfBoundsException: Index {index} out of bounds for length 0")
  let startIndex := firstIndex isForwardSweep order.size
  let startLayer := order[startIndex]?.getD #[]
  if startLayer.isEmpty then
    throw (IO.userError "java.lang.ArrayIndexOutOfBoundsException: Index 0 out of bounds for length 0")
  if let some firstNode := startLayer[0]? then
    if (← getNode firstNode).type == .externalPort then
      let sorted ← sortPortDummiesByPortPositions node startLayer (sideOpposedSweepDirection isForwardSweep)
      modifyHolder nestedIndex fun h => { h with currentNodeOrder := h.currentNodeOrder.setIfInBounds startIndex sorted }
    else
      prepareCrossMinimizer nestedIndex
      let _ ← setFirstLayerOrder nestedIndex isForwardSweep
  let improved ← sweepReducingCrossings nestedIndex isForwardSweep isFirstSweep
  let h ← holderAt nestedIndex
  if let some parent := h.parentNode then
    sortPortsByDummyPositionsInLastLayer h.currentNodeOrder parent isForwardSweep
  return improved

end

/-! ## Minimising methods -/

/-- `minimize_crossings_no_counter(index)`: alternating sweeps until nothing improves. -/
def minimizeCrossingsNoCounter (index : Nat) : SweepM Unit := do
  let mut isForwardSweep ← nextBooleanForGraph index
  let mut improved := true
  while improved do
    prepareCrossMinimizer index
    improved ← setFirstLayerOrder index isForwardSweep
    let r ← sweepReducingCrossings index isForwardSweep false
    improved := improved || r
    isForwardSweep := !isForwardSweep
  setCurrentlyBestNodeOrders

/-- The start of `minimizeCrossingsWithCounter`/`…NodePortOrderWithCounter` after the initial-order
check: the first layer order (unless the initial order is tried), the first sweep and the update of
the initial-order flag. Java's `FIRST_TRY_WITH_INITIAL_ORDER` and `SECOND_TRY_WITH_INITIAL_ORDER` share
one property id, so "clear the second try, then move a pending first try to the second" leaves the
flag `false`: only the first iteration of a `compareDifferentRandomizedLayouts` keeps the initial
order (elk-rs: separate flags, so its second iteration keeps it too, sweeping backwards). Returns the
sweep direction used. -/
def firstSweepWithCounter (index : Nat) (isForwardSweep : Bool) : SweepM Bool := do
  let mut isForwardSweep := isForwardSweep
  let h ← holderAt index
  let useInitial := h.firstTryWithInitialOrder && h.considerModelOrderStrategy != .none
  if !useInitial then
    prepareCrossMinimizer index
    let _ ← setFirstLayerOrder index isForwardSweep
  else
    isForwardSweep := h.firstTryWithInitialOrder
  let _ ← sweepReducingCrossings index isForwardSweep true
  modifyHolder index fun h => { h with firstTryWithInitialOrder := false }
  return isForwardSweep

/-- `minimize_crossings_with_counter(index)`: sweeps in alternating directions while the crossing
count decreases; the count before the last sweep. -/
def minimizeCrossingsWithCounter (index : Nat) : SweepM Int := do
  let mut isForwardSweep ← nextBooleanForGraph index
  let initialCrossingsCount ← countCurrentNumberOfCrossings index
  let initialCrossings := Float.ofInt initialCrossingsCount
  if ElkTrace.global.crossmin then IO.eprintln s!"crossmin: with_counter initial_crossings={initialCrossingsCount}"
  if initialCrossings == 0.0 && (← holderAt index).firstTryWithInitialOrder then return 0
  isForwardSweep ← firstSweepWithCounter index isForwardSweep
  let mut crossingsInGraph ← countCurrentNumberOfCrossings index
  if ElkTrace.global.crossmin then IO.eprintln s!"crossmin: with_counter crossings_in_graph={crossingsInGraph}"
  let mut oldNumberOfCrossings : Int := 0
  repeat
    setCurrentlyBestNodeOrders
    if crossingsInGraph == 0 then return 0
    isForwardSweep := !isForwardSweep
    oldNumberOfCrossings := crossingsInGraph
    let _ ← sweepReducingCrossings index isForwardSweep false
    crossingsInGraph ← countCurrentNumberOfCrossings index
    if ElkTrace.global.crossmin then
      IO.eprintln s!"crossmin: with_counter sweep done old={oldNumberOfCrossings} new={crossingsInGraph}"
    if oldNumberOfCrossings <= crossingsInGraph then break
  return oldNumberOfCrossings

/-- `minimize_crossings_node_port_order_with_counter(index)`: like `minimizeCrossingsWithCounter`
with the model-order-weighted count. -/
def minimizeCrossingsNodePortOrderWithCounter (index : Nat) : SweepM Float := do
  let mut isForwardSweep ← nextBooleanForGraph index
  let initialCrossings ← countCurrentNumberOfCrossingsNodePortOrder index
  if initialCrossings == 0.0 && (← holderAt index).firstTryWithInitialOrder then return 0.0
  isForwardSweep ← firstSweepWithCounter index isForwardSweep
  let mut crossingsInGraph ← countCurrentNumberOfCrossingsNodePortOrder index
  let mut oldNumberOfCrossings : Float := 0.0
  repeat
    setCurrentlyBestNodeOrders
    if crossingsInGraph == 0.0 then return 0.0
    isForwardSweep := !isForwardSweep
    oldNumberOfCrossings := crossingsInGraph
    let _ ← sweepReducingCrossings index isForwardSweep false
    crossingsInGraph ← countCurrentNumberOfCrossingsNodePortOrder index
    if oldNumberOfCrossings <= crossingsInGraph then break
  return oldNumberOfCrossings

/-- The model-order-weighted branch of `compare_different_randomized_layouts` (taken when the node
influence is not zero; Rust and Java test the node influence twice). -/
def compareRandomizedNodePortOrder (index : Nat) (thoroughness : Int) : SweepM Unit := do
  let mut bestCrossings : Float := Float.maxValue
  for _ in [0:thoroughness.toNat] do
    let crossings ← minimizeCrossingsNodePortOrderWithCounter index
    (← holderAt index).crossMinimizer.incrementSweepIteration
    if crossings < bestCrossings then
      bestCrossings := crossings
      saveAllNodeOrdersOfChangedGraphs
      if bestCrossings == 0.0 then break

/-- The plain branch of `compare_different_randomized_layouts`. -/
def compareRandomizedPlain (index : Nat) (thoroughness : Int) : SweepM Unit := do
  let mut bestCrossings : Int := 2147483647
  for _ in [0:thoroughness.toNat] do
    let crossings ← minimizeCrossingsWithCounter index
    (← holderAt index).crossMinimizer.incrementSweepIteration
    if crossings < bestCrossings then
      bestCrossings := crossings
      saveAllNodeOrdersOfChangedGraphs
      if bestCrossings == 0 then break

/-- `compare_different_randomized_layouts(index)`: `thoroughness` randomised runs, the best one kept. -/
def compareDifferentRandomizedLayouts (index : Nat) : SweepM Unit := do
  resetRandomForAllGraphs
  modify fun s => { s with graphsWhoseNodeOrderChanged := #[] }
  let h ← holderAt index
  if h.considerModelOrderStrategy != .none then
    modifyHolder index fun h => { h with firstTryWithInitialOrder := true }
  h.crossMinimizer.resetSweepIteration
  if h.nodeInfluence != 0.0 then
    compareRandomizedNodePortOrder index h.thoroughness
  else
    compareRandomizedPlain index h.thoroughness

/-- `set_port_order_on_parent_graph(index)`: with external ports, the parent node's hierarchical
ports follow the best sweep's first and last layers and get `FIXED_ORDER`. -/
def setPortOrderOnParentGraph (index : Nat) : SweepM Unit := do
  let h ← holderAt index
  let best ← h.bestSweep
  if !h.hasExternalPorts then return
  let some best := best | return
  let some parent := h.parentNode | return
  sortPortsByDummyPositionsInLastLayerSnap best.nodes parent true h.snapshot
  sortPortsByDummyPositionsInLastLayerSnap best.nodes parent false h.snapshot
  setNodeProp parent LayeredOptions.PORT_CONSTRAINTS PortConstraints.fixedOrder

/-- `minimize_crossings(graphs_to_sweep_on, method)`. -/
def minimizeCrossings (graphsToSweepOn : Array Nat) (method : MinimizingMethod) : SweepM Unit := do
  for index in graphsToSweepOn do
    let hasLayers := (((← get).graphInfoHolders[index]?).map (!·.currentNodeOrder.isEmpty)).getD false
    if !hasLayers then continue
    match method with
    | .noCounter => minimizeCrossingsNoCounter index
    | .compareRandomized => compareDifferentRandomizedLayouts index
    | .withCounter => let _ ← minimizeCrossingsWithCounter index
    if (((← get).graphInfoHolders[index]?).map (·.hasParent)).getD false then
      setPortOrderOnParentGraph index

/-! ## Initialisation and write-back -/

/-- The generator of a graph's holder: the shared one for the root, otherwise the graph's `RANDOM`
(one ref per shared state) or a fresh `Random(0)`. -/
def randomFor (graph : LGraphId) (isRoot : Bool) : SweepM (IO.Ref Random) := do
  if isRoot then return (← get).random
  match ← LayeredM.graphRandom? graph with
  | none => IO.mkRef (Random.ofInt 0)
  | some r =>
    let holderGraph ← LayeredM.randomHolder graph
    match (← get).randomRefs.find? (·.1 == holderGraph) with
    | some (_, ref) => return ref
    | none =>
      let ref ← IO.mkRef r
      modify fun s => { s with randomRefs := s.randomRefs.push (holderGraph, ref) }
      return ref

/-- Takes the root graph's `RANDOM` into the shared generator and draws the seed. -/
def initializeRandom (root : LGraphId) : SweepM Unit := do
  let rootRandom ← LayeredM.graphRandom? root
  let s ← get
  s.random.set (rootRandom.getD (Random.ofInt 0))
  if rootRandom.isSome then
    let holderGraph ← LayeredM.randomHolder root
    modify fun s => { s with randomRefs := s.randomRefs.push (holderGraph, s.random) }
  RandomTrace.resetCounter
  let rawSeed ← s.random.modifyGet (·.nextLong)
  let seed ← RandomTrace.traceNextLong rawSeed "graph_info_holder::initialize"
  modify fun s => { s with randomSeed := seed }

/-- `initialize(root_graph, root_graph_guard)`: one holder per graph in BFS order (`LGraph.id :=
index`); returns the graphs to sweep on (those with `dontSweepInto`, last found first). -/
def initializeGraphs (root : LGraphId) : SweepM (Array Nat) := do
  modify fun s => { s with graphInfoHolders := #[], graphsWhoseNodeOrderChanged := #[] }
  initializeRandom root
  let crossMinType := (← get).crossMinType
  let mut graphsToSweepOn : Array Nat := #[]
  let mut queue : Array LGraphId := #[root]
  let mut head := 0
  while h : head < queue.size do
    let graph := queue[head]
    head := head + 1
    let index := (← get).graphInfoHolders.size
    modifyGraph graph fun g => { g with id := index }
    let random ← randomFor graph (graph == root)
    let gData ← GraphInfoHolder.new graph crossMinType random
    let holders := (← get).graphInfoHolders
    let parentIndex := gData.parentGraphRef.bind fun parentGraph =>
      holders.findIdx? (·.lGraph == parentGraph)
    let gData := { gData with parentGraphIndex := parentIndex }
    queue := queue ++ gData.childGraphs
    modify fun s => { s with graphInfoHolders := s.graphInfoHolders.push gData }
    if gData.dontSweepInto then
      graphsToSweepOn := #[index] ++ graphsToSweepOn
  return graphsToSweepOn

/-- `transfer_node_and_port_orders_to_graph(root_graph, root_graph_guard)`: every holder's best sweep
is written to its graph (with port constraints). -/
def transferNodeAndPortOrdersToGraph : SweepM Unit := do
  for h in (← get).graphInfoHolders do
    if let some bestSweep ← h.bestSweep then
      bestSweep.transferNodeAndPortOrdersToGraph h.lGraph true h.snapshot

/-- Writes every holder's `FIRST_TRY_WITH_INITIAL_ORDER` back to its graph. Java keeps the flag on
the `LGraph`: a run that returns early because the initial order has no crossings leaves it `true`,
and a later run on the same graph (e.g. the greedy switch processor, whose `minimizeCrossingsWithCounter`
does not set it) reads it; elk-rs starts every run with a cleared flag. -/
def writeBackFirstTries : SweepM Unit := do
  for h in (← get).graphInfoHolders do
    modifyGraph h.lGraph fun g => { g with internal := { g.internal with firstTryWithInitialOrder := h.firstTryWithInitialOrder } }

/-- Writes the shared generators back to their graphs. -/
def writeBackRandoms : SweepM Unit := do
  for (graph, ref) in (← get).randomRefs do
    LayeredM.setGraphRandom graph (← ref.get)

/-- The early exit of `process_graph`: an empty graph, or a single node outside a hierarchical layout. -/
def isTrivial (graph : LGraphId) : LayeredM Bool := do
  let a ← get
  let gr := a.graph graph
  let emptyGraph := gr.layers.all fun l => (a.layer l).nodes.isEmpty
  let singleNode := gr.layers.size == 1 && (gr.layers[0]?.map fun l => (a.layer l).nodes.size == 1).getD false
  let hierarchicalLayout := gr.props.getD LayeredOptions.HIERARCHY_HANDLING HierarchyHandling.inherit == .includeChildren
  return emptyGraph || (singleNode && !hierarchicalLayout)

/-- `process_graph(graph, monitor)`. -/
def processGraph (graph : LGraphId) (monitor : ProgressMonitor) : SweepM Unit := do
  let _ ← monitor.begin s!"Minimize Crossings {crossMinTypeDebugName (← get).crossMinType}" 1.0
  if ← isTrivial graph then
    monitor.done
    return
  let graphsToSweepOn ← initializeGraphs graph
  let some first := graphsToSweepOn[0]? | do
    writeBackRandoms
    monitor.done
  let method ← chooseMinimizingMethod first
  minimizeCrossings graphsToSweepOn method
  transferNodeAndPortOrdersToGraph
  writeBackFirstTries
  writeBackRandoms
  monitor.done

/-- `process(graph, monitor)`: a fresh minimiser per call. -/
def process (crossMinType : CrossMinType) (graph : LGraphId) (monitor : ProgressMonitor) : LayeredM Unit := do
  let random ← IO.mkRef (Random.ofInt 0)
  let s : LayerSweepCrossingMinimizer := { crossMinType, random }
  let ((), _) ← (processGraph graph monitor).run s

/-- `INTERMEDIATE_PROCESSING_CONFIGURATION`: `LONG_EDGE_SPLITTER` before P3,
`IN_LAYER_CONSTRAINT_PROCESSOR` before P4, `LONG_EDGE_JOINER` after P5. -/
def intermediateProcessingConfiguration : LayeredProcessorConfiguration :=
  (LayoutProcessorConfiguration.create : LayeredProcessorConfiguration)
    |>.addBefore .p3NodeOrdering .longEdgeSplitter
    |>.addBefore .p4NodePlacement .inLayerConstraintProcessor
    |>.addAfter .p5EdgeRouting .longEdgeJoiner

/-- `get_layout_processor_configuration(graph)`: the intermediate configuration plus
`PORT_LIST_SORTER` before P3. -/
def getLayoutProcessorConfiguration (_graph : LGraphId) : LayeredM (Option LayeredProcessorConfiguration) :=
  return some ((LayoutProcessorConfiguration.createFrom intermediateProcessingConfiguration).addBefore
    .p3NodeOrdering .portListSorter)

/-- The phase (`LayerSweepCrossingMinimizer::new(cross_min_type)`), hierarchy aware. -/
def phase (crossMinType : CrossMinType) : LayeredPhase :=
  { name := "LayerSweepCrossingMinimizer"
    process := process crossMinType
    getLayoutProcessorConfiguration := getLayoutProcessorConfiguration
    isHierarchyAware := true }

/-- elk-rs `LayerSweepAsProcessor::new(cross_min_type)`: the minimiser as an intermediate processor
(trace name `LayerSweepCrossingMinimizer`; not hierarchy aware, see the module doc). -/
def processor (crossMinType : CrossMinType) : LayeredProcessor :=
  { name := "LayerSweepCrossingMinimizer", process := process crossMinType }

end LayerSweepCrossingMinimizer

/-- Registers `CrossingMinimizationStrategy.LAYER_SWEEP` → `BARYCENTER`. -/
builtin_initialize registerLayerSweepCrossingMinimizer : Unit ←
  LayeredPhases.registerPhase .p3NodeOrdering (ElkEnum.ordinal CrossingMinimizationStrategy.layerSweep)
    (pure (LayerSweepCrossingMinimizer.phase .barycenter))

/-- Registers `CrossingMinimizationStrategy.MEDIAN_LAYER_SWEEP` → `MEDIAN`. -/
builtin_initialize registerMedianLayerSweepCrossingMinimizer : Unit ←
  LayeredPhases.registerPhase .p3NodeOrdering (ElkEnum.ordinal CrossingMinimizationStrategy.medianLayerSweep)
    (pure (LayerSweepCrossingMinimizer.phase .median))

/-- Registers the `ONE_SIDED_GREEDY_SWITCH` processor. -/
builtin_initialize registerOneSidedGreedySwitch : Unit ←
  IntermediateProcessorStrategy.register .oneSidedGreedySwitch (LayerSweepCrossingMinimizer.processor .oneSidedGreedySwitch)

/-- Registers the `TWO_SIDED_GREEDY_SWITCH` processor. -/
builtin_initialize registerTwoSidedGreedySwitch : Unit ←
  IntermediateProcessorStrategy.register .twoSidedGreedySwitch (LayerSweepCrossingMinimizer.processor .twoSidedGreedySwitch)

end Elk.Alg.Layered.P3Order
