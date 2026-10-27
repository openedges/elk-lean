import Elk.Alg.Layered.Graph
import Elk.Alg.Layered.Options.LayeredOptions
import Elk.Alg.Layered.P3Order.Counting
import Elk.Alg.Layered.P3Order.CrossMinType
import Elk.Alg.Layered.P3Order.CrossMinSnapshot
import Elk.Alg.Layered.P3Order.PortDistributors
import Elk.Alg.Layered.P3Order.Heuristics
import Elk.Alg.Layered.P3Order.LayerSweepTypeDecider
import Elk.Alg.Layered.Intermediate.GreedySwitch.GreedySwitchHeuristic
import Elk.Core.Util.Random
/-!
# `org.eclipse.elk.alg.layered.p3order.GraphInfoHolder`

Collects the per-graph data of the layer sweep crossing minimisation (elk-rs `graph_info_holder.rs`):
the current node order (a copy of the layers, reordered by the heuristics; the graph's layers are
only rewritten from the best `SweepCopy` at the end), the best orders found, the child graphs, the
parent, the heuristic and the port distributor chosen for the `CrossMinType`, the crossings counter,
the sweep type decision (`dontSweepInto`) and the model order settings.

## Construction (Rust `build`)
1. `ISweepPortDistributor` (+ barycenter view): `SweepPortDistributor.createWithBarycenter`, which
   draws one `nextBoolean()` from the holder's generator unless the type is `TWO_SIDED_GREEDY_SWITCH`
   (node-relative for `true`, layer-total for `false`).
2. `AllCrossingsCounter.new graph order`.
3. The heuristic: `BARYCENTER` → a `ForsterConstraintResolver` and, with
   `CROSSING_MINIMIZATION_FORCE_NODE_MODEL_ORDER`, a `ModelOrderBarycenterHeuristic` (the processed
   graph is passed as `lockedGraph`, see its module doc), otherwise a `BarycenterHeuristic`;
   `MEDIAN` → `MedianHeuristic`; the greedy switch types → `GreedySwitchHeuristic`.
4. `LayerSweepTypeDecider.new graph parent hasParent (heuristic.isDeterministic)`.
5. The holder's own initialisation pass (`cachePortSides` and child graph collection per node in
   order, port count, zero port positions), then
   `Initializable.init #[counter, decider, distributor, heuristic] order`.
6. `CrossMinSnapshot.build order nPorts`, `heuristic.setSnapshot` and the counter's `setSnapshot`
   (`set_arena_sync` has no Lean counterpart: the counter reads the arena).
7. `useBottomUp := decider.useBottomUpWithBoundary order hierarchicalSweepiness`, then
   `updateGreedyContext none`.

## Random numbers
Rust's `Random` shares its state between clones (`Arc<Mutex<u64>>`): the holder's `random` field is
the generator its constructor was given (`new_with_graph`: the minimiser's shared generator, which is
the root graph's `RANDOM`; `new`: the graph's own `RANDOM`). Here the caller passes that generator as
an `IO.Ref Random` (the `LayerSweepCrossingMinimizer` keeps one ref per shared state and writes it back
to the graphs); `new` and `new_with_graph` therefore coincide. The heuristics capture the same ref
(`toHeuristic random`).

## Deviations
* `parent_graph_index` is resolved by the caller (Rust: likewise, `set_parent_graph_index`).
* `trace_in_layer_constraints` and the other `ELK_TRACE_CROSSMIN` output are not reproduced; the
  `CROSSMIN_RANDOM_TRACE` line of the distributor draw is printed from a replay of the saved state.
-/
namespace Elk.Alg.Layered.P3Order

open Elk.Core.Options Elk.Core.Util Elk.Alg.Layered.Graph Elk.Alg.Layered.Options
open Elk.Alg.Layered.P3Order.Counting Elk.Alg.Layered.Intermediate.GreedySwitch LayeredM

/-- `GraphInfoHolder`. -/
structure GraphInfoHolder where
  /-- `l_graph`. -/
  lGraph : LGraphId
  /-- `current_node_order`. -/
  currentNodeOrder : Array (Array LNodeId)
  /-- `currently_best_node_and_port_order`. -/
  currentlyBestNodeAndPortOrder : Option SweepCopy := none
  /-- `best_node_and_port_order`. -/
  bestNodeAndPortOrder : Option SweepCopy := none
  /-- `port_positions` (zeros, sized by the initialisation; never updated, as in Rust). -/
  portPositions : Array Int := #[]
  /-- `use_bottom_up` (`dont_sweep_into()`). -/
  useBottomUp : Bool := false
  /-- `child_graphs`: nested graphs of the nodes, in node order. -/
  childGraphs : Array LGraphId := #[]
  /-- `has_external_ports`. -/
  hasExternalPorts : Bool
  /-- `has_parent`. -/
  hasParent : Bool
  /-- `parent_graph_ref`: the graph of the parent node. -/
  parentGraphRef : Option LGraphId
  /-- `parent_graph_index`. -/
  parentGraphIndex : Option Nat := none
  /-- `parent_node`. -/
  parentNode : Option LNodeId
  /-- `cross_minimizer`. -/
  crossMinimizer : CrossingMinimizationHeuristic
  /-- The `GreedySwitchHeuristic` behind `crossMinimizer` (Rust `downcast_mut`). -/
  greedySwitch : Option GreedySwitchHeuristic := none
  /-- `port_distributor`. -/
  portDistributor : SweepPortDistributor
  /-- `crossings_counter`. -/
  crossingsCounter : AllCrossingsCounter
  /-- `n_ports`. -/
  nPorts : Nat := 0
  /-- `consider_model_order_strategy`. -/
  considerModelOrderStrategy : OrderingStrategy
  /-- `group_order_strategy`. -/
  groupOrderStrategy : GroupOrderStrategy
  /-- `port_model_order`. -/
  portModelOrder : Bool
  /-- `node_influence`. -/
  nodeInfluence : Float
  /-- `port_influence`. -/
  portInfluence : Float
  /-- `thoroughness` (`i32`). -/
  thoroughness : Int
  /-- `random` (see the module doc). -/
  random : IO.Ref Random
  /-- `first_try_with_initial_order`. -/
  firstTryWithInitialOrder : Bool := false
  /-- `second_try_with_initial_order`. -/
  secondTryWithInitialOrder : Bool := false
  /-- `snapshot`. -/
  snapshot : CrossMinSnapshot := {}

namespace GraphInfoHolder

/-- The heuristic of a `CrossMinType` (step 3 of `build`) and its greedy switch object. -/
def createCrossMinimizer (graph : LGraphId) (crossMinType : CrossMinType) (order : Array (Array LNodeId))
    (barycenterDistributor : Option BarycenterPortDistributor) (random : IO.Ref Random) (hasParent : Bool)
    (forceModelOrder : Bool) (maxModelOrderNodes : Int) (constraintsBetweenNonDummies : Bool)
    (groupOrderStrategy : GroupOrderStrategy) (lockedGraph : Option LGraphId) :
    LayeredM (CrossingMinimizationHeuristic × Option GreedySwitchHeuristic) := do
  match crossMinType with
  | .barycenter =>
    let resolver ← ForsterConstraintResolver.new order constraintsBetweenNonDummies
    let some distributor := barycenterDistributor
      | throw (IO.userError "java.lang.IllegalStateException: barycenter distributor missing")
    if forceModelOrder then
      let h ← ModelOrderBarycenterHeuristic.new resolver distributor forceModelOrder maxModelOrderNodes
        groupOrderStrategy lockedGraph
      return (h.toHeuristic random, none)
    else
      let h ← BarycenterHeuristic.new resolver distributor
      return (h.toHeuristic random, none)
  | .median => return (MedianHeuristic.new.toHeuristic random, none)
  | .oneSidedGreedySwitch | .twoSidedGreedySwitch =>
    let g ← GreedySwitchHeuristic.create crossMinType hasParent graph
    return (g.toHeuristic, some g)

/-- The holder's own `IInitializable` pass (Rust `init_initializables(&mut [holder], order)`):
`cachePortSides` and the nested graph of every node in order, one port count per port, and the
zero port positions. Returns the child graphs and the port count. -/
def initHolder (order : Array (Array LNodeId)) : LayeredM (Array LGraphId × Nat) := do
  let childGraphs ← IO.mkRef (#[] : Array LGraphId)
  let nPorts ← IO.mkRef (0 : Nat)
  let holderInit : Initializable := {
    initAtNodeLevel := fun l n nodeOrder => do
      let some node := (nodeOrder[l]?).bind (·[n]?) | return
      cachePortSides node
      if let some nested := (← getNode node).nestedGraph then
        childGraphs.modify (·.push nested)
    initAtPortLevel := fun _ _ _ _ => nPorts.modify (· + 1)
    usesEdgeLevel := false }
  Initializable.init #[holderInit] order
  return (← childGraphs.get, ← nPorts.get)

/-- The settings Rust reads from the graph in `new`/`new_with_graph`. -/
structure Settings where
  parentNode : Option LNodeId
  graphProperties : EnumSet GraphProperties
  forceModelOrder : Bool
  maxModelOrderNodes : Int
  constraintsBetweenNonDummies : Bool
  hierarchicalSweepiness : Float
  considerModelOrderStrategy : OrderingStrategy
  groupOrderStrategy : GroupOrderStrategy
  portModelOrder : Bool
  nodeInfluence : Float
  portInfluence : Float
  thoroughness : Int

/-- Reads the `Settings` of a graph (Rust `get_property(..).unwrap_or(..)` for every value). -/
def readSettings (graph : LGraphId) : LayeredM Settings := do
  let g ← getGraph graph
  let p := g.props
  return {
    parentNode := g.parentNode
    graphProperties := g.internal.graphProperties
    forceModelOrder := p.getD LayeredOptions.CROSSING_MINIMIZATION_FORCE_NODE_MODEL_ORDER false
    maxModelOrderNodes := g.internal.maxModelOrderNodes
    constraintsBetweenNonDummies := g.internal.inLayerSuccessorConstraintsBetweenNonDummies
    hierarchicalSweepiness := p.getD LayeredOptions.CROSSING_MINIMIZATION_HIERARCHICAL_SWEEPINESS 0.0
    considerModelOrderStrategy := p.getD LayeredOptions.CONSIDER_MODEL_ORDER_STRATEGY OrderingStrategy.none
    groupOrderStrategy := p.getD LayeredOptions.GROUP_MODEL_ORDER_CM_GROUP_ORDER_STRATEGY GroupOrderStrategy.onlyWithinGroup
    portModelOrder := p.getD LayeredOptions.CONSIDER_MODEL_ORDER_PORT_MODEL_ORDER false
    nodeInfluence := p.getD LayeredOptions.CONSIDER_MODEL_ORDER_CROSSING_COUNTER_NODE_INFLUENCE 0.0
    portInfluence := p.getD LayeredOptions.CONSIDER_MODEL_ORDER_CROSSING_COUNTER_PORT_INFLUENCE 0.0
    thoroughness := p.getD LayeredOptions.THOROUGHNESS 1 }

/-- `GraphInfoHolder::build(..)` (see the module doc for the steps). -/
def build (graph : LGraphId) (crossMinType : CrossMinType) (currentNodeOrder : Array (Array LNodeId))
    (s : Settings) (random : IO.Ref Random) (lockedGraph : Option LGraphId) : LayeredM GraphInfoHolder := do
  let hasParent := s.parentNode.isSome
  let parentGraphRef ← match s.parentNode with
    | some p => nodeGraph p
    | none => pure none
  let hasExternalPorts := s.graphProperties.contains .externalPorts
  let randomBefore ← random.get
  let (portDistributor, barycenterDistributor) ←
    SweepPortDistributor.createWithBarycenter crossMinType random currentNodeOrder.size
  if crossMinType != .twoSidedGreedySwitch then
    -- `random_trace::trace_next_boolean` of the factory's draw (replayed on the saved state)
    let _ ← RandomTrace.traceNextBoolean randomBefore.nextBoolean.1 "graph_info_holder::create_port_distributor"
  let crossingsCounter ← AllCrossingsCounter.new graph currentNodeOrder
  let (crossMinimizer, greedySwitch) ← createCrossMinimizer graph crossMinType currentNodeOrder
    barycenterDistributor random hasParent s.forceModelOrder s.maxModelOrderNodes s.constraintsBetweenNonDummies
    s.groupOrderStrategy lockedGraph
  let crossMinDeterministic ← crossMinimizer.isDeterministic
  let decider ← LayerSweepTypeDecider.new graph s.parentNode hasParent crossMinDeterministic
  let (childGraphs, nPorts) ← initHolder currentNodeOrder
  Initializable.init #[crossingsCounter.initializable, decider.initializable, portDistributor.initializable,
    crossMinimizer.initializable] currentNodeOrder
  let snapshot ← CrossMinSnapshot.build currentNodeOrder nPorts
  crossMinimizer.setSnapshot snapshot
  crossingsCounter.setSnapshot snapshot
  let useBottomUp ← decider.useBottomUpWithBoundary currentNodeOrder s.hierarchicalSweepiness
  -- `update_greedy_context(None)`
  if let some g := greedySwitch then g.setDontSweepInto useBottomUp
  return {
    lGraph := graph, currentNodeOrder, portPositions := Array.replicate nPorts 0, useBottomUp, childGraphs
    hasExternalPorts, hasParent, parentGraphRef, parentNode := s.parentNode, crossMinimizer, greedySwitch
    portDistributor, crossingsCounter, nPorts
    considerModelOrderStrategy := s.considerModelOrderStrategy, groupOrderStrategy := s.groupOrderStrategy
    portModelOrder := s.portModelOrder, nodeInfluence := s.nodeInfluence, portInfluence := s.portInfluence
    thoroughness := s.thoroughness, random, snapshot }

/-- `GraphInfoHolder::new(graph, cross_min_type)` / `new_with_graph(graph_ref, graph, cross_min_type,
shared_random)`: `random` is the generator Rust would use (see the module doc); `lockedGraph` is the
graph elk-rs holds locked while the minimiser runs (for `ModelOrderBarycenterHeuristic`). -/
def new (graph : LGraphId) (crossMinType : CrossMinType) (random : IO.Ref Random)
    (lockedGraph : Option LGraphId := none) : LayeredM GraphInfoHolder := do
  let order := (← get).graphToNodeArray graph
  let s ← readSettings graph
  build graph crossMinType order s random lockedGraph

/-- `dont_sweep_into()`. -/
@[inline] def dontSweepInto (h : GraphInfoHolder) : Bool := h.useBottomUp

/-- `best_sweep()`: the currently best order for deterministic heuristics, else the best one. -/
def bestSweep (h : GraphInfoHolder) : LayeredM (Option SweepCopy) := do
  if ← h.crossMinimizer.isDeterministic then return h.currentlyBestNodeAndPortOrder
  else return h.bestNodeAndPortOrder

/-- `update_currently_best_from_current()`. -/
def updateCurrentlyBestFromCurrent (h : GraphInfoHolder) : LayeredM GraphInfoHolder := do
  return { h with currentlyBestNodeAndPortOrder := some (← SweepCopy.new h.currentNodeOrder h.snapshot) }

/-- `update_best_from_currently_best_or_current()`. -/
def updateBestFromCurrentlyBestOrCurrent (h : GraphInfoHolder) : LayeredM GraphInfoHolder := do
  match h.currentlyBestNodeAndPortOrder with
  | some src => return { h with bestNodeAndPortOrder := some src }
  | none => return { h with bestNodeAndPortOrder := some (← SweepCopy.new h.currentNodeOrder h.snapshot) }

/-- `count_current_crossings()`. -/
def countCurrentCrossings (h : GraphInfoHolder) : LayeredM Int :=
  h.crossingsCounter.countAllCrossings h.currentNodeOrder

/-- `update_greedy_context(parent_snapshot)`: hands `dontSweepInto` and the parent data to the greedy
switch heuristic (no-op for the other heuristics). -/
def updateGreedyContext (h : GraphInfoHolder)
    (parentSnapshot : Option (Array (Array LNodeId) × Array Int × LNodeId)) : BaseIO Unit := do
  let some greedy := h.greedySwitch | return
  greedy.setDontSweepInto h.useBottomUp
  if let some (parentNodeOrder, parentPortPositions, parentNode) := parentSnapshot then
    greedy.updateParentContext parentNodeOrder parentPortPositions parentNode

end GraphInfoHolder

end Elk.Alg.Layered.P3Order
