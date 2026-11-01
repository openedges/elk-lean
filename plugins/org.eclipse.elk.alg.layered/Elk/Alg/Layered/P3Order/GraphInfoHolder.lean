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
1. `ISweepPortDistributor` (+ barycenter view): `PortDistributorImpl.create` (the draw of
   `SweepPortDistributor.createWithBarycenter`), one `nextBoolean()` from the holder's generator unless
   the type is `TWO_SIDED_GREEDY_SWITCH` (node-relative for `true`, layer-total for `false`).
2. `AllCrossingsCounter.new graph order`.
3. The heuristic: `BARYCENTER` → a `ForsterConstraintResolver` and, with
   `CROSSING_MINIMIZATION_FORCE_NODE_MODEL_ORDER`, a `ModelOrderBarycenterHeuristic`, otherwise a
   `BarycenterHeuristic`;
   `MEDIAN` → `MedianHeuristic`; the greedy switch types → `GreedySwitchHeuristic`.
4. `LayerSweepTypeDecider.new graph parent hasParent (heuristic.isDeterministic)`.
5. The holder's own initialisation pass (`cachePortSides` and child graph collection per node in
   order, port count, zero port positions), then
   `Initializable.init #[counter, decider, distributor, heuristic] order` — fused into one pass
   (`FusedInit.run`, see "Fused initialisation"; the generic path is kept with `fused := false`).
6. `CrossMinSnapshot.build order nPorts`, `heuristic.setSnapshot` and the counter's `setSnapshot`
   (`set_arena_sync` has no Lean counterpart: the counter reads the arena).
7. `useBottomUp := decider.useBottomUpWithBoundary order hierarchicalSweepiness`, then
   `updateGreedyContext none`.

## Random numbers
Rust's `Random` shares its state between clones (`Arc<Mutex<u64>>`): the holder's `random` field is
the generator its constructor was given (`new_with_graph`: the minimiser's shared generator, which is
the root graph's `RANDOM`; `new`: the graph's own `RANDOM`). Here the caller passes that generator as
an `IO.Ref Random` (the `LayerSweepCrossingMinimizer` keeps one ref per shared state and writes it back
to the graphs); `new` and `new_with_graph` therefore coincide. The heuristic's methods get the same ref
(`HeuristicImpl.setFirstLayerOrder h.random …`; the `CrossingMinimizationHeuristic` record of
`toHeuristic random` captures it).

## Direct calls (Lean only)
The holder keeps the concrete heuristic and port distributor (`HeuristicImpl`, `PortDistributorImpl`)
and calls them by a `match` instead of through the closure records `CrossingMinimizationHeuristic` and
`SweepPortDistributor` (which are built only for the generic initialisation): the same functions with
the same arguments, without the closures per holder and the `lean_apply` per call.

## Deviations
* `parent_graph_index` is resolved by the caller (Rust: likewise, `set_parent_graph_index`).
* `trace_in_layer_constraints` and the other `ELK_TRACE_CROSSMIN` output are not reproduced; the
  `CROSSMIN_RANDOM_TRACE` line of the distributor draw is printed from a replay of the saved state.
-/
namespace Elk.Alg.Layered.P3Order

open Elk.Core.Options Elk.Core.Util Elk.Alg.Layered.Graph Elk.Alg.Layered.Options
open Elk.Alg.Layered.P3Order.Counting Elk.Alg.Layered.Intermediate.GreedySwitch LayeredM

/-- Lean only: the concrete `ISweepPortDistributor` of a holder. The holder calls it directly (no
closure record) and the fused initialisation reads its state. -/
inductive PortDistributorImpl where
  /-- `NodeRelativePortDistributor` or `LayerTotalPortDistributor` (their `inner` distributor). -/
  | barycenter (d : AbstractBarycenterPortDistributor)
  /-- `GreedyPortDistributor` (`TWO_SIDED_GREEDY_SWITCH`). -/
  | greedy (d : GreedyPortDistributor)

namespace PortDistributorImpl

/-- `ISweepPortDistributor::create(cross_min_type, random, num_layers)` as the concrete object: the
same draw as `SweepPortDistributor.createWithBarycenter` (one `nextBoolean()` unless the type is
`TWO_SIDED_GREEDY_SWITCH`; node-relative for `true`). -/
def create (crossMinType : CrossMinType) (random : IO.Ref Random) (numLayers : Nat) : BaseIO PortDistributorImpl := do
  if crossMinType == .twoSidedGreedySwitch then return .greedy (← GreedyPortDistributor.new)
  if ← random.modifyGet (·.nextBoolean) then return .barycenter (← NodeRelativePortDistributor.new numLayers).inner
  else return .barycenter (← LayerTotalPortDistributor.new numLayers).inner

/-- The `ISweepPortDistributor` view (`NodeRelativePortDistributor.toSweepPortDistributor` and
`LayerTotalPortDistributor.toSweepPortDistributor` are those of `inner`). -/
def toSweepPortDistributor : PortDistributorImpl → SweepPortDistributor
  | .barycenter d => d.toSweepPortDistributor
  | .greedy d => d.toSweepPortDistributor

/-- `distributePortsWhileSweeping(order, freeLayerIndex, isForwardSweep)` (the `SweepPortDistributor`
method, called directly). -/
@[inline] def distributePortsWhileSweeping (d : PortDistributorImpl) (order : Array (Array LNodeId))
    (freeLayerIndex : Nat) (isForwardSweep : Bool) : LayeredM Bool :=
  match d with
  | .barycenter d => d.distributePortsWhileSweeping order freeLayerIndex isForwardSweep
  | .greedy d => d.distributePortsWhileSweeping order freeLayerIndex isForwardSweep

/-- The distributor the barycenter heuristics use (`createWithBarycenter`'s barycenter view): only for
`BARYCENTER`. -/
def barycenterView (crossMinType : CrossMinType) : PortDistributorImpl → Option AbstractBarycenterPortDistributor
  | .barycenter d => if crossMinType == .barycenter then some d else none
  | .greedy _ => none

end PortDistributorImpl

/-- Lean only: the concrete `ICrossingMinimizationHeuristic` of a holder (see `PortDistributorImpl`);
the methods take the holder's generator, which `toHeuristic random` captures in the record. -/
inductive HeuristicImpl where
  /-- `BarycenterHeuristic`. -/
  | barycenter (h : BarycenterHeuristic)
  /-- `ModelOrderBarycenterHeuristic` (its `IInitializable` part is the base one). -/
  | modelOrder (h : ModelOrderBarycenterHeuristic)
  /-- `MedianHeuristic` (its `IInitializable` part does nothing). -/
  | median (h : MedianHeuristic)
  /-- `GreedySwitchHeuristic`. -/
  | greedySwitch (g : GreedySwitchHeuristic)

namespace HeuristicImpl

/-- The `ICrossingMinimizationHeuristic` record of the heuristic (`toHeuristic`). -/
def toHeuristic (h : HeuristicImpl) (random : IO.Ref Random) : CrossingMinimizationHeuristic :=
  match h with
  | .barycenter h => h.toHeuristic random
  | .modelOrder h => h.toHeuristic random
  | .median h => h.toHeuristic random
  | .greedySwitch g => g.toHeuristic

/-- The barycenter heuristic whose `IInitializable` part runs (`none` for median and greedy switch). -/
@[inline] def barycenterBase? : HeuristicImpl → Option BarycenterHeuristic
  | .barycenter h => some h
  | .modelOrder h => some h.base
  | _ => none

/-- The `GreedySwitchHeuristic` (Rust `downcast_mut`). -/
@[inline] def greedySwitch? : HeuristicImpl → Option GreedySwitchHeuristic
  | .greedySwitch g => some g
  | _ => none

/-- `isDeterministic()` (the records' constants). -/
@[inline] def isDeterministic : HeuristicImpl → Bool
  | .barycenter _ | .modelOrder _ => false
  | .median _ | .greedySwitch _ => true

/-- `alwaysImproves()`. -/
@[inline] def alwaysImproves : HeuristicImpl → Bool
  | .greedySwitch g => g.alwaysImproves
  | _ => false

/-- `setFirstLayerOrder(order, forwardSweep, random)`. -/
def setFirstLayerOrder (h : HeuristicImpl) (random : IO.Ref Random) (order : Array (Array LNodeId))
    (forwardSweep : Bool) : LayeredM (Array (Array LNodeId) × Bool) :=
  match h with
  | .barycenter h => h.setFirstLayerOrder order forwardSweep random
  | .modelOrder h => h.setFirstLayerOrder order forwardSweep random
  | .median h => h.setFirstLayerOrder order forwardSweep random
  | .greedySwitch g => g.setFirstLayerOrder order forwardSweep

/-- `minimizeCrossings(order, freeLayerIndex, forwardSweep, isFirstSweep, random)`. -/
def minimizeCrossings (h : HeuristicImpl) (random : IO.Ref Random) (order : Array (Array LNodeId))
    (freeLayerIndex : Nat) (forwardSweep isFirstSweep : Bool) : LayeredM (Array (Array LNodeId) × Bool) :=
  match h with
  | .barycenter h => h.minimizeCrossings order freeLayerIndex forwardSweep isFirstSweep random
  | .modelOrder h => h.minimizeCrossings order freeLayerIndex forwardSweep isFirstSweep random
  | .median h => h.minimizeCrossings order freeLayerIndex forwardSweep isFirstSweep
  | .greedySwitch g => g.minimizeCrossings order freeLayerIndex forwardSweep isFirstSweep

/-- elk-rs `reset_sweep_iteration()` (the barycenter heuristic's; a no-op for the others, whose records
keep the default). -/
def resetSweepIteration : HeuristicImpl → BaseIO Unit
  | .barycenter h => h.sweepIteration.set 0
  | _ => pure ()

/-- elk-rs `increment_sweep_iteration()` (see `resetSweepIteration`). -/
def incrementSweepIteration : HeuristicImpl → BaseIO Unit
  | .barycenter h => h.sweepIteration.modify (· + 1)
  | _ => pure ()

/-- elk-rs `set_snapshot` (the barycenter heuristics; ignored by the others). -/
def setSnapshot (h : HeuristicImpl) (s : CrossMinSnapshot) : BaseIO Unit :=
  match h with
  | .barycenter h => h.setSnapshot s
  | .modelOrder h => h.setSnapshot s
  | _ => pure ()

end HeuristicImpl

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
  /-- `portPositions` (zeros, sized by the initialisation). Java's array is shared by the parent
  crossing counters of the greedy switch deciders of the child graphs, which leave their positions in
  it (elk-rs hands every decider a fresh copy). -/
  portPositions : IO.Ref (Array Int)
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
  /-- `cross_minimizer` (the concrete heuristic, called directly; `greedySwitch?` is Rust's `downcast_mut`). -/
  crossMinimizer : HeuristicImpl
  /-- `port_distributor` (the concrete distributor, called directly). -/
  portDistributor : PortDistributorImpl
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
  /-- `FIRST_TRY_WITH_INITIAL_ORDER` of the graph. Java's `SECOND_TRY_WITH_INITIAL_ORDER` is declared
  with the same property id (`"firstTryWithInitialOrder"`), so both name this one value (elk-rs keeps
  two fields). -/
  firstTryWithInitialOrder : Bool := false
  /-- `snapshot`. -/
  snapshot : CrossMinSnapshot := {}

namespace GraphInfoHolder

/-- The heuristic of a `CrossMinType` (step 3 of `build`). -/
def createCrossMinimizer (graph : LGraphId) (crossMinType : CrossMinType) (order : Array (Array LNodeId))
    (barycenterDistributor : Option AbstractBarycenterPortDistributor) (hasParent : Bool)
    (forceModelOrder : Bool) (maxModelOrderNodes : Int) (constraintsBetweenNonDummies : Bool)
    (groupOrderStrategy : GroupOrderStrategy) : LayeredM HeuristicImpl := do
  match crossMinType with
  | .barycenter =>
    let resolver ← ForsterConstraintResolver.new order constraintsBetweenNonDummies
    let some distributor := barycenterDistributor
      | throw (IO.userError "java.lang.IllegalStateException: barycenter distributor missing")
    if forceModelOrder then
      return .modelOrder (← ModelOrderBarycenterHeuristic.new resolver distributor forceModelOrder maxModelOrderNodes
        groupOrderStrategy)
    else
      return .barycenter (← BarycenterHeuristic.new resolver distributor)
  | .median => return .median MedianHeuristic.new
  | .oneSidedGreedySwitch | .twoSidedGreedySwitch =>
    return .greedySwitch (← GreedySwitchHeuristic.create crossMinType hasParent graph)

/-- The holder's own `IInitializable` pass (Rust `init_initializables(&mut [holder], order)`):
`cachePortSides` and the nested graph of every node in order, one port count per port, and the
zero port positions. Returns the child graphs and the port count. -/
def initHolder (order : Array (Array LNodeId)) : LayeredM (Array LGraphId × Nat) := do
  -- `Initializable.init #[holderInit] order` with `holderInit` doing `cachePortSides` and the nested
  -- graph per node and counting the ports, as one loop (the same calls in the same order)
  let mut childGraphs : Array LGraphId := #[]
  let mut nPorts : Nat := 0
  for layer in order do
    for node in layer do
      cachePortSides node
      let nd ← getNode node
      if let some nested := nd.nestedGraph then
        childGraphs := childGraphs.push nested
      nPorts := nPorts + nd.ports.size
  return (childGraphs, nPorts)

/-! ## Fused initialisation (Lean only)

`build` runs `initHolder` and `Initializable.init #[counter, decider, distributor, heuristic] order`
as one pure pass over the arena (`FusedInit.run`, PLAN 7.1): the generic traversal calls up to four
closures per layer, node and port, each reading and writing the arena through the monad and its own
`IO.Ref`s. The pass does the same arena reads and writes in the same order and keeps the tables of
the initialisables (the counter's layer flags, the `ForsterConstraintResolver`'s tables) as values,
which are written to the refs once afterwards, followed by the `initAfterTraversal`s in list order.
Why this is the same:
* every callback writes only ids (`Layer.id := l`, `LNode.id := n`, `LPort.id := k`) and its own
  state, and none can fail. The writes of the same id by several initialisables (the decider, the
  distributor and the resolver write `LNode.id := n`, every port level counts the ports from `0` in
  traversal order) are one write here; between them nothing reads the id.
* `initHolder`'s `cachePortSides` (all nodes, before the traversal) writes the side cache, which the
  traversal does not read, and reads only port sides, which the traversal does not write: both
  commute, so they are done node by node. The holder's port count is the traversal's.
* the decider's node infos and the distributor's node positions do not depend on the arena: per layer
  `l` the layer level sets the row to `size` defaults (zeros) and the node levels then write the
  default (the index) into each slot, which is what `deciderRows`/`positionRows` compute.
* the resolver's node level reads `Layer.id` and `LNode.id` live, after the writes before it.
The objects must be fresh (as `build` creates them); `buildRef` keeps the generic path as the
reference of the differential test `layered.p3.fusedInit`. -/

namespace FusedInit

/-- The tables of the `ForsterConstraintResolver` (barycenter heuristics only). -/
structure Forster where
  layoutUnits : Std.HashMap LNodeId (Array LNodeId)
  barycenterStates : Array (Array (Option BarycenterState))
  constraintGroups : Array (Array (Option Nat))
  constraintGroupArena : Array ConstraintGroup

/-- The resolver's `initAtLayerLevel` tables (the `Layer.id` write is the decider's). -/
@[inline] def forsterLayer (f : Forster) (l size : Nat) : Forster :=
  match f with
  | ⟨units, states, groups, garena⟩ =>
    let (units, garena) := if l == 0 then ({}, #[]) else (units, garena)
    ⟨units, (growTo states (l + 1) #[]).setIfInBounds l (Array.replicate size none),
      (growTo groups (l + 1) #[]).setIfInBounds l (Array.replicate size none), garena⟩

/-- The resolver's `initAtNodeLevel` after `LNode.id := n` (`ForsterM.initNodeLevel c node true` on the
live ids). -/
@[inline] def forsterNode (a : LGraphArena) (node : LNodeId) (f : Forster) : Forster :=
  let li := liveLayerIndex a node
  let nd := a.node node
  let ni := asUsize nd.id
  let unit := nd.internal.inLayerLayoutUnit
  match f with
  | ⟨units, states, groups, garena⟩ =>
    let (groups, garena) := if li < groups.size then
        (groups.modifyIn li (fun row => (growTo row (ni + 1) none).setIfInBounds ni (some garena.size)),
          garena.push (ConstraintGroup.new node))
      else (groups, garena)
    let states := if li < states.size then
        states.modifyIn li fun row => (growTo row (ni + 1) none).setIfInBounds ni (some (BarycenterState.new node))
      else states
    let units := match unit with
      | some u => units.insert u ((units.getD u #[]).push node)
      | none => units
    ⟨units, states, groups, garena⟩

/-- The port levels of the ports `ports[i:]` of a node of layer `l`: `LPort.id := k` (the next port
id) and the counter's hyperedge marks (more than one edge: `EAST` marks `l`, `WEST` marks `l - 1`).
Returns the arena, the marks and the next id. -/
partial def portLoop (a : LGraphArena) (ports : Array LPortId) (l i k : Nat) (hyper : Array Bool) :
    LGraphArena × Array Bool × Nat :=
  if h : i < ports.size then
    let port := ports[i]
    let a := a.modifyPort port fun x => { x with id := (k : Int) }
    let pt := a.port port
    let many := pt.outgoingEdges.size + pt.incomingEdges.size > 1
    let hyper := if many then
        match pt.side with
        | .east => hyper.setIfInBounds l true
        | .west => if l > 0 then hyper.setIfInBounds (l - 1) true else hyper
        | _ => hyper
      else hyper
    portLoop a ports l (i + 1) (k + 1) hyper
  else (a, hyper, k)

/-- The side ordinal of `ports[i]` (`5`, no side, out of range). -/
@[inline] def sideOrd (a : LGraphArena) (ports : Array LPortId) (i : Nat) : Nat :=
  if h : i < ports.size then ElkEnum.ordinal (a.port ports[i]).side else 5

/-- The index after the last port of side ordinal `o` in `ports[0:j]` (`0`: none). -/
partial def lastOfSide (a : LGraphArena) (ports : Array LPortId) (o j : Nat) : Nat :=
  if j == 0 then 0 else if sideOrd a ports (j - 1) == o then j else lastOfSide a ports o (j - 1)

/-- The start of the run of side ordinal `o` that ends at `j` (`ports[j - 1]` has side `o`). -/
partial def runStart (a : LGraphArena) (ports : Array LPortId) (o j : Nat) : Nat :=
  if j == 0 then 0 else if sideOrd a ports (j - 1) == o then runStart a ports o (j - 1) else j

/-- Whether `cached[o:5]` are the entries `LGraphArena.findPortIndices` computes for `ports`: per side
ordinal the `[first, last)` range of the last run of that side (`findPortIndicesLoop` writes the range
of every run when it ends, so a later run of a side overwrites an earlier one; the leading empty
`NORTH` run is not written), `none` for a side without ports. Allocation free. -/
partial def indicesMatchFrom (a : LGraphArena) (ports : Array LPortId) (cached : Array (Option (Nat × Nat))) (o : Nat) :
    Bool :=
  if o < 5 then
    let last := lastOfSide a ports o ports.size
    let ok := match cached[o]? with
      | some (some (f, l)) => last != 0 && l == last && f == runStart a ports o last
      | some none => last == 0
      | none => false
    ok && indicesMatchFrom a ports cached (o + 1)
  else true

/-- Whether a node's side cache is current: `cachePortSides` would write the values it holds. -/
@[inline] def sideCacheCurrent (a : LGraphArena) (nd : LNode) : Bool :=
  nd.portSidesCached && (match nd.portSideIndices with
    | some idx => idx.size == 5 && indicesMatchFrom a nd.ports idx 0
    | none => false)

/-- The state of the pass between nodes. -/
structure St where
  arena : LGraphArena
  childGraphs : Array LGraphId
  hasNorthSouthPorts : Array Bool
  hasHyperEdgesEastOfIndex : Array Bool
  nPorts : Nat
  forster : Forster

/-- The nodes `layer[n:]` of layer `l`: `cachePortSides` and the nested graph (`initHolder`), the
counter's north/south mark, `LNode.id := n`, the resolver's node level (`withForster`) and the port
levels. -/
partial def nodeLoop (withForster : Bool) (layer : Array LNodeId) (l n : Nat) (st : St) : St :=
  if h : n < layer.size then
    let node := layer[n]
    match st with
    | ⟨a, children, hasNS, hyper, k, f⟩ =>
      let nd := a.node node
      let isNS := match nd.type with
        | .northSouthPort => true
        | _ => false
      let nested := nd.nestedGraph
      let children := match nested with
        | some g => children.push g
        | none => children
      let hasNS := if isNS then hasNS.setIfInBounds l true else hasNS
      -- `cachePortSides`: a current cache is left as it is (the same values, without building them)
      let current := sideCacheCurrent a nd
      let a := if current then a.modifyNode node fun x => { x with id := (n : Int) }
        else
          let indices := a.findPortIndices node
          a.modifyNode node fun x => { x with portSidesCached := true, portSideIndices := some indices, id := (n : Int) }
      let f := if withForster then forsterNode a node f else f
      let ports := (a.node node).ports
      let (a, hyper, k) := portLoop a ports l 0 k hyper
      nodeLoop withForster layer l (n + 1) ⟨a, children, hasNS, hyper, k, f⟩
  else st

/-- The layers `order[l:]`: `Layer.id := l` (of the first node's layer), the resolver's layer level and
the nodes. -/
partial def layerLoop (withForster : Bool) (order : Array (Array LNodeId)) (l : Nat) (st : St) : St :=
  if h : l < order.size then
    let layer := order[l]
    let st := match st with
      | ⟨a, children, hasNS, hyper, k, f⟩ =>
        let layerId := match layer[0]? with
          | some first => (a.node first).layer
          | none => none
        let a := match layerId with
          | some li => a.modifyLayer li fun x => { x with id := (l : Int) }
          | none => a
        let f := if withForster then forsterLayer f l layer.size else f
        ⟨a, children, hasNS, hyper, k, f⟩
    layerLoop withForster order (l + 1) (nodeLoop withForster layer l 0 st)
  else st

/-- The decider's node infos after the traversal (`LayerSweepTypeDecider.initAtLayerLevel` per layer;
the node levels write the defaults again). -/
partial def deciderRows (order : Array (Array LNodeId)) (l : Nat) (info : Array (Array NodeInfo)) :
    Array (Array NodeInfo) :=
  if h : l < order.size then
    let info := if info.size <= l then info ++ Array.replicate (l + 1 - info.size) #[] else info
    deciderRows order (l + 1) (info.set! l (Array.replicate order[l].size (default : NodeInfo)))
  else info

/-- The distributor's node positions after the traversal (the layer level's zeros, then position `n`
of node `n`). -/
partial def positionRows (order : Array (Array LNodeId)) (l : Nat) (positions : Array (Array Nat)) :
    Array (Array Nat) :=
  if h : l < order.size then
    let positions := if l >= positions.size then positions ++ Array.replicate (l + 1 - positions.size) #[] else positions
    positionRows order (l + 1) (positions.setIfInBounds l (Array.range order[l].size))
  else positions

/-- `initHolder` and `Initializable.init #[counter, decider, distributor, heuristic] order` with fresh
objects (see "Fused initialisation"): the child graphs and the port count. -/
def run (order : Array (Array LNodeId)) (counter : AllCrossingsCounter) (decider : LayerSweepTypeDecider)
    (distributor : PortDistributorImpl) (heuristic : HeuristicImpl) : LayeredM (Array LGraphId × Nat) := do
  let resolver := heuristic.barycenterBase?.map (·.constraintResolver)
  let f : Forster ← match resolver with
    | some r => pure ⟨← r.layoutUnits.swap {}, ← r.barycenterStates.swap #[], ← r.constraintGroups.swap #[],
        ← r.constraintGroupArena.swap #[]⟩
    | none => pure ⟨{}, #[], #[], #[]⟩
  let hasNS ← counter.hasNorthSouthPorts.swap #[]
  let hyper ← counter.hasHyperEdgesEastOfIndex.swap #[]
  let st ← modifyGet fun a =>
    match layerLoop resolver.isSome order 0 ⟨a, #[], hasNS, hyper, 0, f⟩ with
    | ⟨a, children, hasNS, hyper, k, f⟩ => (St.mk default children hasNS hyper k f, a)
  let k := st.nPorts
  -- the counter's tables and `initAfterTraversal`
  counter.hasNorthSouthPorts.set st.hasNorthSouthPorts
  counter.hasHyperEdgesEastOfIndex.set st.hasHyperEdgesEastOfIndex
  counter.nPorts.set (k : Int)
  counter.crossingCounter.resetTo (Array.replicate k 0)
  -- the decider (no `initAfterTraversal`)
  decider.nodeInfo.modify (deciderRows order 0)
  -- the distributor
  match distributor with
  | .barycenter d =>
    d.state.modify fun s => { s with
      nodePositions := positionRows order 0 s.nodePositions, nPorts := s.nPorts + k
      portRanks := BarycenterPortDistributorState.zeros (s.nPorts + k)
      portBarycenter := BarycenterPortDistributorState.zeros (s.nPorts + k) }
  | .greedy d =>
    d.nPorts.modify (· + k)
    d.crossingsCounter.set (some (← CrossingsCounter.ofPositions (Array.replicate (← d.nPorts.get) 0)))
  -- the heuristic
  match heuristic.barycenterBase?, heuristic.greedySwitch? with
  | some h, _ =>
    match st.forster with
    | ⟨units, states, groups, garena⟩ =>
      h.constraintResolver.layoutUnits.set units
      h.constraintResolver.barycenterStates.set states
      h.constraintResolver.constraintGroups.set groups
      h.constraintResolver.constraintGroupArena.set garena
    h.portRanks.set (← h.portDistributor.portRanksF)
  | none, none => pure ()
  | none, some g =>
    g.nPorts.modify (· + k)
    g.portPositions.set (Array.replicate (← g.nPorts.get) 0)
  return (st.childGraphs, k)

end FusedInit

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
  /-- The graph's `FIRST_TRY_WITH_INITIAL_ORDER` (left by an earlier run, see `LayerSweepCrossingMinimizer`). -/
  firstTryWithInitialOrder : Bool := false

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
    thoroughness := p.getD LayeredOptions.THOROUGHNESS 1
    firstTryWithInitialOrder := g.internal.firstTryWithInitialOrder }

/-- `GraphInfoHolder::build(..)` (see the module doc for the steps) with the concrete distributor, heuristic
and decider (for the differential test). With `fused` (the default) step 5 is `FusedInit.run`,
otherwise `initHolder` and the generic `Initializable.init` (the reference). -/
def buildParts (graph : LGraphId) (crossMinType : CrossMinType) (currentNodeOrder : Array (Array LNodeId))
    (s : Settings) (random : IO.Ref Random) (fused : Bool := true) :
    LayeredM (GraphInfoHolder × PortDistributorImpl × HeuristicImpl × LayerSweepTypeDecider) := do
  let hasParent := s.parentNode.isSome
  let parentGraphRef ← match s.parentNode with
    | some p => nodeGraph p
    | none => pure none
  let hasExternalPorts := s.graphProperties.contains .externalPorts
  -- the generator before the factory's draw, for its `CROSSMIN_RANDOM_TRACE` line only
  let randomBefore ← if RandomTrace.isEnabled then some <$> random.get else pure none
  let portDistributor ← PortDistributorImpl.create crossMinType random currentNodeOrder.size
  let barycenterDistributor := portDistributor.barycenterView crossMinType
  if let some r := randomBefore then
    if crossMinType != .twoSidedGreedySwitch then
      -- `random_trace::trace_next_boolean` of the factory's draw (replayed on the saved state)
      let _ ← RandomTrace.traceNextBoolean r.nextBoolean.1 "graph_info_holder::create_port_distributor"
  let crossingsCounter ← AllCrossingsCounter.new graph currentNodeOrder
  let crossMinimizer ← createCrossMinimizer graph crossMinType currentNodeOrder barycenterDistributor hasParent
    s.forceModelOrder s.maxModelOrderNodes s.constraintsBetweenNonDummies s.groupOrderStrategy
  let decider ← LayerSweepTypeDecider.new graph s.parentNode hasParent crossMinimizer.isDeterministic
  let (childGraphs, nPorts) ← if fused then
      FusedInit.run currentNodeOrder crossingsCounter decider portDistributor crossMinimizer
    else do
      let r ← initHolder currentNodeOrder
      Initializable.init #[crossingsCounter.initializable, decider.initializable,
        portDistributor.toSweepPortDistributor.initializable, (crossMinimizer.toHeuristic random).initializable]
        currentNodeOrder
      pure r
  let snapshot ← CrossMinSnapshot.build currentNodeOrder nPorts
  crossMinimizer.setSnapshot snapshot
  crossingsCounter.setSnapshot snapshot
  let useBottomUp ← decider.useBottomUpWithBoundary currentNodeOrder s.hierarchicalSweepiness
  -- `update_greedy_context(None)`
  if let some g := crossMinimizer.greedySwitch? then g.setDontSweepInto useBottomUp
  return ({
    lGraph := graph, currentNodeOrder, portPositions := ← IO.mkRef (Array.replicate nPorts 0), useBottomUp, childGraphs
    hasExternalPorts, hasParent, parentGraphRef, parentNode := s.parentNode, crossMinimizer
    portDistributor, crossingsCounter, nPorts
    considerModelOrderStrategy := s.considerModelOrderStrategy, groupOrderStrategy := s.groupOrderStrategy
    portModelOrder := s.portModelOrder, nodeInfluence := s.nodeInfluence, portInfluence := s.portInfluence
    thoroughness := s.thoroughness, random, snapshot, firstTryWithInitialOrder := s.firstTryWithInitialOrder },
    portDistributor, crossMinimizer, decider)

/-- `GraphInfoHolder::build(..)` (see `buildParts`). -/
@[inline] def build (graph : LGraphId) (crossMinType : CrossMinType) (currentNodeOrder : Array (Array LNodeId))
    (s : Settings) (random : IO.Ref Random) (fused : Bool := true) : LayeredM GraphInfoHolder :=
  return (← buildParts graph crossMinType currentNodeOrder s random fused).1

/-- `GraphInfoHolder::new(graph, cross_min_type)` / `new_with_graph(graph_ref, graph, cross_min_type,
shared_random)`: `random` is the generator Rust would use (see the module doc). -/
def new (graph : LGraphId) (crossMinType : CrossMinType) (random : IO.Ref Random) (fused : Bool := true) :
    LayeredM GraphInfoHolder := do
  let order := (← get).graphToNodeArray graph
  let s ← readSettings graph
  build graph crossMinType order s random fused

/-- `dont_sweep_into()`. -/
@[inline] def dontSweepInto (h : GraphInfoHolder) : Bool := h.useBottomUp

/-- `best_sweep()`: the currently best order for deterministic heuristics, else the best one. -/
def bestSweep (h : GraphInfoHolder) : LayeredM (Option SweepCopy) := do
  if h.crossMinimizer.isDeterministic then return h.currentlyBestNodeAndPortOrder
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
    (parentSnapshot : Option (Array (Array LNodeId) × IO.Ref (Array Int) × LNodeId)) : BaseIO Unit := do
  let some greedy := h.crossMinimizer.greedySwitch? | return
  greedy.setDontSweepInto h.useBottomUp
  if let some (parentNodeOrder, parentPortPositions, parentNode) := parentSnapshot then
    greedy.updateParentContext parentNodeOrder parentPortPositions parentNode

end GraphInfoHolder

end Elk.Alg.Layered.P3Order
