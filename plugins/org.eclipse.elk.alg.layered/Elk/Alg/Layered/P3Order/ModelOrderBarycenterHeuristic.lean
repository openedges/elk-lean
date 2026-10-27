import Elk.Alg.Layered.P3Order.BarycenterHeuristic
import Elk.Alg.Layered.Intermediate.Preserveorder.CMGroupModelOrderCalculator
import Elk.Alg.Layered.Options.LayeredOptions
import Std.Data.HashMap
import Std.Data.HashSet
/-!
# `org.eclipse.elk.alg.layered.p3order.ModelOrderBarycenterHeuristic`

The barycenter heuristic for `CROSSING_MINIMIZATION_FORCE_NODE_MODEL_ORDER` (elk-rs
`model_order_barycenter_heuristic.rs`): nodes with a model order keep it, the other nodes (dummies)
are placed between them by barycenter. The comparator is stateful: every decision is recorded in
the transitive `biggerThan`/`smallerThan` relations, which later comparisons consult first, so the
comparison sequence of the sort matters.

## API (for `GraphInfoHolder`)
* `ModelOrderBarycenterHeuristic.new constraintResolver portDistributor forceModelOrder
  maxModelOrderNodes groupOrderStrategy (lockedGraph := none)` (Rust `new` with the same first five
  arguments; `lockedGraph` see below). The elk-rs `GraphInfoHolder` creates it only when
  `forceModelOrder` is `true`.
* `initializable`, `setSnapshot`, the `IO.Ref Random` argument and `toHeuristic random` are those of
  the wrapped `BarycenterHeuristic` (`base`).

## `ModelOrderGraphContext` choice (Rust `try_lock`)
`CMGroupModelOrderCalculator` reads `GROUP_MODEL_ORDER_CM_GROUP_ORDER_STRATEGY` and
`GROUP_MODEL_ORDER_CM_ENFORCED_GROUP_ORDERS` from the node's graph with `try_lock()`. elk-rs runs
every processor with the processed graph locked (`elk_layered.rs` `graph_guard`), so for nodes of
that graph the lock fails and the defaults are used (`ModelOrderGraphContext.unavailable`); nested
graphs swept by the same minimiser (`INCLUDE_CHILDREN`) are not locked and are read
(`ModelOrderGraphContext.ofGraph`). `lockedGraph` is the graph Rust holds locked: the
`LayerSweepCrossingMinimizer` passes the processed (root) graph, the elk-rs unit tests correspond to
`none`.

## Rust semantics kept where they differ from Java
* `setFirstLayerOrder` is the base one (barycenter sort and constraint resolution); Java's override
  of `minimizeCrossings(layer, …)` uses the model order insertion sort there too.
* The relation sets are copied before the update (`update_bigger_and_smaller_associations`); Java
  iterates the live sets.
* `minimizeCrossings` with `forceModelOrder = false` (never created by elk-rs) sorts with Rust's
  `slice::sort_by`, whose comparison sequence for up to 20 nodes is `insertion_sort_shift_left`
  (`is_less(tail, sift)`), reproduced here, and does not clear the relations afterwards (Rust and
  Java). For longer layers Rust switches to driftsort, which is not ported: the insertion sort is
  used for every length, so the result can differ from Rust there (Rust's driftsort may also abort
  with "user-provided comparison function does not correctly implement a total order" on this
  stateful comparator). TODO(rust-sort): a faithful `slice::sort_by` in `Elk.Core.Util.Sort`.
* `sweep_iteration` is not forwarded (Rust uses the trait defaults), so `toHeuristic` keeps the
  no-op `resetSweepIteration`/`incrementSweepIteration`.
-/
namespace Elk.Alg.Layered.P3Order

open Elk.Core.Util Elk.Alg.Layered.Graph Elk.Alg.Layered.Options Elk.Alg.Layered.P3Order.Counting LayeredM
open Elk.Alg.Layered.Intermediate.Preserveorder

/-- `bigger_than`/`smaller_than` (Java `HashMap<LNode, HashSet<LNode>>`; only membership is
observable, so the iteration order of the sets does not matter). -/
structure ModelOrderBarycenterRelations where
  /-- `bigger_than`. -/
  biggerThan : Std.HashMap LNodeId (Std.HashSet LNodeId) := {}
  /-- `smaller_than`. -/
  smallerThan : Std.HashMap LNodeId (Std.HashSet LNodeId) := {}
  deriving Inhabited

namespace ModelOrderBarycenterRelations

/-- `map.entry(k).or_default().insert(v)`. -/
@[inline] def insertInto (m : Std.HashMap LNodeId (Std.HashSet LNodeId)) (k v : LNodeId) :
    Std.HashMap LNodeId (Std.HashSet LNodeId) :=
  m.alter k fun o => some ((o.getD {}).insert v)

/-- `map.entry(k).or_default().extend(s)`. -/
def unionInto (m : Std.HashMap LNodeId (Std.HashSet LNodeId)) (k : LNodeId) (s : Std.HashSet LNodeId) :
    Std.HashMap LNodeId (Std.HashSet LNodeId) :=
  m.alter k fun o => Id.run do
    let mut set := o.getD {}
    for x in s do set := set.insert x
    return some set

/-- Whether `map[k]` contains `v`. -/
@[inline] def holds (m : Std.HashMap LNodeId (Std.HashSet LNodeId)) (k v : LNodeId) : Bool :=
  match m[k]? with
  | some s => s.contains v
  | none => false

/-- `compare_based_on_transitive_dependencies(n1, n2)`: `1` if `biggerThan(n1) ∋ n2`, `-1` if
`biggerThan(n2) ∋ n1`, `-1` if `smallerThan(n1) ∋ n2`, `1` if `smallerThan(n2) ∋ n1`, else `0`. -/
def compareBasedOnTransitiveDependencies (rel : ModelOrderBarycenterRelations) (n1 n2 : LNodeId) : Int :=
  if holds rel.biggerThan n1 n2 then 1
  else if holds rel.biggerThan n2 n1 then -1
  else if holds rel.smallerThan n1 n2 then -1
  else if holds rel.smallerThan n2 n1 then 1
  else 0

/-- `update_bigger_and_smaller_associations(bigger, smaller)`: records the pair and propagates it
through the sets captured before the update. -/
def updateBiggerAndSmallerAssociations (rel : ModelOrderBarycenterRelations) (bigger smaller : LNodeId) :
    ModelOrderBarycenterRelations := Id.run do
  let smallerNodeBiggerThan := rel.biggerThan.getD smaller {}
  let biggerNodeSmallerThan := rel.smallerThan.getD bigger {}
  let mut biggerThan := insertInto rel.biggerThan bigger smaller
  let mut smallerThan := insertInto rel.smallerThan smaller bigger
  for verySmall in smallerNodeBiggerThan do
    biggerThan := insertInto biggerThan bigger verySmall
    smallerThan := insertInto smallerThan verySmall bigger
    smallerThan := unionInto smallerThan verySmall biggerNodeSmallerThan
  for veryBig in biggerNodeSmallerThan do
    smallerThan := insertInto smallerThan smaller veryBig
    biggerThan := insertInto biggerThan veryBig smaller
    biggerThan := unionInto biggerThan veryBig smallerNodeBiggerThan
  return { biggerThan, smallerThan }

end ModelOrderBarycenterRelations

/-- The read-only inputs of the comparator during one sort. -/
structure ModelOrderCompareEnv where
  /-- The barycenter context (arena, ids). -/
  base : BarycenterContext
  /-- The barycenter states after the computation. -/
  states : Array (Array (Option BarycenterState))
  /-- The `ModelOrderGraphContext` of each graph of the sorted nodes (see the module doc). -/
  graphContexts : Std.HashMap LGraphId ModelOrderGraphContext := {}
  /-- `max_model_order_nodes` (the offset of the group model order). -/
  maxModelOrderNodes : Int := 0
  /-- `group_order_strategy`. -/
  groupOrderStrategy : GroupOrderStrategy := .onlyWithinGroup

namespace ModelOrderBarycenterHeuristic

open ModelOrderBarycenterRelations

/-- Rust `Ordering` of `partial_cmp`/`cmp` as `-1`, `0`, `1`. -/
@[inline] def orderingToInt : Ordering → Int
  | .lt => -1
  | .eq => 0
  | .gt => 1

/-- `compare_based_on_barycenter(n1, n2)`: known barycenters ascending (`partial_cmp`), a known one
before an unknown one; a decision is recorded with the first node as the bigger one when it is
`-1` (Java and Rust). -/
def compareBasedOnBarycenter (env : ModelOrderCompareEnv) (rel : ModelOrderBarycenterRelations) (n1 n2 : LNodeId) :
    Int × ModelOrderBarycenterRelations :=
  match BarycenterHeuristic.barycenterIn env.base env.states n1, BarycenterHeuristic.barycenterIn env.base env.states n2 with
  | some s1, some s2 =>
    let value := orderingToInt (Float.comparePartial s1 s2)
    if value < 0 then (value, rel.updateBiggerAndSmallerAssociations n1 n2)
    else if value > 0 then (value, rel.updateBiggerAndSmallerAssociations n2 n1)
    else (value, rel)
  | some _, none => (-1, rel.updateBiggerAndSmallerAssociations n1 n2)
  | none, some _ => (1, rel.updateBiggerAndSmallerAssociations n2 n1)
  | none, none => (0, rel)

/-- `FIRST_SEPARATE` or `LAST_SEPARATE`. -/
@[inline] def isSeparate (c : LayerConstraint) : Bool := c == .firstSeparate || c == .lastSeparate

/-- The model order part of `compare_nodes`: both nodes have a `MODEL_ORDER` and `n1` a graph; the
(group) model orders are compared, ignored across groups with `ONLY_WITHIN_GROUP`; `none` when it
does not decide. -/
def compareByModelOrder (env : ModelOrderCompareEnv) (rel : ModelOrderBarycenterRelations) (n1 n2 : LNodeId) :
    Option (Int × ModelOrderBarycenterRelations) := do
  let a := env.base.arena
  let nd1 := a.node n1
  let nd2 := a.node n2
  if nd1.internal.modelOrder.isNone || nd2.internal.modelOrder.isNone then none
  let graph ← a.nodeGraph n1
  let ctx := env.graphContexts[graph]?.getD ModelOrderGraphContext.unavailable
  let v1 := CMGroupModelOrderCalculator.calculateModelOrderOrGroupModelOrderOf ctx nd1 nd2 env.maxModelOrderNodes
  let v2 := CMGroupModelOrderCalculator.calculateModelOrderOrGroupModelOrderOf ctx nd2 nd1 env.maxModelOrderNodes
  let mut value := orderingToInt (Ord.compare v1 v2)
  if env.groupOrderStrategy == .onlyWithinGroup then
    let g1 := nd1.props.getD LayeredOptions.GROUP_MODEL_ORDER_CROSSING_MINIMIZATION_ID 0
    let g2 := nd2.props.getD LayeredOptions.GROUP_MODEL_ORDER_CROSSING_MINIMIZATION_ID 0
    if g1 != g2 then value := 0
  if value < 0 then some (value, rel.updateBiggerAndSmallerAssociations n1 n2)
  else if value > 0 then some (value, rel.updateBiggerAndSmallerAssociations n2 n1)
  else none

/-- `compare_nodes(n1, n2)`: `0` if one node is `FIRST_SEPARATE`/`LAST_SEPARATE`, then the
transitive relations, then the (group) model order, then the barycenters. -/
def compareNodes (env : ModelOrderCompareEnv) (rel : ModelOrderBarycenterRelations) (n1 n2 : LNodeId) :
    Int × ModelOrderBarycenterRelations :=
  let a := env.base.arena
  let c1 := (a.node n1).props.getD LayeredOptions.LAYERING_LAYER_CONSTRAINT LayerConstraint.none
  let c2 := (a.node n2).props.getD LayeredOptions.LAYERING_LAYER_CONSTRAINT LayerConstraint.none
  if isSeparate c1 || isSeparate c2 then (0, rel)
  else
    let transitive := compareBasedOnTransitiveDependencies rel n1 n2
    if transitive != 0 then (transitive, rel)
    else
      match compareByModelOrder env rel n1 n2 with
      | some r => r
      | none => compareBasedOnBarycenter env rel n1 n2

/-- `insertion_sort(layer)` (Java `insertionSort`): `compare_nodes(layer[j - 1], temp) > 0` moves
`temp` up; the relations are cleared afterwards. -/
def insertionSort (env : ModelOrderCompareEnv) (rel : ModelOrderBarycenterRelations) (layer : Array LNodeId) :
    Array LNodeId × ModelOrderBarycenterRelations := Id.run do
  let mut layer := layer
  let mut rel := rel
  for i in [1:layer.size] do
    let temp := layer[i]!
    let mut j := i
    while j > 0 do
      let (value, rel') := compareNodes env rel layer[j - 1]! temp
      rel := rel'
      if value > 0 then
        layer := layer.set! j layer[j - 1]!
        j := j - 1
      else break
    layer := layer.set! j temp
  return (layer, {})

/-- Rust `slice::sort_by(compare_nodes)` for short slices: `insertion_sort_shift_left(v, 1)`, which
inserts every element with `is_less(tmp, v[j - 1]) = compare_nodes(tmp, v[j - 1]) < 0` from the
right (Rust ≤ 20 elements; used for all lengths, TODO(rust-sort) in the module doc). -/
def sortByCompareNodes (env : ModelOrderCompareEnv) (rel : ModelOrderBarycenterRelations) (v : Array LNodeId) :
    Array LNodeId × ModelOrderBarycenterRelations := Id.run do
  let mut v := v
  let mut rel := rel
  for i in [1:v.size] do
    let tmp := v[i]!
    let (first, rel') := compareNodes env rel tmp v[i - 1]!
    rel := rel'
    if first < 0 then
      v := v.set! i v[i - 1]!
      let mut j := i - 1
      while j > 0 do
        let (value, rel') := compareNodes env rel tmp v[j - 1]!
        rel := rel'
        if value < 0 then
          v := v.set! j v[j - 1]!
          j := j - 1
        else break
      v := v.set! j tmp
  return (v, rel)

end ModelOrderBarycenterHeuristic

/-- `ModelOrderBarycenterHeuristic`. -/
structure ModelOrderBarycenterHeuristic where
  /-- `base`. -/
  base : BarycenterHeuristic
  /-- `bigger_than` and `smaller_than`. -/
  relations : IO.Ref ModelOrderBarycenterRelations
  /-- `force_model_order`. -/
  forceModelOrder : Bool
  /-- `max_model_order_nodes`. -/
  maxModelOrderNodes : Int
  /-- `group_order_strategy`. -/
  groupOrderStrategy : GroupOrderStrategy
  /-- The graph elk-rs holds locked while the heuristic runs (see the module doc). -/
  lockedGraph : Option LGraphId := none

namespace ModelOrderBarycenterHeuristic

/-- `ModelOrderBarycenterHeuristic::new(constraint_resolver, port_distributor, force_model_order,
max_model_order_nodes, group_order_strategy)` plus the locked graph of the Rust run. -/
def new (constraintResolver : ForsterConstraintResolver) (portDistributor : BarycenterPortDistributor)
    (forceModelOrder : Bool) (maxModelOrderNodes : Int) (groupOrderStrategy : GroupOrderStrategy)
    (lockedGraph : Option LGraphId := none) : BaseIO ModelOrderBarycenterHeuristic := do
  return {
    base := ← BarycenterHeuristic.new constraintResolver portDistributor
    relations := ← IO.mkRef {}
    forceModelOrder, maxModelOrderNodes, groupOrderStrategy, lockedGraph }

/-- `set_snapshot(snapshot)` (the base one). -/
def setSnapshot (h : ModelOrderBarycenterHeuristic) (s : CrossMinSnapshot) : BaseIO Unit := h.base.setSnapshot s

/-- `clear_transitive_ordering()`. -/
def clearTransitiveOrdering (h : ModelOrderBarycenterHeuristic) : BaseIO Unit := h.relations.set {}

/-- The comparator inputs for sorting `nodes`: the graph contexts of the nodes' graphs. -/
def compareEnv (h : ModelOrderBarycenterHeuristic) (c : BarycenterContext) (nodes : Array LNodeId) :
    LayeredM ModelOrderCompareEnv := do
  let mut graphContexts : Std.HashMap LGraphId ModelOrderGraphContext := {}
  for n in nodes do
    if let some g := c.arena.nodeGraph n then
      if !graphContexts.contains g then
        let ctx ← if h.lockedGraph == some g then pure ModelOrderGraphContext.unavailable
          else ModelOrderGraphContext.ofGraph g
        graphContexts := graphContexts.insert g ctx
  return {
    base := c, states := ← h.base.constraintResolver.barycenterStates.get, graphContexts
    maxModelOrderNodes := h.maxModelOrderNodes, groupOrderStrategy := h.groupOrderStrategy }

/-- `compare_nodes(n1, n2)` on the current barycenter states and relations (updates the relations). -/
def compareNodesM (h : ModelOrderBarycenterHeuristic) (n1 n2 : LNodeId) : LayeredM Int := do
  let c ← h.base.context true
  let env ← h.compareEnv c #[n1, n2]
  let (value, rel) := compareNodes env (← h.relations.get) n1 n2
  h.relations.set rel
  return value

/-- `set_first_layer_order(order, forward_sweep, random)`: the base one. -/
def setFirstLayerOrder (h : ModelOrderBarycenterHeuristic) (order : Array (Array LNodeId)) (forwardSweep : Bool)
    (random : IO.Ref Random) : LayeredM (Array (Array LNodeId) × Bool) :=
  h.base.setFirstLayerOrder order forwardSweep random

/-- `minimize_crossings(order, free_layer_index, forward_sweep, is_first_sweep, random)`: the base
port ranks, barycenters and filled-in barycenters; then with `forceModelOrder` the model order
insertion sort (no constraint resolution), otherwise `sort_by(compare_nodes)` and the constraint
resolver. Never reports an improvement. -/
def minimizeCrossings (h : ModelOrderBarycenterHeuristic) (order : Array (Array LNodeId)) (freeLayerIndex : Nat)
    (forwardSweep isFirstSweep : Bool) (random : IO.Ref Random) : LayeredM (Array (Array LNodeId) × Bool) := do
  h.base.updatePortRanks order freeLayerIndex forwardSweep
  let some freeLayer := order[freeLayerIndex]? | return (order, false)
  let preOrdered ← h.base.preOrderedFor freeLayer isFirstSweep
  let c ← h.base.context forwardSweep
  h.base.runOnStates random fun d =>
    BarycenterHeuristic.fillInUnknownBarycenters c freeLayer preOrdered (BarycenterHeuristic.calculateBarycenters c freeLayer d)
  let mut nodes := freeLayer
  if nodes.size > 1 then
    let env ← h.compareEnv c nodes
    let rel ← h.relations.swap {}
    if h.forceModelOrder then
      let (sorted, rel) := insertionSort env rel nodes
      h.relations.set rel
      nodes := sorted
    else
      let (sorted, rel) := sortByCompareNodes env rel nodes
      h.relations.set rel
      nodes ← h.base.constraintResolver.processConstraints sorted
  return (order.setIfInBounds freeLayerIndex nodes, false)

/-- The `IInitializable` part (the base one). -/
def initializable (h : ModelOrderBarycenterHeuristic) : Initializable := h.base.initializable

/-- The `ICrossingMinimizationHeuristic` view with the caller's generator. -/
def toHeuristic (h : ModelOrderBarycenterHeuristic) (random : IO.Ref Random) : CrossingMinimizationHeuristic where
  initializable := h.initializable
  alwaysImproves := pure false
  setFirstLayerOrder := fun order forwardSweep => h.setFirstLayerOrder order forwardSweep random
  minimizeCrossings := fun order freeLayerIndex forwardSweep isFirstSweep =>
    h.minimizeCrossings order freeLayerIndex forwardSweep isFirstSweep random
  isDeterministic := pure false
  setSnapshot := h.setSnapshot

end ModelOrderBarycenterHeuristic

end Elk.Alg.Layered.P3Order
