import Elk.Alg.Layered.Graph
import Elk.Alg.Layered.Options.LayeredOptions
/-!
# `org.eclipse.elk.alg.layered.intermediate.preserveorder.CMGroupModelOrderCalculator`

Port of elk-rs `intermediate/preserveorder/cm_group_model_order_calculator.rs`: the (group) model
order of a node used by the crossing minimization model order comparators. It is a helper with one
static function (not a processor), as in Rust and Java.

The Rust calculator (and both comparators) read three graph options from their `graph: LGraphRef`
with `try_lock()`, falling back to defaults when the lock is busy. The Lean port passes these values
explicitly as a `ModelOrderGraphContext`:

* `ModelOrderGraphContext.ofGraph g` reads them from the graph — what Java always does (and what
  `SortByInputModelProcessor`'s `build_ordering_context_graph` copies into its private context graph).
  `ModelOrderBarycenterHeuristic` and the model order counts of `LayerSweepCrossingMinimizer` use it
  also for the processed graph (elk-rs holds that graph locked);
* `ModelOrderGraphContext.unavailable` is what Rust sees when `try_lock` fails (`MAX_MODEL_ORDER_NODES`
  `0`, group order strategy `ONLY_WITHIN_GROUP`, no enforced group orders); no Java path uses it.

Rust differs from Java in that only `LNode`s are supported (Java takes any `LGraphElement`; Rust's
port and edge variants are local helpers of `ModelOrderPortComparator` that check only the group id
of the element itself).
-/
namespace Elk.Alg.Layered.Intermediate.Preserveorder

open Elk.Graph Elk.Core.Util Elk.Alg.Layered.Graph Elk.Alg.Layered.Options LayeredM

/-- The graph options read by the model order comparators and `CMGroupModelOrderCalculator`
(the Rust `graph: LGraphRef` field / `parent` argument, see the module doc). -/
structure ModelOrderGraphContext where
  /-- `InternalProperties.MAX_MODEL_ORDER_NODES` (Rust `unwrap_or(0)`). -/
  maxModelOrderNodes : Int := 0
  /-- `LayeredOptions.GROUP_MODEL_ORDER_CM_GROUP_ORDER_STRATEGY` (Rust `unwrap_or(OnlyWithinGroup)`). -/
  groupOrderStrategy : GroupOrderStrategy := .onlyWithinGroup
  /-- `LayeredOptions.GROUP_MODEL_ORDER_CM_ENFORCED_GROUP_ORDERS` (Rust `unwrap_or_default()`). -/
  enforcedGroupOrders : Array Int := #[]
  deriving Inhabited, Repr, BEq

namespace ModelOrderGraphContext

/-- The values Rust uses when `graph.try_lock()` fails. -/
def unavailable : ModelOrderGraphContext := {}

/-- Reads the options from graph `g` (Rust successful `try_lock`; also the values that
`build_ordering_context_graph` copies). -/
def ofGraph (g : LGraphId) : LayeredM ModelOrderGraphContext := do
  let gr ← getGraph g
  return { maxModelOrderNodes := gr.internal.maxModelOrderNodes
           groupOrderStrategy := gr.props.getD LayeredOptions.GROUP_MODEL_ORDER_CM_GROUP_ORDER_STRATEGY .onlyWithinGroup
           enforcedGroupOrders := gr.props.getD LayeredOptions.GROUP_MODEL_ORDER_CM_ENFORCED_GROUP_ORDERS #[] }

/-- `GROUP_MODEL_ORDER_CM_GROUP_ORDER_STRATEGY == ENFORCED`. -/
@[inline] def enforceGroupModelOrder (c : ModelOrderGraphContext) : Bool := c.groupOrderStrategy == .enforced

end ModelOrderGraphContext

namespace CMGroupModelOrderCalculator

/-- `CMGroupModelOrderCalculator.calculateModelOrderOrGroupModelOrder(element, other, parent, offset)`
(Rust `calculate_model_order_or_group_model_order`): `-1` if `element` has no `MODEL_ORDER`; if the
group order is `ENFORCED` and both nodes' `GROUP_MODEL_ORDER_CROSSING_MINIMIZATION_ID`s are enforced
group orders, `offset * groupId(element) + MODEL_ORDER(element)`; otherwise `MODEL_ORDER(element)`.
Pure over copies of the two nodes. -/
def calculateModelOrderOrGroupModelOrderOf (parent : ModelOrderGraphContext) (element other : LNode) (offset : Int) : Int :=
  match element.internal.modelOrder with
  | none => -1
  | some elementModelOrder =>
    if parent.enforceGroupModelOrder then
      let elementGroupId := element.props.getD LayeredOptions.GROUP_MODEL_ORDER_CROSSING_MINIMIZATION_ID 0
      let otherGroupId := other.props.getD LayeredOptions.GROUP_MODEL_ORDER_CROSSING_MINIMIZATION_ID 0
      if parent.enforcedGroupOrders.contains elementGroupId && parent.enforcedGroupOrders.contains otherGroupId then
        -- Java `int` arithmetic
        Int.wrap32 (offset * elementGroupId + elementModelOrder)
      else elementModelOrder
    else elementModelOrder

/-- `calculateModelOrderOrGroupModelOrder(element, other, parent, offset)` on node ids (reads both
nodes from the arena). -/
def calculateModelOrderOrGroupModelOrder (element other : LNodeId) (parent : ModelOrderGraphContext) (offset : Int) :
    LayeredM Int := do
  return calculateModelOrderOrGroupModelOrderOf parent (← getNode element) (← getNode other) offset

end CMGroupModelOrderCalculator

end Elk.Alg.Layered.Intermediate.Preserveorder
