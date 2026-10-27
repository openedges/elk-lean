import Elk.Alg.Layered.Graph
import Elk.Alg.Layered.Options.LayeredOptions
/-!
# `org.eclipse.elk.alg.layered.p1cycles.GroupModelOrderCalculator`

Port of elk-rs `p1cycles/group_model_order_calculator.rs`. Computes the (group) model order of a
node shifted by its layer constraint (`FIRST_SEPARATE`/`FIRST` before all others, `LAST`/
`LAST_SEPARATE` after all others). The calculator counts the separate nodes it has seen, so the
same instance must be reused for the nodes of one comparison (as in Rust/Java).

The functions are pure over a copy of the `LNode` (they only read the node's options and its
`MODEL_ORDER` field) and return the updated calculator. Rust `i32` arithmetic is done in `Int`.
-/
namespace Elk.Alg.Layered.P1Cycles

open Elk.Graph Elk.Alg.Layered.Graph Elk.Alg.Layered.Options

/-- `GroupModelOrderCalculator`: counters of the `FIRST_SEPARATE`/`LAST_SEPARATE` nodes seen so far. -/
structure GroupModelOrderCalculator where
  /-- `firstSeparateNodes`. -/
  firstSeparateNodes : Int := 0
  /-- `lastSeparateNodes`. -/
  lastSeparateNodes : Int := 0
  deriving Inhabited, Repr, BEq

namespace GroupModelOrderCalculator

/-- `new GroupModelOrderCalculator()`. -/
def new : GroupModelOrderCalculator := {}

/-- `constraintBaseModelOrder(node, separateOffset, offset)` (Rust `constraint_base_model_order`):
the offset implied by the node's `LAYERING_LAYER_CONSTRAINT` (only when the option is set on the node). -/
def constraintBaseModelOrder (c : GroupModelOrderCalculator) (node : LNode) (separateOffset offset : Int) :
    Int × GroupModelOrderCalculator :=
  let constraint : LayerConstraint :=
    if node.props.has LayeredOptions.LAYERING_LAYER_CONSTRAINT then
      node.props.getD LayeredOptions.LAYERING_LAYER_CONSTRAINT .none
    else .none
  match constraint with
  | .firstSeparate => (-separateOffset + c.firstSeparateNodes, { c with firstSeparateNodes := c.firstSeparateNodes + 1 })
  | .first => (-offset, c)
  | .last => (offset, c)
  | .lastSeparate => (separateOffset + c.lastSeparateNodes, { c with lastSeparateNodes := c.lastSeparateNodes + 1 })
  | .none => (0, c)

/-- `computeConstraintModelOrder(node, offset)`: constraint offset plus the node's `MODEL_ORDER` (if any). -/
def computeConstraintModelOrder (c : GroupModelOrderCalculator) (node : LNode) (offset : Int) :
    Int × GroupModelOrderCalculator :=
  let (base, c) := c.constraintBaseModelOrder node (offset * 2) offset
  match node.internal.modelOrder with
  | some mo => (base + mo, c)
  | none => (base, c)

/-- `computeConstraintGroupModelOrder(node, offset, smallOffset)`: constraint offset plus
`GROUP_MODEL_ORDER_CYCLE_BREAKING_ID * smallOffset + MODEL_ORDER` (if the node has a model order). -/
def computeConstraintGroupModelOrder (c : GroupModelOrderCalculator) (node : LNode) (offset smallOffset : Int) :
    Int × GroupModelOrderCalculator :=
  let (base, c) := c.constraintBaseModelOrder node (offset * 2) offset
  let groupId := node.props.getD LayeredOptions.GROUP_MODEL_ORDER_CYCLE_BREAKING_ID 0
  match node.internal.modelOrder with
  | some mo => (base + (groupId * smallOffset + mo), c)
  | none => (base, c)

/-- `resetInternalCounters()`. -/
def resetInternalCounters (_c : GroupModelOrderCalculator) : GroupModelOrderCalculator := {}

end GroupModelOrderCalculator

end Elk.Alg.Layered.P1Cycles
