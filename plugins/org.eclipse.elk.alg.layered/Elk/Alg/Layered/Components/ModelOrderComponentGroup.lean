import Elk.Alg.Layered.Components.ComponentGroup
/-!
# `org.eclipse.elk.alg.layered.components.ModelOrderComponentGroup`

Port of `ModelOrderComponentGroup` in `components/component_group.rs` (elk-rs) and
`ModelOrderComponentGroup.java`: a `ComponentGroup` that additionally keeps the insertion
order of its components and applies the model order constraints
(`MODEL_ORDER_CONSTRAINTS`), e.g. a `NORTH` component cannot join a group that already holds a
`NONE` component since it would be placed above it.

The Rust `MODEL_ORDER_CONSTRAINTS` (`FxHashMap<u8, Vec<u8>>` built from the pair list, only used
for lookups) is the per-mask list `modelOrderConstraintMasks`, deduplicated in pair order like
the Rust builder.
-/
namespace Elk.Alg.Layered.Components

open Elk.Graph Elk.Core.Options Elk.Alg.Layered.Graph ComponentGroup

namespace ModelOrderComponentGroup

/-- Rust `MODEL_ORDER_CONSTRAINT_PAIRS`: `(candidate mask, constraint mask)`. -/
def MODEL_ORDER_CONSTRAINT_PAIRS : Array (Nat × Nat) := #[
  (MASK_NORTH, MASK_NONE),
  (MASK_WEST, MASK_NONE),
  (MASK_NORTH_EAST, MASK_NONE),
  (MASK_NORTH_WEST, MASK_NONE),
  (MASK_NORTH_SOUTH_WEST, MASK_NONE),
  (MASK_NORTH_EAST_WEST, MASK_NONE),
  (MASK_NORTH_WEST, MASK_NORTH),
  (MASK_NONE, MASK_EAST),
  (MASK_NORTH, MASK_EAST),
  (MASK_WEST, MASK_EAST),
  (MASK_NORTH_EAST, MASK_EAST),
  (MASK_NORTH_SOUTH, MASK_EAST),
  (MASK_NORTH_WEST, MASK_EAST),
  (MASK_NORTH_SOUTH_WEST, MASK_EAST),
  (MASK_NORTH_EAST_WEST, MASK_EAST),
  (MASK_EAST_WEST, MASK_EAST),
  (MASK_NONE, MASK_SOUTH),
  (MASK_NORTH, MASK_SOUTH),
  (MASK_EAST, MASK_SOUTH),
  (MASK_WEST, MASK_SOUTH),
  (MASK_NORTH_EAST, MASK_SOUTH),
  (MASK_NORTH_SOUTH, MASK_SOUTH),
  (MASK_NORTH_WEST, MASK_SOUTH),
  (MASK_EAST_WEST, MASK_SOUTH),
  (MASK_SOUTH_WEST, MASK_SOUTH),
  (MASK_NORTH_SOUTH_WEST, MASK_SOUTH),
  (MASK_NORTH_EAST_SOUTH, MASK_SOUTH),
  (MASK_NORTH_EAST_WEST, MASK_SOUTH),
  (MASK_NORTH, MASK_WEST),
  (MASK_NORTH_EAST, MASK_WEST),
  (MASK_NORTH_WEST, MASK_WEST),
  (MASK_NORTH_EAST_WEST, MASK_WEST),
  (MASK_NORTH, MASK_NORTH_EAST),
  (MASK_WEST, MASK_NORTH_EAST),
  (MASK_NORTH_WEST, MASK_NORTH_EAST),
  (MASK_NORTH_EAST, MASK_NORTH_EAST),
  (MASK_NORTH_SOUTH_WEST, MASK_NORTH_EAST),
  (MASK_NONE, MASK_EAST_SOUTH),
  (MASK_NORTH, MASK_EAST_SOUTH),
  (MASK_EAST, MASK_EAST_SOUTH),
  (MASK_SOUTH, MASK_EAST_SOUTH),
  (MASK_WEST, MASK_EAST_SOUTH),
  (MASK_NORTH_EAST, MASK_EAST_SOUTH),
  (MASK_NORTH_SOUTH, MASK_EAST_SOUTH),
  (MASK_NORTH_WEST, MASK_EAST_SOUTH),
  (MASK_SOUTH_WEST, MASK_EAST_SOUTH),
  (MASK_EAST_WEST, MASK_EAST_SOUTH),
  (MASK_NORTH_EAST_WEST, MASK_EAST_SOUTH),
  (MASK_NORTH_SOUTH_WEST, MASK_EAST_SOUTH),
  (MASK_NORTH_EAST_SOUTH_WEST, MASK_EAST_SOUTH),
  (MASK_NONE, MASK_SOUTH_WEST),
  (MASK_NORTH, MASK_SOUTH_WEST),
  (MASK_EAST, MASK_SOUTH_WEST),
  (MASK_WEST, MASK_SOUTH_WEST),
  (MASK_NORTH_EAST, MASK_SOUTH_WEST),
  (MASK_NORTH_SOUTH, MASK_SOUTH_WEST),
  (MASK_NORTH_WEST, MASK_SOUTH_WEST),
  (MASK_EAST_WEST, MASK_SOUTH_WEST),
  (MASK_NORTH_EAST_WEST, MASK_SOUTH_WEST),
  (MASK_NORTH_EAST_SOUTH, MASK_SOUTH_WEST),
  (MASK_NORTH_EAST_SOUTH_WEST, MASK_SOUTH_WEST),
  (MASK_NORTH, MASK_EAST_WEST),
  (MASK_WEST, MASK_EAST_WEST),
  (MASK_NORTH_EAST, MASK_EAST_WEST),
  (MASK_NORTH_WEST, MASK_EAST_WEST),
  (MASK_SOUTH_WEST, MASK_EAST_WEST),
  (MASK_NORTH_EAST_WEST, MASK_EAST_WEST),
  (MASK_NORTH_SOUTH_WEST, MASK_EAST_WEST),
  (MASK_NONE, MASK_EAST_SOUTH_WEST),
  (MASK_NORTH, MASK_EAST_SOUTH_WEST),
  (MASK_EAST, MASK_EAST_SOUTH_WEST),
  (MASK_WEST, MASK_EAST_SOUTH_WEST),
  (MASK_NORTH_EAST, MASK_EAST_SOUTH_WEST),
  (MASK_NORTH_SOUTH, MASK_EAST_SOUTH_WEST),
  (MASK_NORTH_WEST, MASK_EAST_SOUTH_WEST),
  (MASK_EAST_WEST, MASK_EAST_SOUTH_WEST),
  (MASK_NORTH_EAST_WEST, MASK_EAST_SOUTH_WEST),
  (MASK_NORTH, MASK_NORTH_SOUTH_WEST),
  (MASK_EAST, MASK_NORTH_SOUTH_WEST),
  (MASK_SOUTH, MASK_NORTH_SOUTH_WEST),
  (MASK_NORTH_EAST, MASK_NORTH_SOUTH_WEST),
  (MASK_NONE, MASK_NORTH_EAST_SOUTH),
  (MASK_NORTH, MASK_NORTH_EAST_SOUTH),
  (MASK_SOUTH, MASK_NORTH_EAST_SOUTH),
  (MASK_WEST, MASK_NORTH_EAST_SOUTH),
  (MASK_NORTH_EAST, MASK_NORTH_EAST_SOUTH),
  (MASK_NORTH_SOUTH, MASK_NORTH_EAST_SOUTH),
  (MASK_NORTH_WEST, MASK_NORTH_EAST_SOUTH),
  (MASK_NORTH_WEST, MASK_NORTH_EAST_SOUTH_WEST),
  (MASK_NORTH_EAST, MASK_NORTH_EAST_SOUTH_WEST),
  (MASK_EAST_WEST, MASK_NONE),
  (MASK_EAST_WEST, MASK_WEST),
  (MASK_EAST_WEST, MASK_EAST),
  (MASK_NORTH_SOUTH, MASK_NONE),
  (MASK_NORTH_SOUTH, MASK_NORTH),
  (MASK_NORTH_SOUTH, MASK_SOUTH)]

/-- Rust `MODEL_ORDER_CONSTRAINTS`: per candidate mask (`0..15`) the constraint masks in pair
order without duplicates. -/
def MODEL_ORDER_CONSTRAINTS : Array (Array Nat) :=
  (Array.range 16).map fun candidate =>
    MODEL_ORDER_CONSTRAINT_PAIRS.foldl (fun acc (c, k) =>
      if c == candidate && !acc.contains k then acc.push k else acc) #[]

/-- Rust `model_order_constraint_masks(candidate_mask)`. -/
def modelOrderConstraintMasks (candidateMask : Nat) : Array Nat :=
  MODEL_ORDER_CONSTRAINTS[candidateMask]?.getD #[]

end ModelOrderComponentGroup

/-- `ModelOrderComponentGroup` (Rust `components` + `component_order`). -/
structure ModelOrderComponentGroup where
  /-- `components` multimap: `(mask, components)` entries in insertion order of the masks. -/
  byMask : Array (Nat × Array LGraphId) := #[]
  /-- `componentOrder`: `(mask, component)` in insertion order. -/
  componentOrder : Array (Nat × LGraphId) := #[]
  deriving Inhabited

namespace ModelOrderComponentGroup

/-- `new ModelOrderComponentGroup()`. -/
def new : ModelOrderComponentGroup := {}

/-- `canAdd(component)`: the `ComponentGroup` constraints plus the model order constraints. -/
def canAddMask (g : ModelOrderComponentGroup) (candidateMask : Nat) : Bool :=
  !(constraintMasks candidateMask).any (fun c => entriesHaveMask g.byMask c) &&
    !(modelOrderConstraintMasks candidateMask).any (fun c => entriesHaveMask g.byMask c)

/-- `add(component)` for a component whose `EXT_PORT_CONNECTIONS` are `connections`. -/
def addWithConnections (g : ModelOrderComponentGroup) (component : LGraphId) (connections : EnumSet PortSide) :
    Bool × ModelOrderComponentGroup :=
  let mask := connectionsToMask connections
  if !g.canAddMask mask then (false, g)
  else (true, { g with byMask := entriesAdd g.byMask mask component,
                       componentOrder := g.componentOrder.push (mask, component) })

/-- `add(component)`: reads the component's `EXT_PORT_CONNECTIONS` from the arena. -/
def add (g : ModelOrderComponentGroup) (component : LGraphId) : LayeredM (Bool × ModelOrderComponentGroup) := do
  return g.addWithConnections component (← LayeredM.getGraph component).internal.extPortConnections

/-- `new ModelOrderComponentGroup(component)`. -/
def withComponent (component : LGraphId) : LayeredM ModelOrderComponentGroup := do
  return (← (new).add component).2

/-- `getPortSides()`: the port sides of the components in insertion order. -/
def portSides (g : ModelOrderComponentGroup) : Array (EnumSet PortSide) :=
  g.componentOrder.map fun (mask, _) => maskToConnections mask

/-- `getComponents()`: the components in insertion order. -/
def components (g : ModelOrderComponentGroup) : Array LGraphId :=
  g.componentOrder.map (·.2)

/-- `getComponents(connections)`. -/
def componentsFor (g : ModelOrderComponentGroup) (connections : EnumSet PortSide) : Array LGraphId :=
  entriesFor g.byMask connections

end ModelOrderComponentGroup

end Elk.Alg.Layered.Components
