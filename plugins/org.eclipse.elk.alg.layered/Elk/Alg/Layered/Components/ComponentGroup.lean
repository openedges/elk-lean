import Elk.Alg.Layered.Graph.Monad
/-!
# `org.eclipse.elk.alg.layered.components.ComponentGroup`

Port of `components/component_group.rs` (elk-rs) and `ComponentGroup.java`.

A component group is divided into nine sectors (`nw n ne / w c e / sw s se`); the external
port sides a component connects to (`InternalProperties.EXT_PORT_CONNECTIONS`, the typed field
`LGraphInternals.extPortConnections`) determine the sectors it occupies. A component can only be
added if no component already in the group blocks one of its sectors.

Representation (as in Rust): the port side sets are encoded as 4-bit masks
(`NORTH = 1, EAST = 2, SOUTH = 4, WEST = 8`; `UNDEFINED` is ignored), the Java
`ArrayListMultimap<Set<PortSide>, LGraph>` is an insertion-ordered array of
`(mask, components)` entries. The constraint tables are the Rust `CONSTRAINT_*` arrays.

The mask helpers and constraint tables are shared with `ModelOrderComponentGroup`.
-/
namespace Elk.Alg.Layered.Components

open Elk.Graph Elk.Core.Options Elk.Alg.Layered.Graph

namespace ComponentGroup

/-- Rust `MASK_NONE`. -/
def MASK_NONE : Nat := 0
/-- Rust `MASK_NORTH`. -/
def MASK_NORTH : Nat := 1
/-- Rust `MASK_EAST`. -/
def MASK_EAST : Nat := 2
/-- Rust `MASK_SOUTH`. -/
def MASK_SOUTH : Nat := 4
/-- Rust `MASK_WEST`. -/
def MASK_WEST : Nat := 8
/-- Rust `MASK_NORTH_SOUTH`. -/
def MASK_NORTH_SOUTH : Nat := MASK_NORTH ||| MASK_SOUTH
/-- Rust `MASK_EAST_WEST`. -/
def MASK_EAST_WEST : Nat := MASK_EAST ||| MASK_WEST
/-- Rust `MASK_NORTH_WEST`. -/
def MASK_NORTH_WEST : Nat := MASK_NORTH ||| MASK_WEST
/-- Rust `MASK_NORTH_EAST`. -/
def MASK_NORTH_EAST : Nat := MASK_NORTH ||| MASK_EAST
/-- Rust `MASK_SOUTH_WEST`. -/
def MASK_SOUTH_WEST : Nat := MASK_SOUTH ||| MASK_WEST
/-- Rust `MASK_EAST_SOUTH`. -/
def MASK_EAST_SOUTH : Nat := MASK_EAST ||| MASK_SOUTH
/-- Rust `MASK_NORTH_EAST_WEST`. -/
def MASK_NORTH_EAST_WEST : Nat := MASK_NORTH ||| MASK_EAST ||| MASK_WEST
/-- Rust `MASK_EAST_SOUTH_WEST`. -/
def MASK_EAST_SOUTH_WEST : Nat := MASK_EAST ||| MASK_SOUTH ||| MASK_WEST
/-- Rust `MASK_NORTH_SOUTH_WEST`. -/
def MASK_NORTH_SOUTH_WEST : Nat := MASK_NORTH ||| MASK_SOUTH ||| MASK_WEST
/-- Rust `MASK_NORTH_EAST_SOUTH`. -/
def MASK_NORTH_EAST_SOUTH : Nat := MASK_NORTH ||| MASK_EAST ||| MASK_SOUTH
/-- Rust `MASK_NORTH_EAST_SOUTH_WEST`. -/
def MASK_NORTH_EAST_SOUTH_WEST : Nat := MASK_NORTH ||| MASK_EAST ||| MASK_SOUTH ||| MASK_WEST

/-- Rust `CONSTRAINT_NONE` (Java `CONSTRAINTS.put(SIDES_NONE, …)`): components that block a
component without external connections. -/
def CONSTRAINT_NONE : Array Nat := #[MASK_NORTH_EAST_SOUTH_WEST]
/-- Rust `CONSTRAINT_WEST`. -/
def CONSTRAINT_WEST : Array Nat := #[MASK_NORTH_EAST_SOUTH_WEST, MASK_NORTH_SOUTH_WEST]
/-- Rust `CONSTRAINT_EAST`. -/
def CONSTRAINT_EAST : Array Nat := #[MASK_NORTH_EAST_SOUTH, MASK_NORTH_EAST_SOUTH_WEST]
/-- Rust `CONSTRAINT_NORTH`. -/
def CONSTRAINT_NORTH : Array Nat := #[MASK_NORTH_EAST_SOUTH_WEST, MASK_NORTH_EAST_WEST]
/-- Rust `CONSTRAINT_SOUTH`. -/
def CONSTRAINT_SOUTH : Array Nat := #[MASK_EAST_SOUTH_WEST, MASK_NORTH_EAST_SOUTH_WEST]
/-- Rust `CONSTRAINT_NORTH_SOUTH`. -/
def CONSTRAINT_NORTH_SOUTH : Array Nat :=
  #[MASK_EAST_WEST, MASK_NORTH_EAST_SOUTH_WEST, MASK_NORTH_EAST_WEST, MASK_EAST_SOUTH_WEST]
/-- Rust `CONSTRAINT_EAST_WEST`. -/
def CONSTRAINT_EAST_WEST : Array Nat :=
  #[MASK_NORTH_SOUTH, MASK_NORTH_SOUTH_WEST, MASK_NORTH_EAST_SOUTH, MASK_NORTH_EAST_SOUTH_WEST]
/-- Rust `CONSTRAINT_NORTH_WEST`. -/
def CONSTRAINT_NORTH_WEST : Array Nat := #[MASK_NORTH_WEST, MASK_NORTH_EAST_WEST, MASK_NORTH_SOUTH_WEST]
/-- Rust `CONSTRAINT_NORTH_EAST`. -/
def CONSTRAINT_NORTH_EAST : Array Nat := #[MASK_NORTH_EAST, MASK_NORTH_EAST_WEST, MASK_NORTH_EAST_SOUTH]
/-- Rust `CONSTRAINT_SOUTH_WEST`. -/
def CONSTRAINT_SOUTH_WEST : Array Nat := #[MASK_SOUTH_WEST, MASK_EAST_SOUTH_WEST, MASK_NORTH_SOUTH_WEST]
/-- Rust `CONSTRAINT_EAST_SOUTH`. -/
def CONSTRAINT_EAST_SOUTH : Array Nat := #[MASK_EAST_SOUTH, MASK_EAST_SOUTH_WEST, MASK_NORTH_EAST_SOUTH]
/-- Rust `CONSTRAINT_NORTH_EAST_WEST`. -/
def CONSTRAINT_NORTH_EAST_WEST : Array Nat :=
  #[MASK_NORTH, MASK_NORTH_SOUTH, MASK_NORTH_WEST, MASK_NORTH_EAST, MASK_NORTH_EAST_SOUTH_WEST,
    MASK_NORTH_EAST_WEST, MASK_NORTH_SOUTH_WEST, MASK_NORTH_EAST_SOUTH]
/-- Rust `CONSTRAINT_EAST_SOUTH_WEST`. -/
def CONSTRAINT_EAST_SOUTH_WEST : Array Nat :=
  #[MASK_SOUTH, MASK_NORTH_SOUTH, MASK_SOUTH_WEST, MASK_EAST_SOUTH, MASK_EAST_SOUTH_WEST,
    MASK_NORTH_SOUTH_WEST, MASK_NORTH_EAST_SOUTH, MASK_NORTH_EAST_SOUTH_WEST]
/-- Rust `CONSTRAINT_NORTH_SOUTH_WEST`. -/
def CONSTRAINT_NORTH_SOUTH_WEST : Array Nat :=
  #[MASK_WEST, MASK_EAST_WEST, MASK_NORTH_WEST, MASK_SOUTH_WEST, MASK_NORTH_EAST_WEST,
    MASK_EAST_SOUTH_WEST, MASK_NORTH_SOUTH_WEST, MASK_NORTH_EAST_SOUTH_WEST]
/-- Rust `CONSTRAINT_NORTH_EAST_SOUTH`. -/
def CONSTRAINT_NORTH_EAST_SOUTH : Array Nat :=
  #[MASK_EAST, MASK_EAST_WEST, MASK_NORTH_EAST, MASK_EAST_SOUTH, MASK_NORTH_EAST_WEST,
    MASK_EAST_SOUTH_WEST, MASK_NORTH_EAST_SOUTH, MASK_NORTH_EAST_SOUTH_WEST]
/-- Rust `CONSTRAINT_NORTH_EAST_SOUTH_WEST`. -/
def CONSTRAINT_NORTH_EAST_SOUTH_WEST : Array Nat :=
  #[MASK_NONE, MASK_WEST, MASK_EAST, MASK_NORTH, MASK_SOUTH, MASK_NORTH_SOUTH, MASK_EAST_WEST,
    MASK_NORTH_EAST_WEST, MASK_EAST_SOUTH_WEST, MASK_NORTH_SOUTH_WEST, MASK_NORTH_EAST_SOUTH,
    MASK_NORTH_EAST_SOUTH_WEST]

/-- Rust `constraint_masks(candidate_mask)` (Java `CONSTRAINTS.get(sides)`): masks of the
components that prevent a component with the given mask from being added. -/
def constraintMasks (candidateMask : Nat) : Array Nat :=
  if candidateMask == MASK_NONE then CONSTRAINT_NONE
  else if candidateMask == MASK_WEST then CONSTRAINT_WEST
  else if candidateMask == MASK_EAST then CONSTRAINT_EAST
  else if candidateMask == MASK_NORTH then CONSTRAINT_NORTH
  else if candidateMask == MASK_SOUTH then CONSTRAINT_SOUTH
  else if candidateMask == MASK_NORTH_SOUTH then CONSTRAINT_NORTH_SOUTH
  else if candidateMask == MASK_EAST_WEST then CONSTRAINT_EAST_WEST
  else if candidateMask == MASK_NORTH_WEST then CONSTRAINT_NORTH_WEST
  else if candidateMask == MASK_NORTH_EAST then CONSTRAINT_NORTH_EAST
  else if candidateMask == MASK_SOUTH_WEST then CONSTRAINT_SOUTH_WEST
  else if candidateMask == MASK_EAST_SOUTH then CONSTRAINT_EAST_SOUTH
  else if candidateMask == MASK_NORTH_EAST_WEST then CONSTRAINT_NORTH_EAST_WEST
  else if candidateMask == MASK_EAST_SOUTH_WEST then CONSTRAINT_EAST_SOUTH_WEST
  else if candidateMask == MASK_NORTH_SOUTH_WEST then CONSTRAINT_NORTH_SOUTH_WEST
  else if candidateMask == MASK_NORTH_EAST_SOUTH then CONSTRAINT_NORTH_EAST_SOUTH
  else if candidateMask == MASK_NORTH_EAST_SOUTH_WEST then CONSTRAINT_NORTH_EAST_SOUTH_WEST
  else #[]

/-- Rust `connections_to_mask(connections)`: `UNDEFINED` does not contribute. -/
def connectionsToMask (connections : EnumSet PortSide) : Nat := Id.run do
  let mut mask := MASK_NONE
  if connections.contains .north then mask := mask ||| MASK_NORTH
  if connections.contains .east then mask := mask ||| MASK_EAST
  if connections.contains .south then mask := mask ||| MASK_SOUTH
  if connections.contains .west then mask := mask ||| MASK_WEST
  return mask

/-- Rust `mask_to_connections(mask)`. -/
def maskToConnections (mask : Nat) : EnumSet PortSide := Id.run do
  let mut sides : Array PortSide := #[]
  if mask &&& MASK_NORTH != 0 then sides := sides.push .north
  if mask &&& MASK_EAST != 0 then sides := sides.push .east
  if mask &&& MASK_SOUTH != 0 then sides := sides.push .south
  if mask &&& MASK_WEST != 0 then sides := sides.push .west
  return EnumSet.of sides

/-- Rust `component_mask(component)`: mask of the component's `EXT_PORT_CONNECTIONS`. -/
def componentMask (component : LGraphId) : LayeredM Nat := do
  return connectionsToMask (← LayeredM.getGraph component).internal.extPortConnections

/-- Rust `has_component_with_mask(mask)` on a `(mask, components)` entry list. -/
def entriesHaveMask (entries : Array (Nat × Array LGraphId)) (mask : Nat) : Bool :=
  entries.any fun (m, cs) => m == mask && !cs.isEmpty

/-- Appends a component to the entry of its mask (creating the entry at the end if needed). -/
def entriesAdd (entries : Array (Nat × Array LGraphId)) (mask : Nat) (component : LGraphId) :
    Array (Nat × Array LGraphId) :=
  match entries.findIdx? (·.1 == mask) with
  | some i => entries.modify i fun (m, cs) => (m, cs.push component)
  | none => entries.push (mask, #[component])

/-- Rust `get_components_for(connections)` on an entry list. -/
def entriesFor (entries : Array (Nat × Array LGraphId)) (connections : EnumSet PortSide) : Array LGraphId :=
  let mask := connectionsToMask connections
  match entries.find? (·.1 == mask) with
  | some (_, cs) => cs
  | none => #[]

end ComponentGroup

/-- `ComponentGroup` (Rust `ComponentGroup { components: Vec<(u8, Vec<LGraphRef>)> }`): the
components of the group by port side mask, in insertion order of the masks. -/
structure ComponentGroup where
  /-- `components` multimap: `(mask, components)` entries in insertion order. -/
  byMask : Array (Nat × Array LGraphId) := #[]
  deriving Inhabited

namespace ComponentGroup

/-- `new ComponentGroup()`. -/
def new : ComponentGroup := {}

/-- `canAdd(component)` for a component with the given connection mask. -/
def canAddMask (g : ComponentGroup) (candidateMask : Nat) : Bool :=
  !(constraintMasks candidateMask).any fun c => entriesHaveMask g.byMask c

/-- `add(component)` for a component whose `EXT_PORT_CONNECTIONS` are `connections`: returns
whether the component was added and the updated group. -/
def addWithConnections (g : ComponentGroup) (component : LGraphId) (connections : EnumSet PortSide) :
    Bool × ComponentGroup :=
  let mask := connectionsToMask connections
  if !g.canAddMask mask then (false, g)
  else (true, { g with byMask := entriesAdd g.byMask mask component })

/-- `add(component)`: reads the component's `EXT_PORT_CONNECTIONS` from the arena. -/
def add (g : ComponentGroup) (component : LGraphId) : LayeredM (Bool × ComponentGroup) := do
  return g.addWithConnections component (← LayeredM.getGraph component).internal.extPortConnections

/-- `new ComponentGroup(component)`. -/
def withComponent (component : LGraphId) : LayeredM ComponentGroup := do
  return (← (new).add component).2

/-- `getPortSides()` (Rust `get_port_sides`): one entry per component, grouped by mask. -/
def portSides (g : ComponentGroup) : Array (EnumSet PortSide) :=
  g.byMask.foldl (fun acc (mask, cs) => cs.foldl (fun acc _ => acc.push (maskToConnections mask)) acc) #[]

/-- `getComponents()`: all components, grouped by mask in insertion order of the masks. -/
def components (g : ComponentGroup) : Array LGraphId :=
  g.byMask.foldl (fun acc (_, cs) => acc ++ cs) #[]

/-- `getComponents(connections)`. -/
def componentsFor (g : ComponentGroup) (connections : EnumSet PortSide) : Array LGraphId :=
  entriesFor g.byMask connections

end ComponentGroup

end Elk.Alg.Layered.Components
