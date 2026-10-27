import Elk.Alg.Layered.Intermediate.Loops.SelfLoopEdge
import Elk.Alg.Layered.Intermediate.Loops.SelfHyperLoopLabels
import Elk.Core.Util.Sort
/-!
# `org.eclipse.elk.alg.layered.intermediate.loops.SelfHyperLoop` (+ `SelfLoopType`)

Port of elk-rs `intermediate/loops/self_hyper_loop.rs` (pure data; see `SelfLoopPort`).
`SelfLoopType` (Java `SelfLoopType.java`) is defined in the same Rust module and therefore here.

Representation of the Rust collections:
- `sl_ports_by_side: HashMap<PortSide, Vec<_>>` (only looked up by key) → `slPortsBySide`, an
  array indexed by the `PortSide` ordinal;
- `occupied_port_sides: HashSet<PortSide>` → `EnumSet PortSide` (iteration in ordinal order,
  like the Java `EnumSet`; Rust only iterates it for one-sided loops, which occupy one side);
- `routing_slot: Vec<i32>` indexed by `side_index` (= `PortSide` ordinal) → `Array Int`.

Operations that need port sides or port ids take a lookup closure (the holder-level wrappers in
`SelfLoopHolder` / `Loops.Ops` supply them).
-/
namespace Elk.Alg.Layered.Intermediate.Loops

open Elk.Graph Elk.Core.Math Elk.Core.Options Elk.Core.Util Elk.Alg.Layered.Graph

/-- `SelfLoopType`: the kind of a self hyper loop, determined by the port sides it connects. -/
elk_enum SelfLoopType := oneSide twoSidesCorner twoSidesOpposing threeSides fourSides

namespace SelfLoopType

/-- `SelfLoopType::from_port_sides(sides)`: `none` if `UNDEFINED` is among the sides or no
side is given. -/
def fromPortSides (sides : EnumSet PortSide) : Option SelfLoopType :=
  if sides.contains .undefined then none
  else
    match sides.size with
    | 1 => some .oneSide
    | 2 =>
      let eastWest := sides.contains .east && sides.contains .west
      let northSouth := sides.contains .north && sides.contains .south
      if eastWest || northSouth then some .twoSidesOpposing else some .twoSidesCorner
    | 3 => some .threeSides
    | 4 => some .fourSides
    | _ => none

end SelfLoopType

/-- Number of `PortSide` constants (length of the per-side arrays). -/
def PORT_SIDE_COUNT : Nat := ElkEnum.count (α := PortSide)

/-- `SelfHyperLoop`: a self loop hyperedge consisting of at least one self loop edge. -/
structure SelfHyperLoop where
  /-- `getSLPorts()` (insertion order, no duplicates). -/
  slPorts : Array SelfLoopPortId := #[]
  /-- `getSLEdges()`. -/
  slEdges : Array SelfLoopEdgeId := #[]
  /-- `getSLLabels()` (`none` until an edge with labels is added). -/
  slLabels : Option SelfHyperLoopLabels := none
  /-- `getSelfLoopType()` (set by `computePortsPerSide`). -/
  selfLoopType : Option SelfLoopType := none
  /-- `slPortsBySide`: per `PortSide` ordinal the loop's ports on that side (in `slPorts` order). -/
  slPortsBySide : Array (Array SelfLoopPortId) := Array.replicate PORT_SIDE_COUNT #[]
  /-- `getLeftmostPort()`. -/
  leftmostPort : Option SelfLoopPortId := none
  /-- `getRightmostPort()`. -/
  rightmostPort : Option SelfLoopPortId := none
  /-- `getOccupiedPortSides()`. -/
  occupiedPortSides : EnumSet PortSide := EnumSet.empty
  /-- `routingSlot` per `PortSide` ordinal (Rust `side_index`). -/
  routingSlot : Array Int := Array.replicate PORT_SIDE_COUNT 0
  deriving Inhabited, Repr

namespace SelfHyperLoop

/-- `compute_ports_per_side()`: groups the ports by side (ports on `UNDEFINED` are skipped) and
derives the self loop type. `sideOf` is the side of the port's `LPort`. -/
def computePortsPerSide (l : SelfHyperLoop) (sideOf : SelfLoopPortId → PortSide) : SelfHyperLoop := Id.run do
  let mut bySide : Array (Array SelfLoopPortId) := Array.replicate PORT_SIDE_COUNT #[]
  let mut sides : EnumSet PortSide := EnumSet.empty
  for p in l.slPorts do
    let side := sideOf p
    if side == .undefined then continue
    bySide := bySide.modify (ElkEnum.ordinal side) (·.push p)
    sides := sides.insert side
  return { l with slPortsBySide := bySide, selfLoopType := SelfLoopType.fromPortSides sides }

/-- `ports_on_side(side)` / Java `getSLPortsBySide().get(side)`: empty when the side has no ports. -/
def portsOnSide (l : SelfHyperLoop) (side : PortSide) : Array SelfLoopPortId :=
  (l.slPortsBySide[ElkEnum.ordinal side]?).getD #[]

/-- `clear_routing_slots()`. -/
def clearRoutingSlots (l : SelfHyperLoop) : SelfHyperLoop :=
  { l with routingSlot := l.routingSlot.map fun _ => 0 }

/-- `getRoutingSlot(side)`. -/
def getRoutingSlot (l : SelfHyperLoop) (side : PortSide) : Int :=
  (l.routingSlot[ElkEnum.ordinal side]?).getD 0

/-- `setRoutingSlot(side, slot)`. -/
def setRoutingSlot (l : SelfHyperLoop) (side : PortSide) (slot : Int) : SelfHyperLoop :=
  { l with routingSlot := l.routingSlot.set! (ElkEnum.ordinal side) slot }

/-- `sort_ports_by_id()`: stable sort of `slPorts` by the `LPort.id` of each port (`portId`). -/
def sortPortsById (l : SelfHyperLoop) (portId : SelfLoopPortId → Int) : SelfHyperLoop :=
  { l with slPorts := stableSortByKey l.slPorts portId }

end SelfHyperLoop

end Elk.Alg.Layered.Intermediate.Loops
