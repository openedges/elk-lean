import Elk.Alg.Layered.LayeredPhases
import Elk.Alg.Layered.Graph.LGraphUtil
/-!
# `org.eclipse.elk.alg.layered.intermediate.PortListSorter`

Port of elk-rs `intermediate/port_list_sorter.rs`. Sorts the port lists of the layered nodes
clockwise: with fixed order by side and then by `PORT_INDEX` (`FIXED_ORDER` only) and position;
with fixed sides by side only, followed by the (Java-bug-compatible) reversal of the south and
west ranges and, with `PORT_DEGREE` sorting, by the number of non-reversed edges on the east/west
sides. Afterwards the port sides are cached.

All sorts are stable (`stableSort`, the Rust `stable_sort_by` index tie-break). The comparators
read the arena snapshot taken before the sort (`withArena`). Rust behaviour followed here
(deviations from Java): positions are compared with `partial_cmp` (`Float.comparePartial`) and an
undefined port side compares equal instead of throwing.

Note: `compare_port_degree_east_west` returns `Equal` for ports on different sides, which is only
a consistent order because the ports are grouped by side at that point (the side sort and the
range reversals keep the sides contiguous).
-/
namespace Elk.Alg.Layered.Intermediate

open Elk.Graph Elk.Core Elk.Core.Alg Elk.Core.Util Elk.Core.Math Elk.Core.Options Elk.Alg.Layered
  Elk.Alg.Layered.Graph Elk.Alg.Layered.Options LayeredM

namespace PortListSorter

/-- `side_ordinal(side)`: `UNDEFINED = 0, NORTH = 1, EAST = 2, SOUTH = 3, WEST = 4`. -/
@[inline] def sideOrdinal (side : PortSide) : Nat := ElkEnum.ordinal side

/-- `compare_port_side(p1, p2)` (Java `CMP_PORT_SIDE`). -/
def comparePortSide (a : LGraphArena) (p1 p2 : LPortId) : Ordering :=
  compare (sideOrdinal (a.port p1).side) (sideOrdinal (a.port p2).side)

/-- `real_degree(port, outgoing)` (Java `realDegree`): edges without `REVERSED`. -/
def realDegree (a : LGraphArena) (port : LPortId) (outgoing : Bool) : Nat :=
  let pt := a.port port
  let edges := if outgoing then pt.outgoingEdges else pt.incomingEdges
  (edges.filter fun e => !(a.edge e).internal.reversed).size

/-- `compare_port_degree_east_west(p1, p2)` (Java `CMP_PORT_DEGREE_EAST_WEST`): east ports by
decreasing outgoing degree, west ports by increasing incoming degree. -/
def comparePortDegreeEastWest (a : LGraphArena) (p1 p2 : LPortId) : Ordering :=
  let side1 := (a.port p1).side
  let side2 := (a.port p2).side
  if side1 != side2 then .eq
  else match side1 with
    | .east => compare (realDegree a p2 true) (realDegree a p1 true)
    | .west => compare (realDegree a p1 false) (realDegree a p2 false)
    | _ => .eq

/-- `compare_fixed_order_and_pos(p1, p2, constraints)` (Java `CMP_FIXED_ORDER_AND_FIXED_POS`). -/
def compareFixedOrderAndPos (a : LGraphArena) (constraints : PortConstraints) (p1 p2 : LPortId) : Ordering :=
  let pt1 := a.port p1
  let pt2 := a.port p2
  let side1 := pt1.side
  if side1 != pt2.side || !constraints.isOrderFixed then .eq
  else
    let byIndex : Option Ordering :=
      if constraints == .fixedOrder then
        match pt1.props.get LayeredOptions.PORT_INDEX, pt2.props.get LayeredOptions.PORT_INDEX with
        | some i1, some i2 => if i1 != i2 then some (compare i1 i2) else none
        | _, _ => none
      else none
    match byIndex with
    | some o => o
    | none =>
      let pos1 := pt1.position
      let pos2 := pt2.position
      match side1 with
      | .north => Float.comparePartial pos1.x pos2.x
      | .east => Float.comparePartial pos1.y pos2.y
      | .south => Float.comparePartial pos2.x pos1.x
      | .west => Float.comparePartial pos2.y pos1.y
      | .undefined => .eq

/-- `compare_ports_combined(p1, p2, constraints)` (Java `CMP_COMBINED`). -/
def comparePortsCombined (a : LGraphArena) (constraints : PortConstraints) (p1 p2 : LPortId) : Ordering :=
  match comparePortSide a p1 p2 with
  | .eq => compareFixedOrderAndPos a constraints p1 p2
  | o => o

/-- `find_port_side_range(ports, side)` (Java `findPortSideRange`), including both Java bugs: the
loops stop one before the end, and the second loop re-reads the port at `lowIdx`. -/
def findPortSideRange (a : LGraphArena) (ports : Array LPortId) (side : PortSide) : Nat × Nat := Id.run do
  if ports.isEmpty then return (0, 0)
  let mut currentSide := (a.port ports[0]!).side
  let lb := sideOrdinal side
  let hb := lb + 1
  let mut lowIdx := 0
  while lowIdx < ports.size - 1 && sideOrdinal currentSide < lb do
    lowIdx := lowIdx + 1
    currentSide := (a.port ports[lowIdx]!).side
  let mut highIdx := lowIdx
  while highIdx < ports.size - 1 && sideOrdinal currentSide < hb do
    highIdx := highIdx + 1
    currentSide := (a.port ports[lowIdx]!).side -- Java bug: reads lowIdx
  return (lowIdx, highIdx)

/-- `reverse_range(ports, low_idx, high_idx)` (Java `reverse`): reverses `[lowIdx, highIdx)`
unless the range has at most two elements. -/
def reverseRange (ports : Array LPortId) (lowIdx highIdx : Nat) : Array LPortId :=
  if highIdx <= lowIdx + 2 then ports
  else ports.extract 0 lowIdx ++ (ports.extract lowIdx highIdx).reverse ++ ports.extract highIdx ports.size

/-- `reverse_west_and_south_side(ports)` (Java `reverseWestAndSouthSide`). -/
def reverseWestAndSouthSide (a : LGraphArena) (ports : Array LPortId) : Array LPortId :=
  if ports.size <= 1 then ports
  else
    let (southLow, southHigh) := findPortSideRange a ports .south
    let ports := reverseRange ports southLow southHigh
    let (westLow, westHigh) := findPortSideRange a ports .west
    reverseRange ports westLow westHigh

/-- The sorted port list of a node with the given constraints (unchanged when the sides are free). -/
def sortedPorts (a : LGraphArena) (ports : Array LPortId) (constraints : PortConstraints)
    (sortingStrategy : PortSortingStrategy) : Array LPortId :=
  if constraints.isOrderFixed then
    stableSort ports (comparePortsCombined a constraints)
  else if constraints.isSideFixed then
    let ports := stableSort ports (comparePortSide a)
    let ports := reverseWestAndSouthSide a ports
    if sortingStrategy == .portDegree then stableSort ports (comparePortDegreeEastWest a) else ports
  else ports

/-- `process(graph, monitor)`: the nodes of every layer. -/
def process (graph : LGraphId) (monitor : ProgressMonitor) : LayeredM Unit := do
  let _ ← monitor.begin "Port order processing" 1.0
  let sortingStrategy := ((← getGraph graph).props.get LayeredOptions.PORT_SORTING_STRATEGY).getD
    PortSortingStrategy.inputOrder
  for layer in (← getGraph graph).layers do
    let nodes := (← getLayer layer).nodes
    for node in nodes do
      let nd ← getNode node
      let constraints := nd.props.getD LayeredOptions.PORT_CONSTRAINTS PortConstraints.undefined
      let ports := nd.ports
      if constraints.isOrderFixed || constraints.isSideFixed then
        let sorted ← withArena fun a => sortedPorts a ports constraints sortingStrategy
        modifyNode node fun n => { n with ports := sorted }
      cachePortSides node
  monitor.done

/-- The `PortListSorter` processor. -/
def processor : LayeredProcessor := { name := "PortListSorter", process := process }

end PortListSorter

builtin_initialize registerPortListSorter : Unit ←
  IntermediateProcessorStrategy.register .portListSorter PortListSorter.processor

end Elk.Alg.Layered.Intermediate
