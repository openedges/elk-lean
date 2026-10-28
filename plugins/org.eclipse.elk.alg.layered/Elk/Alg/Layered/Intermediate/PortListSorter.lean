import Elk.Alg.Layered.LayeredPhases
import Elk.Alg.Layered.Graph.LGraphUtil
import Elk.Core.Util.JavaSort
import Elk.Core.Exceptions
/-!
# `org.eclipse.elk.alg.layered.intermediate.PortListSorter`

Port of elk-rs `intermediate/port_list_sorter.rs`, sorting like ELK Java (the result reference).
Sorts the port lists of the layered nodes clockwise: with fixed order by side and then by
`PORT_INDEX` (`FIXED_ORDER` only) and position; with fixed sides by side only, followed by the
(Java-bug-compatible) reversal of the south and west ranges and, with `PORT_DEGREE` sorting, by the
number of non-reversed edges on the east/west sides. Afterwards the port sides are cached.

Java's `Collections.sort` is a JDK 21 `TimSort` (`javaSortBy`). `CMP_COMBINED` is not a consistent
order when only some ports of a side have a `PORT_INDEX` (an index pair decides, a missing index
falls back to the position), and `CMP_PORT_DEGREE_EAST_WEST` answers `0` for ports on different
sides, so the result depends on TimSort's comparison sequence; the side-only sort is consistent and
stays `stableSort`. Positions compare with `Double.compare` (`Float.compareJava`), port indices
with Java `int` subtraction, and two ports of side `UNDEFINED` make `CMP_COMBINED` throw Java's
`IllegalStateException("Port side is undefined")` (elk-rs: stable sorts, `partial_cmp`, `Equal`).

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

/-- Message of the `IllegalStateException` thrown by `CMP_FIXED_ORDER_AND_FIXED_POS` for two ports
of side `UNDEFINED`. -/
def undefinedSideMessage : String := "Port side is undefined"

/-- `compare_fixed_order_and_pos(p1, p2, constraints)` (Java `CMP_FIXED_ORDER_AND_FIXED_POS`): `0`
for different sides or a port order that is not fixed; with `FIXED_ORDER` by `PORT_INDEX` when both
ports have one (Java `int` difference); then by position (`Double.compare`; NORTH `x`, EAST `y`,
SOUTH/WEST reversed). `.error undefinedSideMessage` for side `UNDEFINED` (Java throws). -/
def compareFixedOrderAndPos (a : LGraphArena) (constraints : PortConstraints) (p1 p2 : LPortId) :
    Except String Ordering :=
  let pt1 := a.port p1
  let pt2 := a.port p2
  let side1 := pt1.side
  if side1 != pt2.side || !constraints.isOrderFixed then .ok .eq
  else
    let byIndex : Option Ordering :=
      if constraints == .fixedOrder then
        match pt1.props.get LayeredOptions.PORT_INDEX, pt2.props.get LayeredOptions.PORT_INDEX with
        | some i1, some i2 =>
          let indexDifference := Int.wrap32 (i1 - i2)
          if indexDifference != 0 then some (compare indexDifference 0) else none
        | _, _ => none
      else none
    match byIndex with
    | some o => .ok o
    | none =>
      let pos1 := pt1.position
      let pos2 := pt2.position
      match side1 with
      | .north => .ok (Float.compareJava pos1.x pos2.x)
      | .east => .ok (Float.compareJava pos1.y pos2.y)
      | .south => .ok (Float.compareJava pos2.x pos1.x)
      | .west => .ok (Float.compareJava pos2.y pos1.y)
      | .undefined => .error undefinedSideMessage

/-- `compare_ports_combined(p1, p2, constraints)` (Java `CMP_COMBINED` =
`CMP_PORT_SIDE.thenComparing(CMP_FIXED_ORDER_AND_FIXED_POS)`). -/
def comparePortsCombined (a : LGraphArena) (constraints : PortConstraints) (p1 p2 : LPortId) :
    Except String Ordering :=
  match comparePortSide a p1 p2 with
  | .eq => compareFixedOrderAndPos a constraints p1 p2
  | o => .ok o

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

/-- The sorted port list of a node with the given constraints (unchanged when the sides are free):
`Collections.sort(ports, CMP_COMBINED)` (TimSort) for a fixed order; for fixed sides the side sort,
the south/west reversal and, with `PORT_DEGREE`, `Collections.sort(ports, CMP_PORT_DEGREE_EAST_WEST)`.
`.error` carries the comparator's `undefinedSideMessage` or TimSort's
`JavaSort.contractViolationMessage`. -/
def sortedPorts (a : LGraphArena) (ports : Array LPortId) (constraints : PortConstraints)
    (sortingStrategy : PortSortingStrategy) : Except String (Array LPortId) :=
  if constraints.isOrderFixed then
    match javaSortByM (m := Except String) ports (comparePortsCombined a constraints) with
    | .ok (.ok sorted) => .ok sorted
    | .ok (.error msg) => .error msg
    | .error msg => .error msg
  else if constraints.isSideFixed then
    let ports := stableSort ports (comparePortSide a)
    let ports := reverseWestAndSouthSide a ports
    if sortingStrategy == .portDegree then
      match javaSortBy ports (comparePortDegreeEastWest a) with
      | .ok sorted => .ok sorted
      | .error msg => .error msg
    else .ok ports
  else .ok ports

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
        match ← withArena fun a => sortedPorts a ports constraints sortingStrategy with
        | .ok sorted => modifyNode node fun n => { n with ports := sorted }
        | .error msg =>
          if msg == undefinedSideMessage then Elk.Core.throwIllegalState msg
          else throw (IO.userError JavaSort.contractViolationError)
      cachePortSides node
  monitor.done

/-- The `PortListSorter` processor. -/
def processor : LayeredProcessor := { name := "PortListSorter", process := process }

end PortListSorter

builtin_initialize registerPortListSorter : Unit ←
  IntermediateProcessorStrategy.register .portListSorter PortListSorter.processor

end Elk.Alg.Layered.Intermediate
