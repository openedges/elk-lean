import Elk.Alg.Layered.Intermediate.Loops.Ops
import Elk.Core.Util.Sort
/-!
# `org.eclipse.elk.alg.layered.intermediate.loops.routing.RoutingDirector`

Port of elk-rs `intermediate/loops/routing/routing_director.rs`: determines for every hyper loop
of a node the leftmost and rightmost port (the loop is routed clockwise from the leftmost to the
rightmost port) and the port sides the loop occupies.

`determineLoopRoutes(holder)`:
1. `assign_port_ids`: `LPort.id := index` in the node's port list (Rust comment: Java assigns ids
   by list position; the list is already sorted by side and position);
2. `compute_port_penalties`: cumulative penalties along the port list (1 for an unconnected port,
   3 for a connected one; the self loops are hidden at this point);
3. per hyper loop (holder order): `sort_ports_by_id`, `compute_ports_per_side`, the route by loop
   type, `compute_occupied_port_sides` (clockwise from the leftmost to the rightmost port side).

Rust iterator semantics reproduced: `min_by_key` returns the **first** minimum, `max_by_key` the
**last** maximum (`firstMinByKey?`/`lastMaxByKey?`). `occupied_port_sides: HashSet` is an
`EnumSet PortSide` (only `contains` and, for one-sided loops, the single element are read).

Rust/Java difference (Rust followed): opposing loops sort their two sides by the clockwise rank
`NORTH < EAST < SOUTH < WEST` (Rust: "patched Java reference" with `MultimapBuilder.enumKeys`).
-/
namespace Elk.Alg.Layered.Intermediate.Loops.Routing

open Elk.Graph Elk.Core.Math Elk.Core.Options Elk.Core.Util Elk.Alg.Layered.Graph
  Elk.Alg.Layered.Intermediate.Loops LayeredM

namespace RoutingDirector

/-- `UNCONNECTED_PORT_PENALTY`. -/
def UNCONNECTED_PORT_PENALTY : Int := 1
/-- `CONNECTED_PORT_PENALTY`. -/
def CONNECTED_PORT_PENALTY : Int := 3

/-- Rust `Iterator::min_by_key`: the first element with the minimal key. -/
def firstMinByKey? {α : Type} (xs : Array α) (key : α → Int) : Option α := Id.run do
  let mut best : Option (α × Int) := none
  for x in xs do
    let k := key x
    match best with
    | none => best := some (x, k)
    | some (_, bk) => if k < bk then best := some (x, k)
  return best.map (·.1)

/-- Rust `Iterator::max_by_key`: the last element with the maximal key. -/
def lastMaxByKey? {α : Type} (xs : Array α) (key : α → Int) : Option α := Id.run do
  let mut best : Option (α × Int) := none
  for x in xs do
    let k := key x
    match best with
    | none => best := some (x, k)
    | some (_, bk) => if k ≥ bk then best := some (x, k)
  return best.map (·.1)

/-- `assign_port_ids(holder)`: `LPort.id := index` for every port of the node (list order). -/
def assignPortIds (n : LNodeId) : LayeredM Unit := do
  let ports := (← getNode n).ports
  for h : i in [0:ports.size] do
    modifyPort ports[i] fun p => { p with id := (i : Int) }

/-- `compute_port_penalties(holder)`: per port id the cumulative penalty (in id order). Falls back
to the cumulative penalties in list order when the ids are not exactly `0 … n-1`. -/
def computePortPenalties (a : LGraphArena) (n : LNodeId) : Array Int := Id.run do
  let ports := (a.node n).ports
  let mut byId : Array (Nat × Int) := #[]
  let mut fallback : Array Int := Array.replicate ports.size 0
  let mut fallbackSum : Int := 0
  for h : index in [0:ports.size] do
    let port := a.port ports[index]
    let penalty :=
      if port.incomingEdges.isEmpty && port.outgoingEdges.isEmpty then UNCONNECTED_PORT_PENALTY
      else CONNECTED_PORT_PENALTY
    fallbackSum := fallbackSum + penalty
    fallback := fallback.set! index fallbackSum
    if port.id ≥ 0 && port.id.toNat < ports.size then
      byId := byId.push (port.id.toNat, penalty)
  if byId.size != ports.size then return fallback
  let sortedById := stableSortByKey byId (fun x => (x.1 : Int))
  let mut mismatch := false
  for h : expected in [0:sortedById.size] do
    if sortedById[expected].1 != expected then
      mismatch := true
      break
  if mismatch then return fallback
  let mut penalties : Array Int := Array.replicate ports.size 0
  let mut penaltySum : Int := 0
  for (id, penalty) in sortedById do
    penaltySum := penaltySum + penalty
    penalties := penalties.set! id penaltySum
  return penalties

/-- `compute_edge_penalty(holder, penalties, leftmost, rightmost)`: the penalty of routing
clockwise from `leftmost` to `rightmost` (sum of the penalties of the ports strictly between
them, wrapping around the port list); `0` for ids outside the port list. -/
def computeEdgePenalty (portCount : Nat) (penalties : Array Int) (leftmostPortId rightmostPortId : Int) : Int :=
  if portCount == 0 || penalties.isEmpty then 0
  else if leftmostPortId < 0 || rightmostPortId < 0 then 0
  else
    let leftId := leftmostPortId.toNat
    let rightId := rightmostPortId.toNat
    if leftId ≥ portCount || rightId ≥ portCount then 0
    else
      let leftOfRight := if rightId == 0 then portCount - 1 else rightId - 1
      if leftId ≤ leftOfRight then penalties[leftOfRight]! - penalties[leftId]!
      else penalties[portCount - 1]! - penalties[leftId]! + penalties[leftOfRight]!

/-- The facts of the arena the route computation reads: the side and id of each self-loop port's
`LPort`, the node's port count and the port penalties. -/
structure RouteContext where
  /-- `sl_port_side(slPort)`. -/
  sideOf : SelfLoopPortId → PortSide
  /-- `SelfHyperLoop::port_id(slPort)`. -/
  idOf : SelfLoopPortId → Int
  /-- `l_node.ports().len()`. -/
  portCount : Nat
  /-- `compute_port_penalties(holder)`. -/
  penalties : Array Int

namespace RouteContext

/-- `compute_edge_penalty` for two self-loop ports. -/
def edgePenalty (c : RouteContext) (leftmost rightmost : SelfLoopPortId) : Int :=
  computeEdgePenalty c.portCount c.penalties (c.idOf leftmost) (c.idOf rightmost)

/-- `lowest_port_on_side(slLoop, side)`. -/
def lowestPortOnSide (c : RouteContext) (l : SelfHyperLoop) (side : PortSide) : Option SelfLoopPortId :=
  firstMinByKey? (l.portsOnSide side) c.idOf

/-- `highest_port_on_side(slLoop, side)`. -/
def highestPortOnSide (c : RouteContext) (l : SelfHyperLoop) (side : PortSide) : Option SelfLoopPortId :=
  lastMaxByKey? (l.portsOnSide side) c.idOf

/-- `loop_sides(slLoop)`: the distinct defined sides of the loop's ports, in port order. -/
def loopSides (c : RouteContext) (l : SelfHyperLoop) : Array PortSide := Id.run do
  let mut sides : Array PortSide := #[]
  for p in l.slPorts do
    let side := c.sideOf p
    if side != .undefined && !sides.contains side then sides := sides.push side
  return sides

/-- `determine_general_route(slLoop)`: lowest and highest port id among all ports. -/
def determineGeneralRoute (c : RouteContext) (l : SelfHyperLoop) : SelfHyperLoop :=
  { l with leftmostPort := firstMinByKey? l.slPorts c.idOf, rightmostPort := lastMaxByKey? l.slPorts c.idOf }

/-- `assign_leftmost_rightmost_ports(slLoop, leftSide, rightSide)`. -/
def assignLeftmostRightmostPorts (c : RouteContext) (l : SelfHyperLoop) (leftSide rightSide : PortSide) : SelfHyperLoop :=
  { l with leftmostPort := c.lowestPortOnSide l leftSide, rightmostPort := c.highestPortOnSide l rightSide }

/-- `determine_one_side_route(slLoop)`: lowest and highest port id on the first port's side. -/
def determineOneSideRoute (c : RouteContext) (l : SelfHyperLoop) : SelfHyperLoop :=
  let side := match l.slPorts[0]? with
    | some p => c.sideOf p
    | none => .undefined
  if side == .undefined then { l with leftmostPort := none, rightmostPort := none }
  else
    let sidePorts := l.portsOnSide side
    { l with leftmostPort := firstMinByKey? sidePorts c.idOf, rightmostPort := lastMaxByKey? sidePorts c.idOf }

/-- `determine_two_side_corner_route(slLoop)`: from the lowest port on the counter-clockwise side
to the highest port on the clockwise side. -/
def determineTwoSideCornerRoute (c : RouteContext) (l : SelfHyperLoop) : SelfHyperLoop :=
  let sides := c.loopSides l
  if sides.size != 2 then c.determineGeneralRoute l
  else
    let (leftSide, rightSide) :=
      if sides[0]!.right == sides[1]! then (sides[0]!, sides[1]!)
      else if sides[1]!.right == sides[0]! then (sides[1]!, sides[0]!)
      else (sides[0]!, sides[1]!)
    c.assignLeftmostRightmostPorts l leftSide rightSide

/-- `opposing_side_order_rank(side)`: `NORTH < EAST < SOUTH < WEST < UNDEFINED`. -/
def opposingSideOrderRank : PortSide → Int
  | .north => 0
  | .east => 1
  | .south => 2
  | .west => 3
  | .undefined => 4

/-- `determine_two_side_opposing_route(slLoop, holder, penalties)`: of the two ways around the
node (lowest port of the first side to highest port of the second, or the reverse) the one with
the smaller edge penalty; the first wins ties (`<=`). -/
def determineTwoSideOpposingRoute (c : RouteContext) (l : SelfHyperLoop) : SelfHyperLoop :=
  let sides := c.loopSides l
  if sides.size != 2 then c.determineGeneralRoute l
  else
    let sides := stableSortByKey sides opposingSideOrderRank
    match c.lowestPortOnSide l sides[0]!, c.highestPortOnSide l sides[1]!,
        c.lowestPortOnSide l sides[1]!, c.highestPortOnSide l sides[0]! with
    | some option1Left, some option1Right, some option2Left, some option2Right =>
      let option1Penalty := c.edgePenalty option1Left option1Right
      let option2Penalty := c.edgePenalty option2Left option2Right
      if option1Penalty ≤ option2Penalty then
        { l with leftmostPort := some option1Left, rightmostPort := some option1Right }
      else
        { l with leftmostPort := some option2Left, rightmostPort := some option2Right }
    | _, _, _, _ => c.determineGeneralRoute l

/-- `determine_three_side_route(slLoop)`: named by the missing side (first of N, E, S, W not
occupied). -/
def determineThreeSideRoute (c : RouteContext) (l : SelfHyperLoop) : SelfHyperLoop :=
  let sides := c.loopSides l
  if sides.size != 3 then c.determineGeneralRoute l
  else
    let missing := #[PortSide.north, .east, .south, .west].find? (!sides.contains ·)
    match missing with
    | none => c.determineGeneralRoute l
    | some missingSide =>
      let (leftSide, rightSide) : PortSide × PortSide := match missingSide with
        | .north => (.east, .west)
        | .east => (.south, .north)
        | .south => (.west, .east)
        | .west => (.north, .south)
        | .undefined => (.north, .south)
      c.assignLeftmostRightmostPorts l leftSide rightSide

/-- `determine_four_side_route(slLoop, holder, penalties)`: the loop is not routed between the
consecutive (by port id, wrapping) port pair with the highest penalty (first found wins ties);
leftmost = that pair's right port, rightmost = its left port. -/
def determineFourSideRoute (c : RouteContext) (l : SelfHyperLoop) : SelfHyperLoop := Id.run do
  let sortedPorts := l.slPorts
  if sortedPorts.size < 2 then return c.determineGeneralRoute l
  let mut worstLeftPort := sortedPorts[sortedPorts.size - 1]!
  let mut worstRightPort := sortedPorts[0]!
  let mut worstPenalty := c.edgePenalty worstLeftPort worstRightPort
  for rightIndex in [1:sortedPorts.size] do
    let currLeftPort := sortedPorts[rightIndex - 1]!
    let currRightPort := sortedPorts[rightIndex]!
    let currPenalty := c.edgePenalty currLeftPort currRightPort
    if currPenalty > worstPenalty then
      worstLeftPort := currLeftPort
      worstRightPort := currRightPort
      worstPenalty := currPenalty
  return { l with leftmostPort := some worstRightPort, rightmostPort := some worstLeftPort }

/-- `determine_loop_route(slLoop, holder, penalties)`: by self loop type (`none` → general). -/
def determineLoopRoute (c : RouteContext) (l : SelfHyperLoop) : SelfHyperLoop :=
  match l.selfLoopType with
  | some .oneSide => c.determineOneSideRoute l
  | some .twoSidesCorner => c.determineTwoSideCornerRoute l
  | some .twoSidesOpposing => c.determineTwoSideOpposingRoute l
  | some .threeSides => c.determineThreeSideRoute l
  | some .fourSides => c.determineFourSideRoute l
  | none => c.determineGeneralRoute l

/-- `compute_occupied_port_sides(slLoop)`: the sides from the leftmost to the rightmost port's
side, clockwise (empty when either is missing or `UNDEFINED`). -/
def computeOccupiedPortSides (c : RouteContext) (l : SelfHyperLoop) : SelfHyperLoop := Id.run do
  let leftSide := match l.leftmostPort with | some p => c.sideOf p | none => .undefined
  let rightSide := match l.rightmostPort with | some p => c.sideOf p | none => .undefined
  let mut sides : EnumSet PortSide := EnumSet.empty
  if leftSide == .undefined || rightSide == .undefined then
    return { l with occupiedPortSides := sides }
  let mut current := leftSide
  for _ in [0:4] do
    sides := sides.insert current
    if current == rightSide then break
    current := current.right
  return { l with occupiedPortSides := sides }

/-- The per-loop body of `determine_loop_routes`: `sort_ports_by_id`, `compute_ports_per_side`,
`determine_loop_route`, `compute_occupied_port_sides`. -/
def processLoop (c : RouteContext) (l : SelfHyperLoop) : SelfHyperLoop :=
  let l := l.sortPortsById c.idOf
  let l := l.computePortsPerSide c.sideOf
  c.computeOccupiedPortSides (c.determineLoopRoute l)

end RouteContext

/-- The `RouteContext` of a holder (current `LPort` sides and ids, port penalties). -/
def routeContext (a : LGraphArena) (h : SelfLoopHolder) : RouteContext :=
  { sideOf := SelfLoopHolder.portSide a h
    idOf := SelfLoopHolder.portId a h
    portCount := (a.node h.lNode).ports.size
    penalties := computePortPenalties a h.lNode }

/-- `determine_loop_routes(holder)` (Java `determineLoopRoutes`) for the holder stored on `n`
(no-op without holder). -/
def determineLoopRoutes (n : LNodeId) : LayeredM Unit := do
  let some h ← SelfLoopHolder.get? n | return
  assignPortIds h.lNode
  let loops ← withArena fun a =>
    let c := routeContext a h
    h.slHyperLoops.map c.processLoop
  SelfLoopHolder.update n fun h => { h with slHyperLoops := loops }

end RoutingDirector

end Elk.Alg.Layered.Intermediate.Loops.Routing
