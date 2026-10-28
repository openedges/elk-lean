import Elk.Alg.Layered.LayeredPhases
import Elk.Alg.Layered.Options.LayeredOptions
import Elk.Alg.Layered.Intermediate.Loops.Ops
/-!
# `org.eclipse.elk.alg.layered.intermediate.SelfLoopPortRestorer`

Port of elk-rs `intermediate/self_loop_port_restorer.rs` (which inlines Java's
`loops/ordering/PortSideAssigner` and `loops/ordering/PortRestorer`). For every normal node (in
layer order) with a `SelfLoopHolder`: if self-loop ports were hidden, assigns sides to them
(`FREE`/`UNDEFINED` original port constraints, per `EDGE_ROUTING_SELF_LOOP_DISTRIBUTION`),
computes the self loop types and puts the hidden ports back into the port list, ordered by
`EDGE_ROUTING_SELF_LOOP_ORDERING`; otherwise it only computes the self loop types.

Collections: the Rust `TargetAreas` map `(PortSide, PortSideArea) → Vec` is an array indexed by
`side ordinal * 3 + area ordinal` (only looked up by key; un-hiding visits every entry, which is
order independent); `LoopsByType` keeps the loops of each type in hyper loop order.

Rust/Java differences:
- one-sided loops sort their ports by Java's `SelfLoopPort.getSLNetFlow()` (incoming minus outgoing
  self-loop edges, ELK Java is the result reference); elk-rs sorts by `LPort.getNetFlow()`, which
  after `SelfLoopPreProcessor` detached the self loops only counts the port's other edges (Rust
  followed in the rest of this list);
- with `FIXED_ORDER`/`FIXED_RATIO`/`FIXED_POS` original constraints (unreachable: such ports are
  never hidden) Rust still computes the types and restores the ports (Java does nothing).
-/
namespace Elk.Alg.Layered.Intermediate

open Elk.Graph Elk.Core Elk.Core.Alg Elk.Core.Util Elk.Core.Options Elk.Alg.Layered Elk.Alg.Layered.Graph
  Elk.Alg.Layered.Options Elk.Alg.Layered.Intermediate.Loops LayeredM

namespace SelfLoopPortRestorer

/-- `PortSideArea`: the part of a node side a restored port is placed in. -/
inductive PortSideArea where
  | start | middle | «end»
  deriving BEq, Repr, Inhabited

/-- Ordinal of a `PortSideArea`. -/
def PortSideArea.ordinal : PortSideArea → Nat
  | .start => 0
  | .middle => 1
  | .«end» => 2

/-- `AddMode`: whether ports are prepended or appended to a target area. -/
inductive AddMode where
  | prepend | append
  deriving BEq, Repr, Inhabited

/-- `Target`: the side(s) a hyper loop is assigned to by the `EQUALLY` distribution. -/
structure Target where
  firstSide : PortSide
  secondSide : PortSide
  deriving BEq, Repr, Inhabited

/-- `Target.is_corner_target()`. -/
def Target.isCornerTarget (t : Target) : Bool := t.firstSide != t.secondSide

/-- `ASSIGNMENT_TARGETS`: the targets of the `EQUALLY` distribution, used round robin. -/
def ASSIGNMENT_TARGETS : Array Target := #[
  ⟨.north, .north⟩, ⟨.south, .south⟩, ⟨.east, .east⟩, ⟨.west, .west⟩,
  ⟨.west, .north⟩, ⟨.north, .east⟩, ⟨.south, .west⟩, ⟨.east, .south⟩]

/-- `TargetAreas`: the ports to restore per `(side, area)`. -/
abbrev TargetAreas := Array (Array SelfLoopPortId)

/-- Index of `(side, area)` in `TargetAreas`. -/
@[inline] def areaIndex (side : PortSide) (area : PortSideArea) : Nat := ElkEnum.ordinal side * 3 + area.ordinal

/-- `init_target_areas()`: one empty list per `(side, area)`. -/
def initTargetAreas : TargetAreas := Array.replicate (PORT_SIDE_COUNT * 3) #[]

/-- `LoopsByType`: the hyper loops of each `SelfLoopType` (by ordinal), in hyper loop order. -/
abbrev LoopsByType := Array (Array SelfHyperLoopId)

-- Port side assignment (Java `PortSideAssigner`) -------------------------------------------

/-- `set_hidden_port_side(slPort, side)`: `LPort.setSide(side)` on hidden ports only. -/
def setHiddenPortSide (h : SelfLoopHolder) (p : SelfLoopPortId) (side : PortSide) : LayeredM Unit := do
  let slPort := h.slPort p
  if slPort.isHidden then modifyPort slPort.lPort (·.setSide side)

/-- `hidden_ports_of_loop(slLoop)`. -/
def hiddenPortsOfLoop (h : SelfLoopHolder) (l : SelfHyperLoopId) : Array SelfLoopPortId :=
  (h.slHyperLoop l).slPorts.filter fun p => (h.slPort p).isHidden

/-- `assign_to_north_side(loops)`. -/
def assignToNorthSide (h : SelfLoopHolder) : LayeredM Unit := do
  for l in h.hyperLoopIds do
    for p in hiddenPortsOfLoop h l do
      setHiddenPortSide h p .north

/-- `assign_to_north_or_south_side(loops)`: each loop's hidden ports go to the side with fewer
hidden ports so far (north on ties). -/
def assignToNorthOrSouthSide (h : SelfLoopHolder) : LayeredM Unit := do
  let mut northPorts := 0
  let mut southPorts := 0
  for l in h.hyperLoopIds do
    let hidden := hiddenPortsOfLoop h l
    if hidden.isEmpty then continue
    let mut targetSide : PortSide := .north
    if northPorts ≤ southPorts then
      northPorts := northPorts + hidden.size
    else
      southPorts := southPorts + hidden.size
      targetSide := .south
    for p in hidden do
      setHiddenPortSide h p targetSide

/-- `assign_to_target(slLoop, target)`: for corner targets the ports are first sorted (stably) by
`LPort` net flow; the first half goes to `firstSide`, the rest to `secondSide`. -/
def assignToTarget (h : SelfLoopHolder) (l : SelfHyperLoopId) (target : Target) : LayeredM Unit := do
  let mut ports := (h.slHyperLoop l).slPorts
  if target.isCornerTarget then
    let flows ← withArena fun a => ports.map fun p => (p, SelfLoopHolder.portNetFlow a h p)
    ports := (stableSortByKey flows (·.2)).map (·.1)
  let secondHalfStartIndex := ports.size / 2
  for h' : i in [0:ports.size] do
    let side := if i < secondHalfStartIndex then target.firstSide else target.secondSide
    setHiddenPortSide h ports[i] side

/-- `assign_to_all_sides(loops)`: loops sorted (stably) by descending port count get the
`ASSIGNMENT_TARGETS` round robin. -/
def assignToAllSides (h : SelfLoopHolder) : LayeredM Unit := do
  let sorted := stableSort h.hyperLoopIds fun a b =>
    compare (h.slHyperLoop b).slPorts.size (h.slHyperLoop a).slPorts.size
  for h' : i in [0:sorted.size] do
    assignToTarget h sorted[i] ASSIGNMENT_TARGETS[i % ASSIGNMENT_TARGETS.size]!

/-- `assign_hidden_port_sides(holder)` (Java `PortSideAssigner.assignPortSides`). -/
def assignHiddenPortSides (h : SelfLoopHolder) : LayeredM Unit := do
  let distribution := ((← getNode h.lNode).props.get LayeredOptions.EDGE_ROUTING_SELF_LOOP_DISTRIBUTION).getD .north
  match distribution with
  | .north => assignToNorthSide h
  | .northSouth => assignToNorthOrSouthSide h
  | .equally => assignToAllSides h

-- Port restoration (Java `PortRestorer`) -----------------------------------------------------

/-- `compute_self_loop_types(holder)`: `computePortsPerSide` on every hyper loop (stored back). -/
def computeSelfLoopTypes (n : LNodeId) : LayeredM Unit := do
  let some h ← SelfLoopHolder.get? n | return
  let h ← withArena fun a => h.hyperLoopIds.foldl (fun h l => SelfLoopHolder.computePortsPerSide a h l) h
  SelfLoopHolder.store n (some h)

/-- `add_to_target_area_from_ports(ports, side, area, mode, areas)`: the hidden ports, reversed,
prepended or appended to the area. -/
def addToTargetAreaFromPorts (h : SelfLoopHolder) (ports : Array SelfLoopPortId) (side : PortSide)
    (area : PortSideArea) (mode : AddMode) (areas : TargetAreas) : TargetAreas :=
  let hidden := (ports.filter fun p => (h.slPort p).isHidden).reverse
  areas.modify (areaIndex side area) fun xs => if mode == .prepend then hidden ++ xs else xs ++ hidden

/-- `add_to_target_area_loop(slLoop, side, area, mode, areas)`: the loop's ports on `side`. -/
def addToTargetAreaLoop (h : SelfLoopHolder) (l : SelfHyperLoopId) (side : PortSide)
    (area : PortSideArea) (mode : AddMode) (areas : TargetAreas) : TargetAreas :=
  addToTargetAreaFromPorts h ((h.slHyperLoop l).portsOnSide side) side area mode areas

/-- `gather_self_loops_by_type(holder)`: loops without type are dropped. -/
def gatherSelfLoopsByType (h : SelfLoopHolder) : LoopsByType := Id.run do
  let mut byType : LoopsByType := Array.replicate (ElkEnum.count (α := SelfLoopType)) #[]
  for l in h.hyperLoopIds do
    if let some t := (h.slHyperLoop l).selfLoopType then
      byType := byType.modify (ElkEnum.ordinal t) (·.push l)
  return byType

/-- `compute_port_list_split_index(sortedPorts)` (the second pass deliberately repeats the
`> 0` test of Java). `flows` are the net flows of the sorted ports. -/
def computePortListSplitIndex (flows : Array Int) : Nat := Id.run do
  if flows.isEmpty then return 0
  let mut positiveNetFlowIndex := 0
  while positiveNetFlowIndex < flows.size do
    if flows[positiveNetFlowIndex]! > 0 then break
    positiveNetFlowIndex := positiveNetFlowIndex + 1
  if positiveNetFlowIndex > 0 && positiveNetFlowIndex < flows.size - 1 then
    return positiveNetFlowIndex
  let mut nonNegativeNetFlowIndex := 0
  while nonNegativeNetFlowIndex < flows.size do
    if flows[nonNegativeNetFlowIndex]! > 0 then break
    nonNegativeNetFlowIndex := nonNegativeNetFlowIndex + 1
  if nonNegativeNetFlowIndex > 0 && positiveNetFlowIndex < flows.size - 1 then
    return nonNegativeNetFlowIndex
  return flows.size / 2

/-- `process_one_side_loops(ordering, loopsByType, areas)`: reversed for `REVERSE_STACKED`; each
loop's ports (stably sorted by self-loop net flow, Java `getSLNetFlow`) go to the middle of the side of its first port —
appended (`SEQUENCED`) or split around the split index (prepend / append, stacked). -/
def processOneSideLoops (a : LGraphArena) (h : SelfLoopHolder) (ordering : SelfLoopOrderingStrategy)
    (loopsByType : LoopsByType) (areas : TargetAreas) : TargetAreas := Id.run do
  let mut loops := loopsByType[ElkEnum.ordinal SelfLoopType.oneSide]!
  if ordering == .reverseStacked then loops := loops.reverse
  let mut areas := areas
  for l in loops do
    let ports := (h.slHyperLoop l).slPorts
    let side := match ports[0]? with
      | some p => SelfLoopHolder.portSide a h p
      | none => .undefined
    if side == .undefined then continue
    -- Java sorts by `SelfLoopPort.getSLNetFlow()` (self-loop edges in - out); elk-rs reads the
    -- `LPort` net flow, which no longer counts the hidden self loops
    let sorted := stableSortByKey (ports.map fun p => (p, (h.slPort p).slNetFlow)) (·.2)
    let sortedPorts := sorted.map (·.1)
    match ordering with
    | .sequenced =>
      areas := addToTargetAreaFromPorts h sortedPorts side .middle .append areas
    | .stacked | .reverseStacked =>
      let splitIndex := computePortListSplitIndex (sorted.map (·.2))
      areas := addToTargetAreaFromPorts h (sortedPorts.extract 0 splitIndex) side .middle .prepend areas
      areas := addToTargetAreaFromPorts h (sortedPorts.extract splitIndex sortedPorts.size) side .middle .append areas
  return areas

/-- `sorted_two_side_loop_port_sides(slLoop)`: the loop's two sides in ordinal order, except that
`[NORTH, WEST]` becomes `[WEST, NORTH]`; `none` unless there are exactly two sides. -/
def sortedTwoSideLoopPortSides (a : LGraphArena) (h : SelfLoopHolder) (l : SelfHyperLoopId) : Option (PortSide × PortSide) :=
  let sides := SelfLoopHolder.loopPortSides a h l
  if sides.size != 2 then none
  else
    let sides := stableSortByKey sides (ElkEnum.ordinal ·)
    if sides[0]! == .north && sides[1]! == .west then some (.west, .north)
    else some (sides[0]!, sides[1]!)

/-- `process_two_side_corner_loops` / `process_two_side_opposing_loops`: start side → END
(prepend), target side → START (append). -/
def processTwoSideLoops (a : LGraphArena) (h : SelfLoopHolder) (loops : Array SelfHyperLoopId) (areas : TargetAreas) :
    TargetAreas := Id.run do
  let mut areas := areas
  for l in loops do
    let some (startSide, targetSide) := sortedTwoSideLoopPortSides a h l | continue
    areas := addToTargetAreaLoop h l startSide .«end» .prepend areas
    areas := addToTargetAreaLoop h l targetSide .start .append areas
  return areas

/-- `determine_loop_constellation(slLoop)`: `(start, middle, end)` sides of a three-sided loop,
named by the missing side. -/
def determineLoopConstellation (a : LGraphArena) (h : SelfLoopHolder) (l : SelfHyperLoopId) :
    Option (PortSide × PortSide × PortSide) :=
  let sides := SelfLoopHolder.loopPortSides a h l
  if !sides.contains .north then some (.east, .south, .west)
  else if !sides.contains .east then some (.south, .west, .north)
  else if !sides.contains .south then some (.west, .north, .east)
  else if !sides.contains .west then some (.north, .east, .south)
  else none

/-- `process_three_side_loops`: start → END (prepend), middle → MIDDLE (append), end → START (append). -/
def processThreeSideLoops (a : LGraphArena) (h : SelfLoopHolder) (loops : Array SelfHyperLoopId) (areas : TargetAreas) :
    TargetAreas := Id.run do
  let mut areas := areas
  for l in loops do
    let some (startSide, middleSide, endSide) := determineLoopConstellation a h l | continue
    areas := addToTargetAreaLoop h l startSide .«end» .prepend areas
    areas := addToTargetAreaLoop h l middleSide .middle .append areas
    areas := addToTargetAreaLoop h l endSide .start .append areas
  return areas

/-- `process_four_side_loops`: every side of the loop (in port order) → MIDDLE (append). -/
def processFourSideLoops (a : LGraphArena) (h : SelfLoopHolder) (loops : Array SelfHyperLoopId) (areas : TargetAreas) :
    TargetAreas := Id.run do
  let mut areas := areas
  for l in loops do
    for side in SelfLoopHolder.loopPortSides a h l do
      areas := addToTargetAreaLoop h l side .middle .append areas
  return areas

/-- `north_south_port_connection_sides(lPort)`: the sides of the `PORT_DUMMY`'s ports that
originate from `lPort` and have connected edges. -/
def northSouthPortConnectionSides (a : LGraphArena) (p : LPortId) : EnumSet PortSide := Id.run do
  let mut sides : EnumSet PortSide := EnumSet.empty
  let some dummy := (a.port p).internal.portDummy | return sides
  for dp in (a.node dummy).ports do
    let dummyPort := a.port dp
    match dummyPort.internal.origin with
    | some (.lPort origin) =>
      if origin != p then continue
      if !dummyPort.connectedEdges.isEmpty then sides := sides.insert dummyPort.side
    | _ => continue
  return sides

/-- `add_all(areas, side, area, node)`: `LPort.setNode(node)` for every port of the area. -/
def addAll (h : SelfLoopHolder) (areas : TargetAreas) (side : PortSide) (area : PortSideArea) : LayeredM Unit := do
  for p in areas[areaIndex side area]! do
    setPortNode (h.lPortOf p) (some h.lNode)

/-- `add_all_that(ports, fromIndex, condition, node)`: appends the old ports from `fromIndex` on
while `condition` holds (directly to the port list); returns the index of the first rejected port. -/
def addAllThat (n : LNodeId) (ports : Array LPortId) (fromIndex : Nat) (condition : LGraphArena → LPortId → Bool) :
    LayeredM Nat := do
  for h : i in [fromIndex:ports.size] do
    let p := ports[i]
    if ← withArena (condition · p) then
      modifyNode n fun x => { x with ports := x.ports.push p }
    else
      return i
  return ports.size

/-- `restore_ports_to_node(holder, areas)`: rebuilds the port list side by side (north, east,
south, west), interleaving the target areas with the old (visible) ports; old ports that do not
fit the sequence are appended at the end. -/
def restorePortsToNode (h : SelfLoopHolder) (areas : TargetAreas) : LayeredM Unit := do
  let n := h.lNode
  let oldPorts := (← getNode n).ports
  modifyNode n fun x => { x with ports := #[] }
  let sideIs (side : PortSide) := fun (a : LGraphArena) (p : LPortId) => (a.port p).side == side
  let mut next := 0
  addAll h areas .north .start
  next ← addAllThat n oldPorts next fun a p =>
    sideIs .north a p && (northSouthPortConnectionSides a p).contains .west
  addAll h areas .north .middle
  next ← addAllThat n oldPorts next (sideIs .north)
  addAll h areas .north .«end»
  addAll h areas .east .start
  addAll h areas .east .middle
  next ← addAllThat n oldPorts next (sideIs .east)
  addAll h areas .east .«end»
  addAll h areas .south .start
  next ← addAllThat n oldPorts next fun a p =>
    sideIs .south a p && (northSouthPortConnectionSides a p).contains .east
  addAll h areas .south .middle
  next ← addAllThat n oldPorts next (sideIs .south)
  addAll h areas .south .«end»
  addAll h areas .west .start
  next ← addAllThat n oldPorts next (sideIs .west)
  addAll h areas .west .middle
  addAll h areas .west .«end»
  if next < oldPorts.size then
    modifyNode n fun x => { x with ports := x.ports ++ oldPorts.extract next oldPorts.size }

/-- `restore_ports(holder)` (Java `PortRestorer.restorePorts`): fills the target areas (one-sided,
two-sided corner, three-sided, four-sided, two-sided opposing loops), rebuilds the port list and
un-hides the restored ports and the holder. -/
def restorePorts (n : LNodeId) : LayeredM Unit := do
  let some h ← SelfLoopHolder.get? n | return
  let loopsByType := gatherSelfLoopsByType h
  let ordering := ((← getNode n).props.get LayeredOptions.EDGE_ROUTING_SELF_LOOP_ORDERING).getD .stacked
  let byType (t : SelfLoopType) := loopsByType[ElkEnum.ordinal t]!
  let areas ← withArena fun a =>
    let areas := processOneSideLoops a h ordering loopsByType initTargetAreas
    let areas := processTwoSideLoops a h (byType .twoSidesCorner) areas
    let areas := processThreeSideLoops a h (byType .threeSides) areas
    let areas := processFourSideLoops a h (byType .fourSides) areas
    processTwoSideLoops a h (byType .twoSidesOpposing) areas
  restorePortsToNode h areas
  SelfLoopHolder.update n fun h =>
    let h := areas.foldl (fun h ports => ports.foldl (fun h p => h.modifySLPort p fun x => { x with isHidden := false }) h) h
    { h with arePortsHidden := false }

/-- `process_node(holder)`. -/
def processNode (n : LNodeId) : LayeredM Unit := do
  let some h ← SelfLoopHolder.get? n | return
  if !h.arePortsHidden then
    computeSelfLoopTypes n
    return
  match (← getNode n).internal.originalPortConstraints.getD .undefined with
  | .undefined | .free =>
    assignHiddenPortSides h
    computeSelfLoopTypes n
    restorePorts n
  | _ =>
    -- FIXED_SIDE; Rust also takes this path for the (unreachable) order-fixed constraints
    computeSelfLoopTypes n
    restorePorts n

/-- `process(graph, monitor)` body: the normal nodes of all layers with a holder, in order. -/
def run (graph : LGraphId) : LayeredM Unit := do
  for layer in (← getGraph graph).layers do
    for n in (← getLayer layer).nodes do
      let nd ← getNode n
      if nd.type == .normal && nd.internal.selfLoopHolder.isSome then
        processNode n

/-- The `SelfLoopPortRestorer` intermediate processor. -/
def processor : LayeredProcessor :=
  { name := "SelfLoopPortRestorer"
    process := fun graph monitor => do
      let _ ← monitor.begin "Self-Loop ordering" 1.0
      run graph
      monitor.done }

end SelfLoopPortRestorer

builtin_initialize registerSelfLoopPortRestorer : Unit ←
  IntermediateProcessorStrategy.register .selfLoopPortRestorer SelfLoopPortRestorer.processor

end Elk.Alg.Layered.Intermediate
