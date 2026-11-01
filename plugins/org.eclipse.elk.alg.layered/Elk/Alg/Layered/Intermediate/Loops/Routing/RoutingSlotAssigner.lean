import Elk.Alg.Layered.Intermediate.Loops.Routing.RoutingDirector
import Elk.Alg.Layered.P5Edges.Orthogonal.OrthogonalRoutingGenerator
/-!
# `org.eclipse.elk.alg.layered.intermediate.loops.routing.RoutingSlotAssigner`

Port of elk-rs `intermediate/loops/routing/routing_slot_assigner.rs`: assigns every hyper loop a
routing slot on each side it occupies such that loop "trunks" cross as little as possible and
overlapping labels on the same side do not share a slot.

`assignRoutingSlots(holder, random)`:
1. clears the routing slots; collects the port count and the `[min, max]` port id range per side;
2. numbers the loops with labels (`label_id_by_loop`) and computes the symmetric label crossing
   matrix (same northern/southern side and overlapping `x` ranges of the label blocks — the block
   positions are still the defaults here, since Rust only places labels after routing);
3. builds the crossing graph: one `HyperEdgeSegment` (west to east) per loop in holder order, the
   port activity of every loop (ports from leftmost to rightmost, clockwise and wrapping) and a
   dependency for each loop pair `i < j` (weight = crossing difference, or two zero-weight
   dependencies for equal non-zero crossings / overlapping labels);
4. `OrthogonalRoutingGenerator.breakNonCriticalCycles` with the graph's random generator;
5. raw slots: reverse topological numbering from the sinks (FIFO); each loop gets its segment's
   slot on every occupied side;
6. `shift_towards_node` for NORTH, EAST, SOUTH, WEST: the loops occupying the side, stably sorted
   by raw slot, each take the lowest slot above the slots already used at the ports they are
   active at (within the side's port id range) and not used by a crossing label; without ports on
   the side the slot is the loop's rank;
7. `routingSlotCount`: per side the maximum slot plus one over all loops (unoccupied sides count
   slot `0`), written to the holder after the shift (Rust comment: Java updates the counts inline).

The Rust maps keyed by loop pointer (`HashMap<LoopKey, _>`) are arrays indexed by the hyper loop
index; they are only looked up by key, and the slot count is a maximum over all values. The
crossing graph is a `SegmentGraph` whose segment index is the loop index.
-/
namespace Elk.Alg.Layered.Intermediate.Loops.Routing

open Elk.Graph Elk.Core.Math Elk.Core.Options Elk.Core.Util Elk.Alg.Layered.Graph
  Elk.Alg.Layered.Intermediate.Loops Elk.Alg.Layered.P5Edges.Orthogonal
  Elk.Alg.Layered.P5Edges.Orthogonal.Direction LayeredM

namespace RoutingSlotAssigner

/-- `LoopRoutingState`: occupied sides and routing slots per `PortSide` ordinal. -/
structure LoopRoutingState where
  /-- `occupied_sides`. -/
  occupiedSides : Array Bool := Array.replicate PORT_SIDE_COUNT false
  /-- `routing_slots`. -/
  routingSlots : Array Int := Array.replicate PORT_SIDE_COUNT 0
  deriving Inhabited, Repr

/-- `SidePortRanges`: per `PortSide` ordinal the `(min, max)` port id of the side's ports. -/
abbrev SidePortRanges := Array (Option (Nat × Nat))

/-- `collect_port_side_ranges(holder)`: the node's port count and the id range of each side
(ports with negative id are skipped). -/
def collectPortSideRanges (a : LGraphArena) (n : LNodeId) : Nat × SidePortRanges := Id.run do
  let ports := (a.node n).ports
  let mut ranges : SidePortRanges := Array.replicate PORT_SIDE_COUNT none
  for p in ports do
    let port := a.port p
    if port.id < 0 then continue
    let portId := port.id.toNat
    let sideIdx := ElkEnum.ordinal port.side
    match ranges[sideIdx]! with
    | some (minIdx, maxIdx) => ranges := ranges.set! sideIdx (some (min minIdx portId, max maxIdx portId))
    | none => ranges := ranges.set! sideIdx (some (portId, portId))
  return (ports.size, ranges)

/-- `loop_label_span(slLoop)`: side and `[x, x + width]` of the loop's label block. -/
def loopLabelSpan (l : SelfHyperLoop) : Option (PortSide × Float × Float) :=
  l.slLabels.map fun lb => (lb.side, lb.position.x, lb.position.x + lb.size.x)

/-- `labels_overlap(slLoop1, slLoop2)`: same side (not EAST/WEST) and overlapping `x` ranges. -/
def labelsOverlap (l1 l2 : SelfHyperLoop) : Bool :=
  match loopLabelSpan l1, loopLabelSpan l2 with
  | some (side1, start1, end1), some (side2, start2, end2) =>
    if side1 != side2 || side1 == .east || side1 == .west then false
    else start1 ≤ end2 && end1 ≥ start2
  | _, _ => false

/-- `compute_label_crossing_matrix(loops)`: the label ids (loops with labels, in loop order) and
the symmetric crossing matrix. -/
def computeLabelCrossingMatrix (loops : Array SelfHyperLoop) : Array (Array Bool) × Array (Option Nat) := Id.run do
  let mut labelIdByLoop : Array (Option Nat) := #[]
  let mut labelId := 0
  for l in loops do
    -- Java parity: `getSLLabels() != null`, regardless of the number of labels
    if l.slLabels.isSome then
      labelIdByLoop := labelIdByLoop.push (some labelId)
      labelId := labelId + 1
    else
      labelIdByLoop := labelIdByLoop.push none
  let mut matrix : Array (Array Bool) := Array.replicate labelId (Array.replicate labelId false)
  for firstIdx in [0:loops.size] do
    let some label1 := labelIdByLoop[firstIdx]! | continue
    for secondIdx in [firstIdx + 1:loops.size] do
      let some label2 := labelIdByLoop[secondIdx]! | continue
      let overlap := labelsOverlap loops[firstIdx]! loops[secondIdx]!
      matrix := matrix.modify label1 (·.set! label2 overlap)
      matrix := matrix.modify label2 (·.set! label1 overlap)
  return (matrix, labelIdByLoop)

/-- `compute_loop_activity(port_count, loops)`: per loop the ports (by id) it passes clockwise
from its leftmost to its rightmost port, both included. Rust loops `while port_idx != target`
(stepping modulo the port count); the Lean loop is bounded by `portCount + 1` steps, which reaches
every target id inside the port list. -/
def computeLoopActivity (portCount : Nat) (loops : Array SelfHyperLoop) (idOf : SelfLoopPortId → Int) :
    Array (Array Bool) :=
  loops.map fun l => Id.run do
    let mut activity : Array Bool := Array.replicate portCount false
    let (some leftmost, some rightmost) := (l.leftmostPort, l.rightmostPort) | return activity
    let leftmostPortId := idOf leftmost
    let rightmostPortId := idOf rightmost
    if portCount > 0 && leftmostPortId ≥ 0 && rightmostPortId ≥ 0 then
      let mut portIdx : Int := leftmostPortId - 1
      let targetIdx := rightmostPortId
      for _ in [0:portCount + 1] do
        if portIdx == targetIdx then break
        portIdx := (portIdx + 1).emod (portCount : Int)
        activity := activity.set! portIdx.toNat true
    return activity

/-- `count_crossings(upper, lower, activity)`: ports of the upper loop the lower loop is active at. -/
def countCrossings (upper : SelfHyperLoop) (lowerActivity : Array Bool) (idOf : SelfLoopPortId → Int) : Int := Id.run do
  let mut crossings : Int := 0
  for p in upper.slPorts do
    let portId := idOf p
    if portId ≥ 0 && portId.toNat < lowerActivity.size && lowerActivity[portId.toNat]! then
      crossings := crossings + 1
  return crossings

/-- `labels_overlap_by_ids(slLoop1, slLoop2, matrix, labelIds)`. -/
def labelsOverlapByIds (i j : Nat) (matrix : Array (Array Bool)) (labelIdByLoop : Array (Option Nat)) : Bool :=
  match labelIdByLoop[i]!, labelIdByLoop[j]! with
  | some label1, some label2 => ((matrix[label1]?).bind (·[label2]?)).getD false
  | _, _ => false

/-- `create_dependencies(slLoop1, slLoop2, …)` for loops `i < j` (segments `i`, `j`). -/
def createDependencies (g : SegmentGraph) (loops : Array SelfHyperLoop) (i j : Nat) (activity : Array (Array Bool))
    (matrix : Array (Array Bool)) (labelIdByLoop : Array (Option Nat)) (idOf : SelfLoopPortId → Int) : SegmentGraph :=
  let firstAboveSecondCrossings := countCrossings loops[i]! activity[j]! idOf
  let secondAboveFirstCrossings := countCrossings loops[j]! activity[i]! idOf
  if firstAboveSecondCrossings < secondAboveFirstCrossings then
    (g.createAndAddRegular i j (secondAboveFirstCrossings - firstAboveSecondCrossings)).1
  else if secondAboveFirstCrossings < firstAboveSecondCrossings then
    (g.createAndAddRegular j i (firstAboveSecondCrossings - secondAboveFirstCrossings)).1
  else if firstAboveSecondCrossings != 0 || labelsOverlapByIds i j matrix labelIdByLoop then
    let g := (g.createAndAddRegular i j 0).1
    (g.createAndAddRegular j i 0).1
  else g

/-- `create_crossing_graph(loops, portCount, …)`: one west-to-east segment per loop and the
pairwise dependencies; also returns the loop activity. -/
def createCrossingGraph (loops : Array SelfHyperLoop) (portCount : Nat) (matrix : Array (Array Bool))
    (labelIdByLoop : Array (Option Nat)) (idOf : SelfLoopPortId → Int) : SegmentGraph × Array (Array Bool) := Id.run do
  let mut g : SegmentGraph := {}
  for _ in loops do
    g := (g.addSegment (HyperEdgeSegment.new .westToEast)).1
  let activity := computeLoopActivity portCount loops idOf
  for i in [0:loops.size - 1] do
    for j in [i + 1:loops.size] do
      g := createDependencies g loops i j activity matrix labelIdByLoop idOf
  return (g, activity)

/-- `assign_raw_routing_slots_to_segments(segments)`: in/out weights from the dependency lists,
sinks get slot `0`, then (FIFO from the sinks) every dependency source gets at least its
target's slot plus one and becomes a sink once all its outgoing dependencies are processed. -/
def assignRawRoutingSlotsToSegments (g : SegmentGraph) : SegmentGraph := Id.run do
  let mut g := g
  let mut sinks : Array Nat := #[]
  for i in [0:g.segments.size] do
    let seg := g.segment i
    let inWeight : Int := seg.incomingSegmentDependencies.size
    let outWeight : Int := seg.outgoingSegmentDependencies.size
    g := g.modifySegment i fun s => { s with inDepWeight := inWeight, outDepWeight := outWeight }
    if outWeight == 0 then
      g := g.modifySegment i fun s => { s with routingSlot := 0 }
      sinks := sinks.push i
  let mut head := 0
  -- a segment becomes a sink once (when its out weight reaches 0), so every queue entry is unique
  for _ in [0:g.segments.size + 1] do
    if head ≥ sinks.size then break
    let segment := sinks[head]!
    head := head + 1
    let nextRoutingSlot := (g.segment segment).routingSlot + 1
    for d in (g.segment segment).incomingSegmentDependencies do
      let some source := (g.dependency d).source | continue
      g := g.modifySegment source fun s =>
        { s with routingSlot := max s.routingSlot nextRoutingSlot, outDepWeight := s.outDepWeight - 1 }
      if (g.segment source).outDepWeight == 0 then sinks := sinks.push source
  return g

/-- `assign_raw_routing_slots_to_loops(loops, segments)`: each loop gets its segment's slot on
every occupied side (in the loop and in its routing state). -/
def assignRawRoutingSlotsToLoops (loops : Array SelfHyperLoop) (g : SegmentGraph) :
    Array SelfHyperLoop × Array LoopRoutingState := Id.run do
  let mut newLoops := loops
  let mut states : Array LoopRoutingState := #[]
  for i in [0:loops.size] do
    let slot := (g.segments[i]?.map (·.routingSlot)).getD 0
    let mut state : LoopRoutingState := {}
    let mut l := newLoops[i]!
    for side in l.occupiedPortSides.toArray do
      let sideIdx := ElkEnum.ordinal side
      state := { state with occupiedSides := state.occupiedSides.set! sideIdx true
                            routingSlots := state.routingSlots.set! sideIdx slot }
      l := l.setRoutingSlot side slot
    newLoops := newLoops.set! i l
    states := states.push state
  return (newLoops, states)

/-- The state of `shift_towards_node`: the loops, their routing states and `next_free_routing_slot_at_port`. -/
structure ShiftState where
  loops : Array SelfHyperLoop
  states : Array LoopRoutingState
  nextFreeRoutingSlotAtPort : Array Int
  deriving Inhabited

/-- Sets the slot of loop `i` on `side` (loop and routing state). -/
def ShiftState.setSlot (s : ShiftState) (i : Nat) (side : PortSide) (slot : Int) : ShiftState :=
  let sideIdx := ElkEnum.ordinal side
  -- taken apart first and updated with `modifyIn`, so that neither the arrays nor their elements are
  -- shared while they are updated (PLAN 7.1 items 13, 16)
  let ⟨loops, states, nextFree⟩ := s
  ⟨loops.modifyIn i (·.setRoutingSlot side slot),
    states.modifyIn i fun st => { st with routingSlots := st.routingSlots.set! sideIdx slot }, nextFree⟩

/-- The lowest slot of loop `i` above the next free slots of the ports (`minIdx ..= maxIdx`,
within the port list) it is active at. -/
def lowestAvailableSlot (nextFree : Array Int) (active : Array Bool) (minIdx maxIdx : Nat) : Int := Id.run do
  let mut lowest : Int := 0
  for portIndex in [minIdx:min (maxIdx + 1) nextFree.size] do
    if active.getD portIndex false then lowest := max lowest nextFree[portIndex]!
  return lowest

/-- `shift_towards_node_on_side(loops, state, side, range, nextFree, context)`. -/
def shiftTowardsNodeOnSide (s : ShiftState) (side : PortSide) (sidePortRange : Option (Nat × Nat))
    (matrix : Array (Array Bool)) (labelIdByLoop : Array (Option Nat)) (activity : Array (Array Bool)) :
    ShiftState := Id.run do
  let sideIdx := ElkEnum.ordinal side
  let candidates := (Array.range s.loops.size).filter fun i => s.states[i]!.occupiedSides[sideIdx]!
  let slLoops := stableSortByKey candidates fun i => s.states[i]!.routingSlots[sideIdx]!
  let mut s := s
  let (minIdx, maxIdx) ← match sidePortRange with
    | some range => pure range
    | none =>
      -- no ports on this side: the loops' rank is their slot
      return (Array.range slLoops.size).foldl (fun s (slot : Nat) => s.setSlot slLoops[slot]! side (slot : Int)) s
  let mut slotAssignedToLabel : Array Int := Array.replicate matrix.size (-1)
  for i in slLoops do
    let active := activity.getD i #[]
    let mut lowest := lowestAvailableSlot s.nextFreeRoutingSlotAtPort active minIdx maxIdx
    if let some ourLabelIdx := labelIdByLoop[i]! then
      let mut conflicts : Array Int := #[]
      let row := matrix[ourLabelIdx]!
      for h : otherLabelIdx in [0:row.size] do
        if row[otherLabelIdx] then
          let assignedSlot := slotAssignedToLabel[otherLabelIdx]!
          if assignedSlot ≥ 0 then conflicts := conflicts.push assignedSlot
      -- every iteration increases `lowest` past one conflicting slot
      for _ in [0:conflicts.size + 1] do
        if !conflicts.contains lowest then break
        lowest := lowest + 1
    s := s.setSlot i side lowest
    let mut nextFree := s.nextFreeRoutingSlotAtPort
    for portIndex in [minIdx:min (maxIdx + 1) nextFree.size] do
      if active.getD portIndex false then nextFree := nextFree.set! portIndex (lowest + 1)
    s := { s with nextFreeRoutingSlotAtPort := nextFree }
    if let some labelIdx := labelIdByLoop[i]! then
      slotAssignedToLabel := slotAssignedToLabel.set! labelIdx lowest
  return s

/-- `shift_towards_node(...)`: NORTH, EAST, SOUTH, WEST with one shared `next_free_routing_slot_at_port`. -/
def shiftTowardsNode (loops : Array SelfHyperLoop) (states : Array LoopRoutingState) (ranges : SidePortRanges)
    (portCount : Nat) (matrix : Array (Array Bool)) (labelIdByLoop : Array (Option Nat))
    (activity : Array (Array Bool)) : Array SelfHyperLoop × Array LoopRoutingState := Id.run do
  let mut s : ShiftState := { loops, states, nextFreeRoutingSlotAtPort := Array.replicate portCount 0 }
  for side in #[PortSide.north, .east, .south, .west] do
    s := shiftTowardsNodeOnSide s side ranges[ElkEnum.ordinal side]! matrix labelIdByLoop activity
  return (s.loops, s.states)

/-- `update_holder_routing_slot_count(holder, states)`: per side `max(slot, 0) + 1`, maximised
over all loops (index 0 = `UNDEFINED` stays 0). -/
def routingSlotCount (states : Array LoopRoutingState) : Array Int := Id.run do
  let mut counts : Array Int := Array.replicate PORT_SIDE_COUNT 0
  for state in states do
    for side in #[PortSide.north, .east, .south, .west] do
      let sideIdx := ElkEnum.ordinal side
      let slot := max state.routingSlots[sideIdx]! 0
      counts := counts.set! sideIdx (max counts[sideIdx]! (slot + 1))
  return counts

/-- `assign_routing_slots(holder, random)` (Java `assignRoutingSlots`), pure: the holder with the
loops' routing slots and `routingSlotCount`, and the advanced random generator. -/
def assignRoutingSlots (a : LGraphArena) (h : SelfLoopHolder) (random : Random) : SelfLoopHolder × Random :=
  let idOf := SelfLoopHolder.portId a h
  let loops := h.slHyperLoops.map (·.clearRoutingSlots)
  let (portCount, ranges) := collectPortSideRanges a h.lNode
  let (matrix, labelIdByLoop) := computeLabelCrossingMatrix loops
  let (g, activity) := createCrossingGraph loops portCount matrix labelIdByLoop idOf
  let (g, random) := OrthogonalRoutingGenerator.breakNonCriticalCycles g random
  let g := assignRawRoutingSlotsToSegments g
  let (loops, states) := assignRawRoutingSlotsToLoops loops g
  let (loops, states) := shiftTowardsNode loops states ranges portCount matrix labelIdByLoop activity
  ({ h with slHyperLoops := loops, routingSlotCount := routingSlotCount states }, random)

/-- Monadic wrapper: assigns the routing slots of the holder stored on `n` (no-op without holder)
and returns the advanced generator. -/
def assignRoutingSlotsOf (n : LNodeId) (random : Random) : LayeredM Random := do
  let some h ← SelfLoopHolder.get? n | return random
  let (h, random) ← withArena fun a => assignRoutingSlots a h random
  SelfLoopHolder.store n (some h)
  return random

end RoutingSlotAssigner

end Elk.Alg.Layered.Intermediate.Loops.Routing
