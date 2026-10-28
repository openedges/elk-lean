import Elk.Alg.Layered.Intermediate.Loops.Routing.RoutingDirector
import Elk.Alg.Layered.Options.LayeredOptions
/-!
# `org.eclipse.elk.alg.layered.intermediate.loops.routing.LabelPlacer`

Port of elk-rs `intermediate/loops/routing/label_placer.rs`: decides on which side of the node and
with which alignment the label block of every hyper loop is placed (`prepareLabels`), and the
standalone `placeLabels` (positions relative to a base offset).

`prepareLabels(holder, labelManager)` (what `SelfLoopRouter` calls, before the routing slots are
assigned):
- with `SEQUENCED` ordering, the labelled one-sided loops on the northern (southern) side are
  sorted by leftmost port id (descending on the south) and aligned pairwise from the outside in
  (`RIGHT` / `LEFT`, the middle one `CENTER`);
- every other labelled loop gets its side and alignment from its type (`assign_side_and_alignment`);
  except for two-sided opposing and three-sided loops this clears `EDGE_LABELS_INLINE` on the
  loop's labels (`set_property(…, None)` → `PropertyMap.remove`);
- with a label manager the label sizes would be managed. TODO(core-labels): there is no label
  manager in Lean yet (JSON inputs carry none); once it exists, call it per loop with
  `targetWidthForLabelManagement` and spacing `2.0`, then `SelfHyperLoopLabels.sizeAfterLabelManagement`.

Like Java (`placeLabels` → `computeCoordinates`, and unlike elk-rs) the alignment coordinate of each
label block is computed here, before the slot assignment, whose label overlap test reads it; the
router (`OrthogonalSelfLoopRouter.placeLoopLabels`) then sets the coordinate of the routing slot.

The side/alignment decisions are pure (`assignSidesAndAlignments` returns the new loops and the
labels whose inline flag is cleared); `prepareLabels` applies them.
-/
/-! Float literals as global constants (FL): inside branches, loops and specialised code the compiler
shares a literal's `Nat`/`Bool` arguments with unrelated variables (CSE) and then parses it on every
evaluation (`FastFloat.ofScientificImpl`); a top-level constant is a load (PLAN §7.1 items 17, 22). -/
private def fl0p0 : Float := 0.0
private def fl0p75 : Float := 0.75
private def fl2p0 : Float := 2.0

namespace Elk.Alg.Layered.Intermediate.Loops.Routing

open Elk.Graph Elk.Core.Math Elk.Core.Options Elk.Core.Util Elk.Alg.Layered.Graph
  Elk.Alg.Layered.Options Elk.Alg.Layered.Intermediate.Loops LayeredM

namespace LabelPlacer

/-- `MIN_WIDTH_EDGE_LABELS`. -/
def MIN_WIDTH_EDGE_LABELS : Float := 16.0

/-- `i32::MAX` (key of loops without leftmost port). -/
def I32_MAX : Int := 2147483647

/-- Whether any of the labels has `EDGE_LABELS_INLINE` set (`unwrap_or(false)`). -/
def anyInlineLabel (a : LGraphArena) (labels : Array LLabelId) : Bool :=
  labels.any fun l => (a.label l).props.getD LayeredOptions.EDGE_LABELS_INLINE false

/-- Position plus anchor of the self-loop port's `LPort` (`sl_port_y`, `alignment_reference_x`). -/
def portAnchor (a : LGraphArena) (h : SelfLoopHolder) (p : SelfLoopPortId) : KVector :=
  let port := a.port (h.lPortOf p)
  ⟨port.position.x + port.anchor.x, port.position.y + port.anchor.y⟩

/-- `pick_topmost_port(leftmost, rightmost)`: the one with the smaller `y` (leftmost on ties). Java
compares the port positions (`getLPort().getPosition().y`) without the anchors (elk-rs adds them). -/
def pickTopmostPort (a : LGraphArena) (h : SelfLoopHolder) (leftmost rightmost : Option SelfLoopPortId) :
    Option SelfLoopPortId :=
  match leftmost, rightmost with
  | some left, some right =>
    if (a.port (h.lPortOf right)).position.y < (a.port (h.lPortOf left)).position.y then some right else some left
  | some left, none => some left
  | none, some right => some right
  | none, none => none

/-- `set_side_and_alignment(slLoop, side, alignment, reference)` (no-op without labels). -/
def setSideAndAlignment (l : SelfHyperLoop) (side : PortSide) (alignment : SelfHyperLoopLabels.Alignment)
    (reference : Option SelfLoopPortId) : SelfHyperLoop :=
  { l with slLabels := l.slLabels.map fun lb =>
      { lb with side := side, alignment := alignment, alignmentReferenceSLPort := reference } }

/-- The first element of `occupied_port_sides` (`iter().next()`; one-sided loops occupy one side). -/
def firstOccupiedSide (l : SelfHyperLoop) : PortSide :=
  (l.occupiedPortSides.toArray[0]?).getD .undefined

/-- `assign_side_and_alignment(slLoop)`: side and alignment by self loop type; returns the loop and
whether the inline flags of its labels are cleared (`clear_inline_label_property`). -/
def assignSideAndAlignment (a : LGraphArena) (h : SelfLoopHolder) (l : SelfHyperLoop) : SelfHyperLoop × Bool :=
  match l.slLabels with
  | none => (l, false)
  | some lb =>
    let leftmost := l.leftmostPort
    let rightmost := l.rightmostPort
    let occupied := l.occupiedPortSides
    let sideOf (p : Option SelfLoopPortId) : PortSide := match p with
      | some p => SelfLoopHolder.portSide a h p
      | none => .undefined
    let hasInlineLabels := anyInlineLabel a lb.lLabels
    let set := setSideAndAlignment l
    match l.selfLoopType with
    | some .oneSide =>
      let side := firstOccupiedSide l
      if side == .east || side == .west then (set side .top (pickTopmostPort a h leftmost rightmost), true)
      else (set side .center none, true)
    | some .twoSidesCorner =>
      let leftSide := sideOf leftmost
      let rightSide := sideOf rightmost
      let l' :=
        if leftSide == .north then set .north .left leftmost
        else if rightSide == .north then set .north .right rightmost
        else if leftSide == .south then set .south .right leftmost
        else if rightSide == .south then set .south .left rightmost
        else set .north .center none
      (l', true)
    | some .twoSidesOpposing | some .threeSides =>
      let l' :=
        if !occupied.contains .north then set .south .center none
        else if !occupied.contains .south then set .north .center none
        else if !occupied.contains .west then
          if hasInlineLabels then set .east .center none else set .north .left leftmost
        else if !occupied.contains .east then
          if hasInlineLabels then set .west .center none else set .north .right rightmost
        else set .north .center none
      (l', false)
    | some .fourSides | none =>
      -- ELK Java 0.12.0 reads the leftmost port's side twice (`rightmostPortSide =
      -- slLoop.getLeftmostPort()...`), so only the leftmost port decides
      let leftSide := sideOf leftmost
      let side : PortSide := if leftSide == .north then .south else .north
      (set side .center none, true)

/-- `assign_one_sided_sequenced(loops, side)` on the loops with the given indices: sorted by
leftmost port id (descending for SOUTH; stable), aligned pairwise from both ends. -/
def assignOneSidedSequenced (idOf : SelfLoopPortId → Int) (loops : Array SelfHyperLoop) (indices : Array Nat)
    (side : PortSide) : Array SelfHyperLoop := Id.run do
  if indices.isEmpty then return loops
  let key (i : Nat) : Int := match loops[i]!.leftmostPort with
    | some p => idOf p
    | none => I32_MAX
  let sorted :=
    if side == .north then stableSort indices fun i j => compare (key i) (key j)
    else stableSort indices fun i j => compare (key j) (key i)
  let mut loops := loops
  let mut leftIdx := 0
  let mut rightIdx := sorted.size - 1
  -- `leftIdx` grows and `rightIdx` shrinks by one per round
  for _ in [0:sorted.size] do
    if leftIdx ≥ rightIdx then break
    let leftLoop := sorted[leftIdx]!
    let rightLoop := sorted[rightIdx]!
    let leftRef := if side == .north then loops[leftLoop]!.rightmostPort else loops[leftLoop]!.leftmostPort
    let rightRef := if side == .north then loops[rightLoop]!.leftmostPort else loops[rightLoop]!.rightmostPort
    loops := loops.modify leftLoop (setSideAndAlignment · side .right leftRef)
    loops := loops.modify rightLoop (setSideAndAlignment · side .left rightRef)
    leftIdx := leftIdx + 1
    rightIdx := rightIdx - 1
  if leftIdx == rightIdx then
    loops := loops.modify sorted[leftIdx]! (setSideAndAlignment · side .center none)
  return loops

/-- `assign_sides_and_alignments(loops, ordering)`: the new loops (holder order) and the labels
whose `EDGE_LABELS_INLINE` is cleared (in loop order). -/
def assignSidesAndAlignments (a : LGraphArena) (h : SelfLoopHolder) (ordering : SelfLoopOrderingStrategy) :
    Array SelfHyperLoop × Array LLabelId := Id.run do
  let mut loops := h.slHyperLoops
  let mut toClear : Array LLabelId := #[]
  let mut northern : Array Nat := #[]
  let mut southern : Array Nat := #[]
  for i in [0:loops.size] do
    let l := loops[i]!
    let oneSidedSide : PortSide :=
      if l.slLabels.isNone || l.selfLoopType != some .oneSide then .undefined
      else firstOccupiedSide l
    if ordering == .sequenced && oneSidedSide == .north then
      northern := northern.push i
      continue
    if ordering == .sequenced && oneSidedSide == .south then
      southern := southern.push i
      continue
    let (l', clear) := assignSideAndAlignment a h l
    loops := loops.set! i l'
    if clear then toClear := toClear ++ ((l.slLabels.map (·.lLabels)).getD #[])
  if ordering == .sequenced then
    let idOf := SelfLoopHolder.portId a h
    loops := assignOneSidedSequenced idOf loops northern .north
    loops := assignOneSidedSequenced idOf loops southern .south
  return (loops, toClear)

/-- `target_width_for_label_management(slLabels, nodeSize, nodeMargin)` (only used with a label
manager; see the module doc). -/
def targetWidthForLabelManagement (a : LGraphArena) (h : SelfLoopHolder) (lb : SelfHyperLoopLabels)
    (nodeSize : KVector) (nodeMargin : LMargin) : Float :=
  let alignRefX := match lb.alignmentReferenceSLPort with
    | some p => (portAnchor a h p).x
    | none => 0.0
  let targetWidth := match lb.alignment with
    | .center => nodeMargin.left + nodeSize.x + nodeMargin.right
    | .left => nodeSize.x - alignRefX + nodeMargin.right
    | .right => nodeMargin.left + alignRefX
    | .top => MIN_WIDTH_EDGE_LABELS
  fmax targetWidth MIN_WIDTH_EDGE_LABELS

/-- Java `computeCoordinates(slLoop)`: the coordinate of the label block given by the alignment
(`CENTER`: `x` centred on the node, `LEFT`/`RIGHT`: `x` at the reference port's anchor, `TOP`: `y` at
it); the other coordinate keeps its value. `RoutingSlotAssigner` compares these `x` ranges. -/
def computeCoordinates (a : LGraphArena) (h : SelfLoopHolder) (nodeSize : KVector) (l : SelfHyperLoop) :
    SelfHyperLoop :=
  match l.slLabels with
  | none => l
  | some lb =>
    let ref := lb.alignmentReferenceSLPort.map (portAnchor a h)
    let pos := lb.position
    let pos : KVector := match lb.alignment, ref with
      | .center, _ => { pos with x := (nodeSize.x - lb.size.x) / 2.0 }
      | .left, some r => { pos with x := r.x }
      | .right, some r => { pos with x := r.x - lb.size.x }
      | .top, some r => { pos with y := r.y }
      | _, none => pos
    { l with slLabels := some { lb with position := pos } }

/-- `prepare_labels(holder, labelManager)` (Java `placeLabels`: sides, alignments and
`computeCoordinates`) for the holder stored on `n` (no-op without holder). -/
def prepareLabels (n : LNodeId) : LayeredM Unit := do
  let some h ← SelfLoopHolder.get? n | return
  let ordering := ((← getNode n).props.get LayeredOptions.EDGE_ROUTING_SELF_LOOP_ORDERING).getD .stacked
  let nodeSize := (← getNode n).size
  let (loops, toClear) ← withArena fun a =>
    let (loops, toClear) := assignSidesAndAlignments a h ordering
    (loops.map (computeCoordinates a h nodeSize), toClear)
  for lb in toClear do
    modifyLabel lb fun x => { x with props := x.props.remove LayeredOptions.EDGE_LABELS_INLINE }
  SelfLoopHolder.update n fun h => { h with slHyperLoops := loops }
  -- TODO(core-labels): `manage_labels(slLoop, nodeSize, nodeMargin, labelManager)` per loop when the
  -- graph has a `LABEL_MANAGER` (no label manager implementation in Lean yet).

/-- `local_position(nodeSize, labelSize, alignment, reference)` of `label_placer.rs`: centred for
`CENTER`; otherwise only the coordinate given by the reference port's anchor is set (`LEFT`: `x`,
`RIGHT`: `x - width`, `TOP`: `y`), the other stays `0`. -/
def localPosition (a : LGraphArena) (h : SelfLoopHolder) (nodeSize labelSize : KVector) (alignment : SelfHyperLoopLabels.Alignment)
    (reference : Option SelfLoopPortId) : KVector :=
  let ref := reference.map (portAnchor a h)
  match alignment with
  | .center => ⟨(nodeSize.x - labelSize.x) / 2.0, (nodeSize.y - labelSize.y) / 2.0⟩
  | .left => match ref with | some r => ⟨r.x, 0.0⟩ | none => {}
  | .right => match ref with | some r => ⟨r.x - labelSize.x, 0.0⟩ | none => {}
  | .top => match ref with | some r => ⟨0.0, r.y⟩ | none => {}

/-- `compute_loop_label_placement(slLoop, nodePos, nodeSize, baseOffset)`: the absolute label block
position, `baseOffset + slot · (0.75 · baseOffset + 2)` away from the node on the label side,
clamped to non-negative coordinates. -/
def computeLoopLabelPlacement (a : LGraphArena) (h : SelfLoopHolder) (l : SelfHyperLoop) (nodePos nodeSize : KVector)
    (baseOffset : Float) : Option KVector := do
  let lb ← l.slLabels
  let side := lb.side
  guard (side != .undefined)
  let slot := max (l.getRoutingSlot side) 0
  let localPos := localPosition a h nodeSize lb.size lb.alignment lb.alignmentReferenceSLPort
  let slotOffset := baseOffset + slot.toFloat * (baseOffset * fl0p75 + fl2p0)
  let absolute : KVector ← match side with
    | .north => some ⟨nodePos.x + localPos.x, nodePos.y - slotOffset - lb.size.y⟩
    | .south => some ⟨nodePos.x + localPos.x, nodePos.y + nodeSize.y + slotOffset⟩
    | .east => some ⟨nodePos.x + nodeSize.x + slotOffset, nodePos.y + localPos.y⟩
    | .west => some ⟨nodePos.x - slotOffset - lb.size.x, nodePos.y + localPos.y⟩
    | .undefined => none
  -- Keep labels in graph-local positive coordinates for single-node graphs.
  return ⟨fmax absolute.x fl0p0, fmax absolute.y fl0p0⟩

/-- `update_margins_with_point(nodeSize, margins, point)`: grows the margins to include `point`
(node-relative). -/
def updateMarginsWithPoint (nodeSize : KVector) (margins : LMargin) (point : KVector) : LMargin :=
  { margins with
    left := fmax margins.left (-point.x)
    right := fmax margins.right (point.x - nodeSize.x)
    top := fmax margins.top (-point.y)
    bottom := fmax margins.bottom (point.y - nodeSize.y) }

/-- `place_labels(holder, baseOffset, labelManager)`: `prepareLabels`, then the absolute label
positions (block and labels) and the node margins covering them. -/
def placeLabels (n : LNodeId) (baseOffset : Float) : LayeredM Unit := do
  prepareLabels n
  let some h ← SelfLoopHolder.get? n | return
  let nd ← getNode n
  let nodePos := nd.position
  let nodeSize := nd.size
  let mut margin := nd.margin
  for l in h.hyperLoopIds do
    let some absolute ← withArena fun a => computeLoopLabelPlacement a h (h.slHyperLoop l) nodePos nodeSize baseOffset
      | continue
    let some lb := (h.slHyperLoop l).slLabels | continue
    let lb := { lb with position := absolute }
    SelfLoopHolder.update n fun h => h.modifySLHyperLoop l fun x => { x with slLabels := some lb }
    let positions ← withArena fun a => lb.placement {} (fun x => (a.label x).size)
    for (label, pos) in positions do
      modifyLabel label fun x => { x with position := pos }
    let localTopLeft : KVector := ⟨absolute.x - nodePos.x, absolute.y - nodePos.y⟩
    let localBottomRight : KVector := ⟨localTopLeft.x + lb.size.x, localTopLeft.y + lb.size.y⟩
    margin := updateMarginsWithPoint nodeSize margin localTopLeft
    margin := updateMarginsWithPoint nodeSize margin localBottomRight
  let finalMargin := margin
  modifyNode n fun x => { x with margin := finalMargin }

end LabelPlacer

end Elk.Alg.Layered.Intermediate.Loops.Routing
