import Elk.Alg.Layered.Intermediate.Loops.Routing.AbstractSelfLoopRouter
import Elk.Alg.Layered.Intermediate.Loops.Routing.LabelPlacer
import Elk.Core.Util.ElkTrace
/-!
# `org.eclipse.elk.alg.layered.intermediate.loops.routing.OrthogonalSelfLoopRouter`

The routing of elk-rs `intermediate/self_loop_router.rs` (`route_node` and its helpers), which
plays the role of Java's `OrthogonalSelfLoopRouter.routeSelfLoops`: every self loop is routed
orthogonally around the node, the router's `BendPointModifier` turns the orthogonal bend points
into its style, and the loop's label block is placed in its routing slot.

`routeSelfLoopsWith(modify, holder)` (Rust `route_node`):
1. routing slot positions per side: one entry per `routingSlotCount` slot, starting
   `SPACING_NODE_SELF_LOOP` outside the node margin and advancing by `SPACING_EDGE_EDGE` plus, on
   the northern and southern side, the height of the tallest label block in the slot (plus
   `SPACING_EDGE_LABEL`);
2. per hyper loop (holder order), per edge (loop order): edges with `INSIDE_SELF_LOOPS_YO` lose
   their bend points; otherwise the source and target ports are projected into their side's
   routing slot (`UNDEFINED` sides are inferred from the anchor position), the path runs around the
   node through the corner points of the sides passed (clockwise or counter-clockwise, see
   `computeEdgeRoutingDirection`; corners on the side of an inline label move half the label size
   outwards), is modified by the router, written to the edge and included in the node margins;
3. the loop's label block is placed in its slot on its side (`placeLoopLabels`) and included in
   the margins; the label positions are relative to the node (`SelfLoopPostProcessor` adds the node
   position).

Coordinates are relative to the node. Rust/Java differences (Rust followed): Java computes the
bend points per `SelfLoopEdge` from the loop's leftmost/rightmost ports and reads the spacings per
node; the label lanes and positions differ accordingly.

Deviation: the `ELK_TRACE_INSIDE_YO` line prints the arena edge index instead of the Rust edge
pointer.
-/
/-! Float literals as global constants (FL): inside branches, loops and specialised code the compiler
shares a literal's `Nat`/`Bool` arguments with unrelated variables (CSE) and then parses it on every
evaluation (`FastFloat.ofScientificImpl`); a top-level constant is a load (PLAN §7.1 items 17, 22). -/
private def fl0p0 : Float := 0.0
private def fl1p0 : Float := 1.0

namespace Elk.Alg.Layered.Intermediate.Loops.Routing

open Elk.Graph Elk.Core.Math Elk.Core.Options Elk.Core.Util Elk.Alg.Layered.Graph
  Elk.Alg.Layered.Options Elk.Alg.Layered.Intermediate.Loops LayeredM

namespace OrthogonalSelfLoopRouter

/-- `EPSILON` (`near`). -/
def EPSILON : Float := 1e-3

/-- `RoutePoint`: the side a port is routed from and its projection into the side's slot. -/
structure RoutePoint where
  /-- `side`. -/
  side : PortSide
  /-- `outer_anchor`. -/
  outerAnchor : KVector
  deriving Inhabited, Repr, BEq

/-- Routing slot positions: per `PortSide` ordinal (Rust `side_index`) the coordinate of each slot. -/
abbrev SlotPositions := Array (Array Float)

/-- `baseline_position(side, nodeSize, margin, nodeSelfLoopDistance)`: the first slot's coordinate. -/
def baselinePosition (side : PortSide) (nodeSize : KVector) (margin : LMargin) (nodeSelfLoopDistance : Float) : Float :=
  match side with
  | .north => -margin.top - nodeSelfLoopDistance
  | .east => nodeSize.x + margin.right + nodeSelfLoopDistance
  | .south => nodeSize.y + margin.bottom + nodeSelfLoopDistance
  | .west => -margin.left - nodeSelfLoopDistance
  | .undefined => 0.0

/-- `initialize_max_label_height(positions, loops, side)`: per slot of `side` the maximum height of
the label blocks placed on `side` in that slot. -/
def initializeMaxLabelHeight (positions : SlotPositions) (loops : Array SelfHyperLoop) (side : PortSide) : SlotPositions := Id.run do
  let sideIdx := ElkEnum.ordinal side
  let mut positions := positions
  for l in loops do
    let some lb := l.slLabels | continue
    if lb.side != side then continue
    let slot := (max (l.getRoutingSlot side) 0).toNat
    let labelHeight := lb.size.y
    positions := positions.modify sideIdx fun ps =>
      if slot < ps.size then ps.modify slot (fmax · labelHeight) else ps
  return positions

/-- `compute_routing_slot_positions(counts, loops, nodeSize, margin, spacings)`. -/
def computeRoutingSlotPositions (routingSlotCount : Array Int) (loops : Array SelfHyperLoop) (nodeSize : KVector)
    (margin : LMargin) (sp : SelfLoopRoutingSpacings) : SlotPositions := Id.run do
  let sides := #[PortSide.north, .east, .south, .west]
  let mut positions : SlotPositions := Array.replicate PORT_SIDE_COUNT #[]
  for side in sides do
    let count := (max (routingSlotCount.getD (ElkEnum.ordinal side) 0) 0).toNat
    positions := positions.set! (ElkEnum.ordinal side) (Array.replicate count fl0p0)
  positions := initializeMaxLabelHeight positions loops .north
  positions := initializeMaxLabelHeight positions loops .south
  for side in sides do
    let sideIdx := ElkEnum.ordinal side
    let mut sidePositions := positions[sideIdx]!
    let mut currPos := baselinePosition side nodeSize margin sp.nodeSelfLoop
    let factor : Float := if side == .north || side == .west then -fl1p0 else fl1p0
    for i in [0:sidePositions.size] do
      let mut largestLabelSize := sidePositions[i]!
      if largestLabelSize > fl0p0 then largestLabelSize := largestLabelSize + sp.edgeLabel
      sidePositions := sidePositions.set! i currPos
      currPos := currPos + factor * (largestLabelSize + sp.edgeEdge)
    positions := positions.set! sideIdx sidePositions
  return positions

/-- `slot_position(side, slot, positions)`. -/
def slotPosition (side : PortSide) (slot : Nat) (positions : SlotPositions) : Option Float :=
  (positions[ElkEnum.ordinal side]?).bind (·[slot]?)

/-- `base_vector(side, slot, positions)`: the slot coordinate as a vector (`0` if missing). -/
def baseVector (side : PortSide) (slot : Nat) (positions : SlotPositions) : KVector :=
  let position := (slotPosition side slot positions).getD 0.0
  match side with
  | .north | .south => ⟨0.0, position⟩
  | .east | .west => ⟨position, 0.0⟩
  | .undefined => {}

/-- `near(a, b)`. -/
@[inline] def near (a b : Float) : Bool := (a - b).abs ≤ EPSILON

/-- `infer_side_from_position(point, nodeSize)`: the node side closest to the point (ties: north,
east, south, west). -/
def inferSideFromPosition (point nodeSize : KVector) : PortSide :=
  let leftDistance := point.x.abs
  let rightDistance := (nodeSize.x - point.x).abs
  let northDistance := point.y.abs
  let southDistance := (nodeSize.y - point.y).abs
  let m := fmin (fmin (fmin leftDistance rightDistance) northDistance) southDistance
  if near m northDistance then .north
  else if near m rightDistance then .east
  else if near m southDistance then .south
  else .west

/-- `local_port_anchor(port)`: port position plus anchor. -/
def localPortAnchor (a : LGraphArena) (p : LPortId) : KVector :=
  let port := a.port p
  port.position + port.anchor

/-- `route_point_for_port(port, positions, slLoop, nodeSize)`. -/
def routePointForPort (a : LGraphArena) (p : LPortId) (positions : SlotPositions) (l : SelfHyperLoop)
    (nodeSize : KVector) : RoutePoint :=
  let port := a.port p
  let localAnchor : KVector := ⟨port.position.x + port.anchor.x, port.position.y + port.anchor.y⟩
  let side := if port.side == .undefined then inferSideFromPosition localAnchor nodeSize else port.side
  let slot := (max (l.getRoutingSlot side) 0).toNat
  let base := baseVector side slot positions
  let outerAnchor : KVector := match side with
    | .north | .south => ⟨localAnchor.x, base.y⟩
    | .east | .west => ⟨base.x, localAnchor.y⟩
    | .undefined => ⟨localAnchor.x, base.y⟩
  { side, outerAnchor }

/-- `compute_edge_routing_direction(slLoop, sourcePort, targetPort, sourceSide, targetSide)`:
`true` = clockwise. Same side: by port id; neighbouring sides: the short way; opposite sides:
clockwise iff the loop occupies the side clockwise of the source side. -/
def computeEdgeRoutingDirection (a : LGraphArena) (l : SelfHyperLoop) (sourcePort targetPort : LPortId)
    (sourceSide targetSide : PortSide) : Bool :=
  if sourceSide == targetSide then (a.port sourcePort).id < (a.port targetPort).id
  else if sourceSide.right == targetSide then true
  else if sourceSide.left == targetSide then false
  else l.occupiedPortSides.contains sourceSide.right

/-- `inline_label_side_and_size(slEdge, slLoop)`: the loop's label side and size if the edge has an
inline label and the label side is defined. -/
def inlineLabelSideAndSize (a : LGraphArena) (lEdge : LEdgeId) (l : SelfHyperLoop) : Option (PortSide × KVector) :=
  if !LabelPlacer.anyInlineLabel a (a.edge lEdge).labels then none
  else match l.slLabels with
    | some lb => if lb.side == .undefined then none else some (lb.side, lb.size)
    | none => none

/-- `adjust_vector_for_label_side(vector, side, size)`: half the label size outwards. -/
def adjustVectorForLabelSide (v : KVector) (labelSide : PortSide) (labelSize : KVector) : KVector :=
  match labelSide with
  | .north => { v with y := v.y - labelSize.y / 2.0 }
  | .south => { v with y := v.y + labelSize.y / 2.0 }
  | .west => { v with x := v.x - labelSize.x / 2.0 }
  | .east => { v with x := v.x + labelSize.x / 2.0 }
  | .undefined => v

/-- `compute_orthogonal_bend_points(slEdge, slLoop, source, target, positions)`: source outer
anchor, one corner per side change (at most three; Rust loops until the target side is reached),
target outer anchor. -/
def computeOrthogonalBendPoints (a : LGraphArena) (lEdge : LEdgeId) (l : SelfHyperLoop) (sourcePort targetPort : LPortId)
    (source target : RoutePoint) (positions : SlotPositions) : Array KVector := Id.run do
  let mut points : Array KVector := #[source.outerAnchor]
  if source.side != target.side then
    let clockwise := computeEdgeRoutingDirection a l sourcePort targetPort source.side target.side
    let inlineLabel := inlineLabelSideAndSize a lEdge l
    let mut currSide := source.side
    for _ in [0:4] do
      if currSide == target.side then break
      let nextSide := if clockwise then currSide.right else currSide.left
      let currSlot := (max (l.getRoutingSlot currSide) 0).toNat
      let nextSlot := (max (l.getRoutingSlot nextSide) 0).toNat
      let mut currComponent := baseVector currSide currSlot positions
      let mut nextComponent := baseVector nextSide nextSlot positions
      if let some (labelSide, labelSize) := inlineLabel then
        if currSide == labelSide then
          currComponent := adjustVectorForLabelSide currComponent labelSide labelSize
        else if nextSide == labelSide then
          nextComponent := adjustVectorForLabelSide nextComponent labelSide labelSize
      points := points.push (currComponent + nextComponent)
      currSide := nextSide
  return points.push target.outerAnchor

/-- `local_position(nodeSize, labelSize, alignment, reference)` of `self_loop_router.rs`: centred
on both axes for `CENTER`; `LEFT`/`RIGHT` align `x` to the reference anchor (`x`, `x - width`;
defaults `0` / `nodeWidth - width`) with `y` centred; `TOP` aligns `y` (default `0`) with `x`
centred. -/
def localPosition (a : LGraphArena) (h : SelfLoopHolder) (nodeSize labelSize : KVector)
    (alignment : SelfHyperLoopLabels.Alignment) (reference : Option SelfLoopPortId) : KVector :=
  let ref := reference.map (LabelPlacer.portAnchor a h)
  match alignment with
  | .center => ⟨(nodeSize.x - labelSize.x) / 2.0, (nodeSize.y - labelSize.y) / 2.0⟩
  | .left => ⟨(ref.map (·.x)).getD 0.0, (nodeSize.y - labelSize.y) / 2.0⟩
  | .right => ⟨(ref.map (·.x - labelSize.x)).getD (nodeSize.x - labelSize.x), (nodeSize.y - labelSize.y) / 2.0⟩
  | .top => ⟨(nodeSize.x - labelSize.x) / 2.0, (ref.map (·.y)).getD 0.0⟩

/-- `modifyBendPoints` of the orthogonal router: the bend points unchanged (Rust
`modify_bend_points`' `_` arm). -/
def modifyBendPoints : BendPointModifier := fun m => .ok m.bendPoints

/-- The routed path of one self-loop edge: orthogonal bend points (`compute_orthogonal_bend_points`)
passed through `modify` with the routing direction and the port anchors. -/
def computeEdgePath (a : LGraphArena) (l : SelfHyperLoop) (lEdge : LEdgeId) (sourcePort targetPort : LPortId)
    (positions : SlotPositions) (nodeSize : KVector) (edgeLabelDistance : Float) (modify : BendPointModifier) :
    Except String (Array KVector) :=
  let sourcePoint := routePointForPort a sourcePort positions l nodeSize
  let targetPoint := routePointForPort a targetPort positions l nodeSize
  let path := computeOrthogonalBendPoints a lEdge l sourcePort targetPort sourcePoint targetPoint positions
  let clockwise := computeEdgeRoutingDirection a l sourcePort targetPort sourcePoint.side targetPoint.side
  modify { sourceAnchor := localPortAnchor a sourcePort, targetAnchor := localPortAnchor a targetPort
           bendPoints := path, sourceSide := sourcePoint.side, clockwise, edgeLabelDistance }

/-- The label block position of `place_loop_labels`: `none` without labels or label side. -/
def loopLabelPosition (a : LGraphArena) (h : SelfLoopHolder) (l : SelfHyperLoop) (nodeSize : KVector)
    (edgeLabelDistance : Float) (positions : SlotPositions) : Option KVector := do
  let lb ← l.slLabels
  let side := lb.side
  guard (side != .undefined)
  let inlineLabels := LabelPlacer.anyInlineLabel a lb.lLabels
  let slot := (max (l.getRoutingSlot side) 0).toNat
  let lanePosition := (slotPosition side slot positions).getD 0.0
  let localPos := localPosition a h nodeSize lb.size lb.alignment lb.alignmentReferenceSLPort
  let labelDistance := if inlineLabels then 0.0 else edgeLabelDistance
  match side with
  | .north => some ⟨localPos.x, lanePosition - labelDistance - lb.size.y⟩
  | .south => some ⟨localPos.x, lanePosition + labelDistance⟩
  | .east => some ⟨lanePosition + labelDistance, localPos.y⟩
  | .west => some ⟨lanePosition - labelDistance - lb.size.x, localPos.y⟩
  | .undefined => none

/-- `place_loop_labels(slLoop, nodeSize, edgeLabelDistance, positions, margins)` for hyper loop `l`
of the holder on `n`: sets the block position, places the labels (`applyPlacement` with offset 0)
and returns the margins grown by the block's corners. -/
def placeLoopLabels (n : LNodeId) (h : SelfLoopHolder) (l : SelfHyperLoopId) (nodeSize : KVector)
    (edgeLabelDistance : Float) (positions : SlotPositions) (margins : LMargin) : LayeredM LMargin := do
  let loop := h.slHyperLoop l
  let some lb := loop.slLabels | return margins
  let some relative ← withArena fun a => loopLabelPosition a h loop nodeSize edgeLabelDistance positions
    | return margins
  let lb := { lb with position := relative }
  SelfLoopHolder.update n fun h => h.modifySLHyperLoop l fun x => { x with slLabels := some lb }
  let placed ← withArena fun a => lb.placement {} (fun x => (a.label x).size)
  for (label, pos) in placed do
    modifyLabel label fun x => { x with position := pos }
  let localBottomRight : KVector := ⟨relative.x + lb.size.x, relative.y + lb.size.y⟩
  let margins := LabelPlacer.updateMarginsWithPoint nodeSize margins relative
  return LabelPlacer.updateMarginsWithPoint nodeSize margins localBottomRight

/-- Routes one self-loop edge (the inner loop body of `route_node`); returns the grown margins. -/
def routeEdge (h : SelfLoopHolder) (loop : SelfHyperLoop) (e : SelfLoopEdgeId) (positions : SlotPositions)
    (nodeSize : KVector) (edgeLabelDistance : Float) (modify : BendPointModifier) (margins : LMargin) :
    LayeredM LMargin := do
  let slEdge := h.slEdge e
  let lEdge := slEdge.lEdge
  let sourcePort := h.lPortOf slEdge.slSource
  let targetPort := h.lPortOf slEdge.slTarget
  let insideSelfLoopYo := (← getEdge lEdge).props.getD CoreOptions.INSIDE_SELF_LOOPS_YO false
  if ElkTrace.global.insideYo then
    IO.eprintln s!"[self-loop-router] edge={lEdge.idx} inside_self_loop_yo={insideSelfLoopYo}"
  if insideSelfLoopYo then
    modifyEdge lEdge fun x => { x with bendPoints := #[] }
    return margins
  let result ← withArena fun a =>
    computeEdgePath a loop lEdge sourcePort targetPort positions nodeSize edgeLabelDistance modify
  let path ← match result with
    | .ok path => pure path
    | .error msg => throw (IO.userError s!"java.lang.IllegalStateException: {msg}")
  modifyEdge lEdge fun x => { x with bendPoints := path }
  return path.foldl (LabelPlacer.updateMarginsWithPoint nodeSize) margins

/-- `route_node(holder, spacings, edgeRouting)` with the router's bend point modifier (Java
`OrthogonalSelfLoopRouter.routeSelfLoops`) for the holder stored on `n` (no-op without holder). -/
def routeSelfLoopsWith (modify : BendPointModifier) (n : LNodeId) (sp : SelfLoopRoutingSpacings) : LayeredM Unit := do
  let some h ← SelfLoopHolder.get? n | return
  let nd ← getNode n
  let nodeSize := nd.size
  let mut newMargins := nd.margin
  let positions := computeRoutingSlotPositions h.routingSlotCount h.slHyperLoops nodeSize newMargins sp
  for l in h.hyperLoopIds do
    let loop := h.slHyperLoop l
    for e in loop.slEdges do
      newMargins ← routeEdge h loop e positions nodeSize sp.edgeLabel modify newMargins
    newMargins ← placeLoopLabels n h l nodeSize sp.edgeLabel positions newMargins
  let finalMargins := newMargins
  modifyNode n fun x => { x with margin := finalMargins }

/-- The `OrthogonalSelfLoopRouter`. -/
def router : AbstractSelfLoopRouter :=
  { name := "OrthogonalSelfLoopRouter", routeSelfLoops := routeSelfLoopsWith modifyBendPoints }

end OrthogonalSelfLoopRouter

end Elk.Alg.Layered.Intermediate.Loops.Routing
