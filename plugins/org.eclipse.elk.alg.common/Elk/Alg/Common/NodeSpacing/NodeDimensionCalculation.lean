import Elk.Core.Util.Sort
import Elk.Core.Util.Adapters.ElkGraphAdapters
import Elk.Alg.Common.NodeSpacing.Calculators.NodeLabelAndSizeCalculator
import Elk.Alg.Common.NodeSpacing.Calculators.NodeMarginCalculator
/-!
# `org.eclipse.elk.alg.common.nodespacing.NodeDimensionCalculation`

Entry points for node size, port and label placement and node margins (elk-rs
`nodespacing::node_dimension_calculation`). Java's class only forwards to
`NodeLabelAndSizeCalculator.process(adapter)` and `NodeMarginCalculator.process()`; that is
`calculateLabelAndNodeSizesJava`, which `NodeMicroLayout` uses (ELK Java is the result reference).
elk-rs replaces the label/size step by two paths, both ported here:

* `calculateLabelAndNodeSizesForElk` (elk-rs `calculate_label_and_node_sizes_for_elk`, elk-rs'
  `NodeMicroLayout` path; no longer used by `NodeMicroLayout`, kept for its tests): per node
  `NodeLabelAndSizeCalculator.processNode` (node size and node labels), then a simplified port label
  placement (`placePortLabels`) with overlap removal against inside node labels and between
  constrained labels of one side. Ports are not moved. Java has no such path; its results differ
  (e.g. `PORTS` constraints never size the node, constrained labels are stacked).
* `calculateLabelAndNodeSizes` (elk-rs `calculate_label_and_node_sizes_with_process_node`, the
  non-ELK branch used by the layered `LabelAndNodeSizeProcessor`): per node the full Java cell
  system pipeline `NodeLabelAndSizeCalculator.process`, preceded by `processNode` for nodes with
  fixed size constraints and already placed fixed port labels
  (`needsProcessNodeForFixedPortLabels`).

Deviations from elk-rs:
* elk-rs' `calculate_label_and_node_sizes` downcasts the adapter: an `ElkGraphAdapter` takes the
  ELK path, every other adapter the generic one. The Lean adapters are one record type for all
  graph models, so `calculateLabelAndNodeSizes` is always the generic path; `NodeMicroLayout` calls
  `calculateLabelAndNodeSizesJava` (Java) instead of elk-rs' ELK path.
* The environment switches `ELK_NODE_DIM_FULL_FOR_FIXED` and `ELK_NODE_DIM_SKIP_FULL_PROCESS` are
  read once at startup into `NodeDimensionFlags.global` (like `ElkTrace.global`); both entry points
  also take the switch as an explicit parameter.
* elk-rs' dead `calculate_label_and_node_sizes_generic` (`#[allow(dead_code)]`) is not ported.
* The ELK and generic port label passes share one implementation (`placePortLabels`); their
  differences are the fields of `PortLabelVariant`.
-/
/-! Float literals as global constants (FL): inside branches, loops and specialised code the compiler
shares a literal's `Nat`/`Bool` arguments with unrelated variables (CSE) and then parses it on every
evaluation (`FastFloat.ofScientificImpl`); a top-level constant is a load (PLAN §7.1 items 17, 22). -/
private def fl0p0 : Float := 0.0
private def fl0p01 : Float := 0.01
private def fl1p0 : Float := 1.0
private def fl2p0 : Float := 2.0

namespace Elk.Alg.Common.NodeSpacing

open Elk Elk.Graph Elk.Core.Math Elk.Core.Util Elk.Core.Options Elk.Core.Util.Adapters

/-- The elk-rs environment switches of `node_dimension_calculation.rs` (`LazyLock` statics). -/
structure NodeDimensionFlags where
  /-- `NODE_DIM_FULL_FOR_FIXED` (`ELK_NODE_DIM_FULL_FOR_FIXED` set): the ELK path runs the full
  `process` for nodes with fixed port labels instead of `processNode` + port label placement. -/
  fullProcessForFixed : Bool := false
  /-- `NODE_DIM_USE_FULL_PROCESS` (`ELK_NODE_DIM_SKIP_FULL_PROCESS` unset): the generic path runs
  the full `process`; otherwise `processNode` + port label placement. -/
  useFullProcess : Bool := true
  deriving Inhabited, Repr

namespace NodeDimensionFlags

/-- Reads both switches from the environment (set = the variable exists, even if empty). -/
def fromEnv : IO NodeDimensionFlags := do
  return {
    fullProcessForFixed := (← IO.getEnv "ELK_NODE_DIM_FULL_FOR_FIXED").isSome
    useFullProcess := (← IO.getEnv "ELK_NODE_DIM_SKIP_FULL_PROCESS").isNone }

end NodeDimensionFlags

/-- The process-wide switches, computed once at startup (elk-rs `LazyLock`). -/
builtin_initialize NodeDimensionFlags.global : NodeDimensionFlags ← NodeDimensionFlags.fromEnv

namespace NodeDimensionCalculation

variable {m : Type → Type} [Monad m] {G N P L E : Type}

/-- elk-rs `COMPOUND_NODE_PROPERTY` (`"compoundNode"`, default `false`): read by the generic path to
decide whether a node is compound (the layered `InternalProperties.COMPOUND_NODE`). -/
def COMPOUND_NODE_PROPERTY : Property Bool := Property.withDefault "compoundNode" false

/-! ### Rectangles (elk-rs file-private `Rect`) -/

/-- elk-rs `Rect::union`: the bounding box of both rectangles (`f64::min`/`max`, no swapping). -/
def rectUnion (r o : ElkRectangle) : ElkRectangle :=
  let left := fmin r.x o.x
  let top := fmin r.y o.y
  let right := fmax (r.x + r.width) (o.x + o.width)
  let bottom := fmax (r.y + r.height) (o.y + o.height)
  { x := left, y := top, width := right - left, height := bottom - top }

/-- elk-rs `Rect::overlaps`: strict interior overlap. -/
def rectOverlaps (r o : ElkRectangle) : Bool :=
  r.x < o.x + o.width && r.x + r.width > o.x && r.y < o.y + o.height && r.y + r.height > o.y

/-! ### Label placement relation -/

/-- elk-rs file-private `LabelPlacementRelation`: where a port label goes relative to its port. -/
inductive LabelPlacementRelation where
  /-- Centered next to the port. -/
  | centered
  /-- Below (EAST/WEST) or right of (NORTH/SOUTH) the port. -/
  | belowOrRight
  /-- Above (EAST/WEST) or left of (NORTH/SOUTH) the port. -/
  | aboveOrLeft
  deriving BEq, Repr, Inhabited

/-- elk-rs `label_placement_relation(index, port_count, any_incident_edges, inside_label_placement,
next_to_port_if_possible, always_same_side, always_other_same_side, space_efficient,
should_place_next_to_port)`: centered if the labels go next to the port; inside labels otherwise go
below/right when the node has incident edges (or is compound), else centered; outside labels go
below/right for ALWAYS_SAME_SIDE, above/left for ALWAYS_OTHER_SAME_SIDE or for the first port
(`index = 0`) of a side with two ports or space-efficient placement, else below/right. -/
def labelPlacementRelation (index portCount : Nat) (anyIncidentEdges insideLabelPlacement nextToPortIfPossible
    alwaysSameSide alwaysOtherSameSide spaceEfficient shouldPlaceNextToPort : Bool) : LabelPlacementRelation :=
  let labelsNextToPort :=
    if insideLabelPlacement then shouldPlaceNextToPort else nextToPortIfPossible && shouldPlaceNextToPort
  if labelsNextToPort then .centered
  else if insideLabelPlacement then
    if anyIncidentEdges then .belowOrRight else .centered
  else if alwaysSameSide then .belowOrRight
  else if alwaysOtherSameSide || (!labelsNextToPort && (portCount == 2 || spaceEfficient) && index == 0) then
    .aboveOrLeft
  else .belowOrRight

/-- elk-rs side index of the port loops: NORTH 0, EAST 1, SOUTH 2, WEST 3, UNDEFINED 4. -/
def sideIndex : PortSide → Nat
  | .north => 0
  | .east => 1
  | .south => 2
  | .west => 3
  | .undefined => 4

/-- The new relative position of one port label (the `match port.get_side()` block of the label
loop of elk-rs `calculate_label_and_node_sizes_for_elk` / `_with_process_node`) and the next
`y_cursor`. NORTH/SOUTH: x by the relation (`± 1` beside the port), y only for constrained
(INSIDE/OUTSIDE) placement: inside past the port, its border offset and the node padding plus
spacing (`labelBorderOffset`), outside beyond the port plus the vertical spacing. EAST/WEST (and
UNDEFINED like WEST): x only for constrained placement, y stacked from `yCursor` (no gaps) if the
port has several labels, else by the relation. -/
def portLabelPosition (side : PortSide) (relation : LabelPlacementRelation) (constrainedPlacement insideLabelPlacement : Bool)
    (portSize labelSize labelPos : KVector) (portBorderOffset labelBorderOffset gapH gapV : Float)
    (labelCount : Nat) (yCursor : Float) : KVector × Float :=
  let relationX : Float := match relation with
    | .centered => (portSize.x - labelSize.x) / 2.0
    | .belowOrRight => portSize.x + 1.0
    | .aboveOrLeft => -labelSize.x - 1.0
  let relationY : Float := match relation with
    | .centered => (portSize.y - labelSize.y) / 2.0
    | .belowOrRight => portSize.y + gapV
    | .aboveOrLeft => -labelSize.y - gapV
  match side with
  | .north =>
    let y := if constrainedPlacement then
        (if insideLabelPlacement then portSize.y + portBorderOffset + labelBorderOffset else -labelSize.y - gapV)
      else labelPos.y
    (⟨relationX, y⟩, yCursor)
  | .south =>
    let y := if constrainedPlacement then
        (if insideLabelPlacement then -portBorderOffset - labelBorderOffset - labelSize.y else portSize.y + gapV)
      else labelPos.y
    (⟨relationX, y⟩, yCursor)
  | .east =>
    let x := if constrainedPlacement then
        (if insideLabelPlacement then -portBorderOffset - labelBorderOffset - labelSize.x else portSize.x + gapH)
      else labelPos.x
    if labelCount > 1 then (⟨x, yCursor⟩, yCursor + labelSize.y) else (⟨x, relationY⟩, yCursor)
  | .west | .undefined =>
    let x := if constrainedPlacement then
        (if insideLabelPlacement then portSize.x + portBorderOffset + labelBorderOffset else -labelSize.x - gapH)
      else labelPos.x
    if labelCount > 1 then (⟨x, yCursor⟩, yCursor + labelSize.y) else (⟨x, relationY⟩, yCursor)

/-- The first `y_cursor` of a port with several EAST/WEST/UNDEFINED labels: below the port plus
spacing, the whole stack above the port minus spacing, or the stack centered on the port. `0`
otherwise. -/
def initialYCursor (side : PortSide) (labelCount : Nat) (relation : LabelPlacementRelation) (portHeight totalLabelHeight gapV : Float) :
    Float :=
  if labelCount > 1 && (side == .east || side == .west || side == .undefined) then
    match relation with
    | .belowOrRight => portHeight + gapV
    | .aboveOrLeft => -totalLabelHeight - gapV
    | .centered => (portHeight - totalLabelHeight) / fl2p0
  else fl0p0

/-! ### Port label entries and stacking -/

/-- A placed port label of a constrained side (elk-rs keeps `(port, label)` adapter pairs on the
ELK path and `(port_idx, label_idx)` on the generic path; both are kept here). -/
structure PortLabelEntry (P L : Type) where
  /-- Index of the port in `NodeAdapter.getPorts()`. -/
  portIdx : Nat
  /-- The port. -/
  port : P
  /-- The label. -/
  label : L

/-- The constrained port label entries per side (WEST holds UNDEFINED ports too), in placement
order. -/
structure SideEntries (P L : Type) where
  /-- NORTH labels. -/
  north : Array (PortLabelEntry P L) := #[]
  /-- SOUTH labels. -/
  south : Array (PortLabelEntry P L) := #[]
  /-- EAST labels. -/
  east : Array (PortLabelEntry P L) := #[]
  /-- WEST and UNDEFINED labels. -/
  west : Array (PortLabelEntry P L) := #[]

namespace SideEntries

/-- Appends an entry to the list of the port's side. -/
def push (s : SideEntries P L) (side : PortSide) (e : PortLabelEntry P L) : SideEntries P L :=
  match side with
  | .north => { s with north := s.north.push e }
  | .south => { s with south := s.south.push e }
  | .east => { s with east := s.east.push e }
  | .west | .undefined => { s with west := s.west.push e }

end SideEntries

/-- elk-rs file-private `HorizontalStackConfig`. -/
structure HorizontalStackConfig where
  /-- Stack downwards (`true`) or upwards. -/
  positiveDirection : Bool
  /-- Horizontal gap between labels. -/
  gapX : Float
  /-- Vertical gap between labels. -/
  gapY : Float
  /-- Common start y of the stack (`none` = keep each label's y). -/
  startCoordinate : Option Float
  /-- Horizontal clamp bounds `(min_x, max_x)` (inside placement only). -/
  clampX : Option (Float × Float)

/-- elk-rs `inside_node_label_bounds(node)` / `inside_node_label_bounds_generic`: the bounding box
(`rectUnion`, node coordinates) of the node labels whose effective placement contains INSIDE
(label placement if set, else the node's, default `fixed`); `none` without such labels. -/
def insideNodeLabelBounds (a : GraphAdapters m G N P L E) (node : N) : m (Option ElkRectangle) := do
  let nodePlacement ← a.node.getPropertyD node CoreOptions.NODE_LABELS_PLACEMENT NodeLabelPlacement.fixed
  let mut bounds : Option ElkRectangle := none
  for label in ← a.nodeLabels node do
    let placement ← NodeLabelAndSizeCalculator.effectiveNodeLabelPlacement a label nodePlacement
    if !placement.contains .inside then continue
    let pos ← a.label.getPosition label
    let size ← a.label.getSize label
    let rect : ElkRectangle := { x := pos.x, y := pos.y, width := size.x, height := size.y }
    bounds := some (match bounds with
      | some existing => rectUnion existing rect
      | none => rect)
  return bounds

/-- elk-rs `avoid_node_label_overlap(node, port, label_pos, label_size, node_label_bounds,
label_gap_horizontal, label_gap_vertical)` (and `_generic`): a port label overlapping the inside
node label bounds moves above/below them (EAST/WEST/UNDEFINED, by comparing centers) or left/right
of them (NORTH/SOUTH) plus the spacing; a finite result is then clamped so that the label does not
end before `-node size`. -/
def avoidNodeLabelOverlap (a : GraphAdapters m G N P L E) (node : N) (port : P) (labelPos labelSize : KVector)
    (nodeLabelBounds : ElkRectangle) (gapH gapV : Float) : m KVector := do
  let portPos ← a.port.getPosition port
  let labelRect : ElkRectangle :=
    { x := portPos.x + labelPos.x, y := portPos.y + labelPos.y, width := labelSize.x, height := labelSize.y }
  if !rectOverlaps labelRect nodeLabelBounds then return labelPos
  let mut labelPos := labelPos
  match ← a.portSide port with
  | .east | .west | .undefined =>
    let labelCenter := labelRect.y + labelRect.height / fl2p0
    let nodeCenter := nodeLabelBounds.y + nodeLabelBounds.height / fl2p0
    let newAbsY := if labelCenter <= nodeCenter then nodeLabelBounds.y - labelSize.y - gapV
      else nodeLabelBounds.y + nodeLabelBounds.height + gapV
    labelPos := { labelPos with y := newAbsY - portPos.y }
  | .north | .south =>
    let labelCenter := labelRect.x + labelRect.width / fl2p0
    let nodeCenter := nodeLabelBounds.x + nodeLabelBounds.width / fl2p0
    let newAbsX := if labelCenter <= nodeCenter then nodeLabelBounds.x - labelSize.x - gapH
      else nodeLabelBounds.x + nodeLabelBounds.width + gapH
    labelPos := { labelPos with x := newAbsX - portPos.x }
  let nodeSize ← a.node.getSize node
  if labelPos.x.isNaN || labelPos.y.isNaN || labelPos.x.isInf || labelPos.y.isInf then
    return labelPos
  if labelPos.x + labelSize.x < -nodeSize.x then
    labelPos := { labelPos with x := -nodeSize.x }
  if labelPos.y + labelSize.y < -nodeSize.y then
    labelPos := { labelPos with y := -nodeSize.y }
  return labelPos

/-- elk-rs `inside_horizontal_label_clamp_bounds(node, node_width)` (and `_generic`): `[padding
left, width - padding right]` with the effective `PADDING` (defaults included), or `[spacing, width
- spacing]` (at least the padding left) when the node has its own `SPACING_LABEL_NODE`. -/
def insideHorizontalLabelClampBounds (a : GraphAdapters m G N P L E) (node : N) (nodeWidth : Float) :
    m (Float × Float) := do
  let width := fmax nodeWidth 0.0
  let padding ← a.getPadding node
  let mut minX := fmax 0.0 (fmax padding.left 0.0)
  let mut maxX := fmax (width - fmax padding.right 0.0) minX
  if ← a.node.hasProp node CoreOptions.SPACING_LABEL_NODE then
    let spacing := fmax ((← a.node.getProperty node CoreOptions.SPACING_LABEL_NODE).getD 0.0) 0.0
    minX := fmax minX spacing
    maxX := fmax (width - spacing) minX
  return (minX, maxX)

/-- elk-rs `compute_stack_start_coordinate(entries, positive_direction, gap_y)` (and `_generic`):
the lowest port bottom plus the gap (positive direction) or the highest port top minus the gap;
`none` without entries. -/
def computeStackStartCoordinate (a : GraphAdapters m G N P L E) (entries : Array (PortLabelEntry P L))
    (positiveDirection : Bool) (gapY : Float) : m (Option Float) := do
  if entries.isEmpty then return none
  if positiveDirection then
    let mut baseline := Float.negInf
    for e in entries do
      let position ← a.port.getPosition e.port
      let size ← a.port.getSize e.port
      baseline := fmax baseline (position.y + size.y)
    return some (baseline + gapY)
  else
    let mut baseline := Float.posInf
    for e in entries do
      baseline := fmin baseline (← a.port.getPosition e.port).y
    return some (baseline - gapY)

/-- Stable order of `keys` by `partial_cmp().unwrap_or(Equal)` (elk-rs `sort_by` on the entries;
the indices are sorted because the entry type has no `Inhabited` instance). -/
private def sortedOrder (keys : Array Float) : Array Nat :=
  stableSort (Array.range keys.size) fun i j => Float.comparePartial (keys.getD i fl0p0) (keys.getD j fl0p0)

/-- The `loop` of elk-rs `stack_horizontal_side_labels`: moves the label down (positive direction)
or up past every placed rectangle it overlaps (gaps included) until it overlaps none.

Deviation from elk-rs (robustness, `docs/robustness-random-graphs.md`): in the negative direction
the new coordinate `p.y - labelSize.y - gapY` can, after rounding, still satisfy the overlap test
`absoluteY + labelSize.y > p.y - gapY`; the sweep then ends on the value it started with and elk-rs
loops forever (ELK Java has no such loop and lays these graphs out). A sweep that adjusts without
changing the coordinate would repeat identically, so the loop stops there; every input on which
elk-rs terminates keeps its result. -/
private def resolveHorizontalOverlaps (placed : Array ElkRectangle) (absoluteX absoluteY : Float) (labelSize : KVector)
    (config : HorizontalStackConfig) : Float := Id.run do
  let mut absoluteY := absoluteY
  while true do
    let sweepStart := absoluteY
    let mut adjusted := false
    for p in placed do
      let horizontalOverlap := absoluteX < p.x + p.width + config.gapX && absoluteX + labelSize.x > p.x - config.gapX
      let verticalOverlap := absoluteY < p.y + p.height + config.gapY && absoluteY + labelSize.y > p.y - config.gapY
      if horizontalOverlap && verticalOverlap then
        absoluteY := if config.positiveDirection then p.y + p.height + config.gapY else p.y - labelSize.y - config.gapY
        adjusted := true
    if !adjusted || absoluteY == sweepStart then break
  return absoluteY

/-- elk-rs `stack_horizontal_side_labels(entries, config)` (and `_generic`): nothing for no entries,
or for at most two entries without clamping (Java's constrained outside placement falls back to the
simple placement). Otherwise the labels, sorted by absolute x, are clamped to the bounds widened by
their port, start at the common start coordinate and are moved along y past the labels placed
before them. -/
def stackHorizontalSideLabels (a : GraphAdapters m G N P L E) (entries : Array (PortLabelEntry P L))
    (config : HorizontalStackConfig) : m Unit := do
  if entries.isEmpty then return
  if entries.size <= 2 && config.clampX.isNone then return
  let mut keys : Array Float := #[]
  for e in entries do
    keys := keys.push ((← a.port.getPosition e.port).x + (← a.label.getPosition e.label).x)
  let mut placed : Array ElkRectangle := #[]
  for i in sortedOrder keys do
    let some e := entries[i]? | continue
    let portPosition ← a.port.getPosition e.port
    let portSize ← a.port.getSize e.port
    let labelSize ← a.label.getSize e.label
    let labelPosition ← a.label.getPosition e.label
    let mut absoluteX := portPosition.x + labelPosition.x
    if let some (minX, maxX) := config.clampX then
      -- Keep labels from drifting past the port extent at node boundaries
      let actualMinX := fmin minX portPosition.x
      let actualMaxX := fmax maxX (portPosition.x + portSize.x)
      if absoluteX < actualMinX then
        absoluteX := actualMinX
      else if absoluteX + labelSize.x > actualMaxX then
        absoluteX := actualMaxX - labelSize.x
    let startY := match config.startCoordinate with
      | some start => if config.positiveDirection then start else start - labelSize.y
      | none => portPosition.y + labelPosition.y
    let absoluteY := resolveHorizontalOverlaps placed absoluteX startY labelSize config
    a.label.setPosition e.label ⟨absoluteX - portPosition.x, absoluteY - portPosition.y⟩
    placed := placed.push { x := absoluteX, y := absoluteY, width := labelSize.x, height := labelSize.y }

/-- The `loop` of elk-rs `stack_vertical_side_labels`: moves the label down past every placed
rectangle of another port (`key`; avoid rectangles have no key and always count) it overlaps. -/
private def resolveVerticalOverlaps (placed : Array (Option Int × ElkRectangle)) (key : Int) (absoluteX absoluteY : Float)
    (labelSize : KVector) (gapX gapY : Float) : Float := Id.run do
  let mut absoluteY := absoluteY
  while true do
    let mut adjusted := false
    for (placedKey, p) in placed do
      -- Keep intra-port label spacing as defined by the label cell itself
      if placedKey == some key then continue
      let horizontalOverlap := absoluteX < p.x + p.width + gapX && absoluteX + labelSize.x > p.x - gapX
      let verticalOverlap := absoluteY < p.y + p.height + gapY && absoluteY + labelSize.y > p.y - gapY
      if horizontalOverlap && verticalOverlap then
        absoluteY := p.y + p.height + gapY
        adjusted := true
    if !adjusted then break
  return absoluteY

/-- The differences between the ELK and the generic port label pass of elk-rs. -/
structure PortLabelVariant (m : Type → Type) (P L : Type) where
  /-- `any_incident_edges`: a port has edges (generic: or compound connections) or the node is
  compound. -/
  anyIncidentEdges : Bool
  /-- `should_label_be_placed_next_to_port(port, …)` (ELK) / `_generic` for the current node. -/
  shouldPlaceNextToPort : P → m Bool
  /-- Generic `_with_process_node` path: INSIDE labels ignore `PORT_BORDER_OFFSET` (`inside_pbo`). -/
  ignoreInsideBorderOffset : Bool
  /-- Generic path: the port band filter is written as `!(bottom <= 0 || top >= height)` (differs
  from the ELK `bottom > 0 && top < height` only for NaN coordinates). -/
  genericBandFilter : Bool
  /-- The port identity used to skip labels of the same port while stacking EAST/WEST labels: the
  ELK path compares `PortAdapter.getVolatileId()` (never set by `processNode`, so all ports share
  id `0` there), the generic path the port index. -/
  portKey : PortLabelEntry P L → m Int

/-- Whether the label stays in the port band `(0, port height)` for `restrict_to_port_band`. -/
private def inPortBand (genericFilter : Bool) (labelPos labelSize : KVector) (portHeight : Float) : Bool :=
  if genericFilter then !(labelPos.y + labelSize.y <= 0.0 || labelPos.y >= portHeight)
  else labelPos.y + labelSize.y > 0.0 && labelPos.y < portHeight

/-- elk-rs `stack_vertical_side_labels(entries, gap_x, gap_y, avoid_rects, restrict_to_port_band)`
(and `_generic`): nothing for no entries or one entry without avoid rectangles. With
`restrictToPortBand` (NEXT_TO_PORT_IF_POSSIBLE) only labels inside their port band take part. The
labels, sorted by absolute y, move down past the avoid rectangles and the labels of other ports
placed before them; with `restrictToPortBand` the result is clamped to `[port y - label height,
port y + port height]`. Only y changes. -/
def stackVerticalSideLabels (a : GraphAdapters m G N P L E) (entries : Array (PortLabelEntry P L)) (gapX gapY : Float)
    (avoidRects : Array ElkRectangle) (restrictToPortBand : Bool) (v : PortLabelVariant m P L) : m Unit := do
  if entries.isEmpty then return
  if entries.size <= 1 && avoidRects.isEmpty then return
  let sorted ← if restrictToPortBand then
      entries.filterM fun e => do
        let portHeight := (← a.port.getSize e.port).y
        return inPortBand v.genericBandFilter (← a.label.getPosition e.label) (← a.label.getSize e.label) portHeight
    else pure entries
  if sorted.isEmpty then return
  if sorted.size <= 1 && avoidRects.isEmpty then return
  let mut keys : Array Float := #[]
  for e in sorted do
    keys := keys.push ((← a.port.getPosition e.port).y + (← a.label.getPosition e.label).y)
  let mut placed : Array (Option Int × ElkRectangle) := avoidRects.map fun r => (none, r)
  for i in sortedOrder keys do
    let some e := sorted[i]? | continue
    let portPosition ← a.port.getPosition e.port
    let labelSize ← a.label.getSize e.label
    let labelPosition ← a.label.getPosition e.label
    let portHeight := (← a.port.getSize e.port).y
    let key ← v.portKey e
    let absoluteX := portPosition.x + labelPosition.x
    let minAbsY := portPosition.y - labelSize.y
    let maxAbsY := portPosition.y + portHeight
    let mut absoluteY := resolveVerticalOverlaps placed key absoluteX (portPosition.y + labelPosition.y)
      labelSize gapX gapY
    if restrictToPortBand then
      if absoluteY < minAbsY then
        absoluteY := minAbsY
      else if absoluteY > maxAbsY then
        absoluteY := maxAbsY
    a.label.setPosition e.label { labelPosition with y := absoluteY - portPosition.y }
    placed := placed.push (some key, { x := absoluteX, y := absoluteY, width := labelSize.x, height := labelSize.y })

/-- elk-rs `append_label_rects(avoid_rects, entries)` (and `_generic`): appends the absolute
rectangles (node coordinates) of the entries' labels. -/
def appendLabelRects (a : GraphAdapters m G N P L E) (avoidRects : Array ElkRectangle)
    (entries : Array (PortLabelEntry P L)) : m (Array ElkRectangle) := do
  let mut avoidRects := avoidRects
  for e in entries do
    let portPos ← a.port.getPosition e.port
    let labelPos ← a.label.getPosition e.label
    let labelSize ← a.label.getSize e.label
    avoidRects := avoidRects.push
      { x := portPos.x + labelPos.x, y := portPos.y + labelPos.y, width := labelSize.x, height := labelSize.y }
  return avoidRects

/-! ### Port label placement pass -/

/-- The settings of one port label pass (the locals of the elk-rs node loop). -/
private structure PassSettings where
  constrainedPlacement : Bool
  insideLabelPlacement : Bool
  nextToPortIfPossible : Bool
  alwaysSameSide : Bool
  alwaysOtherSameSide : Bool
  spaceEfficient : Bool
  stackLabelOverlaps : Bool
  gapH : Float
  gapV : Float
  nodeLabelBounds : Option ElkRectangle

/-- Places the labels of one port (the `for label in labels` loop of elk-rs) and records the
constrained ones in their side's entries. The label border offset is the node padding of the
port's side plus the label-port spacing. -/
private def placeLabelsOfPort (a : GraphAdapters m G N P L E) (node : N) (port : P) (portIdx : Nat) (side : PortSide)
    (relation : LabelPlacementRelation) (s : PassSettings) (v : PortLabelVariant m P L) (entries : SideEntries P L) :
    m (SideEntries P L) := do
  let portSize ← a.port.getSize port
  let portBorderOffset ← a.port.getPropertyD port CoreOptions.PORT_BORDER_OFFSET fl0p0
  let padding ← a.getPadding node
  let labelBorderOffset := match side with
    | .north => padding.top + s.gapV
    | .east => padding.right + s.gapH
    | .south => padding.bottom + s.gapV
    | .west | .undefined => padding.left + s.gapH
  let labels ← a.portLabels port
  let labelCount := labels.size
  -- Rust's `Sum for f64` starts at -0.0
  let mut totalLabelHeight : Float := -fl0p0
  if labelCount > 1 && (side == .east || side == .west || side == .undefined) then
    for label in labels do
      totalLabelHeight := totalLabelHeight + (← a.label.getSize label).y
  else
    totalLabelHeight := fl0p0
  let mut yCursor := initialYCursor side labelCount relation portSize.y totalLabelHeight s.gapV
  -- Java parity (generic path): INSIDE labels do not include the port border offset
  let borderOffset := if v.ignoreInsideBorderOffset && s.insideLabelPlacement then fl0p0 else portBorderOffset
  let mut entries := entries
  for label in labels do
    let labelPos ← a.label.getPosition label
    let labelSize ← a.label.getSize label
    let (pos, nextYCursor) := portLabelPosition side relation s.constrainedPlacement s.insideLabelPlacement
      portSize labelSize labelPos borderOffset labelBorderOffset s.gapH s.gapV labelCount yCursor
    yCursor := nextYCursor
    let mut pos := pos
    if s.stackLabelOverlaps then
      if let some bounds := s.nodeLabelBounds then
        pos ← avoidNodeLabelOverlap a node port pos labelSize bounds s.gapH s.gapV
    a.label.setPosition label pos
    if s.constrainedPlacement then
      entries := entries.push side { portIdx, port, label }
  return entries

/-- The overlap removal after all labels of a node are placed (the `if constrained_placement`
block of elk-rs): NORTH/SOUTH labels are stacked (downwards for inside NORTH and outside SOUTH)
for `PORT_LABELS` size constraints or constrained inside same-side placement, clamped inside the
node for inside placement; with inside placement and `PORT_LABELS`, WEST and EAST labels are
stacked below the inside node label bounds and the NORTH/SOUTH labels. -/
private def stackConstrainedLabels (a : GraphAdapters m G N P L E) (node : N) (nodeWidth : Float) (s : PassSettings)
    (v : PortLabelVariant m P L) (entries : SideEntries P L) : m Unit := do
  let stackConstrainedInside := s.insideLabelPlacement && (s.alwaysSameSide || s.alwaysOtherSameSide)
  if s.stackLabelOverlaps || stackConstrainedInside then
    let northPositive := s.insideLabelPlacement
    let southPositive := !s.insideLabelPlacement
    let clampX ← if s.insideLabelPlacement then some <$> insideHorizontalLabelClampBounds a node nodeWidth
      else pure none
    -- Java uses a strip overlap remover with side-dependent start coordinates; this simplified
    -- variant keeps the same directional stacking behavior (elk-rs)
    let northStart ← computeStackStartCoordinate a entries.north northPositive s.gapV
    stackHorizontalSideLabels a entries.north
      { positiveDirection := northPositive, gapX := s.gapH, gapY := s.gapV, startCoordinate := northStart, clampX }
    let southStart ← computeStackStartCoordinate a entries.south southPositive s.gapV
    stackHorizontalSideLabels a entries.south
      { positiveDirection := southPositive, gapX := s.gapH, gapY := s.gapV, startCoordinate := southStart, clampX }
  if s.insideLabelPlacement && s.stackLabelOverlaps then
    let mut avoidRects : Array ElkRectangle := #[]
    if let some bounds := s.nodeLabelBounds then
      avoidRects := avoidRects.push bounds
    avoidRects ← appendLabelRects a avoidRects entries.north
    avoidRects ← appendLabelRects a avoidRects entries.south
    stackVerticalSideLabels a entries.west s.gapH s.gapV avoidRects s.nextToPortIfPossible v
    stackVerticalSideLabels a entries.east s.gapH s.gapV avoidRects s.nextToPortIfPossible v

/-- The port label pass of elk-rs `calculate_label_and_node_sizes_for_elk` /
`calculate_label_and_node_sizes_with_process_node` for one node whose port label placement is not
fixed (run after `processNode`): every port label gets the position of `portLabelPosition` for its
port's relation (`labelPlacementRelation` with the per-side index, reversed for SOUTH/WEST like
Java's `NodeContext.comparePortContexts`), moved off the inside node labels for `PORT_LABELS`; then
the constrained (INSIDE/OUTSIDE) labels are stacked (`stackConstrainedLabels`). -/
def placePortLabels (a : GraphAdapters m G N P L E) (node : N) (placement : EnumSet PortLabelPlacement)
    (v : PortLabelVariant m P L) : m Unit := do
  let ports ← a.nodePorts node
  -- without ports there are no labels to place or stack (the pass only reads the node then)
  if ports.isEmpty then return
  let sizeConstraints ← a.node.getPropertyD node CoreOptions.NODE_SIZE_CONSTRAINTS EnumSet.empty
  let s : PassSettings := {
    constrainedPlacement := placement.contains .inside || placement.contains .outside
    insideLabelPlacement := placement.contains .inside
    nextToPortIfPossible := placement.contains .nextToPortIfPossible
    alwaysSameSide := placement.contains .alwaysSameSide
    alwaysOtherSameSide := placement.contains .alwaysOtherSameSide
    spaceEfficient := placement.contains .spaceEfficient
    stackLabelOverlaps := sizeConstraints.contains .portLabels
    gapH := ← a.node.getPropertyD node CoreOptions.SPACING_LABEL_PORT_HORIZONTAL fl1p0
    gapV := ← a.node.getPropertyD node CoreOptions.SPACING_LABEL_PORT_VERTICAL fl1p0
    nodeLabelBounds := ← insideNodeLabelBounds a node }
  let nodeWidth := (← a.node.getSize node).x
  -- Per-side port counts for the label placement relation
  let mut sideCounts : Array Nat := Array.replicate 5 0
  for port in ports do
    sideCounts := sideCounts.modify (sideIndex (← a.portSide port)) (· + 1)
  let mut sideIndices : Array Nat := Array.replicate 5 0
  let mut entries : SideEntries P L := {}
  for portIdx in [0:ports.size] do
    let some port := ports[portIdx]? | continue
    let side ← a.portSide port
    let si := sideIndex side
    let perSideIndex := sideIndices.getD si 0
    let perSideCount := sideCounts.getD si 0
    sideIndices := sideIndices.modify si (· + 1)
    -- Java's NodeContext.comparePortContexts reverses WEST/SOUTH ports in its TreeMultimap
    let effectiveIndex := if side == .south || side == .west then perSideCount - 1 - perSideIndex else perSideIndex
    let relation := labelPlacementRelation effectiveIndex perSideCount v.anyIncidentEdges s.insideLabelPlacement
      s.nextToPortIfPossible s.alwaysSameSide s.alwaysOtherSameSide s.spaceEfficient (← v.shouldPlaceNextToPort port)
    entries ← placeLabelsOfPort a node port portIdx side relation s v entries
  if s.constrainedPlacement then
    stackConstrainedLabels a node nodeWidth s v entries

/-! ### Next-to-port rules -/

/-- elk-rs `should_label_be_placed_next_to_port_generic(port, parent_is_compound,
inside_label_placement, next_to_port_if_possible)`: inside labels of a compound node go next to the
port only with NEXT_TO_PORT_IF_POSSIBLE and no compound connections, inside labels of other nodes
always; outside labels only with NEXT_TO_PORT_IF_POSSIBLE and no incident edges. -/
def shouldLabelBePlacedNextToPortGeneric (a : GraphAdapters m G N P L E) (port : P) (parentIsCompound
    insideLabelPlacement nextToPortIfPossible : Bool) : m Bool := do
  let hasIncidentEdge := !(← a.portIncomingEdges port).isEmpty || !(← a.portOutgoingEdges port).isEmpty
  let hasInsideConnections ← a.hasCompoundConnections port
  if insideLabelPlacement then
    return if parentIsCompound then nextToPortIfPossible && !hasInsideConnections else true
  else
    return nextToPortIfPossible && !hasIncidentEdge

/-- elk-rs `classify_endpoint_against_parent(endpoint, parent_node, edges_to_insides,
edges_to_somewhere_else)`: an end point at the parent node or below it is an inside edge. Returns
the updated `(edgesToInsides, edgesToSomewhereElse)`. -/
def classifyEndpointAgainstParent (g : ElkGraph) (endpoint : ConnectableId) (parent : NodeId) (flags : Bool × Bool) :
    Bool × Bool :=
  match ElkGraphUtil.connectableShapeToNode g endpoint with
  | some endpointNode =>
    let insideEdge := endpointNode == parent || ElkGraphUtil.isDescendant g endpointNode parent
    (flags.1 || insideEdge, flags.2 || !insideEdge)
  | none => flags

/-- elk-rs `classify_incident_edges_from_containment(port, parent_node, …)`: classifies the other
end points of the edges contained in the parent node that start or end at the port. Returns the
updated flags and whether such an edge exists. -/
def classifyIncidentEdgesFromContainment (g : ElkGraph) (port : PortId) (parent : NodeId) (flags : Bool × Bool) :
    (Bool × Bool) × Bool := Id.run do
  let mut flags := flags
  let mut foundIncidentEdge := false
  for e in (g.node parent).containedEdges do
    let edge := g.edge e
    if edge.sources.any (· == ConnectableId.port port) then
      foundIncidentEdge := true
      for target in edge.targets do
        flags := classifyEndpointAgainstParent g target parent flags
    if edge.targets.any (· == ConnectableId.port port) then
      foundIncidentEdge := true
      for source in edge.sources do
        flags := classifyEndpointAgainstParent g source parent flags
  return (flags, foundIncidentEdge)

/-- elk-rs `should_label_be_placed_next_to_port(port, parent, inside_label_placement,
next_to_port_if_possible)` (ELK path): the first target of each outgoing and the first source of
each incoming edge of the port is classified as inside (the parent or below) or somewhere else; a
port without edges looks at the edges contained in the parent. Inside labels of a hierarchical
parent go next to the port only with NEXT_TO_PORT_IF_POSSIBLE and no inside edges, inside labels
of other nodes always; outside labels only with NEXT_TO_PORT_IF_POSSIBLE and no edges somewhere
else. -/
def shouldLabelBePlacedNextToPortElk (g : ElkGraph) (port : PortId) (parent : NodeId)
    (insideLabelPlacement nextToPortIfPossible : Bool) : Bool := Id.run do
  let parentIsCompound := (g.node parent).isHierarchical
  let mut flags : Bool × Bool := (false, false)
  let mut foundIncidentEdge := false
  for e in (g.port port).outgoingEdges do
    foundIncidentEdge := true
    if let some target := (g.edge e).targets[0]? then
      flags := classifyEndpointAgainstParent g target parent flags
  for e in (g.port port).incomingEdges do
    foundIncidentEdge := true
    if let some source := (g.edge e).sources[0]? then
      flags := classifyEndpointAgainstParent g source parent flags
  if !foundIncidentEdge then
    flags := (classifyIncidentEdgesFromContainment g port parent flags).1
  let (edgesToInsides, edgesToSomewhereElse) := flags
  if insideLabelPlacement then
    return if parentIsCompound then nextToPortIfPossible && !edgesToInsides else true
  else
    return nextToPortIfPossible && !edgesToSomewhereElse

/-! ### Entry points -/

/-- Whether a port of the node has incoming or outgoing edges (or, with `compound`, compound
connections). -/
private def anyPortHasEdges (a : GraphAdapters m G N P L E) (ports : Array P) (compound : Bool) : m Bool := do
  for port in ports do
    if !(← a.portIncomingEdges port).isEmpty || !(← a.portOutgoingEdges port).isEmpty then return true
    if compound then
      if ← a.hasCompoundConnections port then return true
  return false

/-- elk-rs `calculate_label_and_node_sizes_for_elk(adapter)` (the ELK branch of
`calculate_label_and_node_sizes`): for each node of the graph (layout direction = the graph's
`DIRECTION`), `NodeLabelAndSizeCalculator.processNode`, then — unless the node's port label
placement is fixed — `placePortLabels` with the ELK rules (`isHierarchical` = has children,
`shouldLabelBePlacedNextToPortElk`, volatile port ids). With `fullProcessForFixed`
(`ELK_NODE_DIM_FULL_FOR_FIXED`) nodes with fixed port labels run the full `process` instead. -/
def calculateLabelAndNodeSizesForElk (a : ElkAdapters) (graph : NodeId)
    (fullProcessForFixed : Bool := NodeDimensionFlags.global.fullProcessForFixed) : ElkM Unit := do
  let layoutDirection ← a.graph.getPropertyD graph CoreOptions.DIRECTION Direction.undefined
  -- the spacings of every node without individual spacings are the graph's (or the defaults); the
  -- loop changes no property of the graph, so they are read once
  let inheritedSpacings ←
    NodeLabelAndSizeCalculator.ProcessNodeSpacings.read a { individual := none, graph := some graph }
  for node in ← a.getNodes graph do
    let placement ← a.node.getPropertyD node CoreOptions.PORT_LABELS_PLACEMENT EnumSet.empty
    if fullProcessForFixed && PortLabelPlacement.isFixed placement then
      let _ ← NodeLabelAndSizeCalculator.process a node layoutDirection
      continue
    let src ← a.spacingSource node
    let spacings ← if src.individual.isNone && src.graph == some graph then pure inheritedSpacings
      else NodeLabelAndSizeCalculator.ProcessNodeSpacings.read a src
    NodeLabelAndSizeCalculator.processNodeWith a node layoutDirection spacings
    if PortLabelPlacement.isFixed placement then continue
    let ports ← a.nodePorts node
    -- `placePortLabels` does nothing without ports
    if ports.isEmpty then continue
    let nodeIsCompound ← ElkM.withGraph fun g => (g.node node).isHierarchical
    let anyIncidentEdges := (← anyPortHasEdges a ports false) || nodeIsCompound
    let insideLabelPlacement := placement.contains .inside
    let nextToPortIfPossible := placement.contains .nextToPortIfPossible
    placePortLabels a node placement {
      anyIncidentEdges
      shouldPlaceNextToPort := fun port => ElkM.withGraph fun g =>
        shouldLabelBePlacedNextToPortElk g port node insideLabelPlacement nextToPortIfPossible
      ignoreInsideBorderOffset := false
      genericBandFilter := false
      portKey := fun e => a.port.getVolatileId e.port }

/-- elk-rs `needs_process_node_for_fixed_port_labels(node)`: effectively fixed size constraints
(empty or `{PORT_LABELS}`), fixed port label placement and a port label off `(0, 0)` (more than
`0.01` in either coordinate) — a compound node whose inner layout set its size without the port
labels placed by an earlier pass. -/
def needsProcessNodeForFixedPortLabels (a : GraphAdapters m G N P L E) (node : N) : m Bool := do
  let sizeConstraints ← a.node.getPropertyD node CoreOptions.NODE_SIZE_CONSTRAINTS EnumSet.empty
  if !NodeLabelAndSizeCalculator.hasEffectivelyFixedSizeConstraints sizeConstraints then return false
  let portLabelsPlacement ← a.node.getPropertyD node CoreOptions.PORT_LABELS_PLACEMENT EnumSet.empty
  if !PortLabelPlacement.isFixed portLabelsPlacement then return false
  for port in ← a.nodePorts node do
    for label in ← a.portLabels port do
      let pos ← a.label.getPosition label
      if pos.x.abs > fl0p01 || pos.y.abs > fl0p01 then return true
  return false

/-- elk-rs `calculate_label_and_node_sizes_with_process_node(adapter)` (the non-ELK branch of
`calculate_label_and_node_sizes`). With `useFullProcess` (default: `ELK_NODE_DIM_SKIP_FULL_PROCESS`
unset): per node the full `NodeLabelAndSizeCalculator.process`, preceded by `processNode` if
`needsProcessNodeForFixedPortLabels`. Otherwise per node `processNode` and — unless the port label
placement is fixed — `placePortLabels` with the generic rules (`COMPOUND_NODE_PROPERTY`, compound
connections, port indices, INSIDE labels without border offset). -/
def calculateLabelAndNodeSizesWith [MonadExcept IO.Error m] (a : GraphAdapters m G N P L E) (graph : G)
    (useFullProcess : Bool) : m Unit := do
  let layoutDirection ← a.graph.getPropertyD graph CoreOptions.DIRECTION Direction.undefined
  if useFullProcess then
    for node in ← a.getNodes graph do
      if ← needsProcessNodeForFixedPortLabels a node then
        -- Compute the size including the port label space, then place the ports (fixed size)
        NodeLabelAndSizeCalculator.processNode a node layoutDirection
        let _ ← NodeLabelAndSizeCalculator.process a node layoutDirection
      else
        let _ ← NodeLabelAndSizeCalculator.process a node layoutDirection
    return
  for node in ← a.getNodes graph do
    NodeLabelAndSizeCalculator.processNode a node layoutDirection
    let placement ← a.node.getPropertyD node CoreOptions.PORT_LABELS_PLACEMENT EnumSet.empty
    if PortLabelPlacement.isFixed placement then continue
    let nodeIsCompound ← a.node.getPropertyD node COMPOUND_NODE_PROPERTY false
    let anyIncidentEdges := (← anyPortHasEdges a (← a.nodePorts node) true) || nodeIsCompound
    let insideLabelPlacement := placement.contains .inside
    let nextToPortIfPossible := placement.contains .nextToPortIfPossible
    placePortLabels a node placement {
      anyIncidentEdges
      shouldPlaceNextToPort := fun port =>
        shouldLabelBePlacedNextToPortGeneric a port nodeIsCompound insideLabelPlacement nextToPortIfPossible
      ignoreInsideBorderOffset := true
      genericBandFilter := true
      portKey := fun e => pure (Int.ofNat e.portIdx) }

/-- `NodeDimensionCalculation.calculateLabelAndNodeSizes(adapter)`: calculates node sizes, places
ports and node/port labels of all nodes of the graph (elk-rs non-ELK branch,
`calculateLabelAndNodeSizesWith a graph NodeDimensionFlags.global.useFullProcess`). Make sure the
port lists are sorted (`sortPortLists`). Used by the layered `LabelAndNodeSizeProcessor`; Java's
exact pipeline without the elk-rs `processNode` pre-pass is `calculateLabelAndNodeSizesJava` (elk-rs
takes `calculateLabelAndNodeSizesForElk` for an `ElkGraph` by downcasting the adapter). -/
def calculateLabelAndNodeSizes [MonadExcept IO.Error m] (a : GraphAdapters m G N P L E) (graph : G) : m Unit :=
  calculateLabelAndNodeSizesWith a graph NodeDimensionFlags.global.useFullProcess

/-- Java `NodeDimensionCalculation.calculateLabelAndNodeSizes(adapter)` exactly as ELK Java runs it
(`NodeLabelAndSizeCalculator.process(adapter)`): for every node of the graph, in
`GraphAdapter.getNodes()` order, the full cell system pipeline
`NodeLabelAndSizeCalculator.process(graph, node, true, false)` (layout direction = the graph's
`DIRECTION`). Used by `NodeMicroLayout`. Throws like Java for invalid port or node label placements
(`NodeContext.new`) and for ports without side (`PortContextCreator`), at the first such node.
Unlike elk-rs (`calculateLabelAndNodeSizesForElk` / `calculateLabelAndNodeSizesWith`) there is no
`processNode` pass and no simplified port label placement. Make sure the port lists are sorted
(`sortPortLists`). -/
def calculateLabelAndNodeSizesJava [MonadExcept IO.Error m] (a : GraphAdapters m G N P L E) (graph : G) :
    m Unit := do
  let layoutDirection ← a.graph.getPropertyD graph CoreOptions.DIRECTION Direction.undefined
  for node in ← a.getNodes graph do
    let _ ← NodeLabelAndSizeCalculator.process a node layoutDirection

/-- `NodeDimensionCalculation.calculateNodeMargins(adapter)`: node margins of all nodes of the
graph with a default `NodeMarginCalculator` (everything included). -/
def calculateNodeMargins (a : GraphAdapters m G N P L E) (graph : G) : m Unit :=
  NodeMarginCalculator.new.process a graph

/-- `NodeDimensionCalculation.getNodeMarginCalculator(adapter)`: a configurable calculator (run it
with `NodeMarginCalculator.process a graph`; the Lean calculator does not store the adapter). -/
def getNodeMarginCalculator (_a : GraphAdapters m G N P L E) : NodeMarginCalculator :=
  NodeMarginCalculator.new

/-- `NodeDimensionCalculation.sortPortLists(adapter)`: sorts the port lists of all nodes of the
graph clockwise (`NodeAdapter.sortPortList`, only for nodes with order-fixing port constraints). -/
def sortPortLists (a : GraphAdapters m G N P L E) (graph : G) : m Unit := do
  for node in ← a.getNodes graph do
    a.sortPortList node

end NodeDimensionCalculation

end Elk.Alg.Common.NodeSpacing
