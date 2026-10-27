import Elk.Alg.Layered.Graph
import Elk.Core.Util.Java
import Elk.Core.Util.Sort
/-!
# `LabelAndNodeSizeProcessor` — phase 1 port placement helpers

The "Phase 1: Port placement" helper group of elk-rs
`intermediate/label_and_node_size_processor.rs` that places ports along the node sides without
resizing the node: `property_with_graph_default`, `node_property_or_graph_default`,
`port_alignment_for_side`, `adjust_ports_on_side` (FIXED_POS border snapping),
`place_ports_fixed_ratio_on_side`, `place_inside_self_loop_ports`, `update_node_margin`, the
`PortPlacementContext` margin setup (`setup_horizontal_port_margins`,
`setup_vertical_port_margins`), `place_ports_on_side` and the clockwise port reordering
(`ensure_clockwise_port_order`, `reverse_west_and_south_side`, …). These helpers have no Java
counterpart: elk-rs uses them in its (environment gated) phase-2 workaround after
`NodeDimensionCalculation.calculateLabelAndNodeSizes`.

The Rust functions lock one node and read its properties through `get_property`/`has_property`;
the Lean helpers read the `LNode` value (`props`, `internal`) and the arena. Every `f64`
expression keeps the Rust operand order; `f64::max`/`min` are `fmax`/`fmin`.
-/
namespace Elk.Alg.Layered.Intermediate.LabelAndNodeSize

open Elk.Graph Elk.Core.Math Elk.Core.Options Elk.Core.Util Elk.Alg.Layered.Graph Elk.Alg.Layered.Options
  LayeredM

/-! ## Property helpers -/

/-- Rust `property_with_graph_default(node, property, graph_default)`: the node's individual spacing
for the property (`SPACING_INDIVIDUAL` stored and containing it), else the node's own stored value,
else `graphDefault` (the property's default is never used). -/
def propertyWithGraphDefault {α : Type} [PropCodec α] (nd : LNode) (p : Property α) (graphDefault : α) : α := Id.run do
  if nd.props.has CoreOptions.SPACING_INDIVIDUAL then
    if let some individual := nd.props.get CoreOptions.SPACING_INDIVIDUAL then
      if individual.props.has p then
        if let some v := individual.props.get p then return v
  if nd.props.has p then
    if let some v := nd.props.get p then return v
  return graphDefault

/-- Rust `node_property_or_graph_default(node, property, graph_default)`: the node's stored value,
else `graphDefault`. -/
def nodePropertyOrGraphDefault {α : Type} [PropCodec α] (nd : LNode) (p : Property α) (graphDefault : α) : α :=
  if nd.props.has p then (nd.props.get p).getD graphDefault else graphDefault

/-- Rust `port_alignment_for_side(node, side)`: the side specific `PORT_ALIGNMENT_<SIDE>`, else
`PORT_ALIGNMENT_DEFAULT`, else `DISTRIBUTED`. -/
def portAlignmentForSide (nd : LNode) (side : PortSide) : PortAlignment :=
  let specific : Option PortAlignment := match side with
    | .north => nd.props.get CoreOptions.PORT_ALIGNMENT_NORTH
    | .south => nd.props.get CoreOptions.PORT_ALIGNMENT_SOUTH
    | .east => nd.props.get CoreOptions.PORT_ALIGNMENT_EAST
    | .west => nd.props.get CoreOptions.PORT_ALIGNMENT_WEST
    | .undefined => none
  match specific with
  | some al => al
  | none => (nd.props.get CoreOptions.PORT_ALIGNMENT_DEFAULT).getD .distributed

/-- `PORT_BORDER_OFFSET` of a port (`0` when not set). -/
@[inline] def portBorderOffset (pt : LPort) : Float := pt.props.getD CoreOptions.PORT_BORDER_OFFSET 0.0

/-- Rust `node_has_non_zero_border_offset(node)`: some port has `|PORT_BORDER_OFFSET| > EPSILON`. -/
def nodeHasNonZeroBorderOffset (node : LNodeId) : LayeredM Bool := do
  for port in (← getNode node).ports do
    if (portBorderOffset (← getPort port)).abs > Float.epsilon then return true
  return false

/-! ## Fixed port positions -/

/-- Rust `adjust_ports_on_side(node, side, width, height)`: snaps the border coordinate of the
side's ports (`port_side_view`) to the node border, respecting `PORT_BORDER_OFFSET`; the coordinate
along the side is kept. -/
def adjustPortsOnSide (node : LNodeId) (side : PortSide) (width height : Float) : LayeredM Unit := do
  let ports ← withArena (·.nodePortSideView node side)
  for port in ports do
    modifyPort port fun pt =>
      let portSize := pt.size
      let borderOffset := portBorderOffset pt
      let pos := pt.position
      let pos := match side with
        | .north => { pos with y := -portSize.y - borderOffset }
        | .south => { pos with y := height + borderOffset }
        | .east => { pos with x := width + borderOffset }
        | .west => { pos with x := -portSize.x - borderOffset }
        | .undefined => pos
      { pt with position := pos }

/-- Rust `place_ports_fixed_ratio_on_side(node, side, width, height)`: positions the side's ports
at `PORT_RATIO_OR_POSITION` times the side length, on the border (with `PORT_BORDER_OFFSET`). -/
def placePortsFixedRatioOnSide (node : LNodeId) (side : PortSide) (width height : Float) : LayeredM Unit := do
  let ports ← withArena (·.nodePortSideView node side)
  for port in ports do
    modifyPort port fun pt =>
      let portSize := pt.size
      let borderOffset := portBorderOffset pt
      let ratio := pt.internal.portRatioOrPosition
      let pos := match side with
        | .north => ⟨width * ratio, -portSize.y - borderOffset⟩
        | .south => ⟨width * ratio, height + borderOffset⟩
        | .east => ⟨width + borderOffset, height * ratio⟩
        | .west => ⟨-portSize.x - borderOffset, height * ratio⟩
        | .undefined => pt.position
      { pt with position := pos }

/-- Rust `place_inside_self_loop_ports(node, width, height)`: NORTH/SOUTH ports are snapped to the
border (`adjust_ports_on_side`), WEST/EAST ports are centred vertically outside the node. -/
def placeInsideSelfLoopPorts (node : LNodeId) (width height : Float) : LayeredM Unit := do
  adjustPortsOnSide node .north width height
  adjustPortsOnSide node .south width height
  let centerY := height / 2.0
  let westPorts ← withArena (·.nodePortSideView node .west)
  for port in westPorts do
    modifyPort port fun pt => { pt with position := ⟨-pt.size.x, centerY - pt.size.y / 2.0⟩ }
  let eastPorts ← withArena (·.nodePortSideView node .east)
  for port in eastPorts do
    modifyPort port fun pt => { pt with position := ⟨width, centerY - pt.size.y / 2.0⟩ }

/-! ## Node margin -/

/-- The margin accumulator of Rust `update_node_margin` (`include_rect` closure). -/
structure MarginAccumulator where
  top : Float := 0.0
  right : Float := 0.0
  bottom : Float := 0.0
  left : Float := 0.0

/-- Rust `include_rect(x, y, width, height)` of `update_node_margin`. -/
def MarginAccumulator.includeRect (m : MarginAccumulator) (nodeWidth nodeHeight x y width height : Float) :
    MarginAccumulator := Id.run do
  let mut m := m
  if x < 0.0 then m := { m with left := fmax m.left (-x) }
  if y < 0.0 then m := { m with top := fmax m.top (-y) }
  let right := x + width
  if right > nodeWidth then m := { m with right := fmax m.right (right - nodeWidth) }
  let bottom := y + height
  if bottom > nodeHeight then m := { m with bottom := fmax m.bottom (bottom - nodeHeight) }
  return m

/-- Rust `update_node_margin(node)`: recomputes all four margins from the node labels, the ports
and the port labels that stick out of the node (no spacing, no edge labels). -/
def updateNodeMargin (node : LNodeId) : LayeredM Unit := do
  let nd ← getNode node
  let nodeWidth := nd.size.x
  let nodeHeight := nd.size.y
  let mut m : MarginAccumulator := {}
  for label in nd.labels do
    let lb ← getLabel label
    m := m.includeRect nodeWidth nodeHeight lb.position.x lb.position.y lb.size.x lb.size.y
  for port in nd.ports do
    let pt ← getPort port
    let portPos := pt.position
    let portSize := pt.size
    m := m.includeRect nodeWidth nodeHeight portPos.x portPos.y portSize.x portSize.y
    for label in pt.labels do
      let lb ← getLabel label
      m := m.includeRect nodeWidth nodeHeight (portPos.x + lb.position.x) (portPos.y + lb.position.y) lb.size.x lb.size.y
  let acc := m
  modifyNode node fun x =>
    { x with margin := { x.margin with top := acc.top, right := acc.right, bottom := acc.bottom, left := acc.left } }

/-! ## Port placement contexts -/

/-- Rust `PortPlacementContext`: a port with its placement margin and label information. -/
structure PortPlacementContext where
  port : LPortId
  margin : ElkMargin := {}
  labelsNextToPort : Bool := false
  labelSize : KVector := {}
  labelCount : Nat := 0
  deriving Inhabited

/-- Rust `port_label_min_size(port, label_label_spacing, port_labels_fixed)`: the size of the
port's labels stacked vertically (max width, heights plus spacings) and their number; `(0, 0)` and
`0` for fixed port labels or a port without labels. -/
def portLabelMinSize (port : LPortId) (labelLabelSpacing : Float) (portLabelsFixed : Bool) :
    LayeredM (KVector × Nat) := do
  if portLabelsFixed then return ({}, 0)
  let labels := (← getPort port).labels
  if labels.isEmpty then return ({}, 0)
  let mut maxWidth := 0.0
  let mut totalHeight := 0.0
  let mut count : Nat := 0
  for label in labels do
    let size := (← getLabel label).size
    maxWidth := fmax maxWidth size.x
    totalHeight := totalHeight + size.y
    count := count + 1
  if count > 1 then
    totalHeight := totalHeight + labelLabelSpacing * (count - 1).toFloat
  return (⟨maxWidth, totalHeight⟩, count)

/-- Rust `labels_bounds_for_port(port)`: the bounding box of the port's labels (relative to the
port); `none` without labels or for non-finite minima. -/
def labelsBoundsForPort (port : LPortId) : LayeredM (Option ElkRectangle) := do
  let labels := (← getPort port).labels
  if labels.isEmpty then return none
  let mut minX := Float.posInf
  let mut minY := Float.posInf
  let mut maxX := Float.negInf
  let mut maxY := Float.negInf
  for label in labels do
    let lb ← getLabel label
    let pos := lb.position
    let size := lb.size
    minX := fmin minX pos.x
    minY := fmin minY pos.y
    maxX := fmax maxX (pos.x + size.x)
    maxY := fmax maxY (pos.y + size.y)
  if !minX.isFinite || !minY.isFinite then return none
  return some (ElkRectangle.ofValues minX minY (maxX - minX) (maxY - minY))

/-- Rust `labels_next_to_port(placement, port_labels_next_to_port, node_is_compound,
has_compound_connections, has_edges)`: INSIDE labels are next to the port unless the node is
compound (then only with `NEXT_TO_PORT_IF_POSSIBLE` and no compound connections); OUTSIDE labels
only with `NEXT_TO_PORT_IF_POSSIBLE` and without edges. -/
def labelsNextToPort (placement : EnumSet PortLabelPlacement) (portLabelsNextToPort nodeIsCompound
    hasCompoundConnections hasEdges : Bool) : Bool :=
  if placement.contains .inside then
    if nodeIsCompound then portLabelsNextToPort && !hasCompoundConnections else true
  else if placement.contains .outside then
    if portLabelsNextToPort then !hasEdges else false
  else false

/-- The flags shared by `setup_horizontal_port_margins` / `setup_vertical_port_margins`. -/
structure PortMarginSettings where
  portLabelsOutside : Bool
  alwaysSameSide : Bool
  alwaysOtherSameSide : Bool
  spaceEfficient : Bool
  uniformPortSpacing : Bool
  portLabelsFixed : Bool
  portLabelsTreatAsGroup : Bool

/-- `space_efficient_labels` of the margin setups. -/
@[inline] def PortMarginSettings.spaceEfficientLabels (s : PortMarginSettings) (count : Nat) : Bool :=
  !s.alwaysSameSide && !s.alwaysOtherSameSide && (s.spaceEfficient || count == 2)

/-- Horizontal per-context margin of `setup_horizontal_port_margins` (first loop body). -/
private def horizontalContextMargin (ctx : PortPlacementContext) (s : PortMarginSettings)
    (portLabelSpacingHorizontal : Float) : LayeredM PortPlacementContext := do
  let labelWidth := ctx.labelSize.x
  if labelWidth > 0.0 then
    if ctx.labelsNextToPort then
      let portWidth := (← getPort ctx.port).size.x
      if labelWidth > portWidth then
        let overhang := (labelWidth - portWidth) / 2.0
        return { ctx with margin := { ctx.margin with left := overhang, right := overhang } }
      return ctx
    else
      return { ctx with margin := { ctx.margin with right := portLabelSpacingHorizontal + labelWidth } }
  else if s.portLabelsFixed then
    if let some bounds ← labelsBoundsForPort ctx.port then
      let portWidth := (← getPort ctx.port).size.x
      let mut margin := ctx.margin
      if bounds.x < 0.0 then margin := { margin with left := -bounds.x }
      if bounds.x + bounds.width > portWidth then margin := { margin with right := bounds.x + bounds.width - portWidth }
      return { ctx with margin := margin }
  return ctx

/-- Rust `setup_horizontal_port_margins(contexts, …)`: left/right margins of NORTH/SOUTH port
contexts from their labels (overhang of labels next to the port, label width plus spacing
otherwise, the fixed label bounds); OUTSIDE labels drop the outer margins (and the first context's
right margin for space efficient labels not next to the port); uniform port spacing gives every
context the maximum margins. -/
def setupHorizontalPortMargins (contexts : Array PortPlacementContext) (s : PortMarginSettings)
    (portLabelSpacingHorizontal : Float) : LayeredM (Array PortPlacementContext) := do
  let spaceEfficientLabels := s.spaceEfficientLabels contexts.size
  let mut contexts ← contexts.mapM fun ctx => horizontalContextMargin ctx s portLabelSpacingHorizontal
  if s.portLabelsOutside && !contexts.isEmpty then
    let rightmost := contexts.size - 1
    contexts := contexts.modify 0 fun c => { c with margin := { c.margin with left := 0.0 } }
    contexts := contexts.modify rightmost fun c => { c with margin := { c.margin with right := 0.0 } }
    if spaceEfficientLabels && !(contexts[0]?.map (·.labelsNextToPort)).getD false then
      contexts := contexts.modify 0 fun c => { c with margin := { c.margin with right := 0.0 } }
  if s.uniformPortSpacing && !contexts.isEmpty then
    let mut maxLeft := 0.0
    let mut maxRight := 0.0
    for ctx in contexts do
      maxLeft := fmax maxLeft ctx.margin.left
      maxRight := fmax maxRight ctx.margin.right
    let (l, r) := (maxLeft, maxRight)
    contexts := contexts.map fun c => { c with margin := { c.margin with left := l, right := r } }
    if s.portLabelsOutside then
      let rightmost := contexts.size - 1
      contexts := contexts.modify 0 fun c => { c with margin := { c.margin with left := 0.0 } }
      contexts := contexts.modify rightmost fun c => { c with margin := { c.margin with right := 0.0 } }
  return contexts

/-- Vertical per-context margin of `setup_vertical_port_margins` (first loop body). -/
private def verticalContextMargin (ctx : PortPlacementContext) (s : PortMarginSettings)
    (portLabelSpacingVertical : Float) : LayeredM PortPlacementContext := do
  let labelHeight := ctx.labelSize.y
  if labelHeight > 0.0 then
    if ctx.labelsNextToPort then
      let pt ← getPort ctx.port
      let portHeight := pt.size.y
      if labelHeight > portHeight then
        if s.portLabelsTreatAsGroup || ctx.labelCount <= 1 then
          let overhang := (labelHeight - portHeight) / 2.0
          return { ctx with margin := { ctx.margin with top := overhang, bottom := overhang } }
        else
          let firstLabelHeight ← match pt.labels[0]? with
            | some l => do pure (← getLabel l).size.y
            | none => pure 0.0
          let firstOverhang := (firstLabelHeight - portHeight) / 2.0
          return { ctx with margin := { ctx.margin with
            top := fmax firstOverhang 0.0
            bottom := labelHeight - firstOverhang - portHeight } }
      return ctx
    else
      return { ctx with margin := { ctx.margin with bottom := portLabelSpacingVertical + labelHeight } }
  else if s.portLabelsFixed then
    if let some bounds ← labelsBoundsForPort ctx.port then
      let portHeight := (← getPort ctx.port).size.y
      let mut margin := ctx.margin
      if bounds.y < 0.0 then margin := { margin with top := -bounds.y }
      if bounds.y + bounds.height > portHeight then margin := { margin with bottom := bounds.y + bounds.height - portHeight }
      return { ctx with margin := margin }
  return ctx

/-- Rust `setup_vertical_port_margins(contexts, …)`: the EAST/WEST counterpart of
`setupHorizontalPortMargins` (top/bottom margins; labels next to the port that are not treated as a
group are centred on the first label). -/
def setupVerticalPortMargins (contexts : Array PortPlacementContext) (s : PortMarginSettings)
    (portLabelSpacingVertical : Float) : LayeredM (Array PortPlacementContext) := do
  let spaceEfficientLabels := s.spaceEfficientLabels contexts.size
  let mut contexts ← contexts.mapM fun ctx => verticalContextMargin ctx s portLabelSpacingVertical
  if s.portLabelsOutside && !contexts.isEmpty then
    let bottommost := contexts.size - 1
    contexts := contexts.modify 0 fun c => { c with margin := { c.margin with top := 0.0 } }
    contexts := contexts.modify bottommost fun c => { c with margin := { c.margin with bottom := 0.0 } }
    if spaceEfficientLabels && !(contexts[0]?.map (·.labelsNextToPort)).getD false then
      contexts := contexts.modify 0 fun c => { c with margin := { c.margin with bottom := 0.0 } }
  if s.uniformPortSpacing && !contexts.isEmpty then
    let mut maxTop := 0.0
    let mut maxBottom := 0.0
    for ctx in contexts do
      maxTop := fmax maxTop ctx.margin.top
      maxBottom := fmax maxBottom ctx.margin.bottom
    let (t, b) := (maxTop, maxBottom)
    contexts := contexts.map fun c => { c with margin := { c.margin with top := t, bottom := b } }
    if s.portLabelsOutside then
      let bottommost := contexts.size - 1
      contexts := contexts.modify 0 fun c => { c with margin := { c.margin with top := 0.0 } }
      contexts := contexts.modify bottommost fun c => { c with margin := { c.margin with bottom := 0.0 } }
  return contexts

/-- The start/end surrounding spacing along a side (Rust inline `match side` of
`place_ports_on_side` / `required_axis_length_for_side`): NORTH/SOUTH use left/right; EAST/WEST use
top/bottom reduced by the vertical label-port spacing (Java parity: the cell system's
`updateVerticalInsidePortLabelCellPadding` always subtracts it), clamped at `0`. -/
def surroundingForSide (side : PortSide) (surrounding : ElkMargin) (labelPortSpacingVertical : Float) : Float × Float :=
  match side with
  | .north | .south => (surrounding.left, surrounding.right)
  | .east | .west =>
    let borderOffset := labelPortSpacingVertical
    (fmax (surrounding.top - borderOffset) 0.0, fmax (surrounding.bottom - borderOffset) 0.0)
  | .undefined => (0.0, 0.0)

/-- `(margin_start, margin_end)` of a context along the side. -/
@[inline] def marginAlongSide (side : PortSide) (m : ElkMargin) : Float × Float :=
  match side with
  | .north | .south => (m.left, m.right)
  | .east | .west => (m.top, m.bottom)
  | .undefined => (0.0, 0.0)

/-- The port size along the side. -/
@[inline] def axisSizeAlongSide (side : PortSide) (size : KVector) : Float :=
  match side with
  | .north | .south => size.x
  | .east | .west => size.y
  | .undefined => 0.0

/-- Rust `ordered_ports` of `place_ports_on_side`: WEST ports with CENTER alignment and a fixed
order are rotated right by one; other WEST and all SOUTH ports are reversed (Java
`NodeContext.comparePortContexts` sorts them by descending volatile id). -/
def orderedPortsForSide (ports : Array LPortId) (side : PortSide) (alignment : PortAlignment)
    (constraints : PortConstraints) : Array LPortId :=
  match side with
  | .west =>
    if alignment == .center && constraints.isOrderFixed then
      if ports.size > 1 then
        match ports.back? with
        | some last => #[last] ++ ports.pop
        | none => ports
      else ports
    else ports.reverse
  | .south => ports.reverse
  | _ => ports

/-- The node values read once by `place_ports_on_side`. -/
private structure SidePlacementSettings where
  alignment : PortAlignment
  portSpacing : Float
  surroundingSpacing : ElkMargin
  constraints : PortConstraints
  sizeConstraints : EnumSet SizeConstraint
  sizeOptions : EnumSet SizeOptions
  portLabelPlacement : EnumSet PortLabelPlacement
  portLabelsTreatAsGroup : Bool
  labelLabelSpacing : Float
  labelPortSpacingHorizontal : Float
  labelPortSpacingVertical : Float
  nodeIsCompound : Bool

/-- The settings block at the start of Rust `place_ports_on_side` (one node lock). -/
private def sidePlacementSettings (nd : LNode) (side : PortSide) (graphPortSpacing : Float)
    (graphPortsSurrounding : ElkMargin) : SidePlacementSettings :=
  { alignment := portAlignmentForSide nd side
    portSpacing := propertyWithGraphDefault nd CoreOptions.SPACING_PORT_PORT graphPortSpacing
    surroundingSpacing := propertyWithGraphDefault nd CoreOptions.SPACING_PORTS_SURROUNDING graphPortsSurrounding
    constraints := nd.props.getD CoreOptions.PORT_CONSTRAINTS PortConstraints.undefined
    sizeConstraints := nd.props.getD CoreOptions.NODE_SIZE_CONSTRAINTS EnumSet.empty
    sizeOptions := nd.props.getD CoreOptions.NODE_SIZE_OPTIONS EnumSet.empty
    portLabelPlacement := nd.props.getD CoreOptions.PORT_LABELS_PLACEMENT EnumSet.empty
    portLabelsTreatAsGroup := nd.props.getD CoreOptions.PORT_LABELS_TREAT_AS_GROUP true
    labelLabelSpacing := propertyWithGraphDefault nd CoreOptions.SPACING_LABEL_LABEL 0.0
    labelPortSpacingHorizontal := propertyWithGraphDefault nd CoreOptions.SPACING_LABEL_PORT_HORIZONTAL 0.0
    labelPortSpacingVertical := propertyWithGraphDefault nd CoreOptions.SPACING_LABEL_PORT_VERTICAL 0.0
    nodeIsCompound := nd.internal.compoundNode }

/-- The placement contexts of the ordered ports (Rust `contexts` of `place_ports_on_side`). -/
private def createContexts (ports : Array LPortId) (st : SidePlacementSettings) (portLabelsFixed : Bool) :
    LayeredM (Array PortPlacementContext) := do
  let portLabelsNextToPort := st.portLabelPlacement.contains .nextToPortIfPossible
  let mut contexts : Array PortPlacementContext := Array.mkEmpty ports.size
  for port in ports do
    let pt ← getPort port
    let hasEdges := !(pt.incomingEdges.isEmpty && pt.outgoingEdges.isEmpty)
    let hasCompoundConnections := pt.internal.insideConnections
    let labelsNext := labelsNextToPort st.portLabelPlacement portLabelsNextToPort st.nodeIsCompound
      hasCompoundConnections hasEdges
    let (labelSize, labelCount) ← portLabelMinSize port st.labelLabelSpacing portLabelsFixed
    contexts := contexts.push { port, labelsNextToPort := labelsNext, labelSize, labelCount }
  return contexts

/-- The start position and the space between ports of `place_ports_on_side` (the alignment block
after the placement size is known). -/
def sideStartAndSpacing (alignment : PortAlignment) (count : Nat) (placementSize availableSpace
    surroundingStart portSpacing : Float) (portsOverhang : Bool) : Float × Float := Id.run do
  let mut alignment := alignment
  let mut placementSize := placementSize
  if (alignment == .distributed || alignment == .justified) && count == 1 then
    if alignment == .distributed then
      placementSize := placementSize - 2.0 * portSpacing
    alignment := .center
  let mut currentPos := surroundingStart
  let mut spaceBetweenPorts := portSpacing
  if availableSpace < placementSize && !portsOverhang then
    if alignment == .distributed then
      spaceBetweenPorts := spaceBetweenPorts + (availableSpace - placementSize) / (count.toFloat + 1.0)
      currentPos := currentPos + spaceBetweenPorts
    else if count > 1 then
      spaceBetweenPorts := spaceBetweenPorts + (availableSpace - placementSize) / (count.toFloat - 1.0)
  else
    if availableSpace < placementSize && (alignment == .distributed || alignment == .justified) then
      if alignment == .distributed then
        placementSize := placementSize - 2.0 * portSpacing
      alignment := .center
    match alignment with
    | .begin => pure ()
    | .center => currentPos := currentPos + (availableSpace - placementSize) / 2.0
    | .«end» => currentPos := currentPos + (availableSpace - placementSize)
    | .distributed =>
      let additional := (availableSpace - placementSize) / (count.toFloat + 1.0)
      spaceBetweenPorts := spaceBetweenPorts + fmax additional 0.0
      currentPos := currentPos + spaceBetweenPorts
    | .justified =>
      if count > 1 then
        let additional := (availableSpace - placementSize) / (count.toFloat - 1.0)
        spaceBetweenPorts := spaceBetweenPorts + fmax additional 0.0
  return (currentPos, spaceBetweenPorts)

/-- Rust `place_ports_on_side(node, side, width, height, graph_port_spacing,
graph_ports_surrounding)`: distributes the side's ports (`port_side_view`, ordered by
`orderedPortsForSide`) along the side by the port alignment, with the port spacing, the surrounding
spacing and (with `PORT_LABELS` size constraints) the label margins of `setup_*_port_margins`;
ports are placed on the border (with `PORT_BORDER_OFFSET`). A one-port DISTRIBUTED/JUSTIFIED side
and a side without room (unless `PORTS_OVERHANG`) fall back to CENTER; without room and without
overhang the spacing is squeezed instead. -/
def placePortsOnSide (node : LNodeId) (side : PortSide) (width height graphPortSpacing : Float)
    (graphPortsSurrounding : ElkMargin) : LayeredM Unit := do
  let nd ← getNode node
  let ports ← withArena (·.nodePortSideView node side)
  let st := sidePlacementSettings nd side graphPortSpacing graphPortsSurrounding
  let count := ports.size
  if count == 0 then return
  if side == .undefined then return
  let length := match side with
    | .north | .south => width
    | _ => height
  let (surroundingStart, surroundingEnd) := surroundingForSide side st.surroundingSpacing st.labelPortSpacingVertical
  let orderedPorts := orderedPortsForSide ports side st.alignment st.constraints
  let portLabelsFixed := PortLabelPlacement.isFixed st.portLabelPlacement
  let settings : PortMarginSettings :=
    { portLabelsOutside := st.portLabelPlacement.contains .outside
      alwaysSameSide := st.portLabelPlacement.contains .alwaysSameSide
      alwaysOtherSameSide := st.portLabelPlacement.contains .alwaysOtherSameSide
      spaceEfficient := st.portLabelPlacement.contains .spaceEfficient
      uniformPortSpacing := st.sizeOptions.contains .uniformPortSpacing
      portLabelsFixed := portLabelsFixed
      portLabelsTreatAsGroup := st.portLabelsTreatAsGroup }
  let mut contexts ← createContexts orderedPorts st portLabelsFixed
  if st.sizeConstraints.contains .portLabels then
    match side with
    | .north | .south => contexts ← setupHorizontalPortMargins contexts settings st.labelPortSpacingHorizontal
    | .east | .west => contexts ← setupVerticalPortMargins contexts settings st.labelPortSpacingVertical
    | .undefined => pure ()
  let portsOverhang := st.sizeOptions.contains .portsOverhang
  let mut placementSize := 0.0
  for index in [0:contexts.size] do
    let some ctx := contexts[index]? | continue
    let portSize := (← getPort ctx.port).size
    let (marginStart, marginEnd) := marginAlongSide side ctx.margin
    let axisSize := axisSizeAlongSide side portSize
    placementSize := placementSize + (marginStart + axisSize + marginEnd)
    if index + 1 < contexts.size then
      placementSize := placementSize + st.portSpacing
  if st.alignment == .distributed then
    placementSize := placementSize + 2.0 * st.portSpacing
  let availableSpace := length - surroundingStart - surroundingEnd
  let (start, spaceBetweenPorts) := sideStartAndSpacing st.alignment count placementSize availableSpace
    surroundingStart st.portSpacing portsOverhang
  let mut currentPos := start
  for ctx in contexts do
    let pt ← getPort ctx.port
    let portSize := pt.size
    let borderOffset := portBorderOffset pt
    let (marginStart, marginEnd) := marginAlongSide side ctx.margin
    let axisSize := axisSizeAlongSide side portSize
    let axisPosition := currentPos + marginStart
    let pos := pt.position
    let pos : KVector := match side with
      | .north => ⟨axisPosition, -portSize.y - borderOffset⟩
      | .south => ⟨axisPosition, height + borderOffset⟩
      | .east => ⟨width + borderOffset, axisPosition⟩
      | .west => ⟨-portSize.x - borderOffset, axisPosition⟩
      | .undefined => pos
    modifyPort ctx.port fun p => { p with position := pos }
    currentPos := currentPos + (marginStart + axisSize + marginEnd + spaceBetweenPorts)

/-! ## Clockwise port order -/

/-- Rust `side_ordinal(side)`: UNDEFINED 0, NORTH 1, EAST 2, SOUTH 3, WEST 4. -/
def sideOrdinal : PortSide → Nat
  | .undefined => 0
  | .north => 1
  | .east => 2
  | .south => 3
  | .west => 4

/-- Rust `find_port_side_range(ports, side)`: `[low, high)` of the ports on `side` in a list
sorted by side (`sides` are the ports' sides). -/
def findPortSideRange (sides : Array PortSide) (side : PortSide) : Nat × Nat := Id.run do
  if sides.isEmpty then return (0, 0)
  let lb := sideOrdinal side
  let hb := lb + 1
  let mut lowIdx := 0
  while lowIdx < sides.size && sideOrdinal (sides.getD lowIdx .undefined) < lb do
    lowIdx := lowIdx + 1
  let mut highIdx := lowIdx
  while highIdx < sides.size && sideOrdinal (sides.getD highIdx .undefined) < hb do
    highIdx := highIdx + 1
  return (lowIdx, highIdx)

/-- Rust `reverse_range(ports, low, high)`: reverses `ports[low..high)` (ranges of at most one port
are kept). -/
def reverseRange {α : Type} (ports : Array α) (lowIdx highIdx : Nat) : Array α :=
  if highIdx ≤ lowIdx + 1 then ports
  else ports.extract 0 lowIdx ++ (ports.extract lowIdx highIdx).reverse ++ ports.extract highIdx ports.size

/-- Rust `reverse_west_and_south_side(ports)`: reverses the SOUTH and the WEST range of a list
sorted by side (Java's `comparePortContexts` orders both descending). -/
def reverseWestAndSouthSide (ports : Array LPortId) (sideOf : LPortId → PortSide) : Array LPortId := Id.run do
  if ports.size ≤ 1 then return ports
  let (southLow, southHigh) := findPortSideRange (ports.map sideOf) .south
  let ports := reverseRange ports southLow southHigh
  let (westLow, westHigh) := findPortSideRange (ports.map sideOf) .west
  return reverseRange ports westLow westHigh

/-- Rust `should_skip_clockwise_reorder_for_phase2f(node)`: nodes with a non-zero port border
offset and both SOUTH and WEST ports keep their port order. -/
def shouldSkipClockwiseReorderForPhase2f (node : LNodeId) : LayeredM Bool := do
  if !(← nodeHasNonZeroBorderOffset node) then return false
  let mut hasSouth := false
  let mut hasWest := false
  for port in (← getNode node).ports do
    match (← getPort port).side with
    | .south => hasSouth := true
    | .west => hasWest := true
    | _ => pure ()
  return hasSouth && hasWest

/-- Rust `ensure_clockwise_port_order(node, port_constraints)`: for side-fixed but not
order-fixed constraints and nodes without dummy edges (a connected edge without `ORIGIN`), the
ports are sorted by side (stable, Rust ties by index), the SOUTH and WEST ranges reversed, and the
port sides cached. -/
def ensureClockwisePortOrder (node : LNodeId) (portConstraints : PortConstraints) : LayeredM Unit := do
  if !portConstraints.isSideFixed || portConstraints.isOrderFixed then return
  let ports := (← getNode node).ports
  if ports.size ≤ 1 then return
  for port in ports do
    for edge in (← getPort port).connectedEdges do
      if (← getEdge edge).internal.origin.isNone then return
  let a ← get
  let sideOf : LPortId → PortSide := fun p => (a.port p).side
  let sorted := stableSort ports fun p q => Ord.compare (sideOrdinal (sideOf p)) (sideOrdinal (sideOf q))
  let sorted := reverseWestAndSouthSide sorted sideOf
  modifyNode node fun x => { x with ports := sorted }
  cachePortSides node

end Elk.Alg.Layered.Intermediate.LabelAndNodeSize
