import Elk.Alg.Layered.Intermediate.LabelAndNodeSize.PortPlacement
/-!
# `LabelAndNodeSizeProcessor` — phase 1 port-driven node sizing

The node sizing part of the "Phase 1: Port placement" helper group of elk-rs
`intermediate/label_and_node_size_processor.rs`: `required_axis_length_for_side`,
`required_inside_port_axis_for_side`, `enforce_port_driven_minimum_size`,
`enforce_inside_port_label_minimum_size` and `apply_inside_north_south_label_post_resize_adjustments`.
They grow (or, when allowed, shrink) a node so that its ports and inside port labels fit, before
the ports are placed by `placePortsOnSide`. No Java counterpart (elk-rs phase-2 workaround).
-/
namespace Elk.Alg.Layered.Intermediate.LabelAndNodeSize

open Elk.Graph Elk.Core.Math Elk.Core.Options Elk.Core.Util Elk.Alg.Layered.Graph Elk.Alg.Layered.Options
  LayeredM

/-- The extent of a port along the side including the parts of its labels that stick out of the
port (the `include_fixed_label_margins` branch of `required_axis_length_for_side`; the first label
initialises the bounds). -/
private def portExtentWithLabels (a : LGraphArena) (side : PortSide) (pt : LPort) (axisSize : Float) : Float := Id.run do
  let mut minX := 0.0
  let mut minY := 0.0
  let mut maxX := 0.0
  let mut maxY := 0.0
  let mut hasLabel := false
  for label in pt.labels do
    let lb := a.label label
    let (bx0, by0, bx1, by1) := (lb.position.x, lb.position.y, lb.position.x + lb.size.x, lb.position.y + lb.size.y)
    if !hasLabel then
      minX := bx0
      minY := by0
      maxX := bx1
      maxY := by1
      hasLabel := true
    else
      minX := fmin minX bx0
      minY := fmin minY by0
      maxX := fmax maxX bx1
      maxY := fmax maxY by1
  if !hasLabel then return axisSize
  match side with
  | .north | .south =>
    let left := fmax (-minX) 0.0
    let right := fmax (maxX - pt.size.x) 0.0
    return axisSize + left + right
  | .east | .west =>
    let top := fmax (-minY) 0.0
    let bottom := fmax (maxY - pt.size.y) 0.0
    return axisSize + top + bottom
  | .undefined => return axisSize

/-- Rust `required_axis_length_for_side(node, side, graph_port_spacing, graph_ports_surrounding,
include_fixed_label_margins)`: the side length needed for the side's ports: surrounding spacing
(EAST/WEST reduced by `SPACING_LABEL_PORT_VERTICAL`), the port extents (optionally with the
overhang of fixed labels), the port spacings, and two more spacings for DISTRIBUTED alignment. -/
def requiredAxisLengthForSide (a : LGraphArena) (node : LNodeId) (side : PortSide) (graphPortSpacing : Float)
    (graphPortsSurrounding : ElkMargin) (includeFixedLabelMargins : Bool) : Float := Id.run do
  let nd := a.node node
  let ports := a.nodePortSideView node side
  if ports.isEmpty then return 0.0
  let count := ports.size
  let alignment := portAlignmentForSide nd side
  let portSpacing := propertyWithGraphDefault nd CoreOptions.SPACING_PORT_PORT graphPortSpacing
  let surroundingSpacing := propertyWithGraphDefault nd CoreOptions.SPACING_PORTS_SURROUNDING graphPortsSurrounding
  let labelPortSpacingVertical := nd.props.getD CoreOptions.SPACING_LABEL_PORT_VERTICAL 1.0
  let (surroundingStart, surroundingEnd) := surroundingForSide side surroundingSpacing labelPortSpacingVertical
  let mut base := fmax surroundingStart 0.0 + fmax surroundingEnd 0.0
  for port in ports do
    let pt := a.port port
    let axisSize := axisSizeAlongSide side pt.size
    let extent := if !includeFixedLabelMargins then axisSize else portExtentWithLabels a side pt axisSize
    base := base + extent
  if count > 1 then
    base := base + fmax portSpacing 0.0 * (count.toFloat - 1.0)
  match alignment with
  | .distributed => return base + 2.0 * fmax portSpacing 0.0
  | _ => return base

/-- Rust `required_inside_port_axis_for_side(node, side, graph_port_spacing,
graph_ports_surrounding)`: like `requiredAxisLengthForSide`, but each port takes the larger of its
size and its largest label along the side, and the DISTRIBUTED spacings are only added for more
than one port. -/
def requiredInsidePortAxisForSide (a : LGraphArena) (node : LNodeId) (side : PortSide) (graphPortSpacing : Float)
    (graphPortsSurrounding : ElkMargin) : Float := Id.run do
  let nd := a.node node
  let ports := a.nodePortSideView node side
  if ports.isEmpty then return 0.0
  let portSpacing := fmax (propertyWithGraphDefault nd CoreOptions.SPACING_PORT_PORT graphPortSpacing) 0.0
  let surroundingSpacing := propertyWithGraphDefault nd CoreOptions.SPACING_PORTS_SURROUNDING graphPortsSurrounding
  let labelPortSpacingVertical := nd.props.getD CoreOptions.SPACING_LABEL_PORT_VERTICAL 1.0
  let (surroundingStart, surroundingEnd) := surroundingForSide side surroundingSpacing labelPortSpacingVertical
  let mut required := fmax surroundingStart 0.0 + fmax surroundingEnd 0.0
  for port in ports do
    let pt := a.port port
    let labelExtent := pt.labels.foldl (fun acc l => fmax acc (axisSizeAlongSide side (a.label l).size)) 0.0
    let axisSize := axisSizeAlongSide side pt.size
    required := required + fmax axisSize labelExtent
  if ports.size > 1 then
    required := required + portSpacing * (ports.size.toFloat - 1.0)
    if portAlignmentForSide nd side == .distributed then
      required := required + 2.0 * portSpacing
  return required

/-- Applies a new node size when it differs from the old one by more than `EPSILON` in either
coordinate (the tail of both `enforce_*_minimum_size` functions); returns the new size. -/
private def applyAdjustedSize (node : LNodeId) (nodeSize adjusted : KVector) : LayeredM KVector := do
  if (adjusted.x - nodeSize.x).abs > Float.epsilon || (adjusted.y - nodeSize.y).abs > Float.epsilon then
    modifyNode node fun x => { x with size := ⟨adjusted.x, adjusted.y⟩ }
  return adjusted

/-- `adjusted` of the `enforce_*_minimum_size` functions: with `shrink` the positive requirements
replace the size, otherwise the size only grows. -/
@[inline] def adjustSize (nodeSize : KVector) (requiredWidth requiredHeight : Float) (shrink : Bool) : KVector :=
  if shrink then
    ⟨if requiredWidth > 0.0 then requiredWidth else nodeSize.x, if requiredHeight > 0.0 then requiredHeight else nodeSize.y⟩
  else
    ⟨fmax nodeSize.x requiredWidth, fmax nodeSize.y requiredHeight⟩

/-- Rust `enforce_port_driven_minimum_size(node, node_size, graph_port_spacing,
graph_ports_surrounding, include_port_labels, allow_shrink)`: width = max of the NORTH/SOUTH
requirements, height = max of the EAST/WEST requirements (fixed label overhangs included when
`includePortLabels` and the port labels are fixed). -/
def enforcePortDrivenMinimumSize (node : LNodeId) (nodeSize : KVector) (graphPortSpacing : Float)
    (graphPortsSurrounding : ElkMargin) (includePortLabels allowShrink : Bool) : LayeredM KVector := do
  let a ← get
  let nd := a.node node
  let fixedPortLabels := includePortLabels &&
    PortLabelPlacement.isFixed (nd.props.getD CoreOptions.PORT_LABELS_PLACEMENT EnumSet.empty)
  let req := fun side => requiredAxisLengthForSide a node side graphPortSpacing graphPortsSurrounding fixedPortLabels
  let requiredWidth := fmax (req .north) (req .south)
  let requiredHeight := fmax (req .east) (req .west)
  applyAdjustedSize node nodeSize (adjustSize nodeSize requiredWidth requiredHeight allowShrink)

/-- The per-side maxima collected by `enforce_inside_port_label_minimum_size`. -/
private structure InsideLabelStats where
  maxWest : Float := 0.0
  maxEast : Float := 0.0
  maxNorth : Float := 0.0
  maxSouth : Float := 0.0
  hasEastWestLabels : Bool := false
  hasNorthSouthLabels : Bool := false
  maxLabelHeightWest : Float := 0.0
  maxLabelHeightEast : Float := 0.0
  maxPortHeightWest : Float := 0.0
  maxPortHeightEast : Float := 0.0
  westPortTotalHeight : Float := 0.0
  eastPortTotalHeight : Float := 0.0
  westPortCount : Nat := 0
  eastPortCount : Nat := 0

/-- The port loop of `enforce_inside_port_label_minimum_size` (UNDEFINED counts as WEST). -/
private def insideLabelStats (a : LGraphArena) (ports : Array LPortId) : InsideLabelStats := Id.run do
  let mut s : InsideLabelStats := {}
  for port in ports do
    let pt := a.port port
    let side := pt.side
    let portSize := pt.size
    match side with
    | .west | .undefined =>
      s := { s with westPortCount := s.westPortCount + 1, westPortTotalHeight := s.westPortTotalHeight + portSize.y,
                    maxPortHeightWest := fmax s.maxPortHeightWest portSize.y }
    | .east =>
      s := { s with eastPortCount := s.eastPortCount + 1, eastPortTotalHeight := s.eastPortTotalHeight + portSize.y,
                    maxPortHeightEast := fmax s.maxPortHeightEast portSize.y }
    | _ => pure ()
    for label in pt.labels do
      let labelSize := (a.label label).size
      match side with
      | .west | .undefined =>
        s := { s with maxWest := fmax s.maxWest labelSize.x, maxLabelHeightWest := fmax s.maxLabelHeightWest labelSize.y,
                      hasEastWestLabels := true }
      | .east =>
        s := { s with maxEast := fmax s.maxEast labelSize.x, maxLabelHeightEast := fmax s.maxLabelHeightEast labelSize.y,
                      hasEastWestLabels := true }
      | .north => s := { s with maxNorth := fmax s.maxNorth labelSize.y, hasNorthSouthLabels := true }
      | .south => s := { s with maxSouth := fmax s.maxSouth labelSize.y, hasNorthSouthLabels := true }
  return s

/-- The height a side needs for its ports with label gaps (`west_required_height` /
`east_required_height`). -/
@[inline] private def sideRequiredHeight (count : Nat) (totalHeight maxLabelHeight maxPortHeight
    labelGapVertical : Float) : Float :=
  if count > 0 then
    let requiredGap := fmax (maxLabelHeight + labelGapVertical - maxPortHeight) 0.0
    totalHeight + (count.toFloat + 1.0) * requiredGap
  else 0.0

/-- Rust `enforce_inside_port_label_minimum_size(node, node_size, graph_port_spacing,
graph_ports_surrounding, allow_shrink)`: for INSIDE port labels, the size that fits the widest
WEST/EAST labels next to each other (with padding and two horizontal gaps), the NORTH/SOUTH label
strips and the stacked EAST/WEST ports with label gaps, at least the inside port axis
requirements, and at least the current height plus symmetric NORTH/SOUTH label strips. Shrinking
is prevented by `NODE_LABELS` size constraints and by labels on both EAST/WEST and NORTH/SOUTH
sides. -/
def enforceInsidePortLabelMinimumSize (node : LNodeId) (nodeSize : KVector) (graphPortSpacing : Float)
    (graphPortsSurrounding : ElkMargin) (allowShrink : Bool) : LayeredM KVector := do
  let a ← get
  let nd := a.node node
  let placement := nd.props.getD CoreOptions.PORT_LABELS_PLACEMENT EnumSet.empty
  if !placement.contains .inside then return nodeSize
  let sizeConstraints := nd.props.getD CoreOptions.NODE_SIZE_CONSTRAINTS EnumSet.empty
  let padding := nd.padding
  let labelGapHorizontal := nd.props.getD CoreOptions.SPACING_LABEL_PORT_HORIZONTAL 1.0
  let labelGapVertical := nd.props.getD CoreOptions.SPACING_LABEL_PORT_VERTICAL 1.0
  let keepCurrentSizeOnShrink := sizeConstraints.contains .nodeLabels
  let req := fun side => requiredInsidePortAxisForSide a node side graphPortSpacing graphPortsSurrounding
  let requiredWidthFromPortLayout := fmax (req .north) (req .south)
  let requiredHeightFromPortLayout := fmax (req .east) (req .west)
  let s := insideLabelStats a nd.ports
  if s.maxWest == 0.0 && s.maxEast == 0.0 && s.maxNorth == 0.0 && s.maxSouth == 0.0 then return nodeSize
  let requiredWidth := padding.left + padding.right + 2.0 * labelGapHorizontal + s.maxWest + s.maxEast
  let northSouthHeight := 2.0 * labelGapVertical + s.maxNorth + s.maxSouth
  -- Java parity: inside N/S labels reserve symmetric strips above and below the content area
  let northSouthAdditiveHeight :=
    if s.hasNorthSouthLabels then 2.0 * (labelGapVertical + fmax s.maxNorth s.maxSouth) else 0.0
  let westRequiredHeight := sideRequiredHeight s.westPortCount s.westPortTotalHeight s.maxLabelHeightWest
    s.maxPortHeightWest labelGapVertical
  let eastRequiredHeight := sideRequiredHeight s.eastPortCount s.eastPortTotalHeight s.maxLabelHeightEast
    s.maxPortHeightEast labelGapVertical
  let requiredWidth := fmax requiredWidth (padding.left + padding.right + requiredWidthFromPortLayout)
  let requiredHeight :=
    fmax (fmax (padding.top + padding.bottom + fmax (fmax northSouthHeight westRequiredHeight) eastRequiredHeight)
        (padding.top + padding.bottom + requiredHeightFromPortLayout))
      (nodeSize.y + northSouthAdditiveHeight)
  let preventShrinkForMixedInsideSides := s.hasEastWestLabels && s.hasNorthSouthLabels
  let preventShrink := keepCurrentSizeOnShrink || preventShrinkForMixedInsideSides
  applyAdjustedSize node nodeSize (adjustSize nodeSize requiredWidth requiredHeight (allowShrink && !preventShrink))

/-- Rust `apply_inside_north_south_label_post_resize_adjustments(node, initial_size, node_size,
has_inside_north_south_port_labels)`: after a resize the node labels move by half the width change
(and half a positive height change with inside NORTH/SOUTH port labels); with inside NORTH/SOUTH
port labels those labels are re-centred horizontally on their ports. -/
def applyInsideNorthSouthLabelPostResizeAdjustments (node : LNodeId) (initialSize nodeSize : KVector)
    (hasInsideNorthSouthPortLabels : Bool) : LayeredM Unit := do
  let deltaWidth := nodeSize.x - initialSize.x
  let deltaHeight := nodeSize.y - initialSize.y
  if deltaWidth.abs ≤ Float.epsilon && deltaHeight.abs ≤ Float.epsilon then return
  let nd ← getNode node
  let labelShiftX := if deltaWidth.abs > Float.epsilon then deltaWidth / 2.0 else 0.0
  let labelShiftY := if hasInsideNorthSouthPortLabels && deltaHeight > Float.epsilon then deltaHeight / 2.0 else 0.0
  if labelShiftX.abs > Float.epsilon || labelShiftY.abs > Float.epsilon then
    for label in nd.labels do
      modifyLabel label fun l => { l with position := ⟨l.position.x + labelShiftX, l.position.y + labelShiftY⟩ }
  if !hasInsideNorthSouthPortLabels then return
  for port in nd.ports do
    let pt ← getPort port
    if pt.side != .north && pt.side != .south then continue
    let portWidth := pt.size.x
    for label in pt.labels do
      modifyLabel label fun l => { l with position := { l.position with x := (portWidth - l.size.x) / 2.0 } }

end Elk.Alg.Layered.Intermediate.LabelAndNodeSize
