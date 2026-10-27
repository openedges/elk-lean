import Elk.Alg.Layered.Graph
import Elk.Core.Util.Java
/-!
# `LabelAndNodeSizeProcessor` — phase 3 external port dummy label placement

The "Phase 3: External port dummy label placement" helper group of elk-rs
`intermediate/label_and_node_size_processor.rs` (Java `LabelAndNodeSizeProcessor
.placeExternalPortDummyLabels`, `computePortLabelBox`, `labelNextToPort`): the labels of the port of
an external port dummy are placed so that the node margins computed later reserve enough space for
them; they are placed for real once the hierarchical node is laid out.

Rust and Java agree; the label box is built inline (Java `computePortLabelBox`).
-/
namespace Elk.Alg.Layered.Intermediate.LabelAndNodeSize

open Elk.Graph Elk.Core.Math Elk.Core.Options Elk.Core.Util Elk.Alg.Layered.Graph Elk.Alg.Layered.Options
  LayeredM

/-- Rust `label_next_to_port(dummy_port, inside_labels, place_next_to_port_if_possible)`: only with
`NEXT_TO_PORT_IF_POSSIBLE`; inside labels when the port has no edges, outside labels when the port
is not connected to external nodes. -/
def labelNextToPort (dummyPort : LPortId) (insideLabels placeNextToPortIfPossible : Bool) : LayeredM Bool := do
  if !placeNextToPortIfPossible then return false
  let pt ← getPort dummyPort
  if insideLabels then
    return pt.incomingEdges.isEmpty && pt.outgoingEdges.isEmpty
  return !pt.connectedToExternalNodes

/-- The y coordinate of a label box centred next to the port (`treat_as_group`: the whole box,
otherwise the first label). -/
private def centredLabelBoxY (dummySize dummyPortPos : KVector) (labelBoxHeight firstLabelHeight : Float)
    (treatAsGroup : Bool) : Float :=
  let labelHeight := if treatAsGroup then labelBoxHeight else firstLabelHeight
  (dummySize.y - labelHeight) / 2.0 - dummyPortPos.y

/-- Rust `place_external_port_dummy_labels(dummy, graph_port_label_placement,
place_next_to_port_if_possible, treat_as_group)`: computes the label box of the dummy's (only)
port (max width, heights plus `SPACING_LABEL_LABEL`), positions it by the `EXT_PORT_SIDE` and the
graph's INSIDE/OUTSIDE port label placement (relative to the port), and stacks the labels
vertically from the box's top-left corner. -/
def placeExternalPortDummyLabels (dummy : LNodeId) (graphPortLabelPlacement : EnumSet PortLabelPlacement)
    (placeNextToPortIfPossible treatAsGroup : Bool) : LayeredM Unit := do
  let nd ← getNode dummy
  let labelPortSpacingHorizontal := nd.props.getD LayeredOptions.SPACING_LABEL_PORT_HORIZONTAL 0.0
  let labelPortSpacingVertical := nd.props.getD LayeredOptions.SPACING_LABEL_PORT_VERTICAL 0.0
  let labelLabelSpacing := nd.props.getD LayeredOptions.SPACING_LABEL_LABEL 0.0
  let dummySize := nd.size
  -- External port dummies have exactly one port
  let some dummyPort := nd.ports[0]? | return
  let pt ← getPort dummyPort
  let dummyPortPos := pt.position
  let portLabels := pt.labels
  if portLabels.isEmpty then return
  let mut labelBox : ElkRectangle := {}
  for label in portLabels do
    let sz := (← getLabel label).size
    labelBox := { labelBox with width := fmax labelBox.width sz.x, height := labelBox.height + sz.y }
  labelBox := { labelBox with height := labelBox.height + (portLabels.size.toFloat - 1.0) * labelLabelSpacing }
  let firstLabelHeight ← match portLabels[0]? with
    | some l => do pure (← getLabel l).size.y
    | none => pure 0.0
  let extPortSide := nd.internal.extPortSide
  if graphPortLabelPlacement.contains .inside then
    match extPortSide with
    | .north =>
      labelBox := { labelBox with
        x := (dummySize.x - labelBox.width) / 2.0 - dummyPortPos.x
        y := labelPortSpacingVertical }
    | .south =>
      labelBox := { labelBox with
        x := (dummySize.x - labelBox.width) / 2.0 - dummyPortPos.x
        y := -labelPortSpacingVertical - labelBox.height }
    | .east =>
      let y := if (← labelNextToPort dummyPort true placeNextToPortIfPossible) then
          centredLabelBoxY dummySize dummyPortPos labelBox.height firstLabelHeight treatAsGroup
        else dummySize.y + labelPortSpacingVertical - dummyPortPos.y
      labelBox := { labelBox with y := y }
      labelBox := { labelBox with x := -labelPortSpacingHorizontal - labelBox.width }
    | .west =>
      let y := if (← labelNextToPort dummyPort true placeNextToPortIfPossible) then
          centredLabelBoxY dummySize dummyPortPos labelBox.height firstLabelHeight treatAsGroup
        else dummySize.y + labelPortSpacingVertical - dummyPortPos.y
      labelBox := { labelBox with y := y }
      labelBox := { labelBox with x := labelPortSpacingHorizontal }
    | .undefined => pure ()
  else if graphPortLabelPlacement.contains .outside then
    match extPortSide with
    | .north | .south =>
      labelBox := { labelBox with x := dummyPortPos.x + labelPortSpacingHorizontal }
    | .east | .west =>
      let y := if (← labelNextToPort dummyPort false placeNextToPortIfPossible) then
          centredLabelBoxY dummySize dummyPortPos labelBox.height firstLabelHeight treatAsGroup
        else dummyPortPos.y + labelPortSpacingVertical
      labelBox := { labelBox with y := y }
    | .undefined => pure ()
  -- Place the labels
  let mut currentY := labelBox.y
  for label in portLabels do
    let labelSizeY := (← getLabel label).size.y
    let x := labelBox.x
    let y := currentY
    modifyLabel label fun l => { l with position := ⟨x, y⟩ }
    currentY := currentY + (labelSizeY + labelLabelSpacing)

end Elk.Alg.Layered.Intermediate.LabelAndNodeSize
