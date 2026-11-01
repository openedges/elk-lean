import Elk.Alg.Layered.LayeredPhases
import Elk.Alg.Layered.Graph.LGraphUtil
import Elk.Core.Util.Java
import Elk.Core.Util.FloatConst
open Elk.Core.Util.FloatConst
/-!
# `org.eclipse.elk.alg.layered.intermediate.LabelManagementProcessor`

Port of elk-rs `intermediate/label_management_processor.rs` (Java `LabelManagementProcessor`):
"Invokes a potentially registered label manager on labels. This processor has two modes of
operation. The first mode seeks out node labels, port labels, and edge labels. This mode is used for
the first label management run before computing node sizes. The second mode manages center edge
labels, which requires node sizes to be fixed."

Slot: before phase 4. `IntermediateProcessorStrategy.END_NODE_PORT_LABEL_MANAGEMENT_PROCESSOR` is
`LabelManagementProcessor(false)`, `CENTER_LABEL_MANAGEMENT_PROCESSOR` is
`LabelManagementProcessor(true)`; both have the trace name `LabelManagementProcessor` (Rust
`type_name`).

Unreachable from the public API (agent COV): Java adds this processor only when the graph has a
`labels.labelManager` (`GraphConfigurator`: `getProperty(LABEL_MANAGER) != null`), and that option
is an `OBJECT` option whose class (`ILabelManager`) is no `IDataObject`: ELK Java's JSON importer
throws `IllegalStateException: IDataType class expected for layout option
org.eclipse.elk.labels.labelManager` for every value (elkjs: no `ElkReflect` factory either), and
elk-lean's importer throws the same exception. The processor is therefore only reachable from Lean
code that sets a manager directly (the unit tests). The elk-rs behaviour kept there: in center mode
a label dummy without represented labels manages its own labels (Java: an empty list, i.e. size
`(0, 0)` plus thickness and spacing).

The label manager: Rust calls `ILabelManager::manage_label_size(&origin, target_width)` with the
label's `InternalProperties::ORIGIN` (an `Origin` value) as the `&dyn Any` label. The Lean core type
`Elk.Core.Labels.ILabelManager` takes a `Dynamic` label, and `LabelManagementOptions.LABEL_MANAGER` is a
`Dynamic`; turning either into a typed value needs `TypeName` instances, which can only be created
with `unsafe` (forbidden). The processor is therefore written against the local `LabelManager`
structure that mirrors the Rust trait with `Origin` labels, and `labelManagerOf` (the only reader of
`LABEL_MANAGER`) returns `none`.

TODO(core-labels): resolve the graph's `LabelManagementOptions.LABEL_MANAGER` to a `LabelManager` in
`labelManagerOf` once the core label manager can be stored as a typed value (JSON inputs never carry
a label manager, so the parity pipeline is unaffected).
-/

namespace Elk.Alg.Layered.Intermediate

open Elk.Graph Elk.Core Elk.Core.Alg Elk.Core.Math Elk.Core.Options Elk.Core.Util Elk.Alg.Layered
  Elk.Alg.Layered.Graph Elk.Alg.Layered.Options LayeredM

namespace LabelManagementProcessor

/-- The Rust trait `ILabelManager` as used by the processor: `manageLabelSize origin targetWidth`
returns the new label size (or `none` if the label was not changed). `origin` is the label's
`InternalProperties.ORIGIN`. `IO` lets managers keep state like the Java ones (which shorten the
label text). -/
structure LabelManager where
  /-- `ILabelManager.manageLabelSize(label, targetWidth)`. -/
  manageLabelSize : Origin → Float → IO (Option KVector)

/-- `MIN_WIDTH_PORT_LABELS`. -/
def MIN_WIDTH_PORT_LABELS : Float := 20.0
/-- `MIN_WIDTH_NODE_LABELS`. -/
def MIN_WIDTH_NODE_LABELS : Float := 40.0
/-- `MIN_WIDTH_EDGE_LABELS`. -/
def MIN_WIDTH_EDGE_LABELS : Float := 60.0

/-- `layeredGraph.getProperty(LabelManagementOptions.LABEL_MANAGER)`.
TODO(core-labels): always `none` (see the module doc). -/
def labelManagerOf (_graph : LGraphId) : LayeredM (Option LabelManager) := pure none

/-- Rust `do_manage_labels(manager, labels, target_width, label_label_spacing, vertical)`: lets the
manager resize every label that has an `ORIGIN` (width and height swapped in vertical layouts) and
returns the space the labels need when stacked (vertical layouts: side by side) with
`labelLabelSpacing` between them. -/
def doManageLabels (labelManager : LabelManager) (labels : Array LLabelId) (targetWidth labelLabelSpacing : Float)
    (verticalLayout : Bool) : LayeredM KVector := do
  let mut required : KVector := ⟨0.0, 0.0⟩
  if labels.isEmpty then return required
  for label in labels do
    if let some origin := (← getLabel label).internal.origin then
      if let some newSize ← labelManager.manageLabelSize origin targetWidth then
        let size : KVector := if verticalLayout then ⟨newSize.y, newSize.x⟩ else ⟨newSize.x, newSize.y⟩
        modifyLabel label fun l => { l with size := size }
    let labelSize := (← getLabel label).size
    if verticalLayout then
      required := ⟨required.x + (labelLabelSpacing + labelSize.x), fmax required.y labelSize.y⟩
    else
      required := ⟨fmax required.x labelSize.x, required.y + (labelLabelSpacing + labelSize.y)⟩
  if verticalLayout then
    required := { required with x := required.x - labelLabelSpacing }
  else
    required := { required with y := required.y - labelLabelSpacing }
  return required

/-- Rust `do_manage_attached_comment_labels(manager, comment_nodes, min_width, vertical)`. -/
def doManageAttachedCommentLabels (labelManager : LabelManager) (commentNodes : Array LNodeId) (minWidthNodeLabels : Float)
    (verticalLayout : Bool) : LayeredM Unit := do
  for commentNode in commentNodes do
    let labels := (← getNode commentNode).labels
    if labels.isEmpty then continue
    let _ ← doManageLabels labelManager labels minWidthNodeLabels fl0p0 verticalLayout

/-- Rust `manage_non_center_labels(graph, manager, label_label_spacing, vertical)`: labels of `NORMAL`
nodes, of their ports and of their attached comments, and the labels of every node's outgoing edges
(the edge list is taken before the node is processed). -/
def manageNonCenterLabels (graph : LGraphId) (labelManager : LabelManager) (labelLabelSpacing : Float)
    (verticalLayout : Bool) : LayeredM Unit := do
  let layers := (← getGraph graph).layers
  for layer in layers do
    let nodes := (← getLayer layer).nodes
    for node in nodes do
      let nd ← getNode node
      let outgoingEdges ← withArena (·.nodeOutgoingEdges node)
      if nd.type == .normal then
        let _ ← doManageLabels labelManager nd.labels MIN_WIDTH_NODE_LABELS labelLabelSpacing verticalLayout
        for port in nd.ports do
          let labels := (← getPort port).labels
          let _ ← doManageLabels labelManager labels MIN_WIDTH_PORT_LABELS labelLabelSpacing verticalLayout
        doManageAttachedCommentLabels labelManager nd.internal.topComments MIN_WIDTH_NODE_LABELS verticalLayout
        doManageAttachedCommentLabels labelManager nd.internal.bottomComments MIN_WIDTH_NODE_LABELS verticalLayout
      for edge in outgoingEdges do
        let labels := (← getEdge edge).labels
        let _ ← doManageLabels labelManager labels MIN_WIDTH_EDGE_LABELS fl0p0 verticalLayout

/-- Rust `manage_center_labels(graph, manager, edge_label_spacing, label_label_spacing, direction,
vertical)`: per layer the target width is `max(MIN_WIDTH_EDGE_LABELS, widest NORMAL node)`; each label
dummy's represented labels (else its own labels) are managed and the dummy is resized to the required
space plus the first connected edge's thickness and the edge label spacing. -/
def manageCenterLabels (graph : LGraphId) (labelManager : LabelManager) (edgeLabelSpacing labelLabelSpacing : Float)
    (direction : Direction) (verticalLayout : Bool) : LayeredM Unit := do
  let layers := (← getGraph graph).layers
  for layer in layers do
    let maxWidth := fmax MIN_WIDTH_EDGE_LABELS (← LGraphUtil.findMaxNonDummyNodeWidth layer direction false)
    let nodes := (← getLayer layer).nodes
    for node in nodes do
      let nd ← getNode node
      if nd.type != .label then continue
      let connectedEdges ← withArena (·.nodeConnectedEdges node)
      let edgeThickness ← match connectedEdges[0]? with
        | some e => pure ((← getEdge e).props.getD CoreOptions.EDGE_THICKNESS fl1p0)
        | none => pure fl1p0
      let labels := if nd.internal.representedLabels.isEmpty then nd.labels else nd.internal.representedLabels
      let required ← doManageLabels labelManager labels maxWidth labelLabelSpacing verticalLayout
      modifyNode node fun n => { n with size := ⟨required.x, required.y + edgeThickness + edgeLabelSpacing⟩ }

/-- `process(layeredGraph, monitor)` with an explicit label manager (Rust: the graph's
`LABEL_MANAGER`). -/
def processWith (centerLabels : Bool) (labelManager : LabelManager) (graph : LGraphId) : LayeredM Unit := do
  let gr ← getGraph graph
  let edgeLabelSpacing := gr.props.getD LayeredOptions.SPACING_EDGE_LABEL 2.0
  let labelLabelSpacing := gr.props.getD LayeredOptions.SPACING_LABEL_LABEL 1.0
  let direction := gr.props.getD LayeredOptions.DIRECTION Direction.right
  let verticalLayout := direction.isVertical
  if centerLabels then
    manageCenterLabels graph labelManager edgeLabelSpacing labelLabelSpacing direction verticalLayout
  else
    manageNonCenterLabels graph labelManager labelLabelSpacing verticalLayout

/-- `process(layeredGraph, monitor)`: nothing to do without a label manager. -/
def process (centerLabels : Bool) (graph : LGraphId) (monitor : ProgressMonitor) : LayeredM Unit := do
  let _ ← monitor.begin "Label management" 1.0
  match ← labelManagerOf graph with
  | none => pure ()
  | some labelManager => processWith centerLabels labelManager graph
  monitor.done

/-- `new LabelManagementProcessor(centerLabels)`. -/
def processorFor (centerLabels : Bool) : LayeredProcessor :=
  { name := "LabelManagementProcessor", process := process centerLabels }

/-- `END_NODE_PORT_LABEL_MANAGEMENT_PROCESSOR` = `new LabelManagementProcessor(false)`. -/
def endNodePortProcessor : LayeredProcessor := processorFor false

/-- `CENTER_LABEL_MANAGEMENT_PROCESSOR` = `new LabelManagementProcessor(true)`. -/
def centerProcessor : LayeredProcessor := processorFor true

end LabelManagementProcessor

builtin_initialize registerEndNodePortLabelManagementProcessor : Unit ←
  IntermediateProcessorStrategy.register .endNodePortLabelManagementProcessor LabelManagementProcessor.endNodePortProcessor

builtin_initialize registerCenterLabelManagementProcessor : Unit ←
  IntermediateProcessorStrategy.register .centerLabelManagementProcessor LabelManagementProcessor.centerProcessor

end Elk.Alg.Layered.Intermediate
