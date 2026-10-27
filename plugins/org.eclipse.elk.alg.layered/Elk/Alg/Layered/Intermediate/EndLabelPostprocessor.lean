import Elk.Alg.Layered.LayeredPhases
import Elk.Alg.Common.NodeSpacing.CellSystem.LabelCell
/-!
# `org.eclipse.elk.alg.layered.intermediate.EndLabelPostprocessor`

Port of elk-rs `intermediate/end_label_postprocessor.rs` (Java `EndLabelPostprocessor`): "After the
`EndLabelPreprocessor` has done all the major work for us, each node may have a list of label cells
full of edge end labels associated with it, along with proper label cell coordinates. The problem is
that when the preprocessor was run, the final coordinates of all the nodes (and with that, the final
coordinates of all the edges) were not known yet. Now they are, so the label cell coordinates can be
offset accordingly and label coordinates can be applied."

Slot: after phase 5 (same-slot dependency `EndLabelSorter`).

The end label cells (`InternalProperties.END_LABELS`, Rust `EndLabelMap =
HashMap<PortRefKey, Arc<Mutex<LabelCell<LLabelAdapter, LLabelRef>>>>`) are standalone label cells:
`Cell LLabelId` values of the node spacing cell system whose `kind` is `.label`. Rust iterates the
`HashMap` in hash order; every cell only writes the positions of its own labels, so the order does
not change the result and the Lean port uses the stored (port insertion) order.

`LabelCell::apply_label_layout` reads each label's current size through the `LLabelAdapter`; the
port re-reads the sizes from the arena (`LabelCell.layoutPositions`) and writes the positions to the
`LLabel`s (`LLabelAdapter::set_position`).

TODO(end-labels): `LNodeInternals` has no `END_LABELS` field yet (its value type needs the cell
system, see the module doc of `InternalProperties`). `endLabelsOf`/`clearEndLabels` are the only
accessors of the property; once the field
`endLabels : Option (Array (LPortId × Elk.Alg.Common.NodeSpacing.CellSystem.Cell LLabelId)) := none`
exists they become `(← getNode n).internal.endLabels` and
`modifyNode n fun x => { x with internal := { x.internal with endLabels := none } }`. Until then the
processor finds no end labels (exactly like a graph without end labels) and `processNode` is the
entry point used by the tests.
-/
namespace Elk.Alg.Layered.Intermediate

open Elk.Graph Elk.Core Elk.Core.Alg Elk.Core.Math Elk.Core.Util Elk.Alg.Layered Elk.Alg.Layered.Graph
  Elk.Alg.Layered.Options LayeredM
open Elk.Alg.Common.NodeSpacing

namespace EndLabelPostprocessor

/-- Value type of `InternalProperties.END_LABELS`: per port the label cell holding its end labels. -/
abbrev EndLabelMap := Array (LPortId × CellSystem.Cell LLabelId)

/-- `node.getProperty(InternalProperties.END_LABELS)` (`none` = not set).
TODO(end-labels): read `(← getNode node).internal.endLabels` once the field exists. -/
def endLabelsOf (_node : LNodeId) : LayeredM (Option EndLabelMap) := pure none

/-- `node.setProperty(InternalProperties.END_LABELS, null)`.
TODO(end-labels): clear `internal.endLabels` once the field exists. -/
def clearEndLabels (_node : LNodeId) : LayeredM Unit := pure ()

/-- Rust `label_cell.cell_rectangle().move_by(node_pos); label_cell.apply_label_layout()` for one end
label cell: offsets the cell rectangle by the node position and writes the label positions (label
sizes are re-read from the arena, like `LLabelAdapter::get_size`). Returns the moved cell. -/
def applyCell (nodePos : KVector) (cell : CellSystem.Cell LLabelId) : LayeredM (CellSystem.Cell LLabelId) := do
  let cell := { cell with cellRectangle := cell.cellRectangle.moveBy nodePos }
  match cell.kind with
  | .label d =>
    let mut sizes : Array KVector := Array.mkEmpty d.labels.size
    for (l, _) in d.labels do
      sizes := sizes.push (← getLabel l).size
    let positions := CellSystem.LabelCell.layoutPositions d cell.cellRectangle cell.padding sizes
    for ((l, _), pos) in d.labels.zip positions do
      modifyLabel l fun x => { x with position := pos }
  | _ => pure ()
  return cell

/-- Rust `process_node(node)` on the node's end label cells: an empty map is just removed; otherwise
every cell is moved by the node position and its labels are placed, then the property is removed. -/
def processNode (node : LNodeId) (cells : EndLabelMap) : LayeredM Unit := do
  if cells.isEmpty then
    clearEndLabels node
    return
  let nodePos := (← getNode node).position
  for (_, cell) in cells do
    let _ ← applyCell nodePos cell
  clearEndLabels node

/-- `process(layeredGraph, monitor)`: the `NORMAL` and `EXTERNAL_PORT` nodes of all layers that have
`END_LABELS`. -/
def process (graph : LGraphId) (monitor : ProgressMonitor) : LayeredM Unit := do
  let _ ← monitor.begin "End label post-processing" 1.0
  let layers := (← getGraph graph).layers
  for layer in layers do
    let nodes := (← getLayer layer).nodes
    for node in nodes do
      let t := (← getNode node).type
      if t != .normal && t != .externalPort then continue
      match ← endLabelsOf node with
      | some cells => processNode node cells
      | none => pure ()
  monitor.done

/-- The `EndLabelPostprocessor` processor. -/
def processor : LayeredProcessor := { name := "EndLabelPostprocessor", process := process }

end EndLabelPostprocessor

builtin_initialize registerEndLabelPostprocessor : Unit ←
  IntermediateProcessorStrategy.register .endLabelPostprocessor EndLabelPostprocessor.processor

end Elk.Alg.Layered.Intermediate
