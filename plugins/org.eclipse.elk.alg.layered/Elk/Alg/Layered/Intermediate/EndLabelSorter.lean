import Elk.Alg.Layered.LayeredPhases
import Elk.Core.Util.Sort
/-!
# `org.eclipse.elk.alg.layered.intermediate.EndLabelSorter`

Port of elk-rs `intermediate/end_label_sorter.rs` (Java `EndLabelSorter`): "Sorts end labels
according to the order of nodes their respective edges come from or head to. This is to prevent
seemingly random label orders in diagrams that employ end labels and have multiple edges going into
or leaving the same port."

Slot: after phase 5 (same-slot dependencies `LongEdgeJoiner`, `NorthSouthPortPostprocessor`).

Deviation of the Rust oracle from Java (followed here): Java sorts the label groups of each port's
`END_LABELS` cell of the `NORMAL` nodes by the order of the opposite nodes/ports. elk-rs instead
sorts the `REPRESENTED_LABELS` of every `LABEL` dummy node in the layers by label text (Rust
`String::cmp`, byte-lexicographic = code point order, which is Lean's `compare` on `String`), with
the stable `sort_by`. Since the label dummies are removed by `LabelDummyRemover` before this slot in
the regular pipeline, the Rust processor is usually a no-op.
-/
namespace Elk.Alg.Layered.Intermediate

open Elk.Graph Elk.Core Elk.Core.Alg Elk.Core.Util Elk.Alg.Layered Elk.Alg.Layered.Graph
  Elk.Alg.Layered.Options LayeredM

namespace EndLabelSorter

/-- Rust `sort_represented_labels(node)`: sorts the dummy's `REPRESENTED_LABELS` by text (stable);
lists with fewer than two labels are left untouched. -/
def sortRepresentedLabels (node : LNodeId) : LayeredM Unit := do
  let labels := (← getNode node).internal.representedLabels
  if labels.size < 2 then return
  let mut keyed : Array (String × LLabelId) := Array.mkEmpty labels.size
  for l in labels do
    keyed := keyed.push ((← getLabel l).text, l)
  let sorted := (stableSort keyed fun a b => compare a.1 b.1).map (·.2)
  modifyNode node fun n => { n with internal := { n.internal with representedLabels := sorted } }

/-- `process(layeredGraph, monitor)`: every `LABEL` node of every layer (layer order, node order). -/
def process (graph : LGraphId) (monitor : ProgressMonitor) : LayeredM Unit := do
  let _ ← monitor.begin "Sort end labels" 1.0
  let layers := (← getGraph graph).layers
  for layer in layers do
    let nodes := (← getLayer layer).nodes
    for node in nodes do
      if (← getNode node).type != .label then continue
      sortRepresentedLabels node
  monitor.done

/-- The `EndLabelSorter` processor. -/
def processor : LayeredProcessor := { name := "EndLabelSorter", process := process }

end EndLabelSorter

builtin_initialize registerEndLabelSorter : Unit ←
  IntermediateProcessorStrategy.register .endLabelSorter EndLabelSorter.processor

end Elk.Alg.Layered.Intermediate
