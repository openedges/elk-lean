import Elk.Graph
import Elk.Core.LayoutProvider
import Elk.Alg.Common.NodeSpacing.NodeMicroLayout
import Elk.Alg.Force.ComponentsProcessor
import Elk.Alg.Force.ElkGraphImporter
import Elk.Alg.Force.ForceLayoutProvider
import Elk.Alg.Force.Stress.StressMajorization
/-!
# `org.eclipse.elk.alg.force.stress.StressLayoutProvider`

Port of `stress_layout_provider.rs` (elk-rs): the `org.eclipse.elk.stress` layout provider.

Unless `INTERACTIVE`, the initial coordinates come from a force layout (Java parity): the options
`PADDING` (50) and `SPACING_NODE_NODE` (80) are stored on the layout node when unset and the
`ForceLayoutProvider` runs with a sub monitor. With `INTERACTIVE` only the node micro layout runs
(unless `OMIT_NODE_MICRO_LAYOUT`). Then the (already positioned) graph is imported again, split into
components, every component with more than one node is optimised by `StressMajorization` and its labels
are repositioned, and the components are packed and applied.
-/
namespace Elk.Alg.Force.Stress

open Elk.Graph Elk.Core Elk.Core.Math Elk.Core.Util Elk.Core.Options Elk.Alg.Force.Graph
  Elk.Alg.Force.Options Elk.Alg.Common.NodeSpacing

namespace StressLayoutProvider

/-- Optimises one component and repositions its labels (components with at most one node are
returned unchanged). -/
def layoutComponent (comp : FGraph) : FGraph :=
  if comp.nodes.size <= 1 then comp
  else
    let stress := StressMajorization.init comp
    let comp := stress.execute comp
    comp.labels.foldl (fun g lid => g.refreshLabelPosition lid) comp

/-- `StressLayoutProvider::layout(layoutGraph, progressMonitor)`. -/
def layout (layoutGraph : NodeId) (monitor : ProgressMonitor) : ElkM Unit := do
  let _ ← monitor.begin "ELK Stress" 1.0
  let interactive := ((← ElkM.getNode layoutGraph).props.get StressOptions.INTERACTIVE).getD false
  if !interactive then
    -- Java parity: Stress delegates to Force for initial coordinates.
    let props := (← ElkM.getNode layoutGraph).props
    if !props.has ForceOptions.PADDING then
      ElkM.setNodeProp layoutGraph ForceOptions.PADDING (ElkPadding.ofAny 50.0)
    if !props.has ForceOptions.SPACING_NODE_NODE then
      ElkM.setNodeProp layoutGraph ForceOptions.SPACING_NODE_NODE 80.0
    ForceLayoutProvider.layout layoutGraph (← monitor.subTask 1.0)
  else
    let omitMicro := ((← ElkM.getNode layoutGraph).props.get StressOptions.OMIT_NODE_MICRO_LAYOUT).getD false
    if !omitMicro then
      (← NodeMicroLayout.forGraph layoutGraph).execute
  let fgraph ← ElkGraphImporter.importGraph layoutGraph
  let components := (ComponentsProcessor.split fgraph).map layoutComponent
  ElkGraphImporter.applyLayout (ComponentsProcessor.recombine components)
  monitor.done

/-- The `org.eclipse.elk.stress` provider. -/
def provider : LayoutProvider := { id := StressOptions.ALGORITHM_ID, layout := layout }

end StressLayoutProvider

end Elk.Alg.Force.Stress
