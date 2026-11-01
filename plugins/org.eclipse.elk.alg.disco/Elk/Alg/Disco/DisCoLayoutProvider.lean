import Elk.Core.LayoutProvider
import Elk.Core.Data
import Elk.Alg.Disco.Options.DisCoOptions
import Elk.Alg.Disco.DisCoPolyominoCompactor
import Elk.Alg.Disco.Transform.ElkGraphTransformer
import Elk.Core.Util.FloatConst
open Elk.Core.Util.FloatConst
/-!
# `org.eclipse.elk.alg.disco.DisCoLayoutProvider`

The layout provider of the DisCo algorithm (elk-rs `disco_layout_provider.rs`): arranges the
unconnected components of a graph. Steps of `layout`:

1. read the component spacing (`spacing.componentComponent`, `0` if missing);
2. if `componentCompaction.componentLayoutAlgorithm` is set to a non-blank algorithm id (matched by
   suffix, e.g. `fixed` or `box`), run that algorithm's provider on the whole layout graph as a
   sub task before compaction (silently skipped for unknown ids and for algorithms without a
   registered provider, like Rust's missing provider pool);
3. transform the graph (`ElkGraphTransformer.importGraph`), compact it with the strategy of
   `componentCompaction.strategy` (`POLYOMINO`) and apply the result.

The debug properties `DEBUG_DISCO_GRAPH` and `DEBUG_DISCO_POLYS` are not stored on the layout
graph (see `DisCoOptions`). `ensureRegistered` installs the provider for `org.eclipse.elk.disco`;
the module registers it at initialisation.
-/

namespace Elk.Alg.Disco

open Elk.Graph Elk.Core Elk.Core.Data Elk.Core.Util
open Elk.Alg.Disco.Options Elk.Alg.Disco.Transform

namespace DisCoLayoutProvider

/-- Runs the layout algorithm selected by `componentLayoutAlgorithm` (if any) on the layout graph
as a sub task of the monitor. -/
private def layoutComponents (layoutGraph : NodeId) (monitor : ProgressMonitor) : ElkM Unit := do
  let props := (← ElkM.getNode layoutGraph).props
  if props.has DisCoOptions.COMPONENT_COMPACTION_COMPONENT_LAYOUT_ALGORITHM then
    if let some requested := props.get DisCoOptions.COMPONENT_COMPACTION_COMPONENT_LAYOUT_ALGORITHM then
      if !requested.trimAscii.toString.isEmpty then
        if let some algorithmData ← LayoutMetaDataService.getAlgorithmDataBySuffix requested then
          if let some provider ← LayoutProvider.create algorithmData.id then
            let sub ← monitor.subTask fl1p0
            provider.layout layoutGraph sub

/-- `layout(layoutGraph, progressMonitor)`. -/
def layout (layoutGraph : NodeId) (monitor : ProgressMonitor) : ElkM Unit := do
  let _ ← monitor.begin "Connected Components Compaction" 1.0
  let componentSpacing :=
    ((← ElkM.getNode layoutGraph).props.get DisCoOptions.SPACING_COMPONENT_COMPONENT).getD 0.0
  layoutComponents layoutGraph monitor
  let transformer := ElkGraphTransformer.toIGraphTransformer componentSpacing
  let run : TransformM Unit := do
    let graph ← transformer.importGraph layoutGraph
    let strategy := (graph.properties.get DisCoOptions.COMPONENT_COMPACTION_STRATEGY).getD default
    let graph ← match strategy with
      | .polyomino => DisCoPolyominoCompactor.new.compact graph
    transformer.applyLayout graph
  let _ ← StateRefT'.run run ({} : ElkGraphTransformer)
  monitor.done

/-- The `org.eclipse.elk.disco` layout provider. -/
def provider : LayoutProvider := { id := DisCoOptions.ALGORITHM_ID, layout := layout }

end DisCoLayoutProvider

builtin_initialize registerDisCoLayoutProvider : Unit ←
  LayoutProvider.register DisCoOptions.ALGORITHM_ID (fun _ => DisCoLayoutProvider.provider)

end Elk.Alg.Disco
