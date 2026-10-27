import Elk.Graph
import Elk.Core.LayoutProvider
import Elk.Core.Util.Random
import Elk.Core.Util.Java
import Elk.Alg.Common.NodeSpacing.NodeMicroLayout
import Elk.Alg.Force.ComponentsProcessor
import Elk.Alg.Force.ElkGraphImporter
import Elk.Alg.Force.Model.EadesModel
import Elk.Alg.Force.Model.FruchtermanReingoldModel
/-!
# `org.eclipse.elk.alg.force.ForceLayoutProvider`

Port of `force_layout_provider.rs` (elk-rs): the `org.eclipse.elk.force` layout provider.

1. unless `OMIT_NODE_MICRO_LAYOUT`, the node micro layout (node sizes, labels, port lists) runs;
2. the graph is imported into an `FGraph` (`ElkGraphImporter`) and split into connected components;
3. the random generator is created from `RANDOM_SEED` (seed 1 if unset, a time based seed if 0) and
   stored in the graph. Rust's `Random` clones share their state, so all components draw from one
   sequence: the generator of a finished component is handed to the next one;
4. each component is laid out with the model selected by `MODEL` (Fruchterman-Reingold by default),
   with a sub monitor of work `1 / components` (single precision like Rust);
5. the components are packed (`ComponentsProcessor.recombine`) and the layout is applied back.
-/
namespace Elk.Alg.Force

open Elk.Graph Elk.Core Elk.Core.Util Elk.Core.Options Elk.Alg.Force.Graph Elk.Alg.Force.Model
  Elk.Alg.Force.Options Elk.Alg.Common.NodeSpacing

namespace ForceLayoutProvider

/-- `ForceLayoutProvider::set_options(graph)`: stores the random generator derived from
`RANDOM_SEED` in the graph (`Random::new(seed as u64)`, seed 1 without the option, wall-clock nanoseconds
for seed 0). -/
def setOptions (graph : FGraph) : IO FGraph := do
  let random ← match graph.props.get ForceOptions.RANDOM_SEED with
    | some 0 => do
      let nanos ← IO.monoNanosNow
      pure (Random.ofUInt64 nanos.toUInt64)
    | some seed => pure (Random.ofInt seed)
    | none => pure (Random.ofInt 1)
  return { graph with random := some random }

/-- Lays out one component with the selected model. -/
def layoutComponent (strategy : ForceModelStrategy) (monitor : ProgressMonitor) : FM Unit :=
  match strategy with
  | .eades => EadesModel.layout monitor
  | .fruchtermanReingold => FruchtermanReingoldModel.layout monitor

/-- `ForceLayoutProvider::layout(layoutGraph, progressMonitor)`. -/
def layout (layoutGraph : NodeId) (monitor : ProgressMonitor) : ElkM Unit := do
  let _ ← monitor.begin "ELK Force" 1.0
  let omitMicro := ((← ElkM.getNode layoutGraph).props.get ForceOptions.OMIT_NODE_MICRO_LAYOUT).getD false
  if !omitMicro then
    (← NodeMicroLayout.forGraph layoutGraph).execute
  let fgraph ← ElkGraphImporter.importGraph layoutGraph
  let fgraph ← setOptions fgraph
  let strategy := fgraph.props.getD ForceOptions.MODEL ForceModelStrategy.fruchtermanReingold
  let components := ComponentsProcessor.split fgraph
  let compWork := Float.toF32 (1.0 / (max components.size 1).toFloat)
  let mut laidOut : Array FGraph := Array.mkEmpty components.size
  -- the generator is shared by all components (Rust `Random` clones share their state)
  let mut random := fgraph.random
  for comp in components do
    let sub ← monitor.subTask compWork
    let result ← ((layoutComponent strategy sub).run { comp with random } : IO (Unit × FGraph))
    let comp' := result.2
    random := comp'.random
    laidOut := laidOut.push comp'
  ElkGraphImporter.applyLayout (ComponentsProcessor.recombine laidOut)
  monitor.done

/-- The `org.eclipse.elk.force` provider. -/
def provider : LayoutProvider := { id := ForceOptions.ALGORITHM_ID, layout := layout }

end ForceLayoutProvider

end Elk.Alg.Force
