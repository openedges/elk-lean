import Elk.Core.LayoutProvider
import Elk.Alg.Common.NodeSpacing.NodeMicroLayout
import Elk.Alg.MrTree.Options.MrTreeOptions
import Elk.Alg.MrTree.ElkGraphImporter
import Elk.Alg.MrTree.ComponentsProcessor
import Elk.Alg.MrTree.MrTreeDriver
/-!
# `org.eclipse.elk.alg.mrtree.TreeLayoutProvider`

Port of `tree_layout_provider.rs` (elk-rs), the layout provider of `org.eclipse.elk.mrtree`:

1. unless `OMIT_NODE_MICRO_LAYOUT` (`unwrap_or(false)`), the node micro layout of the children;
2. `ElkGraphImporter.importGraph` (sub monitor 0.1, "build tGraph");
3. `ComponentsProcessor.split` (sub monitor 0.1, "Split graph");
4. `MrTree.doLayout` on every component (sub monitor `(1 - 0.4) / max(#components, 1)`, `f32`);
5. `ComponentsProcessor.pack` (sub monitor 0.1, "Pack components");
6. `ElkGraphImporter.applyLayout` of the packed graph (sub monitor 0.1, "Apply layout results").

Like Rust, the provider neither begins nor finishes the monitor it receives and does not run the
`InteractiveMrTreeGraphVisitor`. The tree arena is a value created by the importer and threaded
through the `MrTreeM` steps.
-/
namespace Elk.Alg.MrTree

open Elk.Graph Elk.Core Elk.Core.Util Elk.Alg.Common.NodeSpacing Elk.Alg.MrTree.Graph Elk.Alg.MrTree.Options

namespace TreeLayoutProvider

/-- `default_work` (`f32`). -/
def defaultWork : Float := (0.1 : Float).toF32

/-- Runs a tree layout action on an arena from `ElkM`. -/
@[inline] private def runTree {α : Type} (x : MrTreeM α) (a : TArena) : ElkM (α × TArena) :=
  (MrTreeM.run x a : IO (α × TArena))

/-- `IGraphLayoutEngine::layout(layout_graph, progress_monitor)`. -/
def layout (layoutGraph : NodeId) (progressMonitor : ProgressMonitor) : ElkM Unit := do
  let omitMicro := ((← ElkM.getNode layoutGraph).props.get MrTreeOptions.OMIT_NODE_MICRO_LAYOUT).getD false
  if !omitMicro then
    (← NodeMicroLayout.forGraph layoutGraph).execute
  let pm ← progressMonitor.subTask defaultWork
  discard <| pm.begin "build tGraph" 1.0
  let (arena, tgraph) ← ElkGraphImporter.importGraph layoutGraph
  pm.done
  let pm ← progressMonitor.subTask defaultWork
  discard <| pm.begin "Split graph" 1.0
  let (components, arena) ← runTree (ComponentsProcessor.split tgraph) arena
  pm.done
  let compWork := (((1.0 : Float).toF32 - (defaultWork * 4.0).toF32).toF32
    / (Float.ofNat (max components.size 1)).toF32).toF32
  let mut arena := arena
  for comp in components do
    let sub ← progressMonitor.subTask compWork
    let ((), a') ← runTree (MrTree.doLayout comp sub) arena
    arena := a'
  let pm ← progressMonitor.subTask defaultWork
  discard <| pm.begin "Pack components" 1.0
  let (packed, packedArena) ← runTree (ComponentsProcessor.pack components) arena
  pm.done
  let pm ← progressMonitor.subTask defaultWork
  discard <| pm.begin "Apply layout results" 1.0
  ElkGraphImporter.applyLayout packedArena packed
  pm.done

/-- The `org.eclipse.elk.mrtree` layout provider. -/
def provider : LayoutProvider :=
  { id := MrTreeOptions.ALGORITHM_ID
    layout := layout }

end TreeLayoutProvider

end Elk.Alg.MrTree
