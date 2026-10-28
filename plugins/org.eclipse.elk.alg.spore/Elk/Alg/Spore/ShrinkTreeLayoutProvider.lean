import Elk.Core.LayoutProvider
import Elk.Alg.Spore.ElkGraphImporter
import Elk.Alg.Spore.ShrinkTree
/-!
# `org.eclipse.elk.alg.spore.ShrinkTreeLayoutProvider`

Port of `shrink_tree_layout_provider.rs` (elk-rs) and `ShrinkTreeLayoutProvider.java`: the layout
provider of `org.eclipse.elk.sporeCompaction`. If the option `underlyingLayoutAlgorithm` is set (and
not blank), the algorithm with that id (suffix) is applied to the graph first; then the graph is
imported, compacted with `ShrinkTree` and the positions are applied.

An unknown underlying algorithm is silently ignored (Rust).
-/
/-! Float literals as global constants (FL): inside branches, loops and specialised code the compiler
shares a literal's `Nat`/`Bool` arguments with unrelated variables (CSE) and then parses it on every
evaluation (`FastFloat.ofScientificImpl`); a top-level constant is a load (PLAN §7.1 items 17, 22). -/
private def fl1p0 : Float := 1.0

namespace Elk.Alg.Spore

open Elk Elk.Graph Elk.Core Elk.Core.Util Elk.Core.Data Elk.Alg.Spore.Options

namespace ShrinkTreeLayoutProvider

/-- `layout(layout_graph, progress_monitor)`. -/
def layout (layoutGraph : NodeId) (monitor : ProgressMonitor) : ElkM Unit := do
  if ← ElkM.hasNodeProp layoutGraph SporeCompactionOptions.UNDERLYING_LAYOUT_ALGORITHM then
    if let some requested := (← ElkM.getNode layoutGraph).props.get
        SporeCompactionOptions.UNDERLYING_LAYOUT_ALGORITHM then
      if !requested.trimAscii.toString.isEmpty then
        if let some algorithmData ← LayoutMetaDataService.getAlgorithmDataBySuffix requested then
          if let some provider ← LayoutProvider.create algorithmData.id then
            provider.layout layoutGraph (← monitor.subTask fl1p0)
  let importer ← ElkGraphImporter.new
  let graph ← importer.importGraph layoutGraph
  let shrinkTree ← ShrinkTree.new
  let graph ← shrinkTree.shrink graph (← monitor.subTask fl1p0)
  importer.applyPositions graph

/-- The `org.eclipse.elk.sporeCompaction` layout provider. -/
def provider : LayoutProvider := { id := SporeCompactionOptions.ALGORITHM_ID, layout := layout }

end ShrinkTreeLayoutProvider

builtin_initialize registerShrinkTreeLayoutProvider : Unit ←
  LayoutProvider.register SporeCompactionOptions.ALGORITHM_ID (fun _ => ShrinkTreeLayoutProvider.provider)

end Elk.Alg.Spore
