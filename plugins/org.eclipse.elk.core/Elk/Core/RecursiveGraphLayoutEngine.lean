import Elk.Core.LayoutProvider
/-!
# `org.eclipse.elk.core.RecursiveGraphLayoutEngine` (placeholder)

The real engine (hierarchy traversal, option resolution, validation, top-down
layout) is ported once `ElkUtil`/validation are available. This placeholder
keeps the API pipeline compilable: it performs no layout.
-/
namespace Elk.Core

open Elk.Graph Elk.Core.Util

/-- `RecursiveGraphLayoutEngine.layout(layoutGraph, progressMonitor)`.
TODO(engine): replace with the full port of `recursive_graph_layout_engine.rs`. -/
def RecursiveGraphLayoutEngine.layout (_root : NodeId) (_monitor : ProgressMonitor) : ElkM Unit :=
  pure ()

end Elk.Core
