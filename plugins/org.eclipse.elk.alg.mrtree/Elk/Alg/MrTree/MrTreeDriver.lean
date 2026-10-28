import Elk.Alg.MrTree.TreeLayoutPhases
import Elk.Alg.MrTree.Options.MrTreeOptions
import Elk.Alg.MrTree.P1Treeify.DFSTreeifyer
import Elk.Alg.MrTree.P2Order.NodeOrderer
import Elk.Alg.MrTree.P3Place.NodePlacer
import Elk.Alg.MrTree.P4Route.EdgeRouter
/-!
# `org.eclipse.elk.alg.mrtree.MrTree`

Port of `mrtree.rs` (elk-rs), the driver of the tree layout of one connected component, and of the
phase factory half of `tree_layout_phases.rs` (`ILayoutPhaseFactory::create_phase`:
`P1_TREEIFICATION` → `DFSTreeifyer`, `P2_NODE_ORDERING` → `NodeOrderer`, `P3_NODE_PLACEMENT` →
`NodePlacer`, `P4_EDGE_ROUTING` → `EdgeRouter`), which lives here because the phases import the
phase enumeration. The file is named `MrTreeDriver` to keep the module name distinct from the plugin
root module `Elk.Alg.MrTree`.

`doLayout` (`do_layout` with a monitor): `update_modules` builds a fresh `AlgorithmAssembler`
without caching (Rust `with_caching(false)` plus `reset()` before every build; the Lean assembler is
created per call, which is the same) with the four phases; the resulting processor list is, in this
order: `DFSTreeifyer`, `ROOT_PROC` (+ `FAN_PROC` unless the weighting is `MODEL_ORDER`),
`NodeOrderer`, `NodePlacer`, `COMPACTION_PROC`, `LEVEL_COORDS`, `GRAPH_BOUNDS_PROC`,
`DETREEIFYING_PROC` (one slot, sorted by ordinal), `EdgeRouter`. `layout` runs them on the graph,
each with a sub monitor of work 1, stopping when the monitor is cancelled. With `DEBUG_MODE` the
Rust log lines are written to the monitor.
-/
/-! Float literals as global constants (FL): inside branches, loops and specialised code the compiler
shares a literal's `Nat`/`Bool` arguments with unrelated variables (CSE) and then parses it on every
evaluation (`FastFloat.ofScientificImpl`); a top-level constant is a load (PLAN §7.1 items 17, 22). -/
private def fl1p0 : Float := 1.0

namespace Elk.Alg.MrTree

open Elk.Core.Alg Elk.Core.Util Elk.Alg.MrTree.Graph Elk.Alg.MrTree.Options
open Elk.Alg.MrTree.P1Treeify Elk.Alg.MrTree.P2Order Elk.Alg.MrTree.P3Place Elk.Alg.MrTree.P4Route

namespace TreeLayoutPhases

/-- `ILayoutPhaseFactory::create_phase()`. -/
def createPhase : TreeLayoutPhases → TreePhase
  | .p1Treeification => DFSTreeifyer.phase
  | .p2NodeOrdering => NodeOrderer.phase
  | .p3NodePlacement => NodePlacer.phase
  | .p4EdgeRouting => EdgeRouter.phase

/-- The phase factory of a `TreeLayoutPhases` constant (enum identity as the cache key). -/
def phaseFactory (p : TreeLayoutPhases) : TreePhaseFactory :=
  LayoutPhaseFactory.ofEnum "TreeLayoutPhases" p (pure (createPhase p))

end TreeLayoutPhases

namespace MrTree

/-- `update_modules(graph)`: the processor list for the graph. -/
def updateModules (graph : TGraphId) : MrTreeM (Array (LayoutProcessor MrTreeM TGraphId)) := do
  let assembler ← TreeAssembler.create
  assembler.withCaching false
  assembler.reset
  for p in #[TreeLayoutPhases.p1Treeification, .p2NodeOrdering, .p3NodePlacement, .p4EdgeRouting] do
    assembler.setPhase p (TreeLayoutPhases.phaseFactory p)
  assembler.build graph

/-- `layout(graph, monitor)`: runs the processors. -/
def layout (algorithm : Array (LayoutProcessor MrTreeM TGraphId)) (graph : TGraphId)
    (monitor : ProgressMonitor) : MrTreeM Unit := do
  let total := (Float.ofNat (max algorithm.size 1)).toF32
  discard <| monitor.begin "Layout" total
  let debug := ((← MrTreeM.getGraph graph).props.get MrTreeOptions.DEBUG_MODE).getD false
  if debug then monitor.log s!"ELK MrTree uses the following {algorithm.size} modules:"
  let mut idx := 0
  for processor in algorithm do
    if ← monitor.isCanceled then return
    if debug then monitor.log s!"   Slot {idx}: processor"
    processor.process graph (← monitor.subTask fl1p0)
    idx := idx + 1
  monitor.done

/-- `do_layout(graph, Some(monitor))` (`do_layout_with_monitor`). -/
def doLayout (graph : TGraphId) (monitor : ProgressMonitor) : MrTreeM Unit := do
  discard <| monitor.begin "Tree layout" 1.0
  let debug := ((← MrTreeM.getGraph graph).props.get MrTreeOptions.DEBUG_MODE).getD false
  if debug then monitor.log "MrTree! called."
  let algorithm ← updateModules graph
  layout algorithm graph (← monitor.subTask 1.0)
  monitor.done

end MrTree

end Elk.Alg.MrTree
