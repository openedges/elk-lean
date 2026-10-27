import Elk.Alg.Layered.P1Cycles.SCCModelOrderCycleBreaker
import Elk.Alg.Layered.Options.CycleBreakingStrategy
/-!
# `org.eclipse.elk.alg.layered.p1cycles.SCConnectivity`

Port of elk-rs `p1cycles/sc_connectivity_cycle_breaker.rs` (`ScConnectivityCycleBreaker`). For
each strongly connected component it takes the nodes with the minimum and the maximum constraint
model order; if the minimum node has more incoming edges (node-level, all edges) than the maximum
node has outgoing edges, the minimum node's incoming edges from the component are reversed,
otherwise the maximum node's outgoing edges into the component.

The phase name is the Rust `type_name` `ScConnectivityCycleBreaker` (trace file name of the oracle),
not the Java class name `SCConnectivity`.
-/
namespace Elk.Alg.Layered.P1Cycles

open Elk.Graph Elk.Core Elk.Alg.Layered Elk.Alg.Layered.Graph Elk.Alg.Layered.Options LayeredM
  SCCModelOrderCycleBreaker

namespace SCConnectivity

/-- `findNodes(...)` (Rust `ScConnectivityCycleBreaker::find_nodes`). -/
def findNodes : FindNodes := fun graph components offset bigOffset => do
  let mut revEdges : Array LEdgeId := #[]
  for component in components do
    if component.size <= 1 then continue
    let some (minNode, maxNode) ← minMaxNodes graph component offset bigOffset | continue
    let minInDegree := (← withArena (·.nodeIncomingEdges minNode)).size
    let maxOutDegree := (← withArena (·.nodeOutgoingEdges maxNode)).size
    if minInDegree > maxOutDegree then
      revEdges := revEdges ++ (← incomingFromComponent component minNode)
    else
      revEdges := revEdges ++ (← outgoingToComponent component maxNode)
  return revEdges

/-- The `SCConnectivity` phase (`CycleBreakingStrategy.SCC_CONNECTIVITY`). -/
def phase : LayeredPhase :=
  { name := "ScConnectivityCycleBreaker"
    process := fun graph monitor => do
      let _ ← monitor.begin "Model order cycle breaking" 1.0
      processSccModelOrderCycleBreaking graph findNodes
      monitor.done
    getLayoutProcessorConfiguration := fun _ => pure (some layoutProcessorConfiguration) }

end SCConnectivity

builtin_initialize registerSCConnectivity : Unit ←
  LayeredPhases.registerPhase .p1CycleBreaking (ElkEnum.ordinal CycleBreakingStrategy.sccConnectivity)
    (pure SCConnectivity.phase)

end Elk.Alg.Layered.P1Cycles
