import Elk.Alg.MrTree.TreeLayoutPhases
/-!
# `org.eclipse.elk.alg.mrtree.p2order.OrderBalance`

Port of `p2order/order_balance.rs` (elk-rs). The phase is not selectable (`TreeLayoutPhases` always
creates `NodeOrderer` for `P2_NODE_ORDERING`); like Rust its `process` only reports progress (the
Java balancing logic is not ported by elk-rs either). Its processor configuration slots `ROOT_PROC`,
`FAN_PROC` and `NEIGHBORS_PROC` before `P2_NODE_ORDERING`.
-/
namespace Elk.Alg.MrTree.P2Order

open Elk.Core.Alg Elk.Core.Util Elk.Alg.MrTree Elk.Alg.MrTree.Graph Elk.Alg.MrTree.Intermediate

namespace OrderBalance

/-- `OrderBalance::process` (no-op apart from the progress monitor, as in Rust). -/
def process (_graph : TGraphId) (monitor : ProgressMonitor) : MrTreeM Unit := do
  discard <| monitor.begin "Processor arrange node" 1.0
  monitor.done

/-- `get_layout_processor_configuration`. -/
def configuration : TreeProcessorConfiguration :=
  let c : TreeProcessorConfiguration := LayoutProcessorConfiguration.create
  let c := c.addBefore TreeLayoutPhases.p2NodeOrdering IntermediateProcessorStrategy.rootProc
  let c := c.addBefore TreeLayoutPhases.p2NodeOrdering IntermediateProcessorStrategy.fanProc
  c.addBefore TreeLayoutPhases.p2NodeOrdering IntermediateProcessorStrategy.neighborsProc

/-- The `OrderBalance` phase. -/
def phase : TreePhase :=
  { name := "OrderBalance", process, getLayoutProcessorConfiguration := fun _ => pure (some configuration) }

end OrderBalance

end Elk.Alg.MrTree.P2Order
