import Elk.Alg.Layered.P3Order.AbstractBarycenterPortDistributor
/-!
# `org.eclipse.elk.alg.layered.p3order.NodeRelativePortDistributor`

Port ranks relative to the node: every node consumes rank `1`, its input (output) ports get
evenly spaced ranks inside `(rankSum, rankSum + 1)` (elk-rs `node_relative_port_distributor.rs`,
a wrapper around `AbstractBarycenterPortDistributor` with `PortRankStrategy.nodeRelative`).
-/
namespace Elk.Alg.Layered.P3Order

open Elk.Alg.Layered.Graph Elk.Alg.Layered.Options Elk.Alg.Layered.P3Order.Counting

/-- `NodeRelativePortDistributor`. -/
structure NodeRelativePortDistributor where
  /-- `inner`. -/
  inner : AbstractBarycenterPortDistributor

namespace NodeRelativePortDistributor

/-- `NodeRelativePortDistributor::new(num_layers)`. -/
def new (numLayers : Nat) : BaseIO NodeRelativePortDistributor := do
  return { inner := ← AbstractBarycenterPortDistributor.new numLayers .nodeRelative }

/-- `port_ranks()`. -/
def portRanks (d : NodeRelativePortDistributor) : BaseIO (Array Float) := d.inner.portRanks

/-- `calculate_port_ranks(layer, port_type)`. -/
def calculatePortRanks (d : NodeRelativePortDistributor) (layer : Array LNodeId) (portType : PortType) : LayeredM Unit :=
  d.inner.calculatePortRanks layer portType

/-- `distribute_ports_while_sweeping(order, free_layer_index, is_forward_sweep)`. -/
def distributePortsWhileSweeping (d : NodeRelativePortDistributor) (order : Array (Array LNodeId)) (freeLayerIndex : Nat)
    (isForwardSweep : Bool) : LayeredM Bool :=
  d.inner.distributePortsWhileSweeping order freeLayerIndex isForwardSweep

/-- The `IInitializable` implementation (delegates to `inner`). -/
def initializable (d : NodeRelativePortDistributor) : Initializable := d.inner.initializable

/-- The `ISweepPortDistributor` implementation. -/
def toSweepPortDistributor (d : NodeRelativePortDistributor) : SweepPortDistributor := d.inner.toSweepPortDistributor

end NodeRelativePortDistributor

end Elk.Alg.Layered.P3Order
