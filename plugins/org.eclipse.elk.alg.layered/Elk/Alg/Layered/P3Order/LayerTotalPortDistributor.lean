import Elk.Alg.Layered.P3Order.AbstractBarycenterPortDistributor
/-!
# `org.eclipse.elk.alg.layered.p3order.LayerTotalPortDistributor`

Port ranks counted over the whole layer: every input (output) port consumes rank `1`
(elk-rs `layer_total_port_distributor.rs`, a wrapper around `AbstractBarycenterPortDistributor`
with `PortRankStrategy.layerTotal`).
-/
namespace Elk.Alg.Layered.P3Order

open Elk.Alg.Layered.Graph Elk.Alg.Layered.Options Elk.Alg.Layered.P3Order.Counting

/-- `LayerTotalPortDistributor`. -/
structure LayerTotalPortDistributor where
  /-- `inner`. -/
  inner : AbstractBarycenterPortDistributor

namespace LayerTotalPortDistributor

/-- `LayerTotalPortDistributor::new(num_layers)`. -/
def new (numLayers : Nat) : BaseIO LayerTotalPortDistributor := do
  return { inner := ← AbstractBarycenterPortDistributor.new numLayers .layerTotal }

/-- `port_ranks()`. -/
def portRanks (d : LayerTotalPortDistributor) : BaseIO (Array Float) := d.inner.portRanks

/-- `calculate_port_ranks(layer, port_type)`. -/
def calculatePortRanks (d : LayerTotalPortDistributor) (layer : Array LNodeId) (portType : PortType) : LayeredM Unit :=
  d.inner.calculatePortRanks layer portType

/-- `distribute_ports_while_sweeping(order, free_layer_index, is_forward_sweep)`. -/
def distributePortsWhileSweeping (d : LayerTotalPortDistributor) (order : Array (Array LNodeId)) (freeLayerIndex : Nat)
    (isForwardSweep : Bool) : LayeredM Bool :=
  d.inner.distributePortsWhileSweeping order freeLayerIndex isForwardSweep

/-- The `IInitializable` implementation (delegates to `inner`). -/
def initializable (d : LayerTotalPortDistributor) : Initializable := d.inner.initializable

/-- The `ISweepPortDistributor` implementation. -/
def toSweepPortDistributor (d : LayerTotalPortDistributor) : SweepPortDistributor := d.inner.toSweepPortDistributor

end LayerTotalPortDistributor

end Elk.Alg.Layered.P3Order
