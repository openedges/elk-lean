import Elk.Alg.Layered.P3Order.Counting.IInitializable
/-! # `org.eclipse.elk.alg.layered.p3order.ISweepPortDistributor`

`ISweepPortDistributor.create(type, random, numLayers)` is defined with the concrete
distributors (`SweepPortDistributor.create`). -/
namespace Elk.Alg.Layered.P3Order

open Elk.Alg.Layered.Graph Elk.Alg.Layered.P3Order.Counting

/-- `ISweepPortDistributor`. -/
structure SweepPortDistributor where
  /-- The `IInitializable` part. -/
  initializable : Initializable
  /-- `distributePortsWhileSweeping(order, freeLayerIndex, isForwardSweep)`: whether the port
  order of the free layer changed. -/
  distributePortsWhileSweeping : Array (Array LNodeId) → Nat → Bool → LayeredM Bool

end Elk.Alg.Layered.P3Order
