import Elk.Alg.Layered.P3Order.Counting.IInitializable
/-!
# `org.eclipse.elk.alg.layered.p3order.ICrossingMinimizationHeuristic`

A heuristic is created for one graph (`new graph …`), captures its `LGraphId`, keeps its
mutable state behind `IO.Ref`s and draws random numbers from the graph's generator
(`LGraphUtil.drawRandom`), which is what the shared Java/Rust `Random` instance amounts to.
The node order is passed in and returned (Java mutates the arrays in place).
-/
namespace Elk.Alg.Layered.P3Order

open Elk.Alg.Layered.Graph Elk.Alg.Layered.P3Order.Counting

/-- `ICrossingMinimizationHeuristic`. -/
structure CrossingMinimizationHeuristic where
  /-- The `IInitializable` part. -/
  initializable : Initializable
  /-- `alwaysImproves()`. -/
  alwaysImproves : LayeredM Bool
  /-- `setFirstLayerOrder(order, forwardSweep, random)`: returns the order and whether it changed. -/
  setFirstLayerOrder : Array (Array LNodeId) → Bool → LayeredM (Array (Array LNodeId) × Bool)
  /-- `minimizeCrossings(order, freeLayerIndex, forwardSweep, isFirstSweep, random)`: returns
  the order and whether it changed. -/
  minimizeCrossings : Array (Array LNodeId) → Nat → Bool → Bool → LayeredM (Array (Array LNodeId) × Bool)
  /-- `isDeterministic()`. -/
  isDeterministic : LayeredM Bool
  /-- elk-rs `reset_sweep_iteration()` (tracing support). -/
  resetSweepIteration : LayeredM Unit := pure ()
  /-- elk-rs `increment_sweep_iteration()`. -/
  incrementSweepIteration : LayeredM Unit := pure ()

end Elk.Alg.Layered.P3Order
