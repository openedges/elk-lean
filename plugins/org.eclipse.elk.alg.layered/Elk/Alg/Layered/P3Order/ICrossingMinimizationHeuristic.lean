import Elk.Alg.Layered.P3Order.Counting.IInitializable
import Elk.Alg.Layered.P3Order.CrossMinSnapshot
/-!
# `org.eclipse.elk.alg.layered.p3order.ICrossingMinimizationHeuristic`

A heuristic is created for one graph, keeps its mutable state behind `IO.Ref`s and draws random
numbers from the caller's `IO.Ref Random` (captured by `toHeuristic`), which is what the shared
Java/Rust `Random` instance amounts to.
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
  /-- elk-rs `set_snapshot` of the barycenter heuristics (`GraphInfoHolder` downcasts to call it;
  the other heuristics ignore it). -/
  setSnapshot : CrossMinSnapshot → BaseIO Unit := fun _ => pure ()

end Elk.Alg.Layered.P3Order
