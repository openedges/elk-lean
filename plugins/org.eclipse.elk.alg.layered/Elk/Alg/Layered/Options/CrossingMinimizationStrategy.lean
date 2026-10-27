import Elk.Graph.Enum
/-!
# `org.eclipse.elk.alg.layered.options.CrossingMinimizationStrategy`

Port of `options/crossing_minimization_strategy.rs` (elk-rs) and `CrossingMinimizationStrategy.java`.

The Java enum implements `ILayoutPhaseFactory` (`create()` builds the crossing minimizer (`p3order`));
that factory is not part of this module: the phase package adds `createPhase` once
the phase implementations are ported.
-/
namespace Elk.Alg.Layered.Options

/-- `org.eclipse.elk.alg.layered.options.CrossingMinimizationStrategy`: Enumeration of and factory
for the different available crossing minimization strategies. -/
elk_enum CrossingMinimizationStrategy := layerSweep medianLayerSweep interactive none

end Elk.Alg.Layered.Options
