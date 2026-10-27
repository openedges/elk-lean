import Elk.Graph.Enum
/-!
# `org.eclipse.elk.alg.layered.options.LayeringStrategy`

Port of `options/layering_strategy.rs` (elk-rs) and `LayeringStrategy.java`.

The Java enum implements `ILayoutPhaseFactory` (`create()` builds the layerer (`p2layers`));
that factory is not part of this module: the phase package adds `createPhase` once
the phase implementations are ported.
-/
namespace Elk.Alg.Layered.Options

/-- `org.eclipse.elk.alg.layered.options.LayeringStrategy`: Enumeration of and factory for the
different available layering strategies. -/
elk_enum LayeringStrategy := networkSimplex longestPath longestPathSource coffmanGraham interactive stretchWidth minWidth bfModelOrder dfModelOrder

end Elk.Alg.Layered.Options
