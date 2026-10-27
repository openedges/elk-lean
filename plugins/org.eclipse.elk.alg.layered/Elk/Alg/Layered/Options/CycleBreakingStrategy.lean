import Elk.Graph.Enum
/-!
# `org.eclipse.elk.alg.layered.options.CycleBreakingStrategy`

Port of `options/cycle_breaking_strategy.rs` (elk-rs) and `CycleBreakingStrategy.java`.

The Java enum implements `ILayoutPhaseFactory` (`create()` builds the cycle breaker (`p1cycles`));
that factory is not part of this module: the phase package adds `createPhase` once
the phase implementations are ported.
-/
namespace Elk.Alg.Layered.Options

/-- `org.eclipse.elk.alg.layered.options.CycleBreakingStrategy`: Enumeration of and factory for the
different available cycle breaking strategies. The model order cycle breakers additionally allow a
group model order to be set and enforced. -/
elk_enum CycleBreakingStrategy := greedy depthFirst interactive modelOrder greedyModelOrder sccConnectivity sccNodeType dfsNodeOrder bfsNodeOrder

end Elk.Alg.Layered.Options
