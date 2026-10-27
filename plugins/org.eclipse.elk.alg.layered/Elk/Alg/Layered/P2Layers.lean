import Elk.Alg.Layered.P2Layers.NetworkSimplexLayerer
import Elk.Alg.Layered.P2Layers.LongestPathLayerer
import Elk.Alg.Layered.P2Layers.LongestPathSourceLayerer
import Elk.Alg.Layered.P2Layers.CoffmanGrahamLayerer
import Elk.Alg.Layered.P2Layers.InteractiveLayerer
import Elk.Alg.Layered.P2Layers.StretchWidthLayerer
import Elk.Alg.Layered.P2Layers.MinWidthLayerer
import Elk.Alg.Layered.P2Layers.BreadthFirstModelOrderLayerer
import Elk.Alg.Layered.P2Layers.DepthFirstModelOrderLayerer
/-!
# `org.eclipse.elk.alg.layered.p2layers` + `LayeringStrategy.create()`

Aggregator of the layering phase implementations. `LayeringStrategy.createPhase` is the
`ILayoutPhaseFactory.create()` of the Java enum (elk-rs `create_phase` in
`options/layering_strategy.rs`); every constant is registered with
`LayeredPhases.registerPhase .p2Layering` at module initialisation so that
`LayeredPhases.strategyFactory .p2Layering "LayeringStrategy" …` finds it.
-/
namespace Elk.Alg.Layered.P2Layers

open Elk.Graph Elk.Alg.Layered.Options

/-- `LayeringStrategy.create()` (Rust `create_phase`): the layerer of a layering strategy. -/
def _root_.Elk.Alg.Layered.Options.LayeringStrategy.createPhase : LayeringStrategy → LayeredPhase
  | .networkSimplex => NetworkSimplexLayerer.phase
  | .longestPath => LongestPathLayerer.phase
  | .longestPathSource => LongestPathSourceLayerer.phase
  | .coffmanGraham => CoffmanGrahamLayerer.phase
  | .interactive => InteractiveLayerer.phase
  | .stretchWidth => StretchWidthLayerer.phase
  | .minWidth => MinWidthLayerer.phase
  | .bfModelOrder => BreadthFirstModelOrderLayerer.phase
  | .dfModelOrder => DepthFirstModelOrderLayerer.phase

builtin_initialize registerNetworkSimplexLayerer : Unit ←
  LayeredPhases.registerPhase .p2Layering (ElkEnum.ordinal LayeringStrategy.networkSimplex) (pure NetworkSimplexLayerer.phase)
builtin_initialize registerLongestPathLayerer : Unit ←
  LayeredPhases.registerPhase .p2Layering (ElkEnum.ordinal LayeringStrategy.longestPath) (pure LongestPathLayerer.phase)
builtin_initialize registerLongestPathSourceLayerer : Unit ←
  LayeredPhases.registerPhase .p2Layering (ElkEnum.ordinal LayeringStrategy.longestPathSource) (pure LongestPathSourceLayerer.phase)
builtin_initialize registerCoffmanGrahamLayerer : Unit ←
  LayeredPhases.registerPhase .p2Layering (ElkEnum.ordinal LayeringStrategy.coffmanGraham) (pure CoffmanGrahamLayerer.phase)
builtin_initialize registerInteractiveLayerer : Unit ←
  LayeredPhases.registerPhase .p2Layering (ElkEnum.ordinal LayeringStrategy.interactive) (pure InteractiveLayerer.phase)
builtin_initialize registerStretchWidthLayerer : Unit ←
  LayeredPhases.registerPhase .p2Layering (ElkEnum.ordinal LayeringStrategy.stretchWidth) (pure StretchWidthLayerer.phase)
builtin_initialize registerMinWidthLayerer : Unit ←
  LayeredPhases.registerPhase .p2Layering (ElkEnum.ordinal LayeringStrategy.minWidth) (pure MinWidthLayerer.phase)
builtin_initialize registerBreadthFirstModelOrderLayerer : Unit ←
  LayeredPhases.registerPhase .p2Layering (ElkEnum.ordinal LayeringStrategy.bfModelOrder) (pure BreadthFirstModelOrderLayerer.phase)
builtin_initialize registerDepthFirstModelOrderLayerer : Unit ←
  LayeredPhases.registerPhase .p2Layering (ElkEnum.ordinal LayeringStrategy.dfModelOrder) (pure DepthFirstModelOrderLayerer.phase)

end Elk.Alg.Layered.P2Layers
