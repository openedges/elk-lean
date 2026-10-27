import Elk.Alg.Layered.Intermediate.Wrapping
/-!
# Wrapping processors (task I5b)

Aggregator of the wrapping intermediate processors (`breakingPointInserter`,
`breakingPointProcessor`, `breakingPointRemover`, `singleEdgeGraphWrapper`); importing it runs
their `IntermediateProcessorStrategy.register` initialisers. Wired into `Intermediate.lean` by the
main agent.
-/
