import Elk.Alg.Layered.Intermediate.GraphTransformer
import Elk.Alg.Layered.Intermediate.AlternatingLayerUnzipper
import Elk.Alg.Layered.Intermediate.SemiInteractiveCrossMinProcessor
/-!
# Layered intermediate processors: graph transformation group (task I5a)

Aggregates `GraphTransformer` (`DIRECTION_PREPROCESSOR`/`DIRECTION_POSTPROCESSOR`),
`AlternatingLayerUnzipper` (`ALTERNATING_LAYER_UNZIPPER`) and
`SemiInteractiveCrossMinProcessor` (`SEMI_INTERACTIVE_CROSSMIN_PROCESSOR`). Importing this module
registers the processors with `IntermediateProcessorStrategy.register`.
-/
