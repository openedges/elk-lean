import Elk.Alg.Layered.Intermediate.EdgeAndLayerConstraintEdgeReverser
import Elk.Alg.Layered.Intermediate.LayerConstraintPreprocessor
import Elk.Alg.Layered.Intermediate.LayerConstraintPostprocessor
import Elk.Alg.Layered.Intermediate.InLayerConstraintProcessor
import Elk.Alg.Layered.Intermediate.PartitionPreprocessor
import Elk.Alg.Layered.Intermediate.PartitionMidprocessor
import Elk.Alg.Layered.Intermediate.PartitionPostprocessor
import Elk.Alg.Layered.Intermediate.ConstraintsPostprocessor
import Elk.Alg.Layered.Intermediate.CommentPreprocessor
import Elk.Alg.Layered.Intermediate.CommentPostprocessor
import Elk.Alg.Layered.Intermediate.CommentNodeMarginCalculator
import Elk.Alg.Layered.Intermediate.HighDegreeNodeLayeringProcessor
import Elk.Alg.Layered.Intermediate.NodePromotion
/-!
# Layered intermediate processors: constraints, partitions, comments, high-degree nodes, node promotion

Aggregator of the processors that handle layer/in-layer/edge constraints (`EdgeAndLayerConstraintEdgeReverser`,
`LayerConstraintPreprocessor`, `LayerConstraintPostprocessor`, `InLayerConstraintProcessor`,
`ConstraintsPostprocessor`), partitions (`PartitionPreprocessor`, `PartitionMidprocessor`,
`PartitionPostprocessor`), comment boxes (`CommentPreprocessor`, `CommentPostprocessor`,
`CommentNodeMarginCalculator`), `HighDegreeNodeLayeringProcessor` and `NodePromotion`. Each module registers
its processor with `IntermediateProcessorStrategy.register` at initialisation.
-/
