import Elk.Alg.Layered.Intermediate.LabelAndNodeSizeProcessor
import Elk.Alg.Layered.Intermediate.InnermostNodeMarginCalculator
import Elk.Alg.Layered.Intermediate.EndLabelPreprocessor
import Elk.Alg.Layered.Intermediate.NodePlacementRepeater
/-!
# Node size and margin processors of `org.eclipse.elk.alg.layered.intermediate` (task I1b)

Aggregator of `LabelAndNodeSizeProcessor` (with its helper modules
`LabelAndNodeSize/{PortPlacement,PortDrivenSizing,ExternalPortDummyLabels}`) and
`InnermostNodeMarginCalculator` (before P4), `EndLabelPreprocessor` (before P4, requested by the
orthogonal/polyline routers) and `NodePlacementRepeater` (after P4, requested for a second node
placer). Each module registers its processor with `IntermediateProcessorStrategy.register` at
initialisation.
-/
