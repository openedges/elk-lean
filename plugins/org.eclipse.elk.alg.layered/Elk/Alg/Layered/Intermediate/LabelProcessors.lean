import Elk.Alg.Layered.Intermediate.LabelDummyInserter
import Elk.Alg.Layered.Intermediate.LabelDummySwitcher
import Elk.Alg.Layered.Intermediate.LabelManagementProcessor
import Elk.Alg.Layered.Intermediate.LabelSideSelector
import Elk.Alg.Layered.Intermediate.LayerSizeAndGraphHeightCalculator
import Elk.Alg.Layered.Intermediate.LabelDummyRemover
import Elk.Alg.Layered.Intermediate.EndLabelSorter
import Elk.Alg.Layered.Intermediate.EndLabelPostprocessor
/-!
# Label intermediate processors of `org.eclipse.elk.alg.layered.intermediate` (task I1)

Aggregator of the label related processors: `LabelDummyInserter` (before P2), `LabelDummySwitcher`,
`LabelManagementProcessor` (`END_NODE_PORT_…` and `CENTER_…`), `LabelSideSelector` (before P4),
`LayerSizeAndGraphHeightCalculator` (before P5), `LabelDummyRemover`, `EndLabelSorter` and
`EndLabelPostprocessor` (after P5). Each module registers its processor(s) with
`IntermediateProcessorStrategy.register` at initialisation.
-/
