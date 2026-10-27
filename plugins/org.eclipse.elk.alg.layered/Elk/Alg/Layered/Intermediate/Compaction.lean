import Elk.Alg.Layered.Intermediate.Compaction.VerticalSegment
import Elk.Alg.Layered.Intermediate.Compaction.CompactionMetadata
import Elk.Alg.Layered.Intermediate.Compaction.SpecialSpacingsHandler
import Elk.Alg.Layered.Intermediate.Compaction.EdgeAwareScanlineConstraintCalculation
import Elk.Alg.Layered.Intermediate.Compaction.NetworkSimplexCompaction
import Elk.Alg.Layered.Intermediate.Compaction.LGraphToCGraphTransformer
/-!
# `org.eclipse.elk.alg.layered.intermediate.compaction`

Aggregator of the companions of `HorizontalGraphCompactor` (Java package
`intermediate.compaction`; elk-rs keeps them in `intermediate/horizontal_graph_compactor.rs`):
`VerticalSegment`, `LGraphToCGraphTransformer`, `EdgeAwareScanlineConstraintCalculation`,
`NetworkSimplexCompaction`, the special spacings handler and the elk-rs `CompactionMetadata`.
-/
