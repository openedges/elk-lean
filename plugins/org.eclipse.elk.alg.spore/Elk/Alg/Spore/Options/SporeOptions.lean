import Elk.Core.Options
import Elk.Alg.Spore.Options.CompactionStrategy
import Elk.Alg.Spore.Options.RootSelection
import Elk.Alg.Spore.Options.SpanningTreeCostFunction
import Elk.Alg.Spore.Options.StructureExtractionStrategy
import Elk.Alg.Spore.Options.TreeConstructionStrategy
/-!
# Shared SPOrE option constants

Port of `options/spore_options.rs` (elk-rs, `SporeCommonOptions`): the property constants shared by
`SporeCompactionOptions` and `SporeOverlapRemovalOptions`. Java generates the two option classes
from `Spore.melk` and has no common class; elk-rs keeps the definitions in one place, and so does
this port. Ids and defaults are those of the Rust statics; `i32` options are `Property Int`.
-/
namespace Elk.Alg.Spore.Options

open Elk Elk.Graph Elk.Core.Math Elk.Core.Options

namespace SporeCommonOptions

/-- `UNDERLYING_LAYOUT_ALGORITHM` (`org.eclipse.elk.underlyingLayoutAlgorithm`, no default): a layout
algorithm that is applied to the graph before it is compacted. -/
def UNDERLYING_LAYOUT_ALGORITHM : Property String :=
  Property.mk' "org.eclipse.elk.underlyingLayoutAlgorithm"

/-- `STRUCTURE_EXTRACTION_STRATEGY` (default `DELAUNAY_TRIANGULATION`). -/
def STRUCTURE_EXTRACTION_STRATEGY : Property StructureExtractionStrategy :=
  Property.withDefault "org.eclipse.elk.structure.structureExtractionStrategy"
    StructureExtractionStrategy.delaunayTriangulation

/-- `PROCESSING_ORDER_TREE_CONSTRUCTION` (default `MINIMUM_SPANNING_TREE`). -/
def PROCESSING_ORDER_TREE_CONSTRUCTION : Property TreeConstructionStrategy :=
  Property.withDefault "org.eclipse.elk.processingOrder.treeConstruction"
    TreeConstructionStrategy.minimumSpanningTree

/-- `PROCESSING_ORDER_SPANNING_TREE_COST_FUNCTION` (default `CIRCLE_UNDERLAP`). -/
def PROCESSING_ORDER_SPANNING_TREE_COST_FUNCTION : Property SpanningTreeCostFunction :=
  Property.withDefault "org.eclipse.elk.processingOrder.spanningTreeCostFunction"
    SpanningTreeCostFunction.circleUnderlap

/-- `PROCESSING_ORDER_PREFERRED_ROOT` (no default): identifier of the preferred root node. -/
def PROCESSING_ORDER_PREFERRED_ROOT : Property String :=
  Property.mk' "org.eclipse.elk.processingOrder.preferredRoot"

/-- `PROCESSING_ORDER_ROOT_SELECTION` (default `CENTER_NODE`). -/
def PROCESSING_ORDER_ROOT_SELECTION : Property RootSelection :=
  Property.withDefault "org.eclipse.elk.processingOrder.rootSelection" RootSelection.centerNode

/-- `COMPACTION_COMPACTION_STRATEGY` (default `DEPTH_FIRST`). -/
def COMPACTION_COMPACTION_STRATEGY : Property CompactionStrategy :=
  Property.withDefault "org.eclipse.elk.compaction.compactionStrategy" CompactionStrategy.depthFirst

/-- `COMPACTION_ORTHOGONAL` (default `false`). -/
def COMPACTION_ORTHOGONAL : Property Bool :=
  Property.withDefault "org.eclipse.elk.compaction.orthogonal" false

/-- `OVERLAP_REMOVAL_MAX_ITERATIONS` (default `64`). -/
def OVERLAP_REMOVAL_MAX_ITERATIONS : Property Int :=
  Property.withDefault "org.eclipse.elk.overlapRemoval.maxIterations" 64

/-- `OVERLAP_REMOVAL_RUN_SCANLINE` (default `true`). -/
def OVERLAP_REMOVAL_RUN_SCANLINE : Property Bool :=
  Property.withDefault "org.eclipse.elk.overlapRemoval.runScanline" true

/-- `PADDING` (alias of `CoreOptions.PADDING`). -/
def PADDING : Property ElkPadding := CoreOptions.PADDING

/-- `SPACING_NODE_NODE` (alias of `CoreOptions.SPACING_NODE_NODE`). -/
def SPACING_NODE_NODE : Property Float := CoreOptions.SPACING_NODE_NODE

/-- `DEBUG_MODE` (alias of `CoreOptions.DEBUG_MODE`). -/
def DEBUG_MODE : Property Bool := CoreOptions.DEBUG_MODE

end SporeCommonOptions

end Elk.Alg.Spore.Options
