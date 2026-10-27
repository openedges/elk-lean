import Elk.Alg.Spore.Options.SporeOptions
/-!
# `org.eclipse.elk.alg.spore.options.SporeCompactionOptions`

Port of `options/spore_compaction_options.rs` (elk-rs): the option constants of the
`org.eclipse.elk.sporeCompaction` algorithm (Java: generated `SporeCompactionOptions`). Every
constant is an alias of the shared definition in `SporeCommonOptions`.
-/
namespace Elk.Alg.Spore.Options

open Elk Elk.Graph Elk.Core.Math

namespace SporeCompactionOptions

/-- `SporeCompactionOptions.ALGORITHM_ID`. -/
def ALGORITHM_ID : String := "org.eclipse.elk.sporeCompaction"

/-- `UNDERLYING_LAYOUT_ALGORITHM`. -/
def UNDERLYING_LAYOUT_ALGORITHM : Property String := SporeCommonOptions.UNDERLYING_LAYOUT_ALGORITHM
/-- `STRUCTURE_EXTRACTION_STRATEGY`. -/
def STRUCTURE_EXTRACTION_STRATEGY : Property StructureExtractionStrategy :=
  SporeCommonOptions.STRUCTURE_EXTRACTION_STRATEGY
/-- `PROCESSING_ORDER_TREE_CONSTRUCTION`. -/
def PROCESSING_ORDER_TREE_CONSTRUCTION : Property TreeConstructionStrategy :=
  SporeCommonOptions.PROCESSING_ORDER_TREE_CONSTRUCTION
/-- `PROCESSING_ORDER_SPANNING_TREE_COST_FUNCTION`. -/
def PROCESSING_ORDER_SPANNING_TREE_COST_FUNCTION : Property SpanningTreeCostFunction :=
  SporeCommonOptions.PROCESSING_ORDER_SPANNING_TREE_COST_FUNCTION
/-- `PROCESSING_ORDER_PREFERRED_ROOT`. -/
def PROCESSING_ORDER_PREFERRED_ROOT : Property String :=
  SporeCommonOptions.PROCESSING_ORDER_PREFERRED_ROOT
/-- `PROCESSING_ORDER_ROOT_SELECTION`. -/
def PROCESSING_ORDER_ROOT_SELECTION : Property RootSelection :=
  SporeCommonOptions.PROCESSING_ORDER_ROOT_SELECTION
/-- `COMPACTION_COMPACTION_STRATEGY`. -/
def COMPACTION_COMPACTION_STRATEGY : Property CompactionStrategy :=
  SporeCommonOptions.COMPACTION_COMPACTION_STRATEGY
/-- `COMPACTION_ORTHOGONAL`. -/
def COMPACTION_ORTHOGONAL : Property Bool := SporeCommonOptions.COMPACTION_ORTHOGONAL

/-- `PADDING`. -/
def PADDING : Property ElkPadding := SporeCommonOptions.PADDING
/-- `SPACING_NODE_NODE`. -/
def SPACING_NODE_NODE : Property Float := SporeCommonOptions.SPACING_NODE_NODE
/-- `DEBUG_MODE`. -/
def DEBUG_MODE : Property Bool := SporeCommonOptions.DEBUG_MODE

end SporeCompactionOptions

end Elk.Alg.Spore.Options
