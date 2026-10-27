import Elk.Alg.Spore.Options.SporeOptions
/-!
# `org.eclipse.elk.alg.spore.options.SporeOverlapRemovalOptions`

Port of `options/spore_overlap_removal_options.rs` (elk-rs): the option constants of the
`org.eclipse.elk.sporeOverlap` algorithm (Java: generated `SporeOverlapRemovalOptions`). Every
constant is an alias of the shared definition in `SporeCommonOptions`.
-/
namespace Elk.Alg.Spore.Options

open Elk Elk.Graph Elk.Core.Math

namespace SporeOverlapRemovalOptions

/-- `SporeOverlapRemovalOptions.ALGORITHM_ID`. -/
def ALGORITHM_ID : String := "org.eclipse.elk.sporeOverlap"

/-- `UNDERLYING_LAYOUT_ALGORITHM`. -/
def UNDERLYING_LAYOUT_ALGORITHM : Property String := SporeCommonOptions.UNDERLYING_LAYOUT_ALGORITHM
/-- `STRUCTURE_EXTRACTION_STRATEGY`. -/
def STRUCTURE_EXTRACTION_STRATEGY : Property StructureExtractionStrategy :=
  SporeCommonOptions.STRUCTURE_EXTRACTION_STRATEGY
/-- `OVERLAP_REMOVAL_MAX_ITERATIONS`. -/
def OVERLAP_REMOVAL_MAX_ITERATIONS : Property Int := SporeCommonOptions.OVERLAP_REMOVAL_MAX_ITERATIONS
/-- `OVERLAP_REMOVAL_RUN_SCANLINE`. -/
def OVERLAP_REMOVAL_RUN_SCANLINE : Property Bool := SporeCommonOptions.OVERLAP_REMOVAL_RUN_SCANLINE

/-- `PADDING`. -/
def PADDING : Property ElkPadding := SporeCommonOptions.PADDING
/-- `SPACING_NODE_NODE`. -/
def SPACING_NODE_NODE : Property Float := SporeCommonOptions.SPACING_NODE_NODE
/-- `DEBUG_MODE`. -/
def DEBUG_MODE : Property Bool := SporeCommonOptions.DEBUG_MODE

end SporeOverlapRemovalOptions

end Elk.Alg.Spore.Options
