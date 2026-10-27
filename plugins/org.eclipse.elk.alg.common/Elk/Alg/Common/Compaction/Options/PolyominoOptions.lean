import Elk.Graph.Properties
import Elk.Core.Options.CoreOptionsMeta
import Elk.Alg.Common.Compaction.Options.TraversalStrategy
import Elk.Alg.Common.Compaction.Options.HighLevelSortingCriterion
import Elk.Alg.Common.Compaction.Options.LowLevelSortingCriterion
/-!
# `org.eclipse.elk.alg.common.compaction.options.PolyominoOptions`

The polyomino options (generated from `Polyomino.melk` in Java) and their
`ILayoutMetaDataProvider` (elk-rs `polyomino_options.rs`): four options of the group
`polyomino`, all targeting parents and visible, registered in the Rust order. The Rust
`init_reflect` registration has no Lean counterpart (enum values are encoded through
`ElkEnum`).
-/
namespace Elk.Alg.Common.Compaction.Options

open Elk Elk.Graph Elk.Core.Data Elk.Core.Options.CoreOptionsMeta

namespace PolyominoOptions

/-- `PolyominoOptions.POLYOMINO_TRAVERSAL_STRATEGY` (`org.eclipse.elk.polyomino.traversalStrategy`). -/
def POLYOMINO_TRAVERSAL_STRATEGY : Property TraversalStrategy :=
  Property.withDefault "org.eclipse.elk.polyomino.traversalStrategy" .quadrantsLineByLine

/-- `PolyominoOptions.POLYOMINO_LOW_LEVEL_SORT` (`org.eclipse.elk.polyomino.lowLevelSort`). -/
def POLYOMINO_LOW_LEVEL_SORT : Property LowLevelSortingCriterion :=
  Property.withDefault "org.eclipse.elk.polyomino.lowLevelSort" .bySizeAndShape

/-- `PolyominoOptions.POLYOMINO_HIGH_LEVEL_SORT` (`org.eclipse.elk.polyomino.highLevelSort`). -/
def POLYOMINO_HIGH_LEVEL_SORT : Property HighLevelSortingCriterion :=
  Property.withDefault "org.eclipse.elk.polyomino.highLevelSort"
    .numOfExternalSidesThanNumOfExtensionsLast

/-- `PolyominoOptions.POLYOMINO_FILL` (`org.eclipse.elk.polyomino.fill`). -/
def POLYOMINO_FILL : Property Bool :=
  Property.withDefault "org.eclipse.elk.polyomino.fill" true

/-- `PolyominoOptions.apply(registry)` (elk-rs `register_options`). -/
def metaDataProvider : LayoutMetaDataProvider where
  apply r :=
    let r := registerEnumOption r POLYOMINO_TRAVERSAL_STRATEGY
      ((OptionMeta.visible "Polyomino Traversal Strategy"
        "Traversal strategy for trying different candidate positions for polyominoes."
        targetParents).withGroup "polyomino")
    let r := registerEnumOption r POLYOMINO_LOW_LEVEL_SORT
      ((OptionMeta.visible "Polyomino Secondary Sorting Criterion"
        ("Possible secondary sorting criteria for the processing order of polyominoes. " ++
          "They are used when polyominoes are equal according to the primary sorting criterion HighLevelSortingCriterion.")
        targetParents).withGroup "polyomino")
    let r := registerEnumOption r POLYOMINO_HIGH_LEVEL_SORT
      ((OptionMeta.visible "Polyomino Primary Sorting Criterion"
        "Possible primary sorting criteria for the processing order of polyominoes."
        targetParents).withGroup "polyomino")
    registerOption r POLYOMINO_FILL .boolean
      ((OptionMeta.visible "Fill Polyominoes"
        ("Use the Profile Fill algorithm to fill polyominoes to prevent small polyominoes " ++
          "from being placed inside of big polyominoes with large holes. Might increase packing area.")
        targetParents).withGroup "polyomino")

end PolyominoOptions

end Elk.Alg.Common.Compaction.Options
