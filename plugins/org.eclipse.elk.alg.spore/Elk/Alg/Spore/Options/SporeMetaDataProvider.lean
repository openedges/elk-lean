import Elk.Core.Data
import Elk.Alg.Spore.Options.SporeCompactionOptions
import Elk.Alg.Spore.Options.SporeOverlapRemovalOptions
/-!
# `org.eclipse.elk.alg.spore.options.SporeMetaDataProvider`

Port of `options/spore_meta_data_provider.rs` (elk-rs), the counterpart of the Java
`SporeMetaDataProvider` generated from `Spore.melk`. `apply` registers, in the order of the Rust
`apply`: the two algorithms (`org.eclipse.elk.sporeOverlap`, `org.eclipse.elk.sporeCompaction`),
the ten options, and the option supports of both algorithms (in the Rust order).

Rust semantics kept on purpose (they differ from the generated Java provider):
* ENUM options are registered **without** enum choices and **without** a parser (the Rust
  `register_option` helper of this plugin never attaches one, unlike the layered helper). A string
  value for such an option (for example `"org.eclipse.elk.processingOrder.treeConstruction":
  "MAXIMUM_SPANNING_TREE"` in a JSON graph) therefore cannot be parsed
  (`LayoutOptionData.parseValue` is `none`) and is dropped by the importer, exactly as in elk-rs.
  Typed values set through the property API work. (Java registers the enum choices.)
* No legacy ids, no option dependencies, no lower/upper bounds, no category and no supported
  graph features are registered.
* The default of an option is the property default (`property_default_any`); options without a
  property default (`underlyingLayoutAlgorithm`, `processingOrder.preferredRoot`) have none.
-/
namespace Elk.Alg.Spore.Options

open Elk Elk.Graph Elk.Core.Data Elk.Core.Math Elk.Core.Options

namespace SporeMetaDataProvider

/-- `TARGET_PARENTS`. -/
def targetParents : Array LayoutOptionTarget := #[.parents]

/-- `property_default_any`: the default value of a property as a `PropValue`. -/
def propertyDefault {α : Type} [PropCodec α] (property : Property α) : Option PropValue :=
  property.default.map PropCodec.enc

/-- `register_option`: id, type, default value, name, description, targets, visibility and group;
no parser, no choices and no bounds (the Rust helper takes a lower bound but every call passes
`None`). -/
def registerOption {α : Type} [PropCodec α] (r : Registry) (property : Property α)
    (optionType : LayoutOptionType) (name description : String)
    (targets : Array LayoutOptionTarget) (visibility : LayoutOptionVisibility)
    (group : Option String) : Registry :=
  r.registerOption
    { id := property.id, type := optionType, defaultValue := propertyDefault property, name,
      description, targets := EnumSet.of targets, visibility, group := group.getD "" }

/-- `register_algorithms`: the overlap removal and the compaction algorithm. -/
def registerAlgorithms (r : Registry) : Registry :=
  let overlap : LayoutAlgorithmData :=
    { id := SporeOverlapRemovalOptions.ALGORITHM_ID
      name := "ELK SPOrE Overlap Removal"
      description := "A node overlap removal algorithm proposed by Nachmanson et al. in \"Node overlap removal by growing a tree\"."
      definingBundleId := some "org.eclipse.elk.alg.spore"
      previewImagePath := some "images/overlap-removal.png" }
  let compaction : LayoutAlgorithmData :=
    { id := SporeCompactionOptions.ALGORITHM_ID
      name := "ELK SPOrE Compaction"
      description := "ShrinkTree is a compaction algorithm that maintains the topology of a layout. The relocation of diagram elements is based on contracting a spanning tree."
      definingBundleId := some "org.eclipse.elk.alg.spore"
      previewImagePath := some "images/compaction-example.png" }
  (r.registerAlgorithm overlap).registerAlgorithm compaction

/-- `register_options`. -/
def registerOptions (r : Registry) : Registry :=
  let r := registerOption r SporeCompactionOptions.UNDERLYING_LAYOUT_ALGORITHM .string
    "Underlying Layout Algorithm"
    "A layout algorithm that is applied to the graph before it is compacted. If this is null, nothing is applied before compaction."
    targetParents .visible none
  let r := registerOption r SporeCompactionOptions.STRUCTURE_EXTRACTION_STRATEGY .enum
    "Structure Extraction Strategy"
    "This option defines what kind of triangulation or other partitioning of the plane is applied to the vertices."
    targetParents .advanced (some "structure")
  let r := registerOption r SporeCompactionOptions.PROCESSING_ORDER_TREE_CONSTRUCTION .enum
    "Tree Construction Strategy"
    "Whether a minimum spanning tree or a maximum spanning tree should be constructed."
    targetParents .advanced (some "processingOrder")
  let r := registerOption r SporeCompactionOptions.PROCESSING_ORDER_SPANNING_TREE_COST_FUNCTION .enum
    "Cost Function for Spanning Tree"
    "The cost function is used in the creation of the spanning tree."
    targetParents .visible (some "processingOrder")
  let r := registerOption r SporeCompactionOptions.PROCESSING_ORDER_PREFERRED_ROOT .string
    "Root node for spanning tree construction"
    "The identifier of the node that is preferred as the root of the spanning tree. If this is null, the first node is chosen."
    targetParents .advanced (some "processingOrder")
  let r := registerOption r SporeCompactionOptions.PROCESSING_ORDER_ROOT_SELECTION .enum
    "Root selection for spanning tree"
    "This sets the method used to select a root node for the construction of a spanning tree"
    targetParents .advanced (some "processingOrder")
  let r := registerOption r SporeCompactionOptions.COMPACTION_COMPACTION_STRATEGY .enum
    "Compaction Strategy"
    "This option defines how the compaction is applied."
    targetParents .advanced (some "compaction")
  let r := registerOption r SporeCompactionOptions.COMPACTION_ORTHOGONAL .boolean
    "Orthogonal Compaction"
    "Restricts the translation of nodes to orthogonal directions in the compaction phase."
    targetParents .advanced (some "compaction")
  let r := registerOption r SporeOverlapRemovalOptions.OVERLAP_REMOVAL_MAX_ITERATIONS .int
    "Upper limit for iterations of overlap removal" ""
    targetParents .visible (some "overlapRemoval")
  registerOption r SporeOverlapRemovalOptions.OVERLAP_REMOVAL_RUN_SCANLINE .boolean
    "Whether to run a supplementary scanline overlap check." ""
    targetParents .advanced (some "overlapRemoval")

/-- `register_supports`: the option supports of the overlap removal, then of the compaction
algorithm, with their algorithm-specific defaults (`padding` 8, `spacing.nodeNode` 8, `debugMode`
false). -/
def registerSupports (r : Registry) : Registry :=
  let overlap := SporeOverlapRemovalOptions.ALGORITHM_ID
  let r := r.addOptionSupport overlap SporeOverlapRemovalOptions.UNDERLYING_LAYOUT_ALGORITHM.id none
  let r := r.addOptionSupport overlap CoreOptions.PADDING.id (some (PropCodec.enc (ElkPadding.ofAny 8.0)))
  let r := r.addOptionSupport overlap CoreOptions.SPACING_NODE_NODE.id (some (.double 8.0))
  let r := r.addOptionSupport overlap SporeOverlapRemovalOptions.STRUCTURE_EXTRACTION_STRATEGY.id none
  let r := r.addOptionSupport overlap SporeOverlapRemovalOptions.OVERLAP_REMOVAL_MAX_ITERATIONS.id none
  let r := r.addOptionSupport overlap SporeOverlapRemovalOptions.OVERLAP_REMOVAL_RUN_SCANLINE.id none
  let r := r.addOptionSupport overlap CoreOptions.DEBUG_MODE.id (some (.bool false))
  let compaction := SporeCompactionOptions.ALGORITHM_ID
  let r := r.addOptionSupport compaction SporeCompactionOptions.UNDERLYING_LAYOUT_ALGORITHM.id none
  let r := r.addOptionSupport compaction SporeCompactionOptions.PROCESSING_ORDER_TREE_CONSTRUCTION.id none
  let r := r.addOptionSupport compaction SporeCompactionOptions.PROCESSING_ORDER_SPANNING_TREE_COST_FUNCTION.id none
  let r := r.addOptionSupport compaction SporeCompactionOptions.PROCESSING_ORDER_PREFERRED_ROOT.id none
  let r := r.addOptionSupport compaction SporeCompactionOptions.PROCESSING_ORDER_ROOT_SELECTION.id none
  let r := r.addOptionSupport compaction CoreOptions.PADDING.id (some (PropCodec.enc (ElkPadding.ofAny 8.0)))
  let r := r.addOptionSupport compaction CoreOptions.SPACING_NODE_NODE.id (some (.double 8.0))
  let r := r.addOptionSupport compaction SporeCompactionOptions.STRUCTURE_EXTRACTION_STRATEGY.id none
  let r := r.addOptionSupport compaction SporeCompactionOptions.COMPACTION_COMPACTION_STRATEGY.id none
  let r := r.addOptionSupport compaction SporeCompactionOptions.COMPACTION_ORTHOGONAL.id none
  r.addOptionSupport compaction CoreOptions.DEBUG_MODE.id (some (.bool false))

/-- `ILayoutMetaDataProvider.apply` of `SporeMetaDataProvider`. -/
def metaDataProvider : LayoutMetaDataProvider where
  apply r := registerSupports (registerOptions (registerAlgorithms r))

/-- `LayoutMetaDataService.registerLayoutMetaDataProvider(new SporeMetaDataProvider())`:
registers the SPOrE metadata with the global service. Not run at module initialisation (see
`Elk.Alg.Spore.Init`). -/
def register : IO Unit := LayoutMetaDataService.registerLayoutMetaDataProvider metaDataProvider

end SporeMetaDataProvider

end Elk.Alg.Spore.Options
