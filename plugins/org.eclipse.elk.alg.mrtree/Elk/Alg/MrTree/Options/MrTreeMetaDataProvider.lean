import Elk.Core.Data
import Elk.Core.Options
import Elk.Alg.MrTree.Options.MrTreeOptions
/-!
# `org.eclipse.elk.alg.mrtree.options.MrTreeMetaDataProvider`

Port of `options/mrtree_meta_data_provider.rs` (elk-rs), the counterpart of the Java
`MrTreeMetaDataProvider` generated from `Tree.melk`. `metaDataProvider.apply` registers, in the order
of the Rust `apply`: the algorithm `org.eclipse.elk.mrtree` (category `org.eclipse.elk.tree`, feature
`DISCONNECTED`), the eight mrtree options, and the option supports (Rust order) with their algorithm
specific defaults.

Rust semantics kept on purpose (they differ from the generated Java provider):
* ENUM options (`weighting`, `edgeRoutingMode`, `searchOrder`) and the OBJECT option
  `graphProperties` are registered **without** enum choices and **without** a parser
  (`register_option` never attaches one). A string value for them in a JSON or `.elkt` graph cannot
  be parsed and is dropped by the importers, exactly like in the elk-rs oracle; typed values set
  through the property API work.
* No legacy ids and no option dependencies are registered; the only bounds are the inclusive lower
  bounds `edgeEndTextureLength >= 0.0` and `treeLevel >= 0`.
* `init_reflect` (registration of clone/default functions for the option value types) has no Lean
  counterpart: `PropCodec` covers it.
-/
namespace Elk.Alg.MrTree.Options

open Elk Elk.Graph Elk.Core.Data Elk.Core.Math Elk.Core.Util Elk.Core.Options

namespace MrTreeMetaDataProvider

/-- `TARGET_PARENTS`. -/
def targetParents : Array LayoutOptionTarget := #[.parents]
/-- `TARGET_NODES`. -/
def targetNodes : Array LayoutOptionTarget := #[.nodes]

/-- `property_default_any`: the default value of a property as a `PropValue`. -/
def propertyDefault {α : Type} [PropCodec α] (property : Property α) : Option PropValue :=
  property.default.map PropCodec.enc

/-- elk-rs `register_option`: id, type, default value, name, description, targets, visibility and
optional lower bound (no group, no choices, no parser). -/
def registerOption {α : Type} [PropCodec α] (r : Registry) (property : Property α)
    (optionType : LayoutOptionType) (name description : String)
    (targets : Array LayoutOptionTarget) (visibility : LayoutOptionVisibility := .visible)
    (lowerBound : Option OptionBound := none) : Registry :=
  r.registerOption
    { id := property.id, type := optionType, defaultValue := propertyDefault property, name,
      description, targets := EnumSet.of targets, visibility, group := "", lowerBound }

/-- elk-rs `register_algorithm`: "ELK Mr. Tree" with the feature `DISCONNECTED`. -/
def algorithmData : LayoutAlgorithmData :=
  let d : LayoutAlgorithmData :=
    { id := MrTreeOptions.ALGORITHM_ID
      name := "ELK Mr. Tree"
      description := "Tree-based algorithm provided by the Eclipse Layout Kernel. Computes a spanning tree of the input graph and arranges all nodes according to the resulting parent-children hierarchy. I pity the fool who doesn't use Mr. Tree Layout."
      categoryId := some "org.eclipse.elk.tree"
      definingBundleId := some "org.eclipse.elk.alg.mrtree"
      previewImagePath := some "images/mrtree_layout.png" }
  d.addSupportedFeature .disconnected

/-- elk-rs `register_options`. -/
def registerOptions (r : Registry) : Registry :=
  let r := registerOption r MrTreeOptions.COMPACTION .boolean "Compaction"
    "Turns on tree compaction which decreases the size of the whole tree by placing nodes of multiple levels in one large level."
    targetParents
  let r := registerOption r MrTreeOptions.EDGE_END_TEXTURE_LENGTH .double "Edge End Texture Length"
    "Should be set to the length of the texture at the end of an edge. This value can be used to improve the edge routing."
    targetParents .visible (some (OptionBound.atLeast 0.0))
  let r := registerOption r MrTreeOptions.TREE_LEVEL .int "Tree Level"
    "The index for the tree level the node is in." targetNodes .visible (some (OptionBound.atLeastInt 0))
  let r := registerOption r MrTreeOptions.POSITION_CONSTRAINT .int "Position Constraint"
    "When set to a positive number this option will force the algorithm to place the node to the specified position within the tree layer if weighting is set to constraint."
    targetNodes
  let r := registerOption r MrTreeOptions.WEIGHTING .enum "Weighting of Nodes"
    "Which weighting to use when computing a node order." targetParents
  let r := registerOption r MrTreeOptions.EDGE_ROUTING_MODE .enum "Edge Routing Mode"
    "Chooses an edge routing algorithm." targetParents
  let r := registerOption r MrTreeOptions.SEARCH_ORDER .enum "Search Order"
    "Which search order to use when computing a spanning tree." targetParents
  registerOption r MrTreeOptions.GRAPH_PROPERTIES .object "Graph Properties"
    "Properties of the graph that can be used to skip unnecessary processing steps." targetParents
    .advanced

/-- elk-rs `register_supports`: the options known to the algorithm with their algorithm specific
default (registration order of Rust). -/
def optionSupports : Array (String × Option PropValue) := #[
  (CoreOptions.PADDING.id, some (PropCodec.enc (ElkPadding.ofAny 20.0))),
  (CoreOptions.SPACING_NODE_NODE.id, some (.double 20.0)),
  (CoreOptions.SPACING_EDGE_NODE.id, some (.double 3.0)),
  (CoreOptions.ASPECT_RATIO.id, some (.double 1.6)),
  (CoreOptions.PRIORITY.id, some (.int 1)),
  (CoreOptions.SEPARATE_CONNECTED_COMPONENTS.id, some (.bool true)),
  (CoreOptions.DEBUG_MODE.id, none),
  (CoreOptions.DIRECTION.id, some (PropCodec.enc Direction.undefined)),
  (CoreOptions.INTERACTIVE.id, none),
  (CoreOptions.INTERACTIVE_LAYOUT.id, none),
  (CoreOptions.NODE_SIZE_CONSTRAINTS.id, none),
  (CoreOptions.NODE_SIZE_FIXED_GRAPH_SIZE.id, none),
  (CoreOptions.NODE_SIZE_MINIMUM.id, none),
  (CoreOptions.NODE_SIZE_OPTIONS.id, none),
  (CoreOptions.NODE_LABELS_PLACEMENT.id, none),
  (CoreOptions.OMIT_NODE_MICRO_LAYOUT.id, none),
  (CoreOptions.PORT_LABELS_PLACEMENT.id, none),
  (CoreOptions.TOPDOWN_LAYOUT.id, none),
  (CoreOptions.TOPDOWN_SCALE_FACTOR.id, none),
  (CoreOptions.TOPDOWN_HIERARCHICAL_NODE_WIDTH.id, none),
  (CoreOptions.TOPDOWN_HIERARCHICAL_NODE_ASPECT_RATIO.id, none),
  (CoreOptions.TOPDOWN_NODE_TYPE.id, some (PropCodec.enc TopdownNodeTypes.hierarchicalNode)),
  (MrTreeOptions.WEIGHTING.id, none),
  (MrTreeOptions.SEARCH_ORDER.id, none),
  (MrTreeOptions.EDGE_ROUTING_MODE.id, none),
  (MrTreeOptions.POSITION_CONSTRAINT.id, none),
  (MrTreeOptions.TREE_LEVEL.id, none),
  (MrTreeOptions.COMPACTION.id, none),
  (MrTreeOptions.EDGE_END_TEXTURE_LENGTH.id, none)]

/-- elk-rs `register_supports`. -/
def registerSupports (r : Registry) : Registry :=
  optionSupports.foldl (fun r (o, d) => r.addOptionSupport MrTreeOptions.ALGORITHM_ID o d) r

/-- `ILayoutMetaDataProvider.apply` of `MrTreeMetaDataProvider`. -/
def metaDataProvider : LayoutMetaDataProvider where
  apply r := registerSupports (registerOptions (r.registerAlgorithm algorithmData))

/-- `LayoutMetaDataService.registerLayoutMetaDataProvider(new MrTreeMetaDataProvider())`: registers
the mrtree metadata with the global service. Run as an init hook (see `Elk.Alg.MrTree.Init`). -/
def register : IO Unit := LayoutMetaDataService.registerLayoutMetaDataProvider metaDataProvider

end MrTreeMetaDataProvider

end Elk.Alg.MrTree.Options
