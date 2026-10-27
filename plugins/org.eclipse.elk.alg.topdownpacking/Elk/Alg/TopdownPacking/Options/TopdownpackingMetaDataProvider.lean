import Elk.Core.Data
import Elk.Core.Options
import Elk.Alg.TopdownPacking.Options.TopdownpackingOptions
/-!
# `org.eclipse.elk.alg.topdownpacking.options.TopdownpackingMetaDataProvider`

Port of `topdownpacking_meta_data_provider.rs` (elk-rs). `apply` registers, in Rust order:
the algorithm entry `org.eclipse.elk.topdownpacking` ("ELK Top-down Packing"), the two strategy
options (enum, `PARENTS`, visible, groups `nodeArrangement` / `whitespaceElimination`), and the
option supports (`PADDING`, `SPACING_NODE_NODE`, the two hierarchical node options,
`TOPDOWN_LAYOUT`, `TOPDOWN_NODE_TYPE` with default `PARALLEL_NODE`, and the two strategies).
Like elk-rs, no category, no legacy ids, no bounds and no dependencies are registered.
-/
namespace Elk.Alg.TopdownPacking.Options

open Elk Elk.Graph Elk.Core.Data Elk.Core.Options

namespace TopdownpackingMetaDataProvider

/-- `register_algorithm`. -/
def registerAlgorithm (r : Registry) : Registry :=
  r.registerAlgorithm
    { id := TopdownpackingOptions.ALGORITHM_ID
      name := "ELK Top-down Packing"
      description := "An algorithm for placing boxes of fixed sizes. Expands boxes horizontally to fill empty whitespace. This algorithm can be used standalone or specifically for {@link CoreOptions.TOPDOWN_LAYOUT}. In this use case it should be set for nodes whose {@link CoreOptions.TOPDOWN_NODE_TYPE} is set to {@link TopdownNodeTypes.PARALLEL_NODE}. This allows topdown layout to give children larger sizes based on their number of children."
      definingBundleId := some "org.eclipse.elk.alg.topdownpacking" }

/-- `register_option` for an ENUM option with the lenient enum parser. -/
private def registerEnumOption {α : Type} [ElkEnum α] (r : Registry) (property : Property α)
    (name description : String) (group : String) : Registry :=
  r.registerOption
    { id := property.id, type := .enum, defaultValue := property.default.map PropCodec.enc,
      name, description, targets := EnumSet.of #[.parents], visibility := .visible, group,
      choices := LayoutOptionData.enumChoices α, parser := some (LayoutOptionData.enumParser α) }

/-- `register_options`. -/
def registerOptions (r : Registry) : Registry :=
  let r := registerEnumOption r TopdownpackingOptions.NODE_ARRANGEMENT_STRATEGY
    "Node arrangement strategy"
    "Strategy for node arrangement. The strategy determines the size of the resulting graph."
    "nodeArrangement"
  registerEnumOption r TopdownpackingOptions.WHITESPACE_ELIMINATION_STRATEGY
    "Whitespace elimination strategy" "Strategy for whitespace elimination." "whitespaceElimination"

/-- `register_supports`. -/
def registerSupports (r : Registry) : Registry :=
  let algo := TopdownpackingOptions.ALGORITHM_ID
  let r := r.addOptionSupport algo CoreOptions.PADDING.id none
  let r := r.addOptionSupport algo CoreOptions.SPACING_NODE_NODE.id none
  let r := r.addOptionSupport algo CoreOptions.TOPDOWN_HIERARCHICAL_NODE_WIDTH.id none
  let r := r.addOptionSupport algo CoreOptions.TOPDOWN_HIERARCHICAL_NODE_ASPECT_RATIO.id none
  let r := r.addOptionSupport algo CoreOptions.TOPDOWN_LAYOUT.id none
  let r := r.addOptionSupport algo CoreOptions.TOPDOWN_NODE_TYPE.id
    (some (PropCodec.enc TopdownNodeTypes.parallelNode))
  let r := r.addOptionSupport algo TopdownpackingOptions.NODE_ARRANGEMENT_STRATEGY.id none
  r.addOptionSupport algo TopdownpackingOptions.WHITESPACE_ELIMINATION_STRATEGY.id none

/-- `TopdownpackingMetaDataProvider::apply`. -/
def metaDataProvider : LayoutMetaDataProvider where
  apply r := registerSupports (registerOptions (registerAlgorithm r))

/-- `LayoutMetaDataService::register_layout_meta_data_provider(&TopdownpackingMetaDataProvider)`.
Not run at module initialisation; `Elk.Alg.TopdownPacking.Init` installs it as an init hook. -/
def register : IO Unit := LayoutMetaDataService.registerLayoutMetaDataProvider metaDataProvider

end TopdownpackingMetaDataProvider

end Elk.Alg.TopdownPacking.Options
