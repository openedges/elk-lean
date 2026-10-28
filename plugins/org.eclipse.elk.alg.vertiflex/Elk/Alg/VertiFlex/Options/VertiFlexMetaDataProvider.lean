import Elk.Core.Data
import Elk.Core.Options
import Elk.Alg.VertiFlex.Options.VertiFlexOptions
/-!
# `org.eclipse.elk.alg.vertiflex.options.VertiFlexMetaDataProvider`

Port of `vertiflex_meta_data_provider.rs` (elk-rs). `apply` registers, in Rust order: the
algorithm entry `org.eclipse.elk.vertiflex` ("ELK VertiFlex", category `org.eclipse.elk.tree`,
supported features `MULTI_EDGES` and `EDGE_LABELS`), the four options (no group, no bounds), and
the option supports (`SPACING_NODE_NODE` default `20.0`, `PADDING` default `5` on all sides,
`INTERACTIVE`, `PORT_CONSTRAINTS`, `EDGE_LABELS_INLINE` default `false`,
`OMIT_NODE_MICRO_LAYOUT`, `MARGINS`, then the four VertiFlex options).

The ENUM option `LAYOUT_STRATEGY` is registered with its choices and the enum parser like the Java
provider, so `elk.vertiflex.layoutStrategy: BEND` from JSON / ELK Text selects the bend router
(`register_option` of elk-rs installs neither, so elk-rs always uses `STRAIGHT` for string inputs;
elk-lean followed that before agent OPT: "oracle 특이점" F5).
-/
namespace Elk.Alg.VertiFlex.Options

open Elk Elk.Graph Elk.Core.Math Elk.Core.Data Elk.Core.Options

namespace VertiFlexMetaDataProvider

/-- `register_algorithm`. -/
def registerAlgorithm (r : Registry) : Registry :=
  let data : LayoutAlgorithmData :=
    { id := VertiFlexOptions.ALGORITHM_ID
      name := "ELK VertiFlex"
      description := "Tree layout algorithm that allows defining set vertical positions for nodes rather than automatically placing nodes on levels according to their topology."
      categoryId := some "org.eclipse.elk.tree"
      definingBundleId := some "org.eclipse.elk.alg.vertiflex" }
  r.registerAlgorithm ((data.addSupportedFeature .multiEdges).addSupportedFeature .edgeLabels)

/-- `register_option` for the non-enum options. -/
private def registerOption {α : Type} [PropCodec α] (r : Registry) (property : Property α)
    (type : LayoutOptionType) (name description : String) (target : LayoutOptionTarget) : Registry :=
  r.registerOption
    { id := property.id, type, defaultValue := property.default.map PropCodec.enc,
      name, description, targets := EnumSet.of #[target], visibility := .visible }

/-- `register_option` for an ENUM option, with the Java enum choices (constant names in ordinal
order) and the enum parser (Java `LayoutOptionData.parseValue` of an `ENUM`). -/
private def registerEnumOption {α : Type} [ElkEnum α] (r : Registry) (property : Property α)
    (name description : String) (target : LayoutOptionTarget) : Registry :=
  r.registerOption
    { id := property.id, type := .enum, defaultValue := property.default.map PropCodec.enc,
      name, description, targets := EnumSet.of #[target], visibility := .visible,
      choices := LayoutOptionData.enumChoices α, parser := some (LayoutOptionData.enumParser α) }

/-- `register_options`. -/
def registerOptions (r : Registry) : Registry :=
  let r := registerOption r VertiFlexOptions.VERTICAL_CONSTRAINT .double
    "Fixed vertical position" "The Y position that the node should be fixed at." .nodes
  let r := registerEnumOption r VertiFlexOptions.LAYOUT_STRATEGY
    "Edge layout strategy"
    "Strategy for the layout of the children. 'straight' for straight line drawings, 'bend' for a possible bend. When straight edges are prioritized the nodes will be reordered in order to guarantee that straight edges are possible. If bend points are enabled on the other hand, the given model order of the nodes is maintained and bend points are introduced to prevent edge node overlaps."
    .nodes
  let r := registerOption r VertiFlexOptions.LAYER_DISTANCE .double
    "Layer distance"
    "The distance to use between nodes of different layers if no vertical constraints are set."
    .parents
  registerOption r VertiFlexOptions.CONSIDER_NODE_MODEL_ORDER .boolean
    "Consider node model order"
    "Consider node model as a secondary criterion when using straight line routing."
    .parents

/-- `register_supports`. -/
def registerSupports (r : Registry) : Registry :=
  let algo := VertiFlexOptions.ALGORITHM_ID
  let r := r.addOptionSupport algo CoreOptions.SPACING_NODE_NODE.id (some (.double 20.0))
  let r := r.addOptionSupport algo CoreOptions.PADDING.id
    (some (PropCodec.enc (⟨5.0, 5.0, 5.0, 5.0⟩ : ElkPadding)))
  let r := r.addOptionSupport algo CoreOptions.INTERACTIVE.id none
  let r := r.addOptionSupport algo CoreOptions.PORT_CONSTRAINTS.id none
  let r := r.addOptionSupport algo CoreOptions.EDGE_LABELS_INLINE.id (some (.bool false))
  let r := r.addOptionSupport algo CoreOptions.OMIT_NODE_MICRO_LAYOUT.id none
  let r := r.addOptionSupport algo CoreOptions.MARGINS.id none
  let r := r.addOptionSupport algo VertiFlexOptions.VERTICAL_CONSTRAINT.id none
  let r := r.addOptionSupport algo VertiFlexOptions.LAYOUT_STRATEGY.id none
  let r := r.addOptionSupport algo VertiFlexOptions.LAYER_DISTANCE.id none
  r.addOptionSupport algo VertiFlexOptions.CONSIDER_NODE_MODEL_ORDER.id none

/-- `VertiFlexMetaDataProvider::apply`. -/
def metaDataProvider : LayoutMetaDataProvider where
  apply r := registerSupports (registerOptions (registerAlgorithm r))

/-- `LayoutMetaDataService::register_layout_meta_data_provider(&VertiFlexMetaDataProvider)`.
Not run at module initialisation; `Elk.Alg.VertiFlex.Init` installs it as an init hook. -/
def register : IO Unit := LayoutMetaDataService.registerLayoutMetaDataProvider metaDataProvider

end VertiFlexMetaDataProvider

end Elk.Alg.VertiFlex.Options
