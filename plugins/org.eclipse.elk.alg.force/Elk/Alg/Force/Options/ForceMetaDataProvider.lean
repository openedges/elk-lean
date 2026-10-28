import Elk.Core.Data
import Elk.Core.Options
import Elk.Alg.Force.Options.ForceOptions
/-!
# `org.eclipse.elk.alg.force.options.ForceMetaDataProvider`

Port of `force_meta_data_provider.rs` (elk-rs), the counterpart of the Java `ForceMetaDataProvider`
generated from `Force.melk`. `metaDataProvider.apply` registers, in the order of the Rust `apply`:
the algorithm entry `org.eclipse.elk.force`, the five force options, and the option supports
(`registerSupports`, in Rust order) with their algorithm specific defaults.

The ENUM option `MODEL` is registered with its choices and the enum parser like the Java provider,
so `"elk.force.model": "EADES"` from JSON or `.elkt` selects the Eades model (elk-rs registers it
without choices and parser and ignores the string, which elk-lean followed before agent OPT:
"oracle 특이점" F1). The algorithm specific defaults of the option supports are those of the
redeclared `ForceOptions` constants (Java `addOptionSupport(.., X_DEFAULT)`; the aspect ratio is
`1.6f` widened to double, elk-rs registers `1.6`).

Rust semantics kept:
* No legacy ids and no option dependencies are registered.
* Option supports that name an option nobody registered are dropped by
  `LayoutMetaDataService.applyRegistry`, like `Registry::apply_dependencies` does.
-/
namespace Elk.Alg.Force.Options

open Elk Elk.Graph Elk.Core.Data Elk.Core.Math Elk.Core.Util Elk.Core.Options

namespace ForceMetaDataProvider

/-- `TARGET_PARENTS`. -/
def targetParents : Array LayoutOptionTarget := #[.parents]
/-- `TARGET_EDGES`. -/
def targetEdges : Array LayoutOptionTarget := #[.edges]

/-- `property_default_any`: the default value of a property as a `PropValue`. -/
def propertyDefault {α : Type} [PropCodec α] (property : Property α) : Option PropValue :=
  property.default.map PropCodec.enc

/-- elk-rs `register_option`: id, type, default value, name, description, targets, visibility and
optional lower bound (no group, no choices, no parser). -/
def registerOption {α : Type} [PropCodec α] (r : Registry) (property : Property α)
    (optionType : LayoutOptionType) (name description : String)
    (targets : Array LayoutOptionTarget) (lowerBound : Option OptionBound := none) : Registry :=
  r.registerOption
    { id := property.id, type := optionType, defaultValue := propertyDefault property, name,
      description, targets := EnumSet.of targets, visibility := .visible, group := "", lowerBound }

/-- `register_option` for an ENUM option: as `registerOption`, plus the Java enum choices (constant
names in ordinal order) and the enum parser (Java `LayoutOptionData.parseValue` of an `ENUM`). -/
def registerEnumOption {α : Type} [ElkEnum α] (r : Registry) (property : Property α)
    (name description : String) (targets : Array LayoutOptionTarget) : Registry :=
  r.registerOption
    { id := property.id, type := .enum, defaultValue := propertyDefault property, name,
      description, targets := EnumSet.of targets, visibility := .visible, group := "",
      choices := LayoutOptionData.enumChoices α, parser := some (LayoutOptionData.enumParser α) }

/-- elk-rs `register_algorithm`: "ELK Force" with the features `MULTI_EDGES` and `EDGE_LABELS`. -/
def algorithmData : LayoutAlgorithmData :=
  let d : LayoutAlgorithmData :=
    { id := ForceOptions.ALGORITHM_ID
      name := "ELK Force"
      description := "Force-based algorithm provided by the Eclipse Layout Kernel. Implements methods that follow physical analogies by simulating forces that move the nodes into a balanced distribution. Currently the original Eades model and the Fruchterman - Reingold model are supported."
      categoryId := some "org.eclipse.elk.force"
      definingBundleId := some "org.eclipse.elk.alg.force"
      previewImagePath := some "images/force_layout.png" }
  (d.addSupportedFeature .multiEdges).addSupportedFeature .edgeLabels

/-- elk-rs `register_options`. -/
def registerOptions (r : Registry) : Registry :=
  let r := registerEnumOption r ForceOptions.MODEL "Force Model"
    "Determines the model for force calculation." targetParents
  let r := registerOption r ForceOptions.ITERATIONS .int "Iterations"
    "The number of iterations on the force model." targetParents (some (OptionBound.atLeastInt 1))
  let r := registerOption r ForceOptions.REPULSIVE_POWER .int "Repulsive Power"
    "Determines how many bend points are added to the edge; such bend points are regarded as repelling particles in the force model"
    targetEdges (some (OptionBound.atLeastInt 0))
  let r := registerOption r ForceOptions.TEMPERATURE .double "FR Temperature"
    "The temperature is used as a scaling factor for particle displacements." targetParents
    (some (OptionBound.greaterThan 0.0))
  registerOption r ForceOptions.REPULSION .double "Eades Repulsion"
    "Factor for repulsive forces in Eades' model." targetParents (some (OptionBound.greaterThan 0.0))

/-- elk-rs `register_supports`: the options known to the algorithm with their algorithm specific
default (registration order of Rust; the values of the redeclared `ForceOptions` constants). -/
def optionSupports : Array (String × Option PropValue) := #[
  (CoreOptions.PRIORITY.id, propertyDefault ForceOptions.PRIORITY),
  (CoreOptions.SPACING_NODE_NODE.id, propertyDefault ForceOptions.SPACING_NODE_NODE),
  (CoreOptions.SPACING_EDGE_LABEL.id, propertyDefault ForceOptions.SPACING_EDGE_LABEL),
  (CoreOptions.ASPECT_RATIO.id, propertyDefault ForceOptions.ASPECT_RATIO),
  (CoreOptions.RANDOM_SEED.id, propertyDefault ForceOptions.RANDOM_SEED),
  (CoreOptions.SEPARATE_CONNECTED_COMPONENTS.id, propertyDefault ForceOptions.SEPARATE_CONNECTED_COMPONENTS),
  (CoreOptions.PADDING.id, propertyDefault ForceOptions.PADDING),
  (CoreOptions.INTERACTIVE.id, none),
  (CoreOptions.PORT_CONSTRAINTS.id, none),
  (CoreOptions.EDGE_LABELS_INLINE.id, some (.bool false)),
  (CoreOptions.OMIT_NODE_MICRO_LAYOUT.id, none),
  (CoreOptions.NODE_SIZE_FIXED_GRAPH_SIZE.id, none),
  (CoreOptions.NODE_SIZE_OPTIONS.id, none),
  (CoreOptions.NODE_SIZE_CONSTRAINTS.id, none),
  (CoreOptions.NODE_LABELS_PLACEMENT.id, none),
  (CoreOptions.PORT_LABELS_PLACEMENT.id, none),
  (ForceOptions.MODEL.id, none),
  (ForceOptions.TEMPERATURE.id, none),
  (ForceOptions.ITERATIONS.id, none),
  (ForceOptions.REPULSION.id, none),
  (ForceOptions.REPULSIVE_POWER.id, none),
  (CoreOptions.TOPDOWN_LAYOUT.id, none),
  (CoreOptions.TOPDOWN_SCALE_FACTOR.id, none),
  (CoreOptions.TOPDOWN_HIERARCHICAL_NODE_WIDTH.id, none),
  (CoreOptions.TOPDOWN_HIERARCHICAL_NODE_ASPECT_RATIO.id, none),
  (CoreOptions.TOPDOWN_NODE_TYPE.id, propertyDefault ForceOptions.TOPDOWN_NODE_TYPE)]

/-- elk-rs `register_supports`. -/
def registerSupports (r : Registry) : Registry :=
  optionSupports.foldl (fun r (o, d) => r.addOptionSupport ForceOptions.ALGORITHM_ID o d) r

/-- `ILayoutMetaDataProvider.apply` of `ForceMetaDataProvider`. -/
def metaDataProvider : LayoutMetaDataProvider where
  apply r := registerSupports (registerOptions (r.registerAlgorithm algorithmData))

/-- `LayoutMetaDataService.registerLayoutMetaDataProvider(new ForceMetaDataProvider())`: registers
the force metadata with the global service. Not run at module initialisation (see `Init`). -/
def register : IO Unit := LayoutMetaDataService.registerLayoutMetaDataProvider metaDataProvider

end ForceMetaDataProvider

end Elk.Alg.Force.Options
