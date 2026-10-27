import Elk.Core.Data
import Elk.Core.Options
import Elk.Alg.Radial.Options.RadialOptions
/-!
# `org.eclipse.elk.alg.radial.options.RadialMetaDataProvider`

Port of `radial_meta_data_provider.rs` (elk-rs). `apply` registers, in Rust order: the algorithm
entry `org.eclipse.elk.radial` ("ELK Radial", category `org.eclipse.elk.radial`, preview image
`images/radial_layout.png`), the twelve radial options (`CENTER_ON_ROOT`, `ORDER_ID`, `RADIUS`,
`ROTATE`, the three `rotation` group options, `COMPACTOR`, `COMPACTION_STEP_SIZE` with lower
bound `0`, `SORTER`, `WEDGE_CRITERIA`, `OPTIMIZATION_CRITERIA`) and the twenty option supports.
Like elk-rs, no legacy ids, no dependencies and no upper bounds are registered.

Parity quirk (elk-rs is the oracle): the Rust provider registers the four enum options (`COMPACTOR`,
`SORTER`, `WEDGE_CRITERIA`, `OPTIMIZATION_CRITERIA`) without enum choices and without a value
parser (Java: derived from the enum class). Their string values from JSON / ELK Text are therefore
ignored by elk-rs (`parse_value` returns `None`), and so by this port. The options remain usable
through the typed API (`ElkM.setNodeProp`). `enumParserProvider` is the Java-like variant (with
choices and the lenient enum parser) used by the tests that check the enum-driven code paths.
-/
namespace Elk.Alg.Radial.Options

open Elk Elk.Graph Elk.Core.Data Elk.Core.Options

namespace RadialMetaDataProvider

/-- `register_algorithm`. -/
def registerAlgorithm (r : Registry) : Registry :=
  r.registerAlgorithm
    { id := RadialOptions.ALGORITHM_ID
      name := "ELK Radial"
      description := "A radial layout provider which is based on the algorithm of Peter Eades published in \"Drawing free trees.\", published by International Institute for Advanced Study of Social Information Science, Fujitsu Limited in 1991. The radial layouter takes a tree and places the nodes in radial order around the root. The nodes of the same tree level are placed on the same radius."
      previewImagePath := some "images/radial_layout.png"
      categoryId := some "org.eclipse.elk.radial"
      definingBundleId := some "org.eclipse.elk.alg.radial" }

/-- `register_option` for a non-enum option (the default is the property's default). -/
private def registerPlain {α : Type} [PropCodec α] (r : Registry) (property : Property α)
    (type : LayoutOptionType) (name description : String) (targets : Array LayoutOptionTarget)
    (visibility : LayoutOptionVisibility) (group : String := "")
    (lowerBound : Option OptionBound := none) : Registry :=
  r.registerOption
    { id := property.id, type, defaultValue := property.default.map PropCodec.enc, name, description,
      targets := EnumSet.of targets, visibility, group, lowerBound }

/-- `register_option` for an ENUM option. Like elk-rs, no choices and no parser are registered
(`LayoutOptionData.parse_value` of an ENUM option without parser yields `None`), so the string
values of the four enum options cannot be set from JSON / ELK Text; see the module doc. -/
private def registerEnum {α : Type} [ElkEnum α] (r : Registry) (property : Property α)
    (name description : String) : Registry :=
  r.registerOption
    { id := property.id, type := .enum, defaultValue := property.default.map PropCodec.enc,
      name, description, targets := EnumSet.of #[.parents], visibility := .visible }

/-- `register_options`. -/
def registerOptions (r : Registry) : Registry :=
  let parents := #[LayoutOptionTarget.parents]
  let r := registerPlain r RadialOptions.CENTER_ON_ROOT .boolean "Center On Root"
    "Centers the layout on the root of the tree so that the central node is also the center node of the final layout."
    parents .visible
  let r := registerPlain r RadialOptions.ORDER_ID .int "Order ID"
    "The id can be used to define an order for nodes of one radius." #[.nodes] .visible
  let r := registerPlain r RadialOptions.RADIUS .double "Radius"
    "The radius option can be used to set the initial radius for the radial layouter."
    parents .visible
  let r := registerPlain r RadialOptions.ROTATE .boolean "Rotate"
    "Determines whether a rotation of the layout should be performed." parents .visible
  let r := registerPlain r RadialOptions.ROTATION_TARGET_ANGLE .double "Target Angle"
    "The angle in radians that the layout should be rotated to after layout."
    parents .visible "rotation"
  let r := registerPlain r RadialOptions.ROTATION_COMPUTE_ADDITIONAL_WEDGE_SPACE .boolean
    "Additional Wedge Space"
    "If set to true, modifies the target angle by rotating further such that space is left for an edge to pass in between the nodes."
    parents .advanced "rotation"
  let r := registerPlain r RadialOptions.ROTATION_OUTGOING_EDGE_ANGLES .boolean "Outgoing Edge Angles"
    "Calculate the required angle of connected nodes to leave space for an incoming edge."
    parents .advanced "rotation"
  let r := registerEnum r RadialOptions.COMPACTOR "Compaction"
    "Determine how compaction on the graph is done."
  let r := registerPlain r RadialOptions.COMPACTION_STEP_SIZE .int "Compaction Step Size"
    "Determine the size of steps with which the compaction is done." parents .visible
    (lowerBound := some (OptionBound.atLeastInt 0))
  let r := registerEnum r RadialOptions.SORTER "Sorter"
    "Sort the nodes per radius according to the sorting algorithm."
  let r := registerEnum r RadialOptions.WEDGE_CRITERIA "Annulus Wedge Criteria"
    "Determine how the wedge for the node placement is calculated."
  registerEnum r RadialOptions.OPTIMIZATION_CRITERIA "Translation Optimization"
    "Find the optimal translation of the nodes of the first radii according to this criteria."

/-- `register_supports`. -/
def registerSupports (r : Registry) : Registry :=
  let algo := RadialOptions.ALGORITHM_ID
  let ids : Array String := #[
    CoreOptions.POSITION.id, CoreOptions.SPACING_NODE_NODE.id, CoreOptions.NODE_SIZE_CONSTRAINTS.id,
    CoreOptions.NODE_SIZE_MINIMUM.id, CoreOptions.NODE_SIZE_OPTIONS.id,
    CoreOptions.NODE_LABELS_PLACEMENT.id, CoreOptions.OMIT_NODE_MICRO_LAYOUT.id,
    CoreOptions.PORT_LABELS_PLACEMENT.id,
    RadialOptions.COMPACTION_STEP_SIZE.id, RadialOptions.COMPACTOR.id, RadialOptions.ROTATE.id,
    RadialOptions.ROTATION_TARGET_ANGLE.id, RadialOptions.ROTATION_COMPUTE_ADDITIONAL_WEDGE_SPACE.id,
    RadialOptions.ROTATION_OUTGOING_EDGE_ANGLES.id, RadialOptions.OPTIMIZATION_CRITERIA.id,
    RadialOptions.ORDER_ID.id, RadialOptions.RADIUS.id, RadialOptions.SORTER.id,
    RadialOptions.WEDGE_CRITERIA.id, RadialOptions.CENTER_ON_ROOT.id]
  ids.foldl (fun r id => r.addOptionSupport algo id none) r

/-- Java-like variant of the four enum options: same entries as `registerOptions`, plus the enum
choices and the lenient enum parser. Registering it replaces the entries in place. Not part of
the elk-rs provider; see the module doc. -/
def enumParserProvider : LayoutMetaDataProvider where
  apply r :=
    let withParser {α : Type} [ElkEnum α] (r : Registry) (property : Property α)
        (name description : String) : Registry :=
      r.registerOption
        { id := property.id, type := .enum, defaultValue := property.default.map PropCodec.enc,
          name, description, targets := EnumSet.of #[.parents], visibility := .visible,
          choices := LayoutOptionData.enumChoices α, parser := some (LayoutOptionData.enumParser α) }
    let r := withParser r RadialOptions.COMPACTOR "Compaction"
      "Determine how compaction on the graph is done."
    let r := withParser r RadialOptions.SORTER "Sorter"
      "Sort the nodes per radius according to the sorting algorithm."
    let r := withParser r RadialOptions.WEDGE_CRITERIA "Annulus Wedge Criteria"
      "Determine how the wedge for the node placement is calculated."
    withParser r RadialOptions.OPTIMIZATION_CRITERIA "Translation Optimization"
      "Find the optimal translation of the nodes of the first radii according to this criteria."

/-- `RadialMetaDataProvider::apply`. -/
def metaDataProvider : LayoutMetaDataProvider where
  apply r := registerSupports (registerOptions (registerAlgorithm r))

/-- `LayoutMetaDataService::register_layout_meta_data_provider(&RadialMetaDataProvider)`.
Not run at module initialisation; `Elk.Alg.Radial.Init` installs it as an init hook. -/
def register : IO Unit := LayoutMetaDataService.registerLayoutMetaDataProvider metaDataProvider

end RadialMetaDataProvider

end Elk.Alg.Radial.Options
