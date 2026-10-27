import Elk.Core.Data
import Elk.Core.Options
import Elk.Alg.RectPacking.Options.RectPackingOptions
/-!
# `org.eclipse.elk.alg.rectpacking.options.RectPackingMetaDataProvider`

Port of `options/rect_packing_meta_data_provider.rs` (elk-rs), the counterpart of the Java
`RectPackingMetaDataProvider` generated from `RectPacking.melk`. `apply` registers, in the order of
the Rust `apply`: the algorithm `org.eclipse.elk.rectpacking` ("ELK Rectangle Packing"), the
thirteen options, and the option supports (with the algorithm defaults `aspectRatio` 1.3,
`nodeSize.fixedGraphSize` false, `padding` 15, `spacing.nodeNode` 15).

Rust semantics kept on purpose (they differ from the generated Java provider):
* ENUM options are registered **without** enum choices and **without** a parser (the Rust
  `register_option` helper of this plugin never attaches one; `init_reflect` only registers
  clone/default functions). A string value of such an option in a JSON graph therefore cannot be
  parsed (`LayoutOptionData.parseValue` is `none`) and is dropped by the importer, as in elk-rs.
  Typed values set through the property API work. (Java registers the enum choices.)
* No category (the algorithm lands in the "Other" backup category), no legacy ids, no option
  dependencies, no upper bounds and no supported graph features. The lower bounds of
  `packing.compaction.iterations` (1), `currentPosition` (-1) and `desiredPosition` (-1) are
  registered as inclusive integer bounds.
* The default of an option is the property default (`property_default_any`).
-/
namespace Elk.Alg.RectPacking.Options

open Elk Elk.Graph Elk.Core.Data Elk.Core.Math Elk.Core.Options

namespace RectPackingMetaDataProvider

/-- `TARGET_PARENTS`. -/
def targetParents : Array LayoutOptionTarget := #[.parents]

/-- `TARGET_NODES`. -/
def targetNodes : Array LayoutOptionTarget := #[.nodes]

/-- `property_default_any`: the default value of a property as a `PropValue`. -/
def propertyDefault {α : Type} [PropCodec α] (property : Property α) : Option PropValue :=
  property.default.map PropCodec.enc

/-- `register_option`: id, type, default value, name, description, targets, visibility, group and
optional (inclusive) lower bound; no parser and no choices. -/
def registerOption {α : Type} [PropCodec α] (r : Registry) (property : Property α)
    (optionType : LayoutOptionType) (name description : String)
    (targets : Array LayoutOptionTarget) (visibility : LayoutOptionVisibility)
    (group : Option String) (lowerBound : Option OptionBound) : Registry :=
  r.registerOption
    { id := property.id, type := optionType, defaultValue := propertyDefault property, name,
      description, targets := EnumSet.of targets, visibility, group := group.getD "",
      lowerBound := lowerBound }

/-- `register_algorithm`. -/
def registerAlgorithm (r : Registry) : Registry :=
  r.registerAlgorithm
    { id := RectPackingOptions.ALGORITHM_ID
      name := "ELK Rectangle Packing"
      description := "Algorithm for packing of unconnected boxes, i.e. graphs without edges. The given order of the boxes is " ++
        "always preserved and the main reading direction of the boxes is left to right. The algorithm is divided " ++
        "into two phases. One phase approximates the width in which the rectangles can be placed. The next phase " ++
        "places the rectangles in rows using the previously calculated width as bounding width and bundles " ++
        "rectangles with a similar height in blocks. A compaction step reduces the size of the drawing. Finally, " ++
        "the rectangles are expanded to fill their bounding box and eliminate empty unused spaces."
      definingBundleId := some "org.eclipse.elk.alg.rectpacking" }

/-- `register_options`, in the Rust order. -/
def registerOptions (r : Registry) : Registry :=
  let r := registerOption r RectPackingOptions.WIDTH_APPROXIMATION_STRATEGY .enum
    "Width Approximation Strategy" "Strategy for finding an initial width of the drawing."
    targetParents .visible (some "widthApproximation") none
  let r := registerOption r RectPackingOptions.WIDTH_APPROXIMATION_TARGET_WIDTH .double
    "Target Width" "Target width for placement; padding is added externally."
    targetParents .visible (some "widthApproximation") none
  let r := registerOption r RectPackingOptions.WIDTH_APPROXIMATION_OPTIMIZATION_GOAL .enum
    "Optimization Goal"
    "Optimization goal for approximation of the bounding box given by the first iteration."
    targetParents .visible (some "widthApproximation") none
  let r := registerOption r RectPackingOptions.WIDTH_APPROXIMATION_LAST_PLACE_SHIFT .boolean
    "Shift Last Placed" "Allow a shift when placing behind or below the last placed rectangle."
    targetParents .visible (some "widthApproximation") none
  let r := registerOption r RectPackingOptions.PACKING_STRATEGY .enum
    "Compaction Strategy" "Strategy for finding an initial placement on nodes."
    targetParents .visible (some "packing") none
  let r := registerOption r RectPackingOptions.PACKING_COMPACTION_ROW_HEIGHT_REEVALUATION .boolean
    "Row Height Reevaluation" "Reevaluate row height during compaction if needed."
    targetParents .visible (some "packing.compaction") none
  let r := registerOption r RectPackingOptions.PACKING_COMPACTION_ITERATIONS .int
    "Compaction iterations" "Number of compaction iterations."
    targetParents .visible (some "packing.compaction") (some (OptionBound.atLeastInt 1))
  let r := registerOption r RectPackingOptions.WHITE_SPACE_ELIMINATION_STRATEGY .enum
    "White Space Approximation Strategy" "Strategy for expanding nodes to eliminate whitespace."
    targetParents .visible (some "whiteSpaceElimination") none
  let r := registerOption r RectPackingOptions.TRYBOX .boolean
    "Try box layout first" "Check whether regions are stackable to use box layout."
    targetParents .advanced none none
  let r := registerOption r RectPackingOptions.CURRENT_POSITION .int
    "Current position of a node in the order of nodes" "Specifies the current position of a node."
    targetNodes .visible none (some (OptionBound.atLeastInt (-1)))
  let r := registerOption r RectPackingOptions.DESIRED_POSITION .int
    "Desired index of node" "Desired position of a node in the ordering."
    targetNodes .advanced none (some (OptionBound.atLeastInt (-1)))
  let r := registerOption r RectPackingOptions.IN_NEW_ROW .boolean
    "In new Row" "If true, this node begins a new row."
    targetNodes .visible none none
  registerOption r RectPackingOptions.ORDER_BY_SIZE .boolean
    "Order nodes by height" "Sort nodes by height before layout."
    targetParents .visible none none

/-- `register_supports`, in the Rust order. -/
def registerSupports (r : Registry) : Registry :=
  let algo := RectPackingOptions.ALGORITHM_ID
  let r := r.addOptionSupport algo CoreOptions.ASPECT_RATIO.id (some (.double 1.3))
  let r := r.addOptionSupport algo CoreOptions.NODE_SIZE_FIXED_GRAPH_SIZE.id (some (.bool false))
  let r := r.addOptionSupport algo CoreOptions.PADDING.id (some (PropCodec.enc (ElkPadding.ofAny 15.0)))
  let r := r.addOptionSupport algo CoreOptions.SPACING_NODE_NODE.id (some (.double 15.0))
  let r := r.addOptionSupport algo CoreOptions.CONTENT_ALIGNMENT.id none
  let r := r.addOptionSupport algo CoreOptions.NODE_SIZE_CONSTRAINTS.id none
  let r := r.addOptionSupport algo CoreOptions.NODE_SIZE_MINIMUM.id none
  let r := r.addOptionSupport algo CoreOptions.NODE_SIZE_OPTIONS.id none
  let r := r.addOptionSupport algo CoreOptions.NODE_LABELS_PLACEMENT.id none
  let r := r.addOptionSupport algo CoreOptions.OMIT_NODE_MICRO_LAYOUT.id none
  let r := r.addOptionSupport algo CoreOptions.PORT_LABELS_PLACEMENT.id none
  let r := r.addOptionSupport algo RectPackingOptions.WIDTH_APPROXIMATION_OPTIMIZATION_GOAL.id none
  let r := r.addOptionSupport algo RectPackingOptions.WIDTH_APPROXIMATION_LAST_PLACE_SHIFT.id none
  let r := r.addOptionSupport algo RectPackingOptions.WIDTH_APPROXIMATION_TARGET_WIDTH.id none
  let r := r.addOptionSupport algo RectPackingOptions.WIDTH_APPROXIMATION_STRATEGY.id none
  let r := r.addOptionSupport algo RectPackingOptions.PACKING_STRATEGY.id none
  let r := r.addOptionSupport algo RectPackingOptions.PACKING_COMPACTION_ROW_HEIGHT_REEVALUATION.id none
  let r := r.addOptionSupport algo RectPackingOptions.PACKING_COMPACTION_ITERATIONS.id none
  let r := r.addOptionSupport algo RectPackingOptions.WHITE_SPACE_ELIMINATION_STRATEGY.id none
  let r := r.addOptionSupport algo CoreOptions.INTERACTIVE.id none
  let r := r.addOptionSupport algo CoreOptions.INTERACTIVE_LAYOUT.id none
  let r := r.addOptionSupport algo RectPackingOptions.DESIRED_POSITION.id none
  let r := r.addOptionSupport algo RectPackingOptions.CURRENT_POSITION.id none
  let r := r.addOptionSupport algo RectPackingOptions.IN_NEW_ROW.id none
  let r := r.addOptionSupport algo RectPackingOptions.TRYBOX.id none
  r.addOptionSupport algo RectPackingOptions.ORDER_BY_SIZE.id none

/-- `ILayoutMetaDataProvider.apply` of `RectPackingMetaDataProvider`. -/
def metaDataProvider : LayoutMetaDataProvider where
  apply r := registerSupports (registerOptions (registerAlgorithm r))

/-- `LayoutMetaDataService.registerLayoutMetaDataProvider(new RectPackingMetaDataProvider())`.
Not run at module initialisation; `Elk.Alg.RectPacking.Init` installs it as an init hook
(rank 60, the elk-rs registration order). -/
def register : IO Unit := LayoutMetaDataService.registerLayoutMetaDataProvider metaDataProvider

end RectPackingMetaDataProvider

end Elk.Alg.RectPacking.Options
