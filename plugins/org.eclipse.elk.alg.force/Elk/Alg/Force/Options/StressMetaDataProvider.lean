import Elk.Core.Data
import Elk.Core.Options
import Elk.Alg.Force.Options.StressOptions
import Elk.Alg.Force.Options.ForceMetaDataProvider
/-!
# `org.eclipse.elk.alg.force.options.StressMetaDataProvider`

Port of `stress_meta_data_provider.rs` (elk-rs), the counterpart of the Java `StressMetaDataProvider`
generated from `Stress.melk`. `metaDataProvider.apply` registers the algorithm entry
`org.eclipse.elk.stress`, the five stress options and the option supports, in Rust order.

As for `ForceMetaDataProvider`, the ENUM option `DIMENSION` is registered with its choices and the
enum parser like the Java provider, so `"elk.stress.dimension": "X"` from JSON takes effect (elk-rs
registers neither and ignores the string, which elk-lean followed before agent OPT: "oracle 특이점"
F1).
-/
namespace Elk.Alg.Force.Options

open Elk Elk.Graph Elk.Core.Data Elk.Core.Math Elk.Core.Util Elk.Core.Options

namespace StressMetaDataProvider

/-- `TARGET_PARENTS`. -/
def targetParents : Array LayoutOptionTarget := #[.parents]
/-- `TARGET_NODES`. -/
def targetNodes : Array LayoutOptionTarget := #[.nodes]
/-- `TARGET_PARENTS_EDGES`. -/
def targetParentsEdges : Array LayoutOptionTarget := #[.parents, .edges]

/-- elk-rs `register_algorithm`: "ELK Stress" (no supported features). -/
def algorithmData : LayoutAlgorithmData :=
  { id := StressOptions.ALGORITHM_ID
    name := "ELK Stress"
    description := "Minimizes the stress within a layout using stress majorization. Stress exists if the euclidean distance between a pair of nodes doesn't match their graph theoretic distance, that is, the shortest path between the two nodes. The method allows to specify individual edge lengths."
    categoryId := some "org.eclipse.elk.force"
    definingBundleId := some "org.eclipse.elk.alg.force"
    previewImagePath := some "images/stress_layout.png" }

/-- elk-rs `register_options`. -/
def registerOptions (r : Registry) : Registry :=
  let r := ForceMetaDataProvider.registerOption r StressOptions.FIXED .boolean "Fixed Position"
    "Prevent that the node is moved by the layout algorithm." targetNodes
  let r := ForceMetaDataProvider.registerOption r StressOptions.DESIRED_EDGE_LENGTH .double
    "Desired Edge Length"
    "Either specified for parent nodes or for individual edges, where the latter takes higher precedence."
    targetParentsEdges
  let r := ForceMetaDataProvider.registerEnumOption r StressOptions.DIMENSION "Layout Dimension"
    "Dimensions that are permitted to be altered during layout." targetParents
  let r := ForceMetaDataProvider.registerOption r StressOptions.EPSILON .double "Stress Epsilon"
    "Termination criterion for the iterative process." targetParents
  ForceMetaDataProvider.registerOption r StressOptions.ITERATION_LIMIT .int "Iteration Limit"
    "Maximum number of performed iterations. Takes higher precedence than 'epsilon'." targetParents

/-- elk-rs `register_supports`. -/
def optionSupports : Array (String × Option PropValue) := #[
  (CoreOptions.INTERACTIVE.id, none),
  (CoreOptions.EDGE_LABELS_INLINE.id, some (.bool true)),
  (CoreOptions.NODE_SIZE_CONSTRAINTS.id, none),
  (CoreOptions.NODE_SIZE_MINIMUM.id, none),
  (CoreOptions.NODE_SIZE_OPTIONS.id, none),
  (CoreOptions.NODE_LABELS_PLACEMENT.id, none),
  (CoreOptions.OMIT_NODE_MICRO_LAYOUT.id, none),
  (CoreOptions.PORT_LABELS_PLACEMENT.id, none),
  (StressOptions.FIXED.id, none),
  (StressOptions.DIMENSION.id, none),
  (StressOptions.EPSILON.id, none),
  (StressOptions.ITERATION_LIMIT.id, none),
  (StressOptions.DESIRED_EDGE_LENGTH.id, none)]

/-- elk-rs `register_supports`. -/
def registerSupports (r : Registry) : Registry :=
  optionSupports.foldl (fun r (o, d) => r.addOptionSupport StressOptions.ALGORITHM_ID o d) r

/-- `ILayoutMetaDataProvider.apply` of `StressMetaDataProvider`. -/
def metaDataProvider : LayoutMetaDataProvider where
  apply r := registerSupports (registerOptions (r.registerAlgorithm algorithmData))

/-- `LayoutMetaDataService.registerLayoutMetaDataProvider(new StressMetaDataProvider())`. -/
def register : IO Unit := LayoutMetaDataService.registerLayoutMetaDataProvider metaDataProvider

end StressMetaDataProvider

end Elk.Alg.Force.Options
