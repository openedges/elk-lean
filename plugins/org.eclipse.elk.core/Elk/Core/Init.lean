import Elk.Core.Data
import Elk.Core.Options
import Elk.Core.Options.CoreOptionsMeta
import Elk.Core.Labels
/-!
# Core metadata initialisation

Port of `LayoutMetaDataService::get_instance()` / `register_core_algorithms` of elk-rs
(`data/mod.rs`): the first access to the service registers the core algorithms
(fixed, random, box and the layered placeholder entry) and then the providers
`CoreOptions`, `BoxLayouterOptions` and `LabelManagementOptions`, in this order.

The initialisation is installed lazily through `LayoutMetaDataService.setInitHook`
(`initCoreHook`), so the first `getInstance` call runs `initCore`.

The layout provider instances (`FixedLayoutProvider`, `RandomLayoutProvider`,
`BoxLayoutProvider`) are kept in a separate registry; only metadata is registered here.
-/
namespace Elk.Core

open Elk Elk.Graph Elk.Core.Data Elk.Core.Math Elk.Core.Options Elk.Core.Labels

/-- `register_core_algorithms`, fixed layouter: `org.eclipse.elk.fixed` ("ELK Fixed"). -/
def fixedAlgorithmData : LayoutAlgorithmData :=
  let d : LayoutAlgorithmData :=
    { id := FixedLayouterOptions.ALGORITHM_ID
      name := "ELK Fixed"
      description := "Keeps the current layout as it is, without any automatic modification. Optional coordinates can be given for nodes and edge bend points."
      bundleName := some "ELK"
      definingBundleId := some "org.eclipse.elk.core" }
  d.addKnownOptionDefault CoreOptions.PADDING.id (some (PropCodec.enc (ElkPadding.ofAny 15.0)))
    |>.addKnownOptionDefault CoreOptions.POSITION.id none
    |>.addKnownOptionDefault CoreOptions.BEND_POINTS.id none
    |>.addKnownOptionDefault CoreOptions.NODE_SIZE_CONSTRAINTS.id none
    |>.addKnownOptionDefault CoreOptions.NODE_SIZE_MINIMUM.id none
    |>.addKnownOptionDefault CoreOptions.NODE_SIZE_FIXED_GRAPH_SIZE.id none

/-- `register_core_algorithms`, random layouter: `org.eclipse.elk.random` ("ELK Randomizer"). -/
def randomAlgorithmData : LayoutAlgorithmData :=
  let d : LayoutAlgorithmData :=
    { id := RandomLayouterOptions.ALGORITHM_ID
      name := "ELK Randomizer"
      description := "Distributes the nodes randomly on the plane, leading to very obfuscating layouts. Can be useful to demonstrate the power of \"real\" layout algorithms."
      bundleName := some "ELK"
      definingBundleId := some "org.eclipse.elk.core"
      previewImagePath := some "images/random_layout.png" }
  d.addKnownOptionDefault CoreOptions.PADDING.id (some (PropCodec.enc (ElkPadding.ofAny 15.0)))
    |>.addKnownOptionDefault CoreOptions.SPACING_NODE_NODE.id (some (.double 15.0))
    |>.addKnownOptionDefault CoreOptions.RANDOM_SEED.id (some (.int 0))
    |>.addKnownOptionDefault CoreOptions.ASPECT_RATIO.id (some (.double 1.6))

/-- `register_core_algorithms`, box layouter: `org.eclipse.elk.box` ("ELK Box"). -/
def boxAlgorithmData : LayoutAlgorithmData :=
  let d : LayoutAlgorithmData :=
    { id := BoxLayouterOptions.ALGORITHM_ID
      name := "ELK Box"
      description := "Algorithm for packing of unconnected boxes, i.e. graphs without edges."
      bundleName := some "ELK"
      definingBundleId := some "org.eclipse.elk.core"
      previewImagePath := some "images/box_layout.png" }
  d.addKnownOptionDefault CoreOptions.PADDING.id (some (PropCodec.enc (ElkPadding.ofAny 15.0)))
    |>.addKnownOptionDefault CoreOptions.SPACING_NODE_NODE.id (some (.double 15.0))
    |>.addKnownOptionDefault CoreOptions.PRIORITY.id (some (.int 0))
    |>.addKnownOptionDefault CoreOptions.EXPAND_NODES.id none
    |>.addKnownOptionDefault CoreOptions.NODE_SIZE_CONSTRAINTS.id none
    |>.addKnownOptionDefault CoreOptions.NODE_SIZE_OPTIONS.id none
    |>.addKnownOptionDefault CoreOptions.ASPECT_RATIO.id (some (.double 1.3))
    |>.addKnownOptionDefault CoreOptions.INTERACTIVE.id none
    |>.addKnownOptionDefault CoreOptions.NODE_SIZE_MINIMUM.id none
    |>.addKnownOptionDefault BoxLayouterOptions.BOX_PACKING_MODE.id none
    |>.addKnownOptionDefault CoreOptions.CONTENT_ALIGNMENT.id none

/-- `register_core_algorithms`, layered placeholder entry: `org.eclipse.elk.layered`
("ELK Layered"); the real algorithm plugin completes it later. -/
def layeredAlgorithmData : LayoutAlgorithmData :=
  let d : LayoutAlgorithmData :=
    { id := "org.eclipse.elk.layered"
      name := "ELK Layered"
      description := "Layer-based algorithm provided by the Eclipse Layout Kernel. Arranges as many edges as possible into one direction by placing nodes into subsequent layers. This implementation supports different routing styles (straight, orthogonal, splines); if orthogonal routing is selected, arbitrary port constraints are respected, thus enabling the layout of block diagrams such as actor-oriented models or circuit schematics. Furthermore, full layout of compound graphs with cross-hierarchy edges is supported when the respective option is activated on the top level."
      categoryId := some "org.eclipse.elk.layered"
      definingBundleId := some "org.eclipse.elk.alg.layered"
      previewImagePath := some "images/layered_layout.png" }
  let d := d.addSupportedFeature .selfLoops
    |>.addSupportedFeature .insideSelfLoops
    |>.addSupportedFeature .multiEdges
    |>.addSupportedFeature .edgeLabels
    |>.addSupportedFeature .ports
    |>.addSupportedFeature .compound
    |>.addSupportedFeature .clusters
  d.addKnownOptionDefault CoreOptions.SPACING_COMMENT_COMMENT.id none
    |>.addKnownOptionDefault CoreOptions.SPACING_COMMENT_NODE.id none
    |>.addKnownOptionDefault CoreOptions.SPACING_COMPONENT_COMPONENT.id none
    |>.addKnownOptionDefault CoreOptions.SPACING_EDGE_EDGE.id none
    |>.addKnownOptionDefault CoreOptions.SPACING_EDGE_LABEL.id none
    |>.addKnownOptionDefault CoreOptions.SPACING_EDGE_NODE.id none
    |>.addKnownOptionDefault CoreOptions.SPACING_LABEL_LABEL.id none
    |>.addKnownOptionDefault CoreOptions.SPACING_LABEL_PORT_HORIZONTAL.id none
    |>.addKnownOptionDefault CoreOptions.SPACING_LABEL_PORT_VERTICAL.id none
    |>.addKnownOptionDefault CoreOptions.SPACING_LABEL_NODE.id none
    |>.addKnownOptionDefault CoreOptions.SPACING_NODE_NODE.id none
    |>.addKnownOptionDefault CoreOptions.SPACING_NODE_SELF_LOOP.id none
    |>.addKnownOptionDefault CoreOptions.SPACING_PORT_PORT.id none
    |>.addKnownOptionDefault CoreOptions.SPACING_INDIVIDUAL.id none
    |>.addKnownOptionDefault CoreOptions.PRIORITY.id (some (.int 0))
    |>.addKnownOptionDefault CoreOptions.SEPARATE_CONNECTED_COMPONENTS.id (some (.bool true))
    |>.addKnownOptionDefault CoreOptions.PORT_ALIGNMENT_DEFAULT.id
      (some (PropCodec.enc PortAlignment.justified))
    |>.addKnownOptionDefault CoreOptions.TOPDOWN_LAYOUT.id none
    |>.addKnownOptionDefault CoreOptions.TOPDOWN_SCALE_FACTOR.id none
    |>.addKnownOptionDefault CoreOptions.TOPDOWN_HIERARCHICAL_NODE_WIDTH.id none
    |>.addKnownOptionDefault CoreOptions.TOPDOWN_HIERARCHICAL_NODE_ASPECT_RATIO.id none
    |>.addKnownOptionDefault CoreOptions.TOPDOWN_NODE_TYPE.id
      (some (PropCodec.enc TopdownNodeTypes.hierarchicalNode))
    |>.addKnownOptionDefault CoreOptions.PADDING.id (some (PropCodec.enc (ElkPadding.ofAny 12.0)))
    |>.addKnownOptionDefault CoreOptions.EDGE_ROUTING.id
      (some (PropCodec.enc EdgeRouting.orthogonal))
    |>.addKnownOptionDefault CoreOptions.PORT_BORDER_OFFSET.id (some (.double 0.0))
    |>.addKnownOptionDefault CoreOptions.RANDOM_SEED.id (some (.int 1))
    |>.addKnownOptionDefault CoreOptions.ASPECT_RATIO.id (some (.double 1.6))
    |>.addKnownOptionDefault CoreOptions.NO_LAYOUT.id none

/-- `LayoutMetaDataService::register_core_algorithms`: registers the fixed, random and box
algorithms and the layered placeholder entry (skipped if already present). -/
def registerCoreAlgorithms : IO Unit := do
  if (← LayoutMetaDataService.getAlgorithmData FixedLayouterOptions.ALGORITHM_ID).isSome then return
  LayoutMetaDataService.registerAlgorithm fixedAlgorithmData
  LayoutMetaDataService.registerAlgorithm randomAlgorithmData
  LayoutMetaDataService.registerAlgorithm boxAlgorithmData
  LayoutMetaDataService.registerAlgorithm layeredAlgorithmData

/-- The lazy initialisation of `LayoutMetaDataService::get_instance()`: core algorithms, then
the providers `CoreOptions`, `BoxLayouterOptions` and `LabelManagementOptions`. -/
def initCore : IO Unit := do
  registerCoreAlgorithms
  LayoutMetaDataService.registerLayoutMetaDataProvider CoreOptions.metaDataProvider
  LayoutMetaDataService.registerLayoutMetaDataProvider BoxLayouterOptions.metaDataProvider
  LayoutMetaDataService.registerLayoutMetaDataProvider
    LabelManagementOptions.metaDataProvider

/-- Installs `initCore` as the init hook of the metadata service. -/
builtin_initialize initCoreHook : Unit ← LayoutMetaDataService.setInitHook initCore

end Elk.Core
