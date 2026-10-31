import Elk.Core.Data
import Elk.Core.Options
import Elk.Core.Options.CoreOptionsMeta
import Elk.Alg.Common.Compaction.Options.PolyominoOptions
import Elk.Alg.Disco.Options.DisCoOptions
/-!
# `org.eclipse.elk.alg.disco.options.DisCoMetaDataProvider`

Port of `disco_meta_data_provider.rs` (elk-rs), the counterpart of the Java
`DisCoMetaDataProvider` generated from `Disco.melk`. `metaDataProvider.apply` registers, in the
order of the Rust `apply`:
1. the algorithm entry `org.eclipse.elk.disco` ("ELK DisCo", defining bundle
   `org.eclipse.elk.alg.disco`, preview image `images/disco_layout.png`; no category, no graph
   features, no known options yet);
2. the four options of the group `componentCompaction`/`debug` (strategy, component layout
   algorithm, debug graph, debug polyominoes), all targeting parents;
3. the option supports (algorithm-specific defaults), `register_supports`.

The strategy option is registered with its choices and the enum parser like the Java provider
(`register_option` of elk-rs only sets the value type, so elk-rs cannot set it from a string; it has
a single constant, `POLYOMINO`, so this changes no layout).

Java semantics (agent DIS; elk-rs differs):
* the support default of every option is the option's own default (`DisCoOptions` passes
  `X.getDefault()`): `spacing.componentComponent` 20, `edge.thickness` 1, `aspectRatio` none (the
  core option has no default; elk-rs 1.0), `padding` 12 (elk-rs 0), the three polyomino enums
  their `Polyomino.melk` defaults (elk-rs none: their `ElkReflect` registration was missing),
  `polyomino.fill` true, `componentCompaction.strategy` `POLYOMINO`;
* the polyomino options themselves are registered by `PolyominoOptions.metaDataProvider`, which
  ELK Java loads through the `ServiceLoader` entry of `org.eclipse.elk.alg.common`
  (`META-INF/services/org.eclipse.elk.core.data.ILayoutMetaDataProvider`); elk-rs never applies it,
  so its JSON importer ignored `org.eclipse.elk.polyomino.*` and the supports were dropped.
  `Elk.Alg.Disco.Init` registers it right before DisCo. Only `polyomino.fill` changes a layout
  (`DisCoPolyominoCompactor` reads it from the graph); Java's `PolyominoCompactor` reads the
  other three from an empty `Polyominoes` holder, i.e. always their defaults.
-/
namespace Elk.Alg.Disco.Options

open Elk Elk.Graph Elk.Core.Data Elk.Core.Math Elk.Core.Options
open Elk.Core.Options.CoreOptionsMeta
open Elk.Alg.Common.Compaction.Options

namespace DisCoMetaDataProvider

/-- The `org.eclipse.elk.disco` algorithm entry (`register_algorithm`). -/
def algorithmData : LayoutAlgorithmData :=
  { id := DisCoOptions.ALGORITHM_ID
    name := "ELK DisCo"
    description := "Layouter for arranging unconnected subgraphs. The subgraphs themselves are, by default, not laid out."
    definingBundleId := some "org.eclipse.elk.alg.disco"
    previewImagePath := some "images/disco_layout.png" }

/-- `register_algorithm`. -/
def registerAlgorithm (r : Registry) : Registry := r.registerAlgorithm algorithmData

/-- `register_options`. -/
def registerOptions (r : Registry) : Registry :=
  let r := registerEnumOption r DisCoOptions.COMPONENT_COMPACTION_STRATEGY
    ((OptionMeta.visible "Connected Components Compaction Strategy"
      "Strategy for packing different connected components in order to save space and enhance readability of a graph."
      targetParents).withGroup "componentCompaction")
  let r := registerOption r DisCoOptions.COMPONENT_COMPACTION_COMPONENT_LAYOUT_ALGORITHM .string
    ((OptionMeta.visible "Connected Components Layout Algorithm"
      "A layout algorithm that is to be applied to each connected component before the components themselves are compacted."
      targetParents).withGroup "componentCompaction")
  let r := registerOption r DisCoOptions.DEBUG_DISCO_GRAPH .object
    ((OptionMeta.hidden "DCGraph"
      "Access to the DCGraph is intended for the debug view."
      targetParents).withGroup "debug")
  registerOption r DisCoOptions.DEBUG_DISCO_POLYS .object
    ((OptionMeta.hidden "List of Polyominoes"
      "Access to the polyominoes is intended for the debug view."
      targetParents).withGroup "debug")

/-- `property.getDefault()` as a raw value. -/
def propertyDefault {α : Type} [PropCodec α] (property : Property α) : Option PropValue :=
  property.default.map PropCodec.enc

/-- `addOptionSupport` calls of `DisCoMetaDataProvider` (Java order): (option id, the option's
default, `X.getDefault()`). -/
def optionSupports : Array (String × Option PropValue) := #[
  (CoreOptions.SPACING_COMPONENT_COMPONENT.id, propertyDefault CoreOptions.SPACING_COMPONENT_COMPONENT),
  (CoreOptions.EDGE_THICKNESS.id, propertyDefault CoreOptions.EDGE_THICKNESS),
  (CoreOptions.ASPECT_RATIO.id, propertyDefault CoreOptions.ASPECT_RATIO),
  (CoreOptions.PADDING.id, propertyDefault CoreOptions.PADDING),
  (PolyominoOptions.POLYOMINO_LOW_LEVEL_SORT.id, propertyDefault PolyominoOptions.POLYOMINO_LOW_LEVEL_SORT),
  (PolyominoOptions.POLYOMINO_HIGH_LEVEL_SORT.id, propertyDefault PolyominoOptions.POLYOMINO_HIGH_LEVEL_SORT),
  (PolyominoOptions.POLYOMINO_TRAVERSAL_STRATEGY.id,
    propertyDefault PolyominoOptions.POLYOMINO_TRAVERSAL_STRATEGY),
  (PolyominoOptions.POLYOMINO_FILL.id, propertyDefault PolyominoOptions.POLYOMINO_FILL),
  (DisCoOptions.COMPONENT_COMPACTION_STRATEGY.id, propertyDefault DisCoOptions.COMPONENT_COMPACTION_STRATEGY),
  (DisCoOptions.COMPONENT_COMPACTION_COMPONENT_LAYOUT_ALGORITHM.id, none),
  (DisCoOptions.DEBUG_DISCO_GRAPH.id, none),
  (DisCoOptions.DEBUG_DISCO_POLYS.id, none)]

/-- `register_supports`. -/
def registerSupports (r : Registry) : Registry :=
  optionSupports.foldl (fun r (optionId, default) =>
    r.addOptionSupport DisCoOptions.ALGORITHM_ID optionId default) r

/-- `ILayoutMetaDataProvider.apply` of `DisCoMetaDataProvider`. -/
def metaDataProvider : LayoutMetaDataProvider where
  apply r := registerSupports (registerOptions (registerAlgorithm r))

/-- `LayoutMetaDataService.registerLayoutMetaDataProvider(new DisCoMetaDataProvider())`:
registers the DisCo metadata with the global service. Not run at module initialisation; see
`Elk.Alg.Disco.Init`. -/
def register : IO Unit := LayoutMetaDataService.registerLayoutMetaDataProvider metaDataProvider

end DisCoMetaDataProvider

end Elk.Alg.Disco.Options
