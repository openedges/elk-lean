import Elk.Graph.Properties
import Elk.Core.Options
import Elk.Alg.Disco.Options.CompactionStrategy
/-!
# `org.eclipse.elk.alg.disco.options.DisCoOptions`

The DisCo layout options (elk-rs `options/disco_options.rs`, `DisCoOptions.java` generated from
`Disco.melk`). Constants keep the Java names. The option ids are
`org.eclipse.elk.disco.*`.

Type mapping and deviations:
* `DEBUG_DISCO_GRAPH` (a `DCGraph`) and `DEBUG_DISCO_POLYS` (a `Vec<DCPolyomino>`) are `Dynamic`
  properties: they are registered as hidden OBJECT options, but the layout provider does not
  store anything in them (a `Dynamic` value needs a `TypeName` instance, which can only be
  created with `import Lean`). They exist for the debug view only and are not read by any
  algorithm.
-/
namespace Elk.Alg.Disco.Options

open Elk.Graph Elk.Core.Math

namespace DisCoOptions

/-- `DisCoOptions.ALGORITHM_ID`. -/
def ALGORITHM_ID : String := "org.eclipse.elk.disco"

/-- `COMPONENT_COMPACTION_STRATEGY` (`org.eclipse.elk.disco.componentCompaction.strategy`),
default `POLYOMINO`. -/
def COMPONENT_COMPACTION_STRATEGY : Property CompactionStrategy :=
  Property.withDefault "org.eclipse.elk.disco.componentCompaction.strategy" CompactionStrategy.polyomino

/-- `COMPONENT_COMPACTION_COMPONENT_LAYOUT_ALGORITHM`
(`org.eclipse.elk.disco.componentCompaction.componentLayoutAlgorithm`): the algorithm to apply to
the components before they are compacted; no default. -/
def COMPONENT_COMPACTION_COMPONENT_LAYOUT_ALGORITHM : Property String :=
  Property.mk' "org.eclipse.elk.disco.componentCompaction.componentLayoutAlgorithm"

/-- `DEBUG_DISCO_GRAPH` (`org.eclipse.elk.disco.debug.discoGraph`). -/
def DEBUG_DISCO_GRAPH : Property Dynamic :=
  Property.mk' "org.eclipse.elk.disco.debug.discoGraph"

/-- `DEBUG_DISCO_POLYS` (`org.eclipse.elk.disco.debug.discoPolys`). -/
def DEBUG_DISCO_POLYS : Property Dynamic :=
  Property.mk' "org.eclipse.elk.disco.debug.discoPolys"

/-- `EDGE_THICKNESS` (alias of `CoreOptions.EDGE_THICKNESS`). -/
def EDGE_THICKNESS : Property Float := Elk.Core.Options.CoreOptions.EDGE_THICKNESS

/-- `SPACING_COMPONENT_COMPONENT` (alias of `CoreOptions.SPACING_COMPONENT_COMPONENT`). -/
def SPACING_COMPONENT_COMPONENT : Property Float :=
  Elk.Core.Options.CoreOptions.SPACING_COMPONENT_COMPONENT

/-- `ASPECT_RATIO` (alias of `CoreOptions.ASPECT_RATIO`). -/
def ASPECT_RATIO : Property Float := Elk.Core.Options.CoreOptions.ASPECT_RATIO

/-- `PADDING` (alias of `CoreOptions.PADDING`). -/
def PADDING : Property ElkPadding := Elk.Core.Options.CoreOptions.PADDING

end DisCoOptions

end Elk.Alg.Disco.Options
