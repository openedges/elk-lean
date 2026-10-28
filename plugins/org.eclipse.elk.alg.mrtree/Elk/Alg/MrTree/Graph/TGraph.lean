import Elk.Core.Math.KVector
import Elk.Alg.MrTree.Graph.TGraphElement
import Elk.Alg.MrTree.Options.InternalProperties
/-!
# `org.eclipse.elk.alg.mrtree.graph.TGraph`

Port of `graph/t_graph.rs` (elk-rs): a tree graph is a property holder plus the ordered lists of its
nodes and edges (ids into the `TArena`). Several graphs share nodes: the components created by
`ComponentsProcessor.split` and the packed graph of `ComponentsProcessor.pack` list the nodes of the
imported graph, like the shared `TNodeRef`s of Rust.
-/
/-! Float literals as global constants (FL): inside branches, loops and specialised code the compiler
shares a literal's `Nat`/`Bool` arguments with unrelated variables (CSE) and then parses it on every
evaluation (`FastFloat.ofScientificImpl`); a top-level constant is a load (PLAN §7.1 items 17, 22). -/
private def fl0p0 : Float := 0.0

namespace Elk.Alg.MrTree.Graph

open Elk.Graph Elk.Core.Math Elk.Alg.MrTree.Options

/-- The internal properties of a `TGraph`. -/
structure TGraphInternals where
  /-- `ORIGIN`. -/
  origin : Option Origin := none
  /-- `REMOVABLE_EDGES` (Rust `unwrap_or_default` = empty). -/
  removableEdges : Array TEdgeId := #[]
  /-- `GRAPH_XMIN`. -/
  graphXmin : Float := fl0p0
  /-- `GRAPH_YMIN`. -/
  graphYmin : Float := fl0p0
  /-- `GRAPH_XMAX`. -/
  graphXmax : Float := fl0p0
  /-- `GRAPH_YMAX`. -/
  graphYmax : Float := fl0p0
  /-- `BB_UPLEFT`. -/
  bbUpleft : Option KVector := none
  /-- `BB_LOWRIGHT`. -/
  bbLowright : Option KVector := none
  deriving Inhabited

/-- `org.eclipse.elk.alg.mrtree.graph.TGraph`. -/
structure TGraph where
  /-- The `MapPropertyHolder` (public layout options). -/
  props : PropertyMap := {}
  /-- `getNodes()`. -/
  nodes : Array TNodeId := #[]
  /-- `getEdges()`. -/
  edges : Array TEdgeId := #[]
  /-- Internal properties. -/
  internal : TGraphInternals := {}
  deriving Inhabited

namespace TGraph

/-- `copy_properties(other.properties())`: Rust copies the whole property map, which contains the
internal properties as well. The public options are merged with `PropertyMap.copyFrom`; the internal
properties are taken from `other` (every caller copies into a freshly created graph, whose internal
properties are all unset, so this equals the Rust map merge). -/
def copyProperties (g other : TGraph) : TGraph :=
  { g with props := g.props.copyFrom other.props, internal := other.internal }

end TGraph

end Elk.Alg.MrTree.Graph
