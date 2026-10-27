import Std.Data.HashMap
import Elk.Graph
/-!
# `org.eclipse.elk.alg.radial.InternalProperties`

Port of `internal_properties.rs` (elk-rs). The only internal property of the radial algorithm is
`ROOT_NODE`, which Rust stores in the property map of the layout graph as the address of the root
node (`Property<usize>`). Here it is a typed side table keyed by the layout graph (`NodeId`) in
the state of the radial monad `RadialM`; the table is never exported, like the Rust `usize`
property that the JSON transfer never writes back.
-/
namespace Elk.Alg.Radial

open Elk.Graph

/-- State of the radial algorithm: the `ROOT_NODE` side table. -/
structure RadialState where
  /-- `InternalProperties.ROOT_NODE`: layout graph to root node of its tree. -/
  rootNodes : Std.HashMap NodeId NodeId := {}

/-- The monad of the radial phases and processors: the `ElkGraph` arena plus the radial state. -/
abbrev RadialM := StateRefT RadialState ElkM

/-- Read-only snapshot of the `ElkGraph` arena (the `get` of `RadialM` is the radial state). -/
def getGraph : RadialM ElkGraph := (ElkM.withGraph id : ElkM ElkGraph)

namespace InternalProperties

/-- `graph.get_property(InternalProperties::ROOT_NODE)`. -/
def rootNode (graph : NodeId) : RadialM (Option NodeId) := do
  return (← get).rootNodes.get? graph

/-- `graph.set_property(InternalProperties::ROOT_NODE, Some(root))`. -/
def setRootNode (graph root : NodeId) : RadialM Unit :=
  modify fun s => { s with rootNodes := s.rootNodes.insert graph root }

end InternalProperties

end Elk.Alg.Radial
