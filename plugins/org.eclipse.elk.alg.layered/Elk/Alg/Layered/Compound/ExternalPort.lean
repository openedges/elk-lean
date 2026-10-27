import Elk.Alg.Layered.Graph.Ids
import Elk.Alg.Layered.Options.PortType
/-!
# `org.eclipse.elk.alg.layered.compound.CompoundGraphPreprocessor.ExternalPort`

Port of the Rust `ExternalPort` of `compound/mod.rs` (Java inner class
`CompoundGraphPreprocessor.ExternalPort`): an external port created for one or more
cross-hierarchy edges while processing a nested graph. The value is copied between the lists
of the preprocessor; the Rust `&mut` merges into a "default" port are index updates of the
caller's list.
-/
namespace Elk.Alg.Layered.Compound

open Elk.Alg.Layered.Graph Elk.Alg.Layered.Options

/-- `ExternalPort`. -/
structure ExternalPort where
  /-- `origEdges`: the original edges represented by this external port. -/
  origEdges : Array LEdgeId
  /-- `newEdge`: the dummy edge inside the nested graph. -/
  newEdge : LEdgeId
  /-- `dummyNode`: the external port dummy node. -/
  dummyNode : LNodeId
  /-- `dummyPort`: the port represented by the dummy (on the compound node), Rust `origin_port`. -/
  dummyPort : LPortId
  /-- `type`: `INPUT` or `OUTPUT`. -/
  portType : PortType
  /-- `exported`: whether the port must be handled by the parent level. -/
  exported : Bool
  deriving Inhabited, Repr

namespace ExternalPort

/-- `new ExternalPort(origEdge, newEdge, dummyNode, dummyPort, portType, exported)`. -/
def new (origEdge newEdge : LEdgeId) (dummyNode : LNodeId) (dummyPort : LPortId) (portType : PortType)
    (exported : Bool) : ExternalPort :=
  { origEdges := #[origEdge], newEdge, dummyNode, dummyPort, portType, exported }

end ExternalPort

end Elk.Alg.Layered.Compound
