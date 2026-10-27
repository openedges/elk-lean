import Elk.Core.Math.KVectorChain
import Elk.Alg.MrTree.Graph.TGraphElement
import Elk.Alg.MrTree.Options.InternalProperties
/-!
# `org.eclipse.elk.alg.mrtree.graph.TEdge`

Port of `graph/t_edge.rs` (elk-rs): a directed edge between two tree nodes with labels and bend
points. The constructor `TEdge::new` and `set_source`/`set_target` (which update the incident nodes)
live in `Elk.Alg.MrTree.Graph.TArena`.
-/
namespace Elk.Alg.MrTree.Graph

open Elk.Core.Math Elk.Alg.MrTree.Options

/-- The internal properties of a `TEdge`. -/
structure TEdgeInternals where
  /-- `ORIGIN`. -/
  origin : Option Origin := none
  /-- `DUMMY`. -/
  dummy : Bool := false
  deriving Inhabited

/-- `org.eclipse.elk.alg.mrtree.graph.TEdge`. -/
structure TEdge extends TGraphElement where
  /-- `getSource()`. -/
  source : Option TNodeId := none
  /-- `getTarget()`. -/
  target : Option TNodeId := none
  /-- `getLabels()`. -/
  labels : Array TLabelId := #[]
  /-- `getBendPoints()`. -/
  bendPoints : KVectorChain := #[]
  /-- Internal properties. -/
  internal : TEdgeInternals := {}
  deriving Inhabited

end Elk.Alg.MrTree.Graph
