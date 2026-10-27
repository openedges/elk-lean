import Elk.Alg.Layered.Graph.Ids
import Elk.Graph
import Elk.Core.Math
/-! # `org.eclipse.elk.alg.layered.graph.Layer` -/
namespace Elk.Alg.Layered.Graph

open Elk.Graph Elk.Core.Math

/-- `Layer`: an ordered list of nodes of one graph. -/
structure Layer where
  id : Int := 0
  props : PropertyMap := {}
  /-- `getGraph()` (owner). -/
  owner : LGraphId := ⟨0⟩
  size : KVector := {}
  nodes : Array LNodeId := #[]
  deriving Inhabited

end Elk.Alg.Layered.Graph
