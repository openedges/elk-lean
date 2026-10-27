import Elk.Alg.Layered.Options.InternalProperties
/-! # `org.eclipse.elk.alg.layered.graph.LEdge` -/
namespace Elk.Alg.Layered.Graph

open Elk.Graph Elk.Core.Math Elk.Alg.Layered.Options

/-- `LEdge`. -/
structure LEdge where
  id : Int := 0
  props : PropertyMap := {}
  bendPoints : KVectorChain := #[]
  source : Option LPortId := none
  target : Option LPortId := none
  labels : Array LLabelId := #[]
  internal : LEdgeInternals := {}
  deriving Inhabited

end Elk.Alg.Layered.Graph
