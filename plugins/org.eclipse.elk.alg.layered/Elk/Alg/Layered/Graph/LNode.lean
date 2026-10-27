import Elk.Alg.Layered.Options.InternalProperties
import Elk.Alg.Layered.Graph.NodeType
import Elk.Alg.Layered.Graph.LMargin
import Elk.Alg.Layered.Graph.LPadding
/-! # `org.eclipse.elk.alg.layered.graph.LNode` -/
namespace Elk.Alg.Layered.Graph

open Elk.Graph Elk.Core.Math Elk.Alg.Layered.Options

/-- `LNode`. `ports` keeps the port order (sorted by the port list sorter), `labels` the
label order. `portSideIndices` is the `cachePortSides()` cache: per `PortSide` ordinal the
`[first, last)` index range of the ports on that side. -/
structure LNode where
  id : Int := 0
  props : PropertyMap := {}
  position : KVector := {}
  size : KVector := {}
  /-- `getGraph()` as stored at creation (`LNode(graph)`); falls back to the layer's graph. -/
  graph : Option LGraphId := none
  layer : Option LayerId := none
  type : NodeType := .normal
  ports : Array LPortId := #[]
  labels : Array LLabelId := #[]
  nestedGraph : Option LGraphId := none
  margin : LMargin := {}
  padding : LPadding := {}
  portSideIndices : Option (Array (Option (Nat × Nat))) := none
  portSidesCached : Bool := false
  internal : LNodeInternals := {}
  deriving Inhabited

end Elk.Alg.Layered.Graph
