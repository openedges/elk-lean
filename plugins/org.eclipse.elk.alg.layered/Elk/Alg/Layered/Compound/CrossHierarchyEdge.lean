import Elk.Alg.Layered.Graph.Ids
import Elk.Alg.Layered.Options.PortType
/-! # `org.eclipse.elk.alg.layered.compound.CrossHierarchyEdge` (data part)

The dummy edge a cross-hierarchy edge was replaced with, the graph it lives in and
whether it leaves (`OUTPUT`) or enters (`INPUT`) that graph. The accessors that need
the arena (`getActualSource/Target`) live with the compound processors.
-/
namespace Elk.Alg.Layered.Compound

open Elk.Alg.Layered.Graph Elk.Alg.Layered.Options

/-- `CrossHierarchyEdge(edge, graph, type)`. -/
structure CrossHierarchyEdge where
  edge : LEdgeId
  graph : LGraphId
  portType : PortType
  deriving BEq, Repr, Inhabited

end Elk.Alg.Layered.Compound
