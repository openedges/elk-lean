import Elk.Alg.Layered.Graph.Ids
import Elk.Alg.Layered.Options.PortType
/-! # `org.eclipse.elk.alg.layered.compound.CrossHierarchyEdge` (data part)

The dummy edge a cross-hierarchy edge was replaced with, the graph it lives in and
whether it leaves (`OUTPUT`) or enters (`INPUT`) that graph (Rust `CrossHierarchyEdge` of
`compound/mod.rs`; the Rust `Weak` graph reference is the id).

This module is imported by `Options.InternalProperties` (for
`LGraphInternals.crossHierarchyMap`), so it cannot see the arena. The accessors that need it
(`getActualSource`, `getActualTarget`, `hasJunctionPoints`) are defined in the same namespace in
`Elk.Alg.Layered.Compound.CrossHierarchyMap`, so `che.actualSource` works wherever that module
is imported.
-/
namespace Elk.Alg.Layered.Compound

open Elk.Alg.Layered.Graph Elk.Alg.Layered.Options

/-- `CrossHierarchyEdge(edge, graph, type)`. -/
structure CrossHierarchyEdge where
  /-- `getEdge()`: the hierarchy-local dummy edge. -/
  edge : LEdgeId
  /-- `getGraph()`: the graph containing the dummy edge. -/
  graph : LGraphId
  /-- `getType()`: `OUTPUT` if the segment leaves its graph, `INPUT` if it enters it. -/
  portType : PortType
  deriving BEq, Repr, Inhabited

end Elk.Alg.Layered.Compound
