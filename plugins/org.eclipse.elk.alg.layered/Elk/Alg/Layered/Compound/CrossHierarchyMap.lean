import Elk.Alg.Layered.Graph.Monad
import Elk.Alg.Layered.Options.LayeredOptions
/-!
# `CrossHierarchyMap` (Java `Multimap<LEdge, CrossHierarchyEdge>` of `InternalProperties.CROSS_HIERARCHY_MAP`)

Port of the Rust `CrossHierarchyMap` of `compound/mod.rs`: original cross-hierarchy edge →
the dummy edge segments that replace it, as an insertion-ordered association array (keys in
first-`put` order, values in `put` order). The map is stored in
`LGraphInternals.crossHierarchyMap` of the top-level graph.

This module also hosts the arena-based accessors of `CrossHierarchyEdge`
(`getActualSource`, `getActualTarget`, Rust `has_junction_points`), which cannot live in the
data module (see `Elk.Alg.Layered.Compound.CrossHierarchyEdge`).
-/
namespace Elk.Alg.Layered.Compound

open Elk.Graph Elk.Core.Options Elk.Alg.Layered.Graph Elk.Alg.Layered.Options

/-- Rust `CrossHierarchyMap { entries: Vec<(LEdgeRef, Vec<CrossHierarchyEdge>)> }` (same type
as `LGraphInternals.crossHierarchyMap`). -/
abbrev CrossHierarchyMap := Array (LEdgeId × Array CrossHierarchyEdge)

namespace CrossHierarchyMap

/-- `put(edge, crossEdge)`: appends to the edge's entry (created at the end if missing). -/
def put (m : CrossHierarchyMap) (edge : LEdgeId) (crossEdge : CrossHierarchyEdge) : CrossHierarchyMap :=
  match m.findIdx? (·.1 == edge) with
  | some i => m.modifyIn i fun (e, edges) => (e, edges.push crossEdge)
  | none => m.push (edge, #[crossEdge])

/-- `get(edge)`: the segments of the edge (empty if unknown). -/
def get (m : CrossHierarchyMap) (edge : LEdgeId) : Array CrossHierarchyEdge :=
  match m.find? (·.1 == edge) with
  | some (_, edges) => edges
  | none => #[]

/-- `keySet()` (Rust `keys`): the original edges in insertion order. -/
def keys (m : CrossHierarchyMap) : Array LEdgeId := m.map (·.1)

end CrossHierarchyMap

namespace CrossHierarchyEdge

/-- The actual port of a segment end: for an external port dummy with an `LPort` origin, that
port, else the end itself. -/
private def actualEnd (a : LGraphArena) (port : LPortId) : Option LPortId := do
  let node ← (a.port port).owner
  let nd := a.node node
  if nd.type == .externalPort then
    if let some (.lPort p) := nd.internal.origin then return p
  return port

/-- `getActualSource()` on an arena: the source port of the segment, or the port represented by
the source external port dummy. -/
def actualSourceIn (a : LGraphArena) (che : CrossHierarchyEdge) : Option LPortId :=
  (a.edge che.edge).source.bind (actualEnd a)

/-- `getActualTarget()` on an arena. -/
def actualTargetIn (a : LGraphArena) (che : CrossHierarchyEdge) : Option LPortId :=
  (a.edge che.edge).target.bind (actualEnd a)

/-- Java's `(LPort) node.getProperty(ORIGIN)` of `getActualSource()`/`getActualTarget()` fails with a
`ClassCastException` when the end is an external port dummy of the top-level graph of the layout run
(created by `ElkGraphImporter.transformExternalPort`, whose `ORIGIN` is the `ElkPort`): a
hierarchy-crossing edge of an `INCLUDE_CHILDREN` compound node laid out on its own that reaches
one of that node's ports (elk-rs and elk-lean before EXT used the dummy's port). -/
private def checkActualEnd (port : Option LPortId) : LayeredM Unit := do
  let some port := port | return
  let some node := (← LayeredM.getPort port).owner | return
  let nd ← LayeredM.getNode node
  if nd.type == .externalPort then
    if let some (.elkPort _) := nd.internal.origin then
      throw (IO.userError ("java.lang.ClassCastException: class org.eclipse.elk.graph.impl.ElkPortImpl cannot " ++
        "be cast to class org.eclipse.elk.alg.layered.graph.LPort (org.eclipse.elk.graph.impl.ElkPortImpl and " ++
        "org.eclipse.elk.alg.layered.graph.LPort are in unnamed module of loader 'app')"))

/-- `getActualSource()` (with Java's `ClassCastException`, see `checkActualEnd`). -/
def actualSource (che : CrossHierarchyEdge) : LayeredM (Option LPortId) := do
  checkActualEnd (← LayeredM.getEdge che.edge).source
  LayeredM.withArena (actualSourceIn · che)

/-- `getActualTarget()` (with Java's `ClassCastException`, see `checkActualEnd`). -/
def actualTarget (che : CrossHierarchyEdge) : LayeredM (Option LPortId) := do
  checkActualEnd (← LayeredM.getEdge che.edge).target
  LayeredM.withArena (actualTargetIn · che)

/-- Rust `has_junction_points()`: the segment has a non-empty `JUNCTION_POINTS` chain. -/
def hasJunctionPoints (che : CrossHierarchyEdge) : LayeredM Bool := do
  return match (← LayeredM.getEdge che.edge).props.get LayeredOptions.JUNCTION_POINTS with
    | some jps => !jps.isEmpty
    | none => false

end CrossHierarchyEdge

end Elk.Alg.Layered.Compound
