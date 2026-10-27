import Elk.Graph
import Elk.Alg.Layered.Graph.Ids
/-!
# `org.eclipse.elk.alg.layered.intermediate.wrapping.BreakingPointInserter.BPInfo`

Port of elk-rs `intermediate/breaking_point_info.rs` (Java: the static inner class `BPInfo` of
`BreakingPointInserter`). The information about one breaking point, stored on both of its marker
dummies as `InternalProperties.BREAKING_POINT_INFO`:

```
u --nodeStartEdge--> start --startEndEdge--> end --originalEdge--> v
```

## Value representation of the shared mutable object

Java/Rust share one mutable `BPInfo` object (`Arc<Mutex<_>>`) between the `start` and the `end`
dummy and link the infos of a chain with object references (`prev`/`next`). The Lean port keeps
the info as a **value** on both marker nodes and identifies an info by its `start` dummy:

* `prev`/`next` hold the `start` dummy of the linked info (`none` = Java `null`);
* every mutation of an info is written to both its `start` and its `end` node
  (`BreakingPointInfo.write` in `BreakingPointInserter`), which reproduces the object identity: in
  Rust an info object is only referenced by its two markers and by the `prev`/`next` links, and the
  merge step of `BreakingPointProcessor` keeps the `start` dummy of the surviving info. Stale
  copies remain only on dummies that were removed from their layers (as in Rust, where those
  dummies keep the old object); they are never read again.

## Storage (TODO(internal-field))

`LNodeInternals` has no `breakingPointInfo` field yet. Until it is added the value is stored in
the node's `props` under the Java property id `breakingPoint.info`, encoded as an `intList`
(`LNodeInternals.breakingPointInfo`). All accesses go through `BreakingPointInfo.get?`/`write` in
`BreakingPointInserter`, so switching to the typed field only changes those two functions.
Requested field: `breakingPointInfo : Option BreakingPointInfo := none` in `LNodeInternals`
(this module only imports `Elk.Graph` and `Graph.Ids`, so `InternalProperties` can import it).
-/
namespace Elk.Alg.Layered.Intermediate.Wrapping

open Elk.Graph Elk.Alg.Layered.Graph

/-- `BPInfo` / elk-rs `BreakingPointInfo`. -/
structure BreakingPointInfo where
  /-- `start`: the breaking point start dummy (in the first of the two inserted layers). -/
  start : LNodeId
  /-- `end`: the breaking point end dummy (in the second inserted layer). -/
  endNode : LNodeId
  /-- `nodeStartEdge`: original source → `start`. -/
  nodeStartEdge : LEdgeId
  /-- `startEndEdge`: `start` → `end` (rerouted backwards by the `BreakingPointProcessor`). -/
  startEndEdge : LEdgeId
  /-- `originalEdge`: the split edge, now `end` → original target. -/
  originalEdge : LEdgeId
  /-- `startInLayerDummy`. -/
  startInLayerDummy : Option LNodeId := none
  /-- `startInLayerEdge`. -/
  startInLayerEdge : Option LEdgeId := none
  /-- `endInLayerDummy`. -/
  endInLayerDummy : Option LNodeId := none
  /-- `endInLayerEdge`. -/
  endInLayerEdge : Option LEdgeId := none
  /-- `prev`: the `start` dummy of the previous info of the chain. -/
  prev : Option LNodeId := none
  /-- `next`: the `start` dummy of the next info of the chain. -/
  next : Option LNodeId := none
  deriving BEq, Repr, Inhabited

namespace BreakingPointInfo

/-- `BPInfo(startDummy, endDummy, nodeStartEdge, startEndEdge, originalEdge)` (Rust
`BreakingPointInfo::new`). -/
def new (start endNode : LNodeId) (nodeStartEdge startEndEdge originalEdge : LEdgeId) : BreakingPointInfo :=
  { start, endNode, nodeStartEdge, startEndEdge, originalEdge }

end BreakingPointInfo

end Elk.Alg.Layered.Intermediate.Wrapping
