import Elk.Alg.Common.Compaction.OneD.CNode
/-!
# `org.eclipse.elk.alg.common.compaction.oned.CGroup`

A group of `CNode`s that is compacted as a unit (elk-rs `c_group.rs`).

The arena-dependent operations (`CGroup.create`, `CGroup.addCNode`, `CGroup.removeCNode`)
live in `Elk.Alg.Common.Compaction.OneD.CGraph`.
-/
namespace Elk.Alg.Common.Compaction.OneD

open Elk.Core.Util

/-- `CGroup`. -/
structure CGroup where
  /-- `CGroup.id`. -/
  id : Int := 0
  /-- `CGroup.master`. -/
  master : Option CNodeId := none
  /-- `CGroup.cNodes` (insertion order, no duplicates). -/
  cNodes : Array CNodeId := #[]
  /-- `CGroup.startPos`. -/
  startPos : Float := Float.negInf
  /-- `CGroup.incomingConstraints` (insertion order, no duplicates). -/
  incomingConstraints : Array CNodeId := #[]
  /-- `CGroup.outDegree`. -/
  outDegree : Int := 0
  /-- `CGroup.outDegreeReal`. -/
  outDegreeReal : Int := 0
  /-- `CGroup.reference`: the left-most node of the group. -/
  reference : Option CNodeId := none
  /-- `CGroup.delta`. -/
  delta : Float := 0.0
  /-- `CGroup.deltaNormalized`. -/
  deltaNormalized : Float := 0.0
  deriving Inhabited

end Elk.Alg.Common.Compaction.OneD
