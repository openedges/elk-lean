import Elk.Alg.Common.Compaction.OneD.CNode
/-!
# `org.eclipse.elk.alg.common.compaction.oned.CGroup`

A group of `CNode`s that is compacted as a unit (elk-rs `c_group.rs`).

The arena-dependent operations (`CGroup.create`, `CGroup.addCNode`, `CGroup.removeCNode`)
live in `Elk.Alg.Common.Compaction.OneD.CGraph`.
-/
/-! Float literals as global constants (FL): inside branches, loops and specialised code the compiler
shares a literal's `Nat`/`Bool` arguments with unrelated variables (CSE) and then parses it on every
evaluation (`FastFloat.ofScientificImpl`); a top-level constant is a load (PLAN §7.1 items 17, 22). -/
private def fl0p0 : Float := 0.0

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
  delta : Float := fl0p0
  /-- `CGroup.deltaNormalized`. -/
  deltaNormalized : Float := fl0p0
  deriving Inhabited

end Elk.Alg.Common.Compaction.OneD
