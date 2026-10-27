import Elk.Core.Math.KVector
import Elk.Core.Math.ElkRectangle
import Elk.Core.Util.Java
/-!
# `org.eclipse.elk.alg.common.compaction.oned.CNode`

A node of the constraint graph `CGraph` (elk-rs `c_node.rs`). CNodes and CGroups live in the
arenas `CGraph.cNodes` / `CGraph.cGroups` and are referenced by the typed ids `CNodeId` /
`CGroupId` (PORTING.md §14): Rust `Rc::ptr_eq` becomes id equality and the `Weak` group
back reference becomes `Option CGroupId`.

The arena-dependent constructor `CNode.create` (Rust `CNode::create(graph, hitbox)`) lives in
`Elk.Alg.Common.Compaction.OneD.CGraph`, the first module that knows the arena.
-/
namespace Elk.Alg.Common.Compaction.OneD

open Elk.Core.Math Elk.Core.Util

/-- Index of a `CNode` in `CGraph.cNodes` (replaces Rust `CNodeRef = Rc<RefCell<CNode>>`). -/
structure CNodeId where
  idx : Nat
  deriving BEq, Hashable, Repr, Inhabited, DecidableEq

/-- Index of a `CGroup` in `CGraph.cGroups` (replaces Rust `CGroupRef = Rc<RefCell<CGroup>>`). -/
structure CGroupId where
  idx : Nat
  deriving BEq, Hashable, Repr, Inhabited, DecidableEq

instance : ToString CNodeId := ⟨fun i => s!"CN{i.idx}"⟩
instance : ToString CGroupId := ⟨fun i => s!"CG{i.idx}"⟩

/-- `CNode`: a rectangle (`hitbox`) taking part in one-dimensional compaction. -/
structure CNode where
  /-- `CNode.id`: scratch id, e.g. the scanline index assigned by `ScanlineConstraintCalculator`. -/
  id : Int := 0
  /-- `CNode.cGroup` (Rust `Option<Weak<RefCell<CGroup>>>`). -/
  cGroup : Option CGroupId := none
  /-- `CNode.cGroupOffset`: offset to the reference node of the group. -/
  cGroupOffset : KVector := KVector.zero
  /-- `CNode.hitboxPreCompaction`: copy of the hitbox before the compaction started. -/
  hitboxPreCompaction : Option ElkRectangle := none
  /-- `CNode.hitbox`. -/
  hitbox : ElkRectangle := {}
  /-- `CNode.constraints`: nodes that have to be placed after this node. -/
  constraints : Array CNodeId := #[]
  /-- `CNode.startPos`. -/
  startPos : Float := Float.negInf
  deriving Inhabited

namespace CNode

/-- `CNode::group()` (Rust upgrades the weak reference; here the id is returned as is). -/
@[inline] def group (n : CNode) : Option CGroupId := n.cGroup

end CNode

end Elk.Alg.Common.Compaction.OneD
