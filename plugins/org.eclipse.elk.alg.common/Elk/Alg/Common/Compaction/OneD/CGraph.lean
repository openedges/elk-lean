import Elk.Alg.Common.Compaction.OneD.CNode
import Elk.Alg.Common.Compaction.OneD.CGroup
import Elk.Core.Options.Direction
/-!
# `org.eclipse.elk.alg.common.compaction.oned.CGraph`

The constraint graph of the one-dimensional compactor (elk-rs `c_graph.rs`): arenas of
`CNode`s and `CGroup`s plus the predefined constraints. This module also hosts the arena
operations of `CNode` and `CGroup` (`CNode.create`, `CGroup.create`, `CGroup.addCNode`,
`CGroup.removeCNode`) since those need the graph.

Representation: `CGraph` is a value; the Rust `CGraphRef = Rc<RefCell<CGraph>>` sharing is
replaced by passing the (unique) value around and handing it back to the caller
(`OneDimensionalCompactor.cGraph`). Element updates go through `modifyCNode` /
`modifyCGroup`, which update the arenas in place when the graph is unique.
-/
namespace Elk.Alg.Common.Compaction.OneD

open Elk.Core.Math Elk.Core.Options

/-- `CGraph`. -/
structure CGraph where
  /-- `CGraph.cNodes` (arena, creation order). -/
  cNodes : Array CNode := #[]
  /-- `CGraph.cGroups` (arena, creation order). -/
  cGroups : Array CGroup := #[]
  /-- `CGraph.supportedDirections`. -/
  supportedDirections : Array Direction := #[]
  /-- `CGraph.predefinedHorizontalConstraints`: `(first, second)` pairs. -/
  predefinedHorizontalConstraints : Array (CNodeId × CNodeId) := #[]
  /-- `CGraph.predefinedVerticalConstraints`: `(first, second)` pairs. -/
  predefinedVerticalConstraints : Array (CNodeId × CNodeId) := #[]
  deriving Inhabited

namespace CGraph

/-- `new CGraph(supportedDirections)`. -/
def new (supportedDirections : Array Direction) : CGraph := { supportedDirections }

/-- `CGraph::all_directions()`: supports `LEFT`, `RIGHT`, `UP`, `DOWN` (in this order). -/
def allDirections : CGraph := new #[.left, .right, .up, .down]

/-- `CGraph.supports(direction)`. -/
def supports (g : CGraph) (direction : Direction) : Bool := g.supportedDirections.contains direction

/-- Arena lookup of a node (Rust `node.borrow()`); out-of-range ids yield a default node. -/
@[inline] def cNode (g : CGraph) (n : CNodeId) : CNode := g.cNodes[n.idx]?.getD default

/-- Arena lookup of a group (Rust `group.borrow()` / `Weak::upgrade`). -/
@[inline] def cGroup (g : CGraph) (c : CGroupId) : CGroup := g.cGroups[c.idx]?.getD default

/-- In-place update of a node (Rust `node.borrow_mut()`). -/
@[inline] def modifyCNode (g : CGraph) (n : CNodeId) (f : CNode → CNode) : CGraph :=
  { g with cNodes := g.cNodes.modify n.idx f }

/-- In-place update of a group (Rust `group.borrow_mut()`). -/
@[inline] def modifyCGroup (g : CGraph) (c : CGroupId) (f : CGroup → CGroup) : CGraph :=
  { g with cGroups := g.cGroups.modify c.idx f }

/-- Ids of all nodes in arena order (Rust `c_graph.borrow().c_nodes.clone()`). -/
def cNodeIds (g : CGraph) : Array CNodeId := (Array.range g.cNodes.size).map (⟨·⟩)

/-- Ids of all groups in arena order (Rust `c_graph.borrow().c_groups.clone()`). -/
def cGroupIds (g : CGraph) : Array CGroupId := (Array.range g.cGroups.size).map (⟨·⟩)

/-- The group of a node (Rust `CNode::group()`). -/
@[inline] def groupOf (g : CGraph) (n : CNodeId) : Option CGroupId := (g.cNode n).cGroup

end CGraph

namespace CNode

/-- `CNode::create(graph, hitbox)`: appends a new node with the given hitbox to the graph. -/
def create (g : CGraph) (hitbox : ElkRectangle) : CGraph × CNodeId :=
  let id : CNodeId := ⟨g.cNodes.size⟩
  ({ g with cNodes := g.cNodes.push { hitbox } }, id)

end CNode

namespace CGroup

/-- Error of `addCNode` (Rust `panic!("CNode belongs to another CGroup")`, Java
`RuntimeException`), in the elk-lean exception convention. -/
def belongsToAnotherGroupMessage : String :=
  "java.lang.IllegalStateException: CNode belongs to another CGroup"

/-- `CGroup::add_c_node(group, node)`: adds the node (once) and makes it the reference if the
group has none yet. Fails if the node already belongs to a group. -/
def addCNode (g : CGraph) (group : CGroupId) (node : CNodeId) : Except String CGraph :=
  if (g.cNode node).cGroup.isSome then
    .error belongsToAnotherGroupMessage
  else
    let g := g.modifyCGroup group fun grp =>
      let grp := if grp.cNodes.contains node then grp else { grp with cNodes := grp.cNodes.push node }
      if grp.reference.isNone then { grp with reference := some node } else grp
    .ok (g.modifyCNode node fun n => { n with cGroup := some group })

/-- `CGroup::create(graph, nodes)`: creates a group containing `nodes` (added in order) and
appends it to the graph. -/
def create (g : CGraph) (nodes : Array CNodeId) : Except String (CGraph × CGroupId) := do
  let id : CGroupId := ⟨g.cGroups.size⟩
  -- Rust adds the nodes before pushing the group; the difference is not observable.
  let mut g := { g with cGroups := g.cGroups.push {} }
  for n in nodes do
    g ← addCNode g id n
  return (g, id)

/-- `CGroup.create` in `IO`: throws `java.lang.IllegalStateException` like the Rust panic. -/
def createIO (g : CGraph) (nodes : Array CNodeId) : IO (CGraph × CGroupId) :=
  match create g nodes with
  | .ok r => pure r
  | .error e => throw (IO.userError e)

/-- `CGroup::remove_c_node(group, node)`: removes the node and clears its group reference.
Returns whether the node was contained. -/
def removeCNode (g : CGraph) (group : CGroupId) (node : CNodeId) : CGraph × Bool :=
  if (g.cGroup group).cNodes.contains node then
    let g := g.modifyCGroup group fun grp => { grp with cNodes := grp.cNodes.filter (· != node) }
    (g.modifyCNode node fun n => { n with cGroup := none }, true)
  else
    (g, false)

end CGroup

end Elk.Alg.Common.Compaction.OneD
