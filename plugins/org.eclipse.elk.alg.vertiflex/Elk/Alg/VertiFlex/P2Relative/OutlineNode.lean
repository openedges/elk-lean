/-!
# `org.eclipse.elk.alg.vertiflex.p2relative.OutlineNode`

Port of `outline_node.rs` (elk-rs): one node of the outline (a linked polyline) of a subtree.
Rust owns the successor with `Option<Box<OutlineNode>>` and clones the whole list whenever an
outline property is read; the Lean structure is an immutable value with the same semantics
(every "mutation" returns an updated copy that has to be stored back).
-/
namespace Elk.Alg.VertiFlex.P2Relative

/-- `OutlineNode`: `relative_x` is relative to the previous outline node (the first node: to the
owning tree node), `absolute_y` is absolute, `next` the following outline node. -/
structure OutlineNode where
  /-- `relative_x()`. -/
  relativeX : Float
  /-- `absolute_y()`. -/
  absoluteY : Float
  /-- `next()`. -/
  next : Option OutlineNode := none
  deriving Inhabited

namespace OutlineNode

/-- `OutlineNode::new(relative_x, absolute_y, next)`. -/
def new (relativeX absoluteY : Float) (next : Option OutlineNode := none) : OutlineNode :=
  { relativeX, absoluteY, next }

/-- `is_last()`. -/
def isLast (o : OutlineNode) : Bool := o.next.isNone

/-- `set_next(next)`. -/
def setNext (o : OutlineNode) (next : Option OutlineNode) : OutlineNode := { o with next }

/-- `outline_tail_mut(outline).set_next(Some(next))` of `relative_x_placer.rs`: appends `next`
behind the last node of the list. -/
def appendToTail : OutlineNode → OutlineNode → OutlineNode
  | ⟨relativeX, absoluteY, none⟩, next => ⟨relativeX, absoluteY, some next⟩
  | ⟨relativeX, absoluteY, some nx⟩, next => ⟨relativeX, absoluteY, some (appendToTail nx next)⟩

/-- `set_outline_third_next(outline, next)` of `relative_x_placer.rs`: sets the successor of the
fourth node (`outline.next.next.next`); the list is returned unchanged if it has fewer than four
nodes. -/
def setThirdNext (o : OutlineNode) (next : OutlineNode) : OutlineNode :=
  match o.next with
  | none => o
  | some level1 =>
    match level1.next with
    | none => o
    | some level2 =>
      match level2.next with
      | none => o
      | some level3 =>
        { o with next := some { level1 with next := some { level2 with next := some { level3 with next := some next } } } }

/-- `outline_abs_x_and_last_y(outline, base_x)` of `relative_x_placer.rs`: the absolute x of the
last node (`base_x` plus the sum of all relative x) and the absolute y of the last node. -/
def absXAndLastY (outline : OutlineNode) (baseX : Float) : Float × Float := Id.run do
  let mut absX := outline.relativeX + baseX
  let mut lastY := outline.absoluteY
  let mut current := outline
  while true do
    match current.next with
    | some nx =>
      absX := absX + nx.relativeX
      lastY := nx.absoluteY
      current := nx
    | none => break
  return (absX, lastY)

end OutlineNode

end Elk.Alg.VertiFlex.P2Relative
