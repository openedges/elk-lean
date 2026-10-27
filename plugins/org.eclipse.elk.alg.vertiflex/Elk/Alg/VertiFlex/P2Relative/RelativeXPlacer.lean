import Elk.Core.Alg
import Elk.Core.Options
import Elk.Core.Util.Java
import Elk.Core.Util.Sort
import Elk.Core.Util.ProgressMonitor
import Elk.Alg.VertiFlex.VertiFlexLayoutPhases
import Elk.Alg.VertiFlex.VertiFlexUtil
import Elk.Alg.VertiFlex.EdgeRoutingStrategy
import Elk.Alg.VertiFlex.Options.VertiFlexOptions
import Elk.Alg.VertiFlex.P2Relative.OutlineNode
import Elk.Alg.VertiFlex.P2Relative.NodeComparator
/-!
# `org.eclipse.elk.alg.vertiflex.p2relative.RelativeXPlacer`

Port of `relative_x_placer.rs` (elk-rs): phase 2 of VertiFlex. Places the children of every tree
node next to each other (x relative to the parent, subtrees are pushed apart using their left and
right outlines) and the parent above the middle of its children. Two variants: straight line
placement (children are re-ordered in a V shape) and bend line placement (model order is kept,
edges may get bend points).

Conventions of the port:

* The Rust fields `spacing_node_node` / `consider_node_model_order` of the placer struct are the
  `Config` parameter.
* Rust's `node_get_property(.., InternalProperties::..)` returns clones of the outlines and
  `node_set_property` stores them back; the Lean outlines are values, so the read-modify-store
  sequences are kept as in Rust (`getProps` / `modifyProps`).
* Rust's `.expect(..)` on a missing property throws (`VertiFlexM.expectSome`).
* `children.sort_by` is stable (`stableSort`); keys are read once before sorting.
-/
namespace Elk.Alg.VertiFlex.P2Relative

open Elk.Graph Elk.Core.Alg Elk.Core.Util Elk.Core.Options Elk.Alg.VertiFlex.Options

namespace RelativeXPlacer

/-- The fields of the Rust placer struct, set in `process`. -/
structure Config where
  /-- `spacing_node_node`. -/
  spacingNodeNode : Float := 0.0
  /-- `consider_node_model_order`. -/
  considerNodeModelOrder : Bool := false

/-- `MINIMAL_Y`. -/
def MINIMAL_Y : Float := -100.0

/-- `outline_distance(outline1, outline2)`: the minimal horizontal distance between the root of
the outline `outline1` (right outline of the left tree) and the root of `outline2` (left outline
of the right tree) such that the two polylines do not intersect. -/
def outlineDistance (outline1 outline2 : OutlineNode) : Float := Id.run do
  let changed1 : OutlineNode :=
    OutlineNode.new outline1.relativeX MINIMAL_Y (some (OutlineNode.new 0.0 outline1.absoluteY outline1.next))
  let changed2 : OutlineNode :=
    OutlineNode.new outline2.relativeX MINIMAL_Y (some (OutlineNode.new 0.0 outline2.absoluteY outline2.next))
  let mut dist := changed1.relativeX - changed2.relativeX
  let mut o1 : Option OutlineNode := some changed1
  let mut o2 : Option OutlineNode := some changed2
  let mut x1 := changed1.relativeX
  let mut x2 := changed2.relativeX
  while true do
    match o1, o2 with
    | some a, some b =>
      match b.next with
      | none => break
      | some bNext =>
        if bNext.absoluteY > a.absoluteY then
          let deltaX := bNext.relativeX
          let deltaY := bNext.absoluteY - b.absoluteY
          let newdist := x1 - x2 - ((a.absoluteY - b.absoluteY) * deltaX) / deltaY
          if newdist > dist then
            dist := newdist
          o1 := a.next
          if let some next := o1 then
            x1 := x1 + next.relativeX
        else
          o2 := b.next
          if let some next := o2 then
            x2 := x2 + next.relativeX
    | _, _ => break
  o1 := some changed1
  o2 := some changed2
  x1 := changed1.relativeX
  x2 := changed2.relativeX
  while true do
    match o1, o2 with
    | some a, some b =>
      match a.next with
      | none => break
      | some aNext =>
        if aNext.absoluteY > b.absoluteY then
          let deltaX := aNext.relativeX
          let deltaY := aNext.absoluteY - a.absoluteY
          let newdist := x1 - x2 + ((b.absoluteY - a.absoluteY) * deltaX) / deltaY
          if newdist > dist then
            dist := newdist
          o2 := b.next
          if let some next := o2 then
            x2 := x2 + next.relativeX
        else
          o1 := a.next
          if let some next := o1 then
            x1 := x1 + next.relativeX
    | _, _ => break
  return dist

/-- `LEFT_OUTLINE.expect("left outline")`. -/
def leftOutlineOf (n : NodeId) : VertiFlexM OutlineNode := do
  VertiFlexM.expectSome (← VertiFlexM.getProps n).leftOutline "left outline"

/-- `RIGHT_OUTLINE.expect("right outline")`. -/
def rightOutlineOf (n : NodeId) : VertiFlexM OutlineNode := do
  VertiFlexM.expectSome (← VertiFlexM.getProps n).rightOutline "right outline"

/-- `make_simple_outlines(graph)`: the four-node left and right outline of a single node and the
bounding box properties. -/
def makeSimpleOutlines (cfg : Config) (graph : NodeId) : VertiFlexM Unit := do
  let node ← ElkM.getNode graph
  let margins := node.props.getD CoreOptions.MARGINS {}
  let sp := cfg.spacingNodeNode
  let endPart1 := OutlineNode.new 0.0 (node.y + node.height + margins.bottom + sp / 2.0)
    (some (OutlineNode.new (node.width / 2.0) (node.y + node.height + margins.bottom + sp / 2.0) none))
  let leftOutline := OutlineNode.new ((-margins.left - sp / 2.0) + node.width / 2.0)
    (node.y - margins.top - sp / 2.0)
    (some (OutlineNode.new (-node.width / 2.0) (node.y - margins.top) (some endPart1)))
  let endPart2 := OutlineNode.new 0.0 (node.y + node.height + margins.bottom)
    (some (OutlineNode.new (-node.width / 2.0) (node.y + node.height + margins.bottom + sp / 2.0) none))
  let rightOutline := OutlineNode.new (node.width / 2.0 + margins.right + sp / 2.0)
    (node.y - margins.top)
    (some (OutlineNode.new (node.width / 2.0) (node.y - margins.top - sp / 2.0) (some endPart2)))
  let outlineMaxDepth := (((leftOutline.next).bind (·.next)).map (·.absoluteY)).getD 0.0
  VertiFlexM.modifyProps graph fun p =>
    { p with
      leftOutline := some leftOutline
      rightOutline := some rightOutline
      minX := some (node.x - margins.left)
      maxX := some (node.x + margins.right + node.width)
      minY := some (node.y - margins.top)
      maxY := some (node.y + margins.bottom + node.height)
      outlineMaxDepth := some outlineMaxDepth }

/-- `bundle_children(left_subtree, a, b)`: moves `b` to the right of `a` so that the outlines do
not intersect and extends the outlines of `left_subtree` (left) and `b` (right) when the tree
they stand for is shallower than the other one. -/
def bundleChildren (leftSubtree a b : NodeId) : VertiFlexM Unit := do
  let aX := (← ElkM.getNode a).x
  let dist := outlineDistance (← rightOutlineOf a) (← leftOutlineOf b)
  ElkM.modifyNode b fun nd => { nd with x := aX + dist }
  let leftMaxDepth := ((← VertiFlexM.getProps leftSubtree).outlineMaxDepth).getD 0.0
  let bMaxDepth := ((← VertiFlexM.getProps b).outlineMaxDepth).getD 0.0
  if leftMaxDepth < bMaxDepth then
    let leftOutline ← leftOutlineOf leftSubtree
    let (lAbsX, lastLAbsY) := leftOutline.absXAndLastY (← ElkM.getNode leftSubtree).x
    let bLeft ← leftOutlineOf b
    let mut bIterator := OutlineNode.new bLeft.relativeX MINIMAL_Y bLeft.next
    let mut rAbsX := bIterator.relativeX + (← ElkM.getNode b).x
    while true do
      match bIterator.next with
      | some next =>
        if next.absoluteY <= lastLAbsY then
          rAbsX := rAbsX + next.relativeX
          bIterator := next
        else break
      | none => break
    let bNext ← VertiFlexM.expectSome bIterator.next "next"
    let deltaX := bNext.relativeX
    let deltaY := bNext.absoluteY - bIterator.absoluteY
    let change := ((lastLAbsY - bIterator.absoluteY) * deltaX) / deltaY
    let newX := -lAbsX + rAbsX + change
    let newNext := OutlineNode.new (bNext.relativeX - change) bNext.absoluteY bNext.next
    let leftOutline := leftOutline.appendToTail (OutlineNode.new newX lastLAbsY (some newNext))
    VertiFlexM.modifyProps leftSubtree fun p =>
      { p with leftOutline := some leftOutline, outlineMaxDepth := some bMaxDepth }
  let bMaxDepth := ((← VertiFlexM.getProps b).outlineMaxDepth).getD 0.0
  let aMaxDepth := ((← VertiFlexM.getProps a).outlineMaxDepth).getD 0.0
  if bMaxDepth < aMaxDepth then
    let rightOutline ← rightOutlineOf b
    let bX := (← ElkM.getNode b).x
    let (rAbsX, lastBAbsY) := rightOutline.absXAndLastY bX
    let aRight ← rightOutlineOf a
    let mut aIterator := OutlineNode.new aRight.relativeX MINIMAL_Y aRight.next
    let mut aAbsX := aIterator.relativeX + (← ElkM.getNode a).x
    while true do
      match aIterator.next with
      | some next =>
        if next.absoluteY <= lastBAbsY then
          aAbsX := aAbsX + next.relativeX
          aIterator := next
        else break
      | none => break
    let aNext ← VertiFlexM.expectSome aIterator.next "next"
    let deltaX := aNext.relativeX
    let deltaY := aNext.absoluteY - aIterator.absoluteY
    let change := ((lastBAbsY - aIterator.absoluteY) * deltaX) / deltaY
    let newX := aAbsX - rAbsX + change
    let newNext := OutlineNode.new (aNext.relativeX - change) aNext.absoluteY aNext.next
    let rightOutline := rightOutline.appendToTail (OutlineNode.new newX lastBAbsY (some newNext))
    VertiFlexM.modifyProps b fun p =>
      { p with rightOutline := some rightOutline, outlineMaxDepth := some aMaxDepth }

/-- The tail of `recursive_*_placement`: the aggregated `OUTLINE_MAX_DEPTH`, `MIN_X`, `MAX_X` of
the graph over its children, and `MAX_Y := OUTLINE_MAX_DEPTH`. -/
def aggregateBounds (graph : NodeId) (children : Array NodeId) : VertiFlexM Unit := do
  let gp ← VertiFlexM.getProps graph
  let mut outlineMaxDepth := gp.outlineMaxDepth.getD 0.0
  let mut minX := gp.minX.getD 0.0
  let mut maxX := gp.maxX.getD 0.0
  for child in children do
    let cp ← VertiFlexM.getProps child
    let childX := (← ElkM.getNode child).x
    outlineMaxDepth := fmax outlineMaxDepth (cp.outlineMaxDepth.getD 0.0)
    minX := fmin minX (childX + cp.minX.getD 0.0)
    maxX := fmax maxX (childX + cp.maxX.getD 0.0)
  VertiFlexM.modifyProps graph fun p =>
    { p with outlineMaxDepth := some outlineMaxDepth, minX := some minX, maxX := some maxX,
             maxY := some outlineMaxDepth }

/-- `split_group(group, width_left_right)`: the index of the last node of the group that goes to
the left, with the updated `(width_left, width_right)` pair. -/
def splitGroup (group : Array NodeId) (widthLeft widthRight : Float) : ElkM (Nat × Float × Float) := do
  if group.size == 1 then
    return (0, widthLeft, widthRight)
  let mut widths : Array Float := #[]
  for node in group do
    widths := widths.push (← ElkM.getNode node).width
  let mut totalNewWidth := 0.0
  for w in widths do
    totalNewWidth := totalNewWidth + w
  let desiredLeft := (totalNewWidth - widthLeft + widthRight) / 2.0
  let mut i := 0
  let mut newLeftWidth := 0.0
  while desiredLeft < newLeftWidth && i < group.size do
    newLeftWidth := newLeftWidth + widths[i]!
    i := i + 1
  let exceed := newLeftWidth - desiredLeft
  let under := desiredLeft - (newLeftWidth - widths[i - 1]!)
  let resultIndex := if exceed > under then i else i - 1
  let mut newRightWidth := 0.0
  for w in widths.extract (resultIndex + 1) widths.size do
    newRightWidth := newRightWidth + w
  return (resultIndex, widthLeft + exceed, widthRight + newRightWidth)

/-- `split_nodes_with_model_order(original, left, right)`. Like Rust (and Java) the cases of one
and two nodes fall through into the group logic, so with exactly two nodes both are added twice;
the caller then fails on the index overflow exactly like the Rust slice assignment. -/
def splitNodesWithModelOrder (original : Array NodeId) : VertiFlexM (Array NodeId × Array NodeId) := do
  if original.isEmpty then
    return (#[], #[])
  let mut left : Array NodeId := #[]
  let mut right : Array NodeId := #[]
  if original.size == 1 then
    left := left.push original[0]!
  if original.size == 2 then
    let first := original[0]!
    let second := original[1]!
    let firstOrder := ((← VertiFlexM.getProps first).nodeModelOrder).getD 0
    let secondOrder := ((← VertiFlexM.getProps second).nodeModelOrder).getD 0
    if firstOrder > secondOrder then
      left := left.push second
      right := right.push first
    else
      left := left.push first
      right := right.push second
  let mut currentGroup : Array NodeId := #[]
  let mut widthLeft := 0.0
  let mut widthRight := 0.0
  let mut current := original[0]!
  currentGroup := currentGroup.push current
  for i in [1:original.size] do
    let next := original[i]!
    if (← ElkM.getNode current).y == (← ElkM.getNode next).y then
      currentGroup := currentGroup.push next
    else
      let (finalIndexOfLeft, wl, wr) ← splitGroup currentGroup widthLeft widthRight
      widthLeft := wl
      widthRight := wr
      left := left ++ currentGroup.extract 0 (finalIndexOfLeft + 1)
      right := right ++ currentGroup.extract (finalIndexOfLeft + 1) currentGroup.size
      currentGroup := #[next]
    current := next
    if i == original.size - 1 then
      let (finalIndexOfLeft, wl, wr) ← splitGroup currentGroup widthLeft widthRight
      widthLeft := wl
      widthRight := wr
      left := left ++ currentGroup.extract 0 (finalIndexOfLeft + 1)
      right := right ++ currentGroup.extract (finalIndexOfLeft + 1) currentGroup.size
  return (left, right)

/-- `sort_subtrees(children)`: sorts by y (stable, model order as tie breaker), then arranges the
children in a V shape (the deepest child in the middle): children are dealt to the lighter side,
the left list is reversed and the right list sorted descending. Returns the new order.

Rust writes the result back with `children[idx] = node` for `idx in 0..left.len()`; a result
longer than `children` (exactly two children with `consider_node_model_order`) panics there with
`index out of bounds`, reproduced as an exception. -/
def sortSubtrees (cfg : Config) (children : Array NodeId) : VertiFlexM (Array NodeId) := do
  let mut keys : Array NodeKey := #[]
  for c in children do
    keys := keys.push (← NodeComparator.key c)
  let sorted := (stableSort keys (NodeComparator.compare false)).map (·.node)
  let mut left : Array NodeId := #[]
  let mut right : Array NodeId := #[]
  if cfg.considerNodeModelOrder then
    let (l, r) ← splitNodesWithModelOrder sorted
    left := l
    right := r
  else if !sorted.isEmpty then
    left := left.push sorted[sorted.size - 1]!
    let mut widthLeft := 0.0
    let mut widthRight := 0.0
    for i in [1:sorted.size] do
      let idx := sorted.size - 1 - i
      let w := (← ElkM.getNode sorted[idx]!).width
      if widthLeft <= widthRight then
        left := left.push sorted[idx]!
        widthLeft := widthLeft + w
      else
        right := right.push sorted[idx]!
        widthRight := widthRight + w
    left := left.reverse
  let mut rightKeys : Array NodeKey := #[]
  for c in right do
    rightKeys := rightKeys.push (← NodeComparator.key c)
  right := (stableSort rightKeys (NodeComparator.compare true)).map (·.node)
  left := left ++ right
  if left.size > sorted.size then
    throw (IO.userError s!"index out of bounds: the len is {sorted.size} but the index is {sorted.size}")
  let mut result := sorted
  for idx in [0:left.size] do
    result := result.set! idx left[idx]!
  return result

/-- `recursive_straightline_placement(graph)`. -/
partial def recursiveStraightlinePlacement (cfg : Config) (graph : NodeId) : VertiFlexM Unit := do
  makeSimpleOutlines cfg graph
  let outgoing ← ElkM.withGraph fun g => ElkGraphUtil.allOutgoingEdges g graph
  if outgoing.isEmpty then return
  let mut children : Array NodeId := #[]
  for edge in outgoing do
    if let some child ← VertiFlexUtil.edgeTargetNode edge then
      recursiveStraightlinePlacement cfg child
      children := children.push child
  children ← sortSubtrees cfg children
  if children.isEmpty then
    throw (IO.userError "index out of bounds: the len is 0 but the index is 0")
  for i in [0:children.size - 1] do
    bundleChildren children[0]! children[i]! children[i + 1]!
  let mut pos := 0
  let mut maxDepth := 0.0
  let mut maxDepthStartPos := 0
  while pos < children.size do
    let childY := (← ElkM.getNode children[pos]!).y
    if !(childY >= maxDepth) then break
    if childY > maxDepth then
      maxDepthStartPos := pos
      maxDepth := childY
    pos := pos + 1
  let gNode ← ElkM.getNode graph
  let first ← ElkM.getNode children[0]!
  let last ← ElkM.getNode children[children.size - 1]!
  let mut moveRoot := 0.0
  if pos > 0 then
    let childStart ← ElkM.getNode children[maxDepthStartPos]!
    let childEnd ← ElkM.getNode children[pos - 1]!
    moveRoot := (childStart.x + childEnd.x + childEnd.width) / 2.0 - gNode.x - gNode.width / 2.0
  if !cfg.considerNodeModelOrder then
    let mut betterMoveRoot := (first.x + last.x + last.width - gNode.width) / 2.0 - gNode.x
    if betterMoveRoot < moveRoot then
      for i in [0:maxDepthStartPos] do
        for j in [i + 1:maxDepthStartPos + 1] do
          let rightOutline ← rightOutlineOf children[i]!
          let ci ← ElkM.getNode children[i]!
          let cj ← ElkM.getNode children[j]!
          let mut rightOutlineX := ci.x + rightOutline.relativeX
          let posX := cj.x + cj.width / 2.0
          let mut outlineIter : Option OutlineNode := some rightOutline
          while true do
            match outlineIter with
            | none => break
            | some outline =>
              if outline.absoluteY >= maxDepth then break
              let newMoveRoot := posX - gNode.width / 2.0
                + (posX - rightOutlineX) * ((gNode.y + gNode.height) - maxDepth)
                  / (maxDepth - outline.absoluteY)
              if newMoveRoot > betterMoveRoot then
                betterMoveRoot := newMoveRoot
              outlineIter := outline.next
              if let some next := outlineIter then
                rightOutlineX := rightOutlineX + next.relativeX
      moveRoot := betterMoveRoot
    if betterMoveRoot > moveRoot then
      for i in [pos:children.size] do
        for j in [pos - 1:i] do
          let leftOutline ← leftOutlineOf children[i]!
          let ci ← ElkM.getNode children[i]!
          let cj ← ElkM.getNode children[j]!
          let mut leftOutlineX := ci.x + leftOutline.relativeX
          let posX := cj.x + cj.width / 2.0
          let mut outlineIter : Option OutlineNode := some leftOutline
          while true do
            match outlineIter with
            | none => break
            | some outline =>
              if outline.absoluteY >= maxDepth then break
              let newMoveRoot := posX - gNode.width / 2.0
                + (posX - leftOutlineX) * ((gNode.y + gNode.height) - maxDepth)
                  / (maxDepth - outline.absoluteY)
              if newMoveRoot < betterMoveRoot then
                betterMoveRoot := newMoveRoot
              outlineIter := outline.next
              if let some next := outlineIter then
                leftOutlineX := leftOutlineX + next.relativeX
      moveRoot := betterMoveRoot
  for child in children do
    ElkM.modifyNode child fun nd => { nd with x := nd.x - moveRoot }
  let graphLeftOutline ← leftOutlineOf graph
  let leftChildOutline ← leftOutlineOf children[0]!
  let firstX := (← ElkM.getNode children[0]!).x
  let newLeftX := firstX + leftChildOutline.relativeX - graphLeftOutline.relativeX
  let newLeftOutline := OutlineNode.new newLeftX leftChildOutline.absoluteY leftChildOutline.next
  let graphLeftOutline := graphLeftOutline.setThirdNext newLeftOutline
  VertiFlexM.modifyProps graph fun p => { p with leftOutline := some graphLeftOutline }
  let graphRightOutline ← rightOutlineOf graph
  let rightChildOutline ← rightOutlineOf children[children.size - 1]!
  let lastX := (← ElkM.getNode children[children.size - 1]!).x
  let newRightX := lastX + rightChildOutline.relativeX - graphRightOutline.relativeX
  let newRightOutline := OutlineNode.new newRightX rightChildOutline.absoluteY rightChildOutline.next
  let graphRightOutline := graphRightOutline.setThirdNext newRightOutline
  VertiFlexM.modifyProps graph fun p => { p with rightOutline := some graphRightOutline }
  aggregateBounds graph children

/-- `recursive_bentline_placement(graph)`. -/
partial def recursiveBentlinePlacement (cfg : Config) (graph : NodeId) : VertiFlexM Unit := do
  makeSimpleOutlines cfg graph
  let outgoing ← ElkM.withGraph fun g => ElkGraphUtil.allOutgoingEdges g graph
  if outgoing.isEmpty then return
  let mut children : Array NodeId := #[]
  for edge in outgoing do
    if let some child ← VertiFlexUtil.edgeTargetNode edge then
      recursiveBentlinePlacement cfg child
      children := children.push child
  if children.isEmpty then
    throw (IO.userError "index out of bounds: the len is 0 but the index is 0")
  for i in [0:children.size - 1] do
    bundleChildren children[0]! children[i]! children[i + 1]!
  let gNode ← ElkM.getNode graph
  let first ← ElkM.getNode children[0]!
  let last ← ElkM.getNode children[children.size - 1]!
  let moveRoot := (first.x + first.width / 2.0 + last.x + last.width / 2.0 - gNode.width) / 2.0 - gNode.x
  for child in children do
    ElkM.modifyNode child fun nd => { nd with x := nd.x - moveRoot }
    let bendHeight := (← leftOutlineOf child).absoluteY
    VertiFlexM.modifyProps child fun p => { p with edgeBendHeight := some bendHeight }
  let childrenSize := children.size
  let mut i := 0
  while i < childrenSize - 1 do
    let ci ← ElkM.getNode children[i]!
    let margins := ci.props.getD CoreOptions.MARGINS {}
    if !(ci.x + ci.width + margins.right - gNode.width / 2.0 <= 0.0) then break
    i := i + 1
  let mut globalBendHeight := ((← VertiFlexM.getProps children[i]!).edgeBendHeight).getD 0.0
  for child in children do
    let childHeight := ((← VertiFlexM.getProps child).edgeBendHeight).getD 0.0
    if globalBendHeight < childHeight then
      VertiFlexM.modifyProps child fun p => { p with edgeBendHeight := some globalBendHeight }
    else
      globalBendHeight := childHeight
  i := childrenSize - 1
  while i > 0 do
    let ci ← ElkM.getNode children[i]!
    let margins := ci.props.getD CoreOptions.MARGINS {}
    if !(ci.x - margins.left - gNode.width / 2.0 >= 0.0) then break
    i := i - 1
  if i < childrenSize then
    for k in [0:i + 1] do
      let a := i - k
      let childHeight := ((← VertiFlexM.getProps children[a]!).edgeBendHeight).getD 0.0
      if globalBendHeight < childHeight then
        VertiFlexM.modifyProps children[a]! fun p => { p with edgeBendHeight := some globalBendHeight }
      else
        globalBendHeight := childHeight
  let leftChildOutline ← leftOutlineOf children[0]!
  let graphLeftOutline ← leftOutlineOf graph
  let firstX := (← ElkM.getNode children[0]!).x
  let newLeftX := firstX + leftChildOutline.relativeX - graphLeftOutline.relativeX
  let newLeftPart := OutlineNode.new 0.0 leftChildOutline.absoluteY leftChildOutline.next
  let firstBend := ((← VertiFlexM.getProps children[0]!).edgeBendHeight).getD 0.0
  let newLeftOutline := OutlineNode.new newLeftX firstBend (some newLeftPart)
  let graphLeftOutline := graphLeftOutline.setThirdNext newLeftOutline
  VertiFlexM.modifyProps graph fun p => { p with leftOutline := some graphLeftOutline }
  let lastChild := children[childrenSize - 1]!
  let rightChildOutline ← rightOutlineOf lastChild
  let graphRightOutline ← rightOutlineOf graph
  let lastX := (← ElkM.getNode lastChild).x
  let newRightX := lastX + rightChildOutline.relativeX - graphRightOutline.relativeX
  let newRightPart := OutlineNode.new 0.0 rightChildOutline.absoluteY rightChildOutline.next
  let lastBend := ((← VertiFlexM.getProps lastChild).edgeBendHeight).getD 0.0
  let newRightOutline := OutlineNode.new newRightX lastBend (some newRightPart)
  let graphRightOutline := graphRightOutline.setThirdNext newRightOutline
  VertiFlexM.modifyProps graph fun p => { p with rightOutline := some graphRightOutline }
  aggregateBounds graph children

/-- `process(graph, progress_monitor)`. -/
def process (graph : NodeId) (monitor : ProgressMonitor) : VertiFlexM Unit := do
  let _ ← monitor.begin "XPlacer" 1.0
  let props := (← ElkM.getNode graph).props
  let cfg : Config :=
    { spacingNodeNode := props.getD CoreOptions.SPACING_NODE_NODE 0.0
      considerNodeModelOrder := props.getD VertiFlexOptions.CONSIDER_NODE_MODEL_ORDER true }
  let hasChildren := !(← ElkM.getNode graph).children.isEmpty
  if hasChildren then
    if let some parent ← VertiFlexUtil.findRoot graph then
      match props.getD VertiFlexOptions.LAYOUT_STRATEGY default with
      | .straight => recursiveStraightlinePlacement cfg parent
      | .bend => recursiveBentlinePlacement cfg parent
  monitor.done

/-- The phase (`ILayoutPhase`) without a processor configuration. -/
def phase : VertiFlexPhase :=
  { name := "RelativeXPlacer"
    process := process
    getLayoutProcessorConfiguration := fun _ => pure none }

end RelativeXPlacer

end Elk.Alg.VertiFlex.P2Relative
