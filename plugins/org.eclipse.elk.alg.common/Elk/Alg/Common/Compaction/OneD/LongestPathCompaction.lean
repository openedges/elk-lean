import Elk.Alg.Common.Compaction.OneD.ICompactionAlgorithm
/-!
# `org.eclipse.elk.alg.common.compaction.oned.LongestPathCompaction`

Longest path compaction of the CGroups (elk-rs `longest_path_compaction.rs`): groups are
processed from the sinks (out degree 0) in FIFO order; each processed group pushes the start
positions of the groups constrained by it. The Rust `VecDeque` is an array with a head index;
the duplicate check (`sinks.iter().any(..)`) only looks at the not yet popped entries.

`compact` is a pure fast path: it takes the `CGraph` out of the compactor state once, runs the
same reads and updates in the same order on the unique graph value (`Pure`; the lock function and
the spacings handler receive the current graph, as in the monadic version) and stores it back. The
monadic original is kept as `compactReference` (differential test
`alg.common.compaction.longestPathFast`).
-/
namespace Elk.Alg.Common.Compaction.OneD

open Elk.Core.Util Elk.Core.Options CompactM

namespace LongestPathCompaction

/-- Processes one sink group (body of the Rust `while let Some(group) = sinks.pop_front()`).
Returns the new sink queue. -/
private def processGroupReference (group : CGroupId) (sinks : Array CGroupId) (head : Nat) :
    CompactM (Array CGroupId) := do
  let grp ← getCGroup group
  let some reference := grp.reference | return sinks
  let dir ← direction
  let mut diff := (← getCNode reference).hitbox.x
  let groupNodes := grp.cNodes
  for node in groupNodes do
    let suggestedX := (← getCGroup group).startPos + (← getCNode node).cGroupOffset.x
    let currentX := (← getCNode node).hitbox.x
    let canMove := !(← isLockedGroup group dir) || currentX < suggestedX
    modifyCNode node fun n => { n with startPos := if canMove then suggestedX else currentX }
  diff := diff - (← getCNode reference).startPos
  modifyCGroup group fun g =>
    { g with
      delta := g.delta + diff
      deltaNormalized :=
        if dir == .right || dir == .down then g.deltaNormalized + diff
        else g.deltaNormalized - diff }
  let mut sinks := sinks
  for node in groupNodes do
    let n ← getCNode node
    let nodeStartPos := n.startPos
    let nodeWidth := n.hitbox.width
    for incNode in n.constraints do
      let spacing ←
        if dir.isHorizontal then horizontalSpacing node incNode else verticalSpacing node incNode
      let inc ← getCNode incNode
      let some incGroup := inc.cGroup | continue
      let incOffsetX := inc.cGroupOffset.x
      modifyCGroup incGroup fun g =>
        { g with startPos := fmax g.startPos (nodeStartPos + nodeWidth + spacing - incOffsetX) }
      if ← isLockedNode incNode dir then
        let lockedX := (← getCNode incNode).hitbox.x - incOffsetX
        modifyCGroup incGroup fun g => { g with startPos := fmax g.startPos lockedX }
      modifyCGroup incGroup fun g => { g with outDegree := g.outDegree - 1 }
      let pushSink := (← getCGroup incGroup).outDegree == 0
      if pushSink && !((sinks.extract head sinks.size).contains incGroup) then
        sinks := sinks.push incGroup
  return sinks

/-- The original monadic `LongestPathCompaction.compact(compactor)` (reference of `compact`). -/
def compactReference : CompactM Unit := do
  let cNodes ← cNodeIds
  let mut minStartPos := Float.posInf
  for cNode in cNodes do
    let n ← getCNode cNode
    let some nodeGroup := n.cGroup | continue
    let some reference := (← getCGroup nodeGroup).reference | continue
    let referenceX := (← getCNode reference).hitbox.x
    minStartPos := fmin minStartPos (referenceX + n.cGroupOffset.x)
  if !minStartPos.isFinite then
    minStartPos := 0.0
  let cGroups ← cGroupIds
  let mut sinks : Array CGroupId := #[]
  for group in cGroups do
    modifyCGroup group fun g => { g with startPos := minStartPos }
    if (← getCGroup group).outDegree == 0 then
      sinks := sinks.push group
  let mut head := 0
  while head < sinks.size do
    let group := sinks[head]!
    head := head + 1
    sinks ← processGroupReference group sinks head
  for cNode in cNodes do
    let startPos := (← getCNode cNode).startPos
    modifyCNode cNode fun n => { n with hitbox := { n.hitbox with x := startPos } }

namespace Pure

/-- `isLockedNode` on the graph value. -/
@[inline] def lockedNode (lockFun : Option LockFunction) (g : CGraph) (n : CNodeId) (dir : Direction) : Bool :=
  match lockFun with
  | some f => f g n dir
  | none => false

/-- `isLockedGroup` on the graph value. -/
@[inline] def lockedGroup (lockFun : Option LockFunction) (g : CGraph) (group : CGroupId) (dir : Direction) : Bool :=
  (g.cGroup group).cNodes.any fun n => lockedNode lockFun g n dir

/-- Whether `group` occurs in `sinks` from index `i` on (Rust `sinks.iter().any(..)` on the
not yet popped entries). -/
partial def pendingContains (sinks : Array CGroupId) (group : CGroupId) (i : Nat) : Bool :=
  if h : i < sinks.size then sinks[i] == group || pendingContains sinks group (i + 1) else false

/-- `processGroupReference` on the graph value. -/
def processGroup (lockFun : Option LockFunction) (sh : SpacingsHandler) (dir : Direction)
    (group : CGroupId) (g : CGraph) (sinks : Array CGroupId) (head : Nat) : CGraph × Array CGroupId := Id.run do
  let grp := g.cGroup group
  let some reference := grp.reference | return (g, sinks)
  let mut g := g
  let mut diff := (g.cNode reference).hitbox.x
  let groupNodes := grp.cNodes
  for node in groupNodes do
    let suggestedX := (g.cGroup group).startPos + (g.cNode node).cGroupOffset.x
    let currentX := (g.cNode node).hitbox.x
    let canMove := !(lockedGroup lockFun g group dir) || currentX < suggestedX
    g := g.modifyCNode node fun n => { n with startPos := if canMove then suggestedX else currentX }
  diff := diff - (g.cNode reference).startPos
  let right := dir == .right || dir == .down
  g := g.modifyCGroup group fun gr =>
    { gr with
      delta := gr.delta + diff
      deltaNormalized := if right then gr.deltaNormalized + diff else gr.deltaNormalized - diff }
  let horizontal := dir.isHorizontal
  let mut sinks := sinks
  for node in groupNodes do
    let n := g.cNode node
    let nodeStartPos := n.startPos
    let nodeWidth := n.hitbox.width
    for incNode in n.constraints do
      let spacing := if horizontal then sh.horizontal g node incNode else sh.vertical g node incNode
      let inc := g.cNode incNode
      let some incGroup := inc.cGroup | continue
      let incOffsetX := inc.cGroupOffset.x
      g := g.modifyCGroup incGroup fun gr =>
        { gr with startPos := fmax gr.startPos (nodeStartPos + nodeWidth + spacing - incOffsetX) }
      if lockedNode lockFun g incNode dir then
        let lockedX := (g.cNode incNode).hitbox.x - incOffsetX
        g := g.modifyCGroup incGroup fun gr => { gr with startPos := fmax gr.startPos lockedX }
      g := g.modifyCGroup incGroup fun gr => { gr with outDegree := gr.outDegree - 1 }
      if (g.cGroup incGroup).outDegree == 0 && !(pendingContains sinks incGroup head) then
        sinks := sinks.push incGroup
  return (g, sinks)

/-- Processes the sink queue from `head` on. -/
partial def drain (lockFun : Option LockFunction) (sh : SpacingsHandler) (dir : Direction)
    (g : CGraph) (sinks : Array CGroupId) (head : Nat) : CGraph :=
  if h : head < sinks.size then
    let (g, sinks) := processGroup lockFun sh dir sinks[head] g sinks (head + 1)
    drain lockFun sh dir g sinks (head + 1)
  else g

/-- `compactReference` on the graph value. -/
def compact (lockFun : Option LockFunction) (sh : SpacingsHandler) (dir : Direction) (g : CGraph) : CGraph := Id.run do
  let nodeCount := g.cNodes.size
  let groupCount := g.cGroups.size
  let mut minStartPos := Float.posInf
  for i in [0:nodeCount] do
    let n := g.cNode ⟨i⟩
    let some nodeGroup := n.cGroup | continue
    let some reference := (g.cGroup nodeGroup).reference | continue
    let referenceX := (g.cNode reference).hitbox.x
    minStartPos := fmin minStartPos (referenceX + n.cGroupOffset.x)
  if !minStartPos.isFinite then
    minStartPos := 0.0
  let mut g := g
  let mut sinks : Array CGroupId := #[]
  for i in [0:groupCount] do
    g := g.modifyCGroup ⟨i⟩ fun gr => { gr with startPos := minStartPos }
    if (g.cGroup ⟨i⟩).outDegree == 0 then
      sinks := sinks.push ⟨i⟩
  g := drain lockFun sh dir g sinks 0
  for i in [0:nodeCount] do
    g := g.modifyCNode ⟨i⟩ fun n => { n with hitbox := { n.hitbox with x := n.startPos } }
  return g

end Pure

/-- `LongestPathCompaction.compact(compactor)` (fast path of `compactReference`, see the module
doc). -/
def compact : CompactM Unit := do
  let s ← get
  let lockFun := s.lockFun
  let sh := s.spacingsHandler
  let dir := s.direction
  let g ← modifyGet fun s => (s.cGraph, { s with cGraph := {} })
  let g := Pure.compact lockFun sh dir g
  modify fun s => { s with cGraph := g }

end LongestPathCompaction

/-- `new LongestPathCompaction()`. -/
def LongestPathCompaction : CompactionAlgorithm := ⟨LongestPathCompaction.compact⟩

end Elk.Alg.Common.Compaction.OneD
