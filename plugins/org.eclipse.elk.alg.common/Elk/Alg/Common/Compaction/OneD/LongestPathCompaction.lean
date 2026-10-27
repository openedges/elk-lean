import Elk.Alg.Common.Compaction.OneD.ICompactionAlgorithm
/-!
# `org.eclipse.elk.alg.common.compaction.oned.LongestPathCompaction`

Longest path compaction of the CGroups (elk-rs `longest_path_compaction.rs`): groups are
processed from the sinks (out degree 0) in FIFO order; each processed group pushes the start
positions of the groups constrained by it. The Rust `VecDeque` is an array with a head index;
the duplicate check (`sinks.iter().any(..)`) only looks at the not yet popped entries.
-/
namespace Elk.Alg.Common.Compaction.OneD

open Elk.Core.Util Elk.Core.Options CompactM

namespace LongestPathCompaction

/-- Processes one sink group (body of the Rust `while let Some(group) = sinks.pop_front()`).
Returns the new sink queue. -/
private def processGroup (group : CGroupId) (sinks : Array CGroupId) (head : Nat) :
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

/-- `LongestPathCompaction.compact(compactor)`. -/
def compact : CompactM Unit := do
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
    sinks ← processGroup group sinks head
  for cNode in cNodes do
    let startPos := (← getCNode cNode).startPos
    modifyCNode cNode fun n => { n with hitbox := { n.hitbox with x := startPos } }

end LongestPathCompaction

/-- `new LongestPathCompaction()`. -/
def LongestPathCompaction : CompactionAlgorithm := ⟨LongestPathCompaction.compact⟩

end Elk.Alg.Common.Compaction.OneD
