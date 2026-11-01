import Elk.Alg.Common.Compaction.OneD.ICompactionAlgorithm
import Elk.Core.Util.FloatConst
open Elk.Core.Util.FloatConst
/-!
# `org.eclipse.elk.alg.common.compaction.oned.LongestPathCompaction`

Longest path compaction of the CGroups (elk-rs `longest_path_compaction.rs`): groups are
processed from the sinks (out degree 0) in FIFO order; each processed group pushes the start
positions of the groups constrained by it. The Rust `VecDeque` is an array with a head index;
the duplicate check (`sinks.iter().any(..)`) only looks at the not yet popped entries.

`compact` is a pure fast path: it takes the `CGraph` out of the compactor state once, runs the
same reads and updates in the same order on its unpacked node and group arenas (`Pure`, tail
recursive loops; a `CGraph` value is only built for a closure lock function or spacings handler,
which receive the current graph as in the monadic version) and stores it back. Rebuilding the graph
and the groups around every update after a branch allocated two cells per constraint (PLAN 7.1 item
13). A `LockFunction.flags` lock reads neither the graph nor the direction, so `isLockedGroup` of the
processed group is evaluated once per group instead of once per node (its node list does not change
while the group is processed); an `individualMin` spacings handler is evaluated without a closure.
The monadic original is kept as `compactReference` (differential test
`alg.common.compaction.longestPathFast`, closure and flag locks, closure and individual spacings).
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

/-- The read-only part of one `compact` run: the lock function, the spacings handler, the
direction and the graph fields the strategies never change (to hand a `CGraph` to a closure). -/
structure Env where
  lockFun : Option LockFunction
  sh : SpacingsHandler
  dir : Direction
  /-- `dir.isHorizontal`. -/
  horizontal : Bool
  /-- `dir == RIGHT || dir == DOWN`. -/
  right : Bool
  supportedDirections : Array Direction
  predefinedHorizontal : Array (CNodeId × CNodeId)
  predefinedVertical : Array (CNodeId × CNodeId)

/-- The current graph of the unpacked arenas (only built for a closure that reads it). -/
@[inline] def Env.graph (e : Env) (nodes : Array CNode) (groups : Array CGroup) : CGraph :=
  ⟨nodes, groups, e.supportedDirections, e.predefinedHorizontal, e.predefinedVertical⟩

/-- `CGraph.cNode` on the node arena. -/
@[inline] def nodeAt (nodes : Array CNode) (i : Nat) : CNode := if h : i < nodes.size then nodes[i] else default

/-- `CGraph.cGroup` on the group arena. -/
@[inline] def groupAt (groups : Array CGroup) (i : Nat) : CGroup := if h : i < groups.size then groups[i] else default

/-- `isLockedNode(n, dir)` on the current arenas. -/
@[inline] def lockedNode (e : Env) (nodes : Array CNode) (groups : Array CGroup) (n : CNodeId) : Bool :=
  match e.lockFun with
  | none => false
  | some (.flags locked) => locked[n.idx]?.getD false
  | some (.fn f) => f (e.graph nodes groups) n e.dir

/-- `isLockedGroup(group, dir)` on the current arenas: some node of the group is locked. -/
@[inline] def lockedGroup (e : Env) (nodes : Array CNode) (groups : Array CGroup) (gi : Nat) : Bool :=
  match e.lockFun with
  | none => false
  | some (.flags locked) => (groupAt groups gi).cNodes.any fun n => locked[n.idx]?.getD false
  | some (.fn f) =>
    let g := e.graph nodes groups
    (groupAt groups gi).cNodes.any fun n => f g n e.dir

/-- The spacing between `a` and `b` in the compaction dimension (`getHorizontalSpacing` for a
horizontal direction, else `getVerticalSpacing`) on the current arenas. -/
@[inline] def spacing (e : Env) (nodes : Array CNode) (groups : Array CGroup) (a b : CNodeId) : Float :=
  match e.sh with
  | .individualMin sp d => fmin (SpacingsHandler.individualOf sp d a) (SpacingsHandler.individualOf sp d b)
  | .mk h v => if e.horizontal then h (e.graph nodes groups) a b else v (e.graph nodes groups) a b

/-- Whether `group` occurs in `sinks` from index `i` on (Rust `sinks.iter().any(..)` on the
not yet popped entries). -/
partial def pendingContains (sinks : Array CGroupId) (group : CGroupId) (i : Nat) : Bool :=
  if h : i < sinks.size then sinks[i] == group || pendingContains sinks group (i + 1) else false

/-- `startPos := x` (unshared node: updated in place). -/
@[inline] def setStartPos (x : Float) (n : CNode) : CNode := { n with startPos := x }

/-- `startPos := fmax startPos x`. -/
@[inline] def raiseStartPos (x : Float) (g : CGroup) : CGroup := { g with startPos := fmax g.startPos x }

/-- `outDegree := outDegree - 1`. -/
@[inline] def decOutDegree (g : CGroup) : CGroup := { g with outDegree := g.outDegree - 1 }

/-- `delta += diff`, `deltaNormalized ±= diff` (`+` for `RIGHT`/`DOWN`). -/
@[inline] def addDelta (right : Bool) (diff : Float) (g : CGroup) : CGroup :=
  { g with
    delta := g.delta + diff
    deltaNormalized := if right then g.deltaNormalized + diff else g.deltaNormalized - diff }

/-- The first node loop of the processed group `gi`: every node of `groupNodes[i:]` moves to its
suggested position unless the group is locked and the node lies right of it. `lockMode` is `0`
(the group is not locked), `1` (locked) or `2` (`isLockedGroup` is asked per node, as in Java: a
lock function reading the graph sees the start positions written so far). A lock given by node
flags does not depend on the graph, and the group's node list does not change here, so its value
is fixed for the loop (`0`/`1`). -/
partial def startLoop (e : Env) (gi : Nat) (groupNodes : Array CNodeId) (lockMode : UInt8) (i : Nat)
    (nodes : Array CNode) (groups : Array CGroup) : Array CNode :=
  if h : i < groupNodes.size then
    let node := groupNodes[i]
    let suggestedX := (groupAt groups gi).startPos + (nodeAt nodes node.idx).cGroupOffset.x
    let currentX := (nodeAt nodes node.idx).hitbox.x
    let locked := if lockMode == 0 then false else if lockMode == 1 then true else lockedGroup e nodes groups gi
    let canMove := !locked || currentX < suggestedX
    startLoop e gi groupNodes lockMode (i + 1)
      (nodes.modifyIn node.idx (setStartPos (if canMove then suggestedX else currentX))) groups
  else nodes

/-- The constraint loop of the processed group: for the node `groupNodes[i]`, its constraint
`k` on, then the following nodes. Pushes every group whose out degree drops to `0` and that is not
pending (`sinks[head:]`). -/
partial def edgeLoop (e : Env) (groupNodes : Array CNodeId) (head : Nat) (i k : Nat) (nodes : Array CNode)
    (groups : Array CGroup) (sinks : Array CGroupId) : Array CGroup × Array CGroupId :=
  if h : i < groupNodes.size then
    let node := groupNodes[i]
    let n := nodeAt nodes node.idx
    let cs := n.constraints
    if h2 : k < cs.size then
      let incNode := cs[k]
      let sp := spacing e nodes groups node incNode
      let inc := nodeAt nodes incNode.idx
      match inc.cGroup with
      | none => edgeLoop e groupNodes head i (k + 1) nodes groups sinks
      | some incGroup =>
        let incOffsetX := inc.cGroupOffset.x
        let groups := groups.modifyIn incGroup.idx (raiseStartPos (n.startPos + n.hitbox.width + sp - incOffsetX))
        let groups := if lockedNode e nodes groups incNode then
            groups.modifyIn incGroup.idx (raiseStartPos ((nodeAt nodes incNode.idx).hitbox.x - incOffsetX))
          else groups
        let groups := groups.modifyIn incGroup.idx decOutDegree
        let push := (groupAt groups incGroup.idx).outDegree == 0 && !pendingContains sinks incGroup head
        edgeLoop e groupNodes head i (k + 1) nodes groups (if push then sinks.push incGroup else sinks)
    else edgeLoop e groupNodes head (i + 1) 0 nodes groups sinks
  else (groups, sinks)

/-- Processes the sink queue from `head` on (body of the Rust `while let Some(group) =
sinks.pop_front()`, `processGroupReference`). -/
partial def drain (e : Env) (nodes : Array CNode) (groups : Array CGroup) (sinks : Array CGroupId) (head : Nat) :
    Array CNode × Array CGroup :=
  if h : head < sinks.size then
    let gi := sinks[head].idx
    let grp := groupAt groups gi
    match grp.reference with
    | none => drain e nodes groups sinks (head + 1)
    | some reference =>
      let groupNodes := grp.cNodes
      let referenceX := (nodeAt nodes reference.idx).hitbox.x
      let lockMode : UInt8 := match e.lockFun with
        | none => 0
        | some (.flags _) => if lockedGroup e nodes groups gi then 1 else 0
        | some (.fn _) => 2
      let nodes := startLoop e gi groupNodes lockMode 0 nodes groups
      let diff := referenceX - (nodeAt nodes reference.idx).startPos
      let groups := groups.modifyIn gi (addDelta e.right diff)
      let (groups, sinks) := edgeLoop e groupNodes (head + 1) 0 0 nodes groups sinks
      drain e nodes groups sinks (head + 1)
  else (nodes, groups)

/-- The minimum over the nodes `nodes[i:]` with a group that has a reference of the reference's x
plus the node's group offset. -/
partial def minStart (nodes : Array CNode) (groups : Array CGroup) (i : Nat) (acc : Float) : Float :=
  if h : i < nodes.size then
    let n := nodes[i]
    match n.cGroup with
    | none => minStart nodes groups (i + 1) acc
    | some nodeGroup =>
      match (groupAt groups nodeGroup.idx).reference with
      | none => minStart nodes groups (i + 1) acc
      | some reference =>
        minStart nodes groups (i + 1) (fmin acc ((nodeAt nodes reference.idx).hitbox.x + n.cGroupOffset.x))
  else acc

/-- `startPos := minStartPos` for the groups `groups[i:]`; the groups of out degree `0` are pushed
onto `sinks`. -/
partial def initGroups (minStartPos : Float) (i : Nat) (groups : Array CGroup) (sinks : Array CGroupId) :
    Array CGroup × Array CGroupId :=
  if i < groups.size then
    let groups := groups.modifyIn i fun gr => { gr with startPos := minStartPos }
    let sink := (groupAt groups i).outDegree == 0
    initGroups minStartPos (i + 1) groups (if sink then sinks.push ⟨i⟩ else sinks)
  else (groups, sinks)

/-- `hitbox.x := startPos` for the nodes `nodes[i:]`. -/
partial def applyStarts (i : Nat) (nodes : Array CNode) : Array CNode :=
  if i < nodes.size then
    applyStarts (i + 1) (nodes.modifyIn i fun n => { n with hitbox := { n.hitbox with x := n.startPos } })
  else nodes

/-- `compactReference` on the graph value, on the unpacked arenas: the same reads and updates in
the same order (the lock function and the spacings handler see the current graph; a closure form
gets it as a value, the `flags`/`individualMin` forms read their tables). -/
def compact (lockFun : Option LockFunction) (sh : SpacingsHandler) (dir : Direction) (g : CGraph) : CGraph :=
  match g with
  | ⟨nodes, groups, sd, ph, pv⟩ =>
    let minStartPos := minStart nodes groups 0 Float.posInf
    let minStartPos := if !minStartPos.isFinite then fl0p0 else minStartPos
    let (groups, sinks) := initGroups minStartPos 0 groups #[]
    let e : Env := { lockFun, sh, dir, horizontal := dir.isHorizontal, right := dir == .right || dir == .down,
                     supportedDirections := sd, predefinedHorizontal := ph, predefinedVertical := pv }
    let (nodes, groups) := drain e nodes groups sinks 0
    ⟨applyStarts 0 nodes, groups, sd, ph, pv⟩

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
