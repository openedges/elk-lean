import Elk.Alg.Common.Compaction.OneD.LongestPathCompaction
import Elk.Alg.Common.Compaction.OneD.QuadraticConstraintCalculation
import Elk.Alg.Common.Compaction.OneD.ScanlineConstraintCalculator
import Elk.Core.Exceptions
/-!
# `org.eclipse.elk.alg.common.compaction.oned.OneDimensionalCompactor`

One-dimensional compaction of a `CGraph` in the four directions (elk-rs
`one_dimensional_compactor.rs`). Compaction always happens "to the left": the other directions
are realised by mirroring/transposing the hitboxes, and `finish` restores the `LEFT`
orientation.

API: the compactor is a value. The builder-style Java/Rust methods are functions
`OneDimensionalCompactor → OneDimensionalCompactor` (setters, `calculateGroupOffsets`) or
`OneDimensionalCompactor → IO OneDimensionalCompactor` (everything that runs a strategy or can
throw), so that a Rust chain `c.change_direction(d).compact().finish()` reads
`c.changeDirection d >>= (·.compact) >>= (·.finish)`. The resulting graph is
`compactor.cGraph` (the Rust code shares it through `Rc`).

Strategies run on the `CompactorState` part of the compactor (see `ICompactionAlgorithm`). The
`reverse_constraints` hash map (keyed by node pointer, only used for lookups) is an array
indexed by `CNodeId`.
-/
/-! Float literal as a global constant (PLAN §7.1 items 17, 22). -/
private def fl0p0 : Float := 0.0

namespace Elk.Alg.Common.Compaction.OneD

open Elk.Core Elk.Core.Math Elk.Core.Util Elk.Core.Options

/-- `OneDimensionalCompactor`. -/
structure OneDimensionalCompactor extends CompactorState where
  /-- `compactionAlgorithm` (default `LongestPathCompaction`). -/
  compactionAlgorithm : CompactionAlgorithm := LongestPathCompaction
  /-- `constraintAlgorithm` (default `ScanlineConstraintCalculator`). -/
  constraintAlgorithm : ConstraintCalculationAlgorithm := ScanlineConstraintCalculator
  /-- `finished`. -/
  finished : Bool := false

namespace CGraph

/-- The original `calculateGroupOffsets` on the graph (reference of the fast path
`calculateGroupOffsets`). -/
def calculateGroupOffsetsReference (g : CGraph) : CGraph := Id.run do
  let mut g := g
  for gi in g.cGroupIds do
    let groupNodes := (g.cGroup gi).cNodes
    g := g.modifyCGroup gi fun grp => { grp with reference := none }
    for n in groupNodes do
      g := g.modifyCNode n fun c => { c with cGroupOffset := KVector.zero }
      let candidateX := (g.cNode n).hitbox.x
      let replace : Bool :=
        match (g.cGroup gi).reference with
        | some cur => candidateX < (g.cNode cur).hitbox.x
        | none => true
      if replace then
        g := g.modifyCGroup gi fun grp => { grp with reference := some n }
    let some reference := (g.cGroup gi).reference | continue
    let refX := (g.cNode reference).hitbox.x
    let refY := (g.cNode reference).hitbox.y
    for n in groupNodes do
      g := g.modifyCNode n fun c =>
        { c with cGroupOffset := ⟨c.hitbox.x - refX, c.hitbox.y - refY⟩ }
  return g

/-- `calculateGroupOffsets` on the graph: the reference of each group becomes its left-most node
(first one on ties) and every node stores its offset to the reference.

Fast path of `calculateGroupOffsetsReference` (differential test
`alg.common.compaction.cgraphFast`): the reference updates and the zero offsets the original writes
first are overwritten before anything reads them (a group without reference has no nodes), so
only the final reference and offsets are written, on the unpacked arenas. -/
def calculateGroupOffsets (g : CGraph) : CGraph :=
  match g with
  | ⟨nodes, groups, sd, ph, pv⟩ => Id.run do
    let mut nodes := nodes
    let mut groups := groups
    for gi in [0:groups.size] do
      let groupNodes := groups[gi]!.cNodes
      let mut reference : Option CNodeId := none
      let mut referenceX := fl0p0
      for n in groupNodes do
        let x := (nodes[n.idx]?.getD default).hitbox.x
        match reference with
        | some _ =>
          if x < referenceX then
            reference := some n
            referenceX := x
        | none =>
          reference := some n
          referenceX := x
      groups := groups.modifyIn gi fun grp => { grp with reference := reference }
      if let some r := reference then
        let rh := (nodes[r.idx]?.getD default).hitbox
        let refX := rh.x
        let refY := rh.y
        for n in groupNodes do
          nodes := nodes.modifyIn n.idx fun c =>
            { c with cGroupOffset := ⟨c.hitbox.x - refX, c.hitbox.y - refY⟩ }
    return ⟨nodes, groups, sd, ph, pv⟩

/-- `mirrorHitboxes`: `x := -x - width` for all nodes, then `calculateGroupOffsets`. -/
def mirrorHitboxes (g : CGraph) : CGraph := Id.run do
  let mut g := g
  for n in g.cNodeIds do
    g := g.modifyCNode n fun c => { c with hitbox := { c.hitbox with x := -c.hitbox.x - c.hitbox.width } }
  return g.calculateGroupOffsets

/-- `transposeHitboxes`: swaps x/y, width/height and the group offset coordinates, then
`calculateGroupOffsets`. -/
def transposeHitboxes (g : CGraph) : CGraph := Id.run do
  let mut g := g
  for n in g.cNodeIds do
    g := g.modifyCNode n fun c =>
      { c with
        hitbox := { x := c.hitbox.y, y := c.hitbox.x, width := c.hitbox.height, height := c.hitbox.width }
        cGroupOffset := ⟨c.cGroupOffset.y, c.cGroupOffset.x⟩ }
  return g.calculateGroupOffsets

/-- `calculateConstraintsForCGroups`: recomputes `outDegree`, `outDegreeReal` and
`incomingConstraints` of all groups from the node constraints. -/
def calculateConstraintsForCGroups (g : CGraph) : CGraph := Id.run do
  let mut g := g
  let groups := g.cGroupIds
  for gi in groups do
    g := g.modifyCGroup gi fun grp =>
      { grp with outDegree := 0, outDegreeReal := 0, incomingConstraints := #[] }
  for gi in groups do
    for n in (g.cGroup gi).cNodes do
      for incoming in (g.cNode n).constraints do
        let some incomingGroup := (g.cNode incoming).cGroup | continue
        if incomingGroup == gi then continue
        g := g.modifyCGroup gi fun grp =>
          if grp.incomingConstraints.contains incoming then grp
          else { grp with incomingConstraints := grp.incomingConstraints.push incoming }
        g := g.modifyCGroup incomingGroup fun grp =>
          { grp with outDegree := grp.outDegree + 1, outDegreeReal := grp.outDegreeReal + 1 }
  return g

/-- `reverseConstraints`: every constraint `a → b` becomes `b → a` (the new lists are ordered by
the source node index), start positions are reset, then `calculateConstraintsForCGroups`. -/
def reverseConstraints (g : CGraph) : CGraph := Id.run do
  let mut g := g
  let nodes := g.cNodeIds
  let mut incoming : Array (Array CNodeId) := Array.replicate nodes.size #[]
  for n in nodes do
    g := g.modifyCNode n fun c => { c with startPos := Float.negInf }
    for inc in (g.cNode n).constraints do
      incoming := incoming.modifyIn inc.idx (·.push n)
  for n in nodes do
    let cs := incoming[n.idx]?.getD #[]
    g := g.modifyCNode n fun c => { c with constraints := cs }
  return g.calculateConstraintsForCGroups

end CGraph

namespace OneDimensionalCompactor

/-- Runs a strategy on the `CompactorState` part (Rust moves the strategy out of `self` while it
runs). -/
private def runStrategy (c : OneDimensionalCompactor) (act : CompactM Unit) :
    IO OneDimensionalCompactor := do
  let compactionAlgorithm := c.compactionAlgorithm
  let constraintAlgorithm := c.constraintAlgorithm
  let finished := c.finished
  let (_, st) ← act.run c.toCompactorState
  return { toCompactorState := st, compactionAlgorithm, constraintAlgorithm, finished }

/-- `calculateGroupOffsets()`. -/
def calculateGroupOffsets (c : OneDimensionalCompactor) : OneDimensionalCompactor :=
  { c with cGraph := c.cGraph.calculateGroupOffsets }

/-- `new OneDimensionalCompactor(cGraph)`: calculates the group offsets, puts every node without
a group into a new singleton group and stores `hitboxPreCompaction`. -/
def new (cGraph : CGraph) : OneDimensionalCompactor := Id.run do
  let c : OneDimensionalCompactor := { cGraph }
  let c := c.calculateGroupOffsets
  let mut g := c.cGraph
  for n in g.cNodeIds do
    if (g.cNode n).cGroup.isNone then
      -- cannot fail: the node has no group
      match CGroup.create g #[n] with
      | .ok (g', _) => g := g'
      | .error _ => pure ()
    g := g.modifyCNode n fun cn => { cn with hitboxPreCompaction := some cn.hitbox }
  return { c with cGraph := g }

/-- `setSpacingsHandler(handler)`. -/
def setSpacingsHandler (c : OneDimensionalCompactor) (handler : SpacingsHandler) :
    OneDimensionalCompactor :=
  { c with spacingsHandler := handler }

/-- `setCompactionAlgorithm(compactor)`. -/
def setCompactionAlgorithm (c : OneDimensionalCompactor) (alg : CompactionAlgorithm) :
    OneDimensionalCompactor :=
  { c with compactionAlgorithm := alg }

/-- `setConstraintAlgorithm(algorithm)`. -/
def setConstraintAlgorithm (c : OneDimensionalCompactor) (alg : ConstraintCalculationAlgorithm) :
    OneDimensionalCompactor :=
  { c with constraintAlgorithm := alg }

/-- `setLockFunction(lockFunction)` (`none` unlocks everything). -/
def setLockFunction (c : OneDimensionalCompactor) (lockFun : Option LockFunction) :
    OneDimensionalCompactor :=
  { c with lockFun }

/-- `isLockedNode(node, direction)`. -/
def isLockedNode (c : OneDimensionalCompactor) (node : CNodeId) (direction : Direction) : Bool :=
  c.toCompactorState.isLockedNode node direction

/-- `isLockedGroup(group, direction)`. -/
def isLockedGroup (c : OneDimensionalCompactor) (group : CGroupId) (direction : Direction) : Bool :=
  c.toCompactorState.isLockedGroup group direction

private def finishedMessage : String :=
  "The OneDimensionalCompactor instance has been finished already."

/-- `calculateConstraints`: clears the constraints, adds the predefined ones for the current
dimension, runs the constraint strategy and updates the group constraints. -/
private def calculateConstraints (c : OneDimensionalCompactor) : IO OneDimensionalCompactor := do
  let dir := c.direction
  let mut g := c.cGraph
  let c := { c with cGraph := {} }
  for n in g.cNodeIds do
    g := g.modifyCNode n fun cn => { cn with constraints := #[] }
  let constraints :=
    if dir.isHorizontal then g.predefinedHorizontalConstraints else g.predefinedVerticalConstraints
  for (first, second) in constraints do
    if dir == .left || dir == .up then
      g := g.modifyCNode first fun cn => { cn with constraints := cn.constraints.push second }
    else
      g := g.modifyCNode second fun cn => { cn with constraints := cn.constraints.push first }
  let c := { c with cGraph := g }
  let c ← c.runStrategy c.constraintAlgorithm.calculateConstraints
  return { c with cGraph := c.cGraph.calculateConstraintsForCGroups }

/-- `forceConstraintsRecalculation()`. -/
def forceConstraintsRecalculation (c : OneDimensionalCompactor) : IO OneDimensionalCompactor :=
  c.calculateConstraints

private def mirror (c : OneDimensionalCompactor) : OneDimensionalCompactor :=
  { c with cGraph := c.cGraph.mirrorHitboxes }

private def transpose (c : OneDimensionalCompactor) : OneDimensionalCompactor :=
  { c with cGraph := c.cGraph.transposeHitboxes }

private def reverse (c : OneDimensionalCompactor) : OneDimensionalCompactor :=
  { c with cGraph := c.cGraph.reverseConstraints }

/-- `changeDirection(direction)`: transforms the hitboxes from the current to the new direction
and recalculates (or reverses) the constraints. Throws if the compactor is finished or the
direction is not supported by the graph. -/
def changeDirection (c : OneDimensionalCompactor) (dir : Direction) : IO OneDimensionalCompactor := do
  if c.finished then throwIllegalState finishedMessage
  if !c.cGraph.supports dir then
    throwIllegalState s!"The direction {dir} is not supported by the CGraph instance."
  if dir == c.direction then return c
  let old := c.direction
  let c := { c with direction := dir }
  match old, dir with
  | .undefined, .left => c.calculateConstraints
  | .undefined, .right => c.mirror.calculateConstraints
  | .undefined, .up => c.transpose.calculateConstraints
  | .undefined, .down => c.transpose.mirror.calculateConstraints
  | .left, .right => return c.mirror.reverse
  | .left, .up => c.transpose.calculateConstraints
  | .left, .down => c.transpose.mirror.calculateConstraints
  | .right, .left => return c.mirror.reverse
  | .right, .up => c.mirror.transpose.calculateConstraints
  | .right, .down => c.mirror.transpose.mirror.calculateConstraints
  | .up, .left => c.transpose.calculateConstraints
  | .up, .right => c.transpose.mirror.calculateConstraints
  | .up, .down => return c.mirror.reverse
  | .down, .left => c.mirror.transpose.calculateConstraints
  | .down, .right => c.mirror.transpose.mirror.calculateConstraints
  | .down, .up => return c.mirror.reverse
  | _, _ => return c

/-- `compact()`: compacts in the current direction (`LEFT` if none was set yet). -/
def compact (c : OneDimensionalCompactor) : IO OneDimensionalCompactor := do
  if c.finished then throwIllegalState finishedMessage
  let c ← if c.direction == .undefined then c.changeDirection .left else pure c
  let mut g := c.cGraph
  let c := { c with cGraph := {} }
  for gi in g.cGroupIds do
    g := g.modifyCGroup gi fun grp => { grp with outDegree := grp.outDegreeReal }
  for n in g.cNodeIds do
    g := g.modifyCNode n fun cn => { cn with startPos := Float.negInf }
  let c := { c with cGraph := g }
  c.runStrategy c.compactionAlgorithm.compact

/-- `finish()`: restores the `LEFT` orientation and marks the compactor as finished. -/
def finish (c : OneDimensionalCompactor) : IO OneDimensionalCompactor := do
  let c ← c.changeDirection .left
  return { c with finished := true }

end OneDimensionalCompactor

end Elk.Alg.Common.Compaction.OneD
