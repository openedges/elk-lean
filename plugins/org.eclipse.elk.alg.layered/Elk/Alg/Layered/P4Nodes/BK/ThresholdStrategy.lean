import Elk.Alg.Layered.P4Nodes.BK.BKAlignedLayout
import Std.Data.HashSet
/-!
# `org.eclipse.elk.alg.layered.p4nodes.bk.ThresholdStrategy` (elk-rs `threshold_strategy.rs`)

Threshold strategies of the BK compactor: `NullThresholdStrategy` (classic compaction, the
threshold has no effect) and `SimpleThresholdStrategy` (only the root and the last node of a
block compute a threshold, from the first valid edge; blocks whose edges cannot be
straightened yet are post-processed after all blocks are placed).

Java's abstract base class holds the shared state (`blockFinished`, the post-processing queue
and stack); the subclasses are the constructors of `ThresholdStrategyKind`. The strategy state
is the `StateRefT` layer of `ThresholdM` on top of the layout monad `BalM` (the Java strategy
keeps a reference to the current layout, `init(bal, ni)`).

Rust deviations from Java that are followed: the `usize` id range checks in `pick_edge` and
`get_bound` (out-of-range ids yield "no edge"/the invalid threshold instead of an exception).
The `debug_assert!`s on the available space in `process` are not ported.
-/
namespace Elk.Alg.Layered.P4Nodes.BK

open Elk.Graph Elk.Core.Math Elk.Core.Util Elk.Alg.Layered.Graph Elk.Alg.Layered.Options

/-- `ThresholdStrategy.Postprocessable`: a unit to be post-processed. -/
structure Postprocessable where
  /-- `free`: the node whose block can potentially be moved. -/
  free : Nat
  /-- `isRoot`: whether `free` is regarded as the root node of its block. -/
  isRoot : Bool
  /-- `hasEdges`: whether `free` has candidate edges. -/
  hasEdges : Bool := false
  /-- `edge`: the edge that was selected to be straightened. -/
  edge : Option LEdgeId := none
  deriving Inhabited

/-- The concrete `ThresholdStrategy` subclass. -/
inductive ThresholdStrategyKind where
  /-- `NullThresholdStrategy`. -/
  | null
  /-- `SimpleThresholdStrategy`. -/
  | simple
  deriving BEq, Inhabited, Repr

/-- `ThresholdStrategy`: the strategy and its state. -/
structure ThresholdStrategy where
  /-- The subclass. -/
  kind : ThresholdStrategyKind
  /-- `blockFinished`: roots of the blocks that have been completely placed. -/
  blockFinished : Std.HashSet Nat := {}
  /-- `postProcessablesQueue` (FIFO from `queueHead`). -/
  postProcessQueue : Array Postprocessable := #[]
  /-- Index of the queue head. -/
  queueHead : Nat := 0
  /-- `postProcessablesStack`. -/
  postProcessStack : Array Postprocessable := #[]
  deriving Inhabited

/-- Threshold strategy computations: the strategy state over the layout monad. -/
abbrev ThresholdM := StateRefT ThresholdStrategy BalM

namespace ThresholdStrategy

/-- `THRESHOLD` (`Double.MAX_VALUE`). -/
def THRESHOLD : Float := Float.maxValue

/-- `EPSILON` (only used by the Java assertions). -/
def EPSILON : Float := 0.0001

/-- `new NullThresholdStrategy()` / `new SimpleThresholdStrategy()`. -/
def create (kind : ThresholdStrategyKind) : ThresholdStrategy := { kind }

/-- `init(bal, ni)`: resets the internal state (a no-op for the null strategy). -/
def init : ThresholdM Unit :=
  modifyThe ThresholdStrategy fun s =>
    match s.kind with
    | .null => s
    | .simple => { s with blockFinished := {}, postProcessQueue := #[], queueHead := 0, postProcessStack := #[] }

/-- `finishBlock(root)`: marks the block of `root` as completely placed (no-op for the null
strategy). -/
def finishBlock (root : Nat) : ThresholdM Unit :=
  modifyThe ThresholdStrategy fun s =>
    match s.kind with
    | .null => s
    | .simple => { s with blockFinished := s.blockFinished.insert root }

/-- The invalid threshold: `+∞` for `UP` (no effect on `min`), else `-∞`. -/
@[inline] private def invalidThreshold (vdir : Option VDirection) : Float :=
  if vdir == some .up then Float.posInf else Float.negInf

/-- `bal.od[bal.root[free]]`. -/
@[inline] private def onlyDummies (bal : BKAlignedLayout) (free : Nat) : Bool := bal.od[bal.rootOf free]!

/-- `SimpleThresholdStrategy.pickEdge(pp)`: the first edge of `pp.free` (incoming edges for a
root with `RIGHT` / a last node with `LEFT`, else outgoing) whose other end belongs to a
finished block. In-layer edges are ignored unless the block consists of dummies only, and no
edge is picked for blocks already part of a straightened edge (`su`). `hasEdges` tells whether
candidate edges exist that might become valid later. -/
private def pickEdge (ctx : BKContext) (pp : Postprocessable) : ThresholdM Postprocessable := do
  let bal ← getThe BKAlignedLayout
  let finished := (← getThe ThresholdStrategy).blockFinished
  let a := ctx.arena
  let freeNode := ctx.nodeOf pp.free
  let incoming := if pp.isRoot then bal.hdir == some .right else bal.hdir == some .left
  -- the node's incoming (outgoing) edges, ports in order, visited without building the list
  let mut hasEdges := false
  for p in (a.node freeNode).ports do
    let pt := a.port p
    for e in (if incoming then pt.incomingEdges else pt.outgoingEdges) do
      if !onlyDummies bal pp.free && a.edgeIsInLayerEdge e then continue
      if bal.su[bal.rootOf pp.free]! then continue
      hasEdges := true
      let some other := a.edgeOtherNode e freeNode
        | throw (IO.userError "java.lang.IllegalArgumentException: node must either be the source node or target node of the edge")
      let otherNodeId := ctx.nodeId other
      if otherNodeId ≥ bal.root.size then continue
      if finished.contains (bal.rootOf otherNodeId) then
        return { pp with hasEdges := true, edge := some e }
  return { pp with hasEdges := hasEdges, edge := none }

/-- The threshold of `getBound` for the picked edge `left → right` (`none` = an id out of
range, Rust returns the invalid threshold): the y position the root (`isRoot`) or last node
must have for the edge to be straight. -/
private def boundFor (ctx : BKContext) (bal : BKAlignedLayout) (isRoot : Bool) (leftPort rightPort : LPortId) :
    Option (Float × Nat × Nat) := do
  let (rootPort, otherPort) :=
    if isRoot then
      if bal.hdir == some .right then (rightPort, leftPort) else (leftPort, rightPort)
    else
      if bal.hdir == some .left then (rightPort, leftPort) else (leftPort, rightPort)
  let otherNodeId := ctx.portNodeId otherPort
  if otherNodeId ≥ bal.root.size then none
  let rootNodeId := ctx.portNodeId rootPort
  if rootNodeId ≥ bal.root.size then none
  let otherRoot := bal.rootOf otherNodeId
  -- Java: y[otherRoot] + innerShift[other] + other.pos.y + other.anchor.y - innerShift[root]
  -- - root.pos.y - root.anchor.y, left to right
  let threshold := ctx.minusPortY
    (ctx.plusPortY (bal.yOf otherRoot + bal.innerShiftOf otherNodeId) otherPort - bal.innerShiftOf rootNodeId)
    rootPort
  let leftNodeId := ctx.portNodeId leftPort
  if leftNodeId ≥ bal.root.size then none
  let rightNodeId := ctx.portNodeId rightPort
  if rightNodeId ≥ bal.root.size then none
  return (threshold, bal.rootOf leftNodeId, bal.rootOf rightNodeId)

/-- `SimpleThresholdStrategy.getBound(blockNode, isRoot)`: picks an edge; if candidates exist
but none is valid yet, the node is queued for post-processing and the invalid threshold is
returned. For a picked edge the threshold that straightens it is returned and both blocks
are flagged as part of a straightened edge (`su`). -/
private def getBound (ctx : BKContext) (blockNode : Nat) (isRoot : Bool) : ThresholdM Float := do
  let trace := ElkTrace.global.bkThresh
  let invalid := invalidThreshold (← getThe BKAlignedLayout).vdir
  let pick ← pickEdge ctx { free := blockNode, isRoot }
  if pick.edge.isNone && pick.hasEdges then
    if trace then
      IO.eprintln s!"bk-thresh: queue free={blockNode} is_root={isRoot} has_edges=true reason=no_finished_neighbor"
    modifyThe ThresholdStrategy fun s => { s with postProcessQueue := s.postProcessQueue.push pick }
    return invalid
  let some edge := pick.edge | return invalid
  let ed := ctx.arena.edge edge
  let (some leftPort, some rightPort) := (ed.source, ed.target)
    | throw (IO.userError "java.lang.IllegalStateException: picked edge without source or target port")
  let some (threshold, leftRoot, rightRoot) := boundFor ctx (← getThe BKAlignedLayout) isRoot leftPort rightPort
    | return invalid
  modifyThe BKAlignedLayout fun b => { b with su := (b.su.set! leftRoot true).set! rightRoot true }
  if trace then
    IO.eprintln s!"bk-thresh: bound free={blockNode} is_root={isRoot} threshold={fmt3 threshold} left_root={leftRoot} right_root={rightRoot}"
  return threshold

/-- `calculateThreshold(oldThresh, blockRoot, currentNode)`: a threshold value representing a
bound that would allow an additional edge to be drawn straight. Null strategy: `+∞` for `UP`,
else `-∞`. Simple strategy: only for the root (`getBound(root, true)`) and — if that is
infinite — the last node of a block (`getBound(current, false)`); other nodes keep
`oldThresh`. -/
def calculateThreshold (ctx : BKContext) (oldThresh : Float) (blockRoot currentNode : Nat) : ThresholdM Float := do
  match (← getThe ThresholdStrategy).kind with
  | .null => return invalidThreshold (← getThe BKAlignedLayout).vdir
  | .simple =>
    let isRoot := blockRoot == currentNode
    let isLast := (← getThe BKAlignedLayout).alignOf currentNode == blockRoot
    if !(isRoot || isLast) then return oldThresh
    let mut t := oldThresh
    if isRoot then
      t ← getBound ctx blockRoot true
    if t.isInf && isLast then
      t ← getBound ctx currentNode false
    return t

/-- `SimpleThresholdStrategy.process(pp)`: tries to straighten `pp.edge` by moving the block of
`pp.free` as far as the neighbors allow; returns whether the block was moved. -/
private def process (ctx : BKContext) (ni : NeighborhoodInformation) (pp : Postprocessable) : ThresholdM Bool := do
  let trace := ElkTrace.global.bkThresh
  let some edge := pp.edge
    | throw (IO.userError "java.lang.IllegalStateException: processable edge missing")
  let ed := ctx.arena.edge edge
  let (some sourcePort, some targetPort) := (ed.source, ed.target)
    | throw (IO.userError "java.lang.IllegalStateException: processable edge without source or target port")
  let freeId := pp.free
  let (fix, block) :=
    if ctx.portNodeId sourcePort == freeId then (targetPort, sourcePort) else (sourcePort, targetPort)
  let blockNodeId := ctx.portNodeId block
  let delta := (← getThe BKAlignedLayout).calculateDelta ctx fix block
  if trace then
    IO.eprintln s!"bk-thresh: process free={freeId} is_root={pp.isRoot} block_node={blockNodeId} delta={fmt3 delta}"
  if delta > 0.0 && delta < THRESHOLD then
    let availableSpace ← (← getThe BKAlignedLayout).checkSpaceAbove ctx ni blockNodeId delta
    BKAlignedLayout.shiftBlock blockNodeId (-availableSpace)
    if trace then
      IO.eprintln s!"bk-thresh: process-up block_node={blockNodeId} delta={fmt3 delta} available={fmt3 availableSpace}"
    return availableSpace > 0.0
  else if delta < 0.0 && -delta < THRESHOLD then
    let availableSpace ← (← getThe BKAlignedLayout).checkSpaceBelow ctx ni blockNodeId (-delta)
    BKAlignedLayout.shiftBlock blockNodeId availableSpace
    if trace then
      IO.eprintln s!"bk-thresh: process-down block_node={blockNodeId} delta={fmt3 delta} available={fmt3 availableSpace}"
    return availableSpace > 0.0
  return false

/-- Pops the head of the post-processing queue. -/
private def popQueue : ThresholdM (Option Postprocessable) :=
  modifyGetThe ThresholdStrategy fun s =>
    match s.postProcessQueue[s.queueHead]? with
    | some pp => (some pp, { s with queueHead := s.queueHead + 1 })
    | none => (none, s)

/-- Pops the top of the post-processing stack. -/
private def popStack : ThresholdM (Option Postprocessable) :=
  modifyGetThe ThresholdStrategy fun s =>
    match s.postProcessStack.back? with
    | some pp => (some pp, { s with postProcessStack := s.postProcessStack.pop })
    | none => (none, s)

/-- `postProcess()`: handles the queued nodes after all blocks were placed, first in the original
order (nodes that could not be moved are pushed onto a stack), then the stacked ones in
reverse order. No-op for the null strategy. -/
def postProcess (ctx : BKContext) (ni : NeighborhoodInformation) : ThresholdM Unit := do
  if (← getThe ThresholdStrategy).kind == .null then return
  let trace := ElkTrace.global.bkThresh
  while true do
    let some pp ← popQueue | break
    let pick ← pickEdge ctx pp
    let some edge := pick.edge
      | do
        if trace then
          IO.eprintln s!"bk-thresh: dequeue free={pick.free} is_root={pick.isRoot} no-edge"
        continue
    let dummiesOnly := onlyDummies (← getThe BKAlignedLayout) pick.free
    if !dummiesOnly && ctx.arena.edgeIsInLayerEdge edge then continue
    let moved ← process ctx ni pick
    if trace then
      IO.eprintln s!"bk-thresh: dequeue free={pick.free} is_root={pick.isRoot} moved={moved}"
    if !moved then
      modifyThe ThresholdStrategy fun s => { s with postProcessStack := s.postProcessStack.push pick }
  while true do
    let some pp ← popStack | break
    if trace then
      IO.eprintln s!"bk-thresh: stack-pop free={pp.free} is_root={pp.isRoot}"
    let _ ← process ctx ni pp

end ThresholdStrategy

end Elk.Alg.Layered.P4Nodes.BK
