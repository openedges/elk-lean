import Elk.Core.Util.Sort
import Elk.Alg.MrTree.TreeLayoutPhases
import Elk.Alg.MrTree.Options.MrTreeOptions
/-!
# `org.eclipse.elk.alg.mrtree.p2order.NodeOrderer`

Port of `p2order/node_orderer.rs` (elk-rs), the phase `P2_NODE_ORDERING`: starting at the first
`ROOT` node, the nodes of every level get an order index (`POSITION`) and the outgoing edges of the
inner nodes are reordered accordingly (`replace_outgoing_edges`, which also rebuilds the
`direct_children` cache). The weighting is the graph's `WEIGHTING` (`unwrap_or(MODEL_ORDER)`):

* `MODEL_ORDER`: nothing happens;
* `FAN` / `DESCENDANTS` (`order_level_fan_descendants`): the level is sorted stably by increasing
  `FAN`/`DESCENDANTS` (Rust sorts by ascending key, unlike Java's descending comparator); the
  trailing nodes with key 0 are the leaves, the others the inner nodes. Without inner nodes the
  leaves get consecutive positions; otherwise every inner node gets the next position, its children
  are ordered recursively and then sorted stably by *decreasing* position, its outgoing edges are
  reordered, and up to (number of outgoing edges) leaves taken from the *end* of the leaf list
  (Rust `Vec::pop`) get the next positions;
* `CONSTRAINT` (`order_level_constraint`): the nodes with a `POSITION_CONSTRAINT` inside the level
  take that slot (first come, first served; then the nearest free slot searching `+j` before `-j`),
  the out-of-bound constraints fill the free slots from the back (sorted stably by decreasing
  constraint), the unconstrained nodes fill the remaining slots from the front; `POSITION` is the
  slot index. Then the children of every node with a non-zero `FAN` are ordered recursively,
  sorted stably by increasing position and the outgoing edges reordered.

`get_layout_processor_configuration` slots `ROOT_PROC` and, unless the weighting is `MODEL_ORDER`,
`FAN_PROC` before `P2_NODE_ORDERING` (Rust drops Java's `LEVEL_PROC`).

All sorts use consistent integer comparators, so `stableSort` equals Rust's `sort_by`. Rust sorts
the slice of the caller in place; the Lean recursion returns the reordered level instead.
-/
/-! Float literals as global constants (FL): inside branches, loops and specialised code the compiler
shares a literal's `Nat`/`Bool` arguments with unrelated variables (CSE) and then parses it on every
evaluation (`FastFloat.ofScientificImpl`); a top-level constant is a load (PLAN §7.1 items 17, 22). -/
private def fl1p0 : Float := 1.0

namespace Elk.Alg.MrTree.P2Order

open Elk.Core.Alg Elk.Core.Util Elk.Alg.MrTree Elk.Alg.MrTree.Graph Elk.Alg.MrTree.Options
open Elk.Alg.MrTree.Intermediate

namespace NodeOrderer

/-- `reorder_edges(parent, children)`: for every child in order, the outgoing edges of the parent
leading to it (in edge order). -/
def reorderEdges (a : TArena) (parent : TNodeId) (children : Array TNodeId) : Array TEdgeId := Id.run do
  let outgoing := (a.node parent).outgoingEdges
  let mut result : Array TEdgeId := #[]
  for child in children do
    for edge in outgoing do
      if (a.edge edge).target == some child then
        result := result.push edge
  return result

/-- `POSITION := pos`. -/
@[inline] private def setPosition (n : TNodeId) (pos : Int) : MrTreeM Unit :=
  MrTreeM.modifyNode n fun x => { x with internal.position := pos }

/-- The sort property of `order_level_fan_descendants`: `DESCENDANTS` or `FAN`. -/
@[inline] private def sortKey (weighting : OrderWeighting) (n : TNode) : Int :=
  match weighting with
  | .descendants => n.internal.descendants
  | _ => n.internal.fan

/-- `order_level_fan_descendants(current_level, monitor)`: returns the sorted level. -/
partial def orderLevelFanDescendants (weighting : OrderWeighting) (currentLevel : Array TNodeId)
    (monitor : ProgressMonitor) : MrTreeM (Array TNodeId) := do
  discard <| monitor.begin "Processor arrange level" fl1p0
  let a ← get
  let keyed := currentLevel.map fun n => (n, sortKey weighting (a.node n))
  let sorted := stableSort keyed fun x y => compare x.2 y.2
  let level := sorted.map (·.1)
  let sortKeys := sorted.map (·.2)
  let mut firstOcc := level.size
  for i in [0:sortKeys.size] do
    let val := sortKeys[sortKeys.size - 1 - i]!
    if val == 0 then firstOcc := firstOcc - 1
    else break
  let inners := level.extract 0 firstOcc
  let mut leaves := level.extract firstOcc level.size
  let mut pos : Int := 0
  if inners.isEmpty then
    for leaf in leaves do
      setPosition leaf pos
      pos := pos + 1
  else
    let size := max inners.size 1
    for parent in inners do
      setPosition parent pos
      pos := pos + 1
      let children := (← MrTreeM.getNode parent).children
      let children ← orderLevelFanDescendants weighting children
        (← monitor.subTask ((fl1p0 : Float).toF32 / (Float.ofNat size).toF32).toF32)
      let a ← get
      let children := stableSort children fun x y =>
        compare (a.node y).internal.position (a.node x).internal.position
      MrTreeM.replaceOutgoingEdges parent (reorderEdges a parent children)
      let mut fillGap := (← MrTreeM.getNode parent).outgoingEdges.size
      while fillGap > 0 && !leaves.isEmpty do
        let some leaf := leaves.back? | break
        leaves := leaves.pop
        let val := sortKey weighting (← MrTreeM.getNode leaf)
        if val == 0 then
          setPosition leaf pos
          pos := pos + 1
          fillGap := fillGap - 1
        else
          leaves := leaves.push leaf
          break
  monitor.done
  return level

/-- `POSITION_CONSTRAINT` of a node (`unwrap_or(default)`). -/
@[inline] private def constraintOf (n : TNode) (default : Int) : Int :=
  (n.props.get MrTreeOptions.POSITION_CONSTRAINT).getD default

/-- The slot assignment of `order_level_constraint`: the node of every slot. -/
def constraintSlots (a : TArena) (currentLevel : Array TNodeId) : Array (Option TNodeId) := Id.run do
  let len := currentLevel.size
  let lenI : Int := len
  let mut undefinedNodes : Array TNodeId := #[]
  let mut inBoundNodes : Array TNodeId := #[]
  let mut outOfBoundNodes : Array TNodeId := #[]
  for node in currentLevel do
    let constraint := constraintOf (a.node node) (-1)
    if constraint < 0 then undefinedNodes := undefinedNodes.push node
    else if constraint < lenI then inBoundNodes := inBoundNodes.push node
    else outOfBoundNodes := outOfBoundNodes.push node
  let mut sortedNodes : Array (Option TNodeId) := Array.replicate len none
  let free (s : Array (Option TNodeId)) (p : Int) : Bool :=
    p >= 0 && p < lenI && (s[p.toNat]!).isNone
  let mut idx := 0
  while idx < inBoundNodes.size do
    let node := inBoundNodes[idx]!
    let targetPos := constraintOf (a.node node) (-1)
    if free sortedNodes targetPos then
      sortedNodes := sortedNodes.set! targetPos.toNat (some node)
      inBoundNodes := inBoundNodes.eraseIdx! idx
    else
      idx := idx + 1
  idx := 0
  while idx < inBoundNodes.size do
    let node := inBoundNodes[idx]!
    let targetPos := constraintOf (a.node node) (-1)
    -- terminates: fewer placed nodes than slots, so a free slot within distance `len` exists
    for j in [0:2 * len + 1] do
      let j : Int := j
      if free sortedNodes (targetPos + j) then
        sortedNodes := sortedNodes.set! (targetPos + j).toNat (some node)
        inBoundNodes := inBoundNodes.eraseIdx! idx
        break
      if free sortedNodes (targetPos - j) then
        sortedNodes := sortedNodes.set! (targetPos - j).toNat (some node)
        inBoundNodes := inBoundNodes.eraseIdx! idx
        break
  outOfBoundNodes := stableSort outOfBoundNodes fun x y =>
    compare (constraintOf (a.node y) 0) (constraintOf (a.node x) 0)
  for i in [0:len] do
    let slot := len - 1 - i
    if sortedNodes[slot]!.isNone && !outOfBoundNodes.isEmpty then
      sortedNodes := sortedNodes.set! slot (some outOfBoundNodes[0]!)
      outOfBoundNodes := outOfBoundNodes.eraseIdx! 0
  for slot in [0:len] do
    if sortedNodes[slot]!.isNone && !undefinedNodes.isEmpty then
      sortedNodes := sortedNodes.set! slot (some undefinedNodes[0]!)
      undefinedNodes := undefinedNodes.eraseIdx! 0
  return sortedNodes

/-- `order_level_constraint(current_level, monitor)`. -/
partial def orderLevelConstraint (debug : Bool) (currentLevel : Array TNodeId) (monitor : ProgressMonitor) :
    MrTreeM Unit := do
  discard <| monitor.begin "Processor arrange level" fl1p0
  if debug then monitor.log "OrderLevelConstraint!"
  let sortedNodes := constraintSlots (← get) currentLevel
  for index in [0:sortedNodes.size] do
    if let some node := sortedNodes[index]! then setPosition node index
  let a ← get
  let inners := currentLevel.filter fun n => (a.node n).internal.fan != 0
  let size := max inners.size 1
  for parent in inners do
    let children := (← MrTreeM.getNode parent).children
    orderLevelConstraint debug children
      (← monitor.subTask ((fl1p0 : Float).toF32 / (Float.ofNat size).toF32).toF32)
    let a ← get
    let children := stableSort children fun x y =>
      compare (a.node x).internal.position (a.node y).internal.position
    MrTreeM.replaceOutgoingEdges parent (reorderEdges a parent children)
  monitor.done

/-- `NodeOrderer::process`. -/
def process (graph : TGraphId) (monitor : ProgressMonitor) : MrTreeM Unit := do
  discard <| monitor.begin "Processor arrange node" 1.0
  let g ← MrTreeM.getGraph graph
  let debug := (g.props.get MrTreeOptions.DEBUG_MODE).getD false
  let weighting := (g.props.get MrTreeOptions.WEIGHTING).getD .modelOrder
  let a ← get
  let root := g.nodes.find? fun n => (a.node n).internal.root
  if let some root := root then
    match weighting with
    | .fan | .descendants =>
      discard <| orderLevelFanDescendants weighting #[root] (← monitor.subTask 1.0)
    | .constraint => orderLevelConstraint debug #[root] (← monitor.subTask 1.0)
    | .modelOrder => pure ()
  monitor.done

/-- `get_layout_processor_configuration(graph)`. -/
def configuration (graph : TGraphId) : MrTreeM (Option TreeProcessorConfiguration) := do
  let mut config : TreeProcessorConfiguration :=
    LayoutProcessorConfiguration.create.addBefore TreeLayoutPhases.p2NodeOrdering
      IntermediateProcessorStrategy.rootProc
  let weighting := ((← MrTreeM.getGraph graph).props.get MrTreeOptions.WEIGHTING).getD .modelOrder
  if weighting != .modelOrder then
    config := config.addBefore TreeLayoutPhases.p2NodeOrdering IntermediateProcessorStrategy.fanProc
  return some config

/-- The `NodeOrderer` phase. -/
def phase : TreePhase :=
  { name := "NodeOrderer", process, getLayoutProcessorConfiguration := configuration }

end NodeOrderer

end Elk.Alg.MrTree.P2Order
