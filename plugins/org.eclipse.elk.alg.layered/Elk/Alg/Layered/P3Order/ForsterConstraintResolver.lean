import Elk.Alg.Layered.Graph
import Elk.Alg.Layered.P3Order.CrossMinSnapshot
import Elk.Alg.Layered.P3Order.Counting.IInitializable
import Elk.Alg.Layered.P3Order.Counting.BinaryIndexedTree
import Elk.Alg.Layered.P3Order.Counting.CrossMinUtil
import Std.Data.HashMap
/-!
# `org.eclipse.elk.alg.layered.p3order.ForsterConstraintResolver`

Resolves in-layer ordering constraints (successor constraints, non-overlapping layout units)
after the barycenter sort with the method of Forster ("A Fast and Simple Heuristic for
Constrained Two-Level Crossing Reduction"), elk-rs `forster_constraint_resolver.rs`.

Representation:
- `ConstraintGroup`s live in an arena (`constraintGroupArena`, Rust `Vec<ConstraintGroup>`)
  and are referenced by their index (Rust `ConstraintGroupId`, Java object identity). The
  arena and the layout units are cleared when layer `0` is initialised (Rust).
- `barycenterStates` is owned by the resolver like in elk-rs (`pub barycenter_states`): the
  barycenter heuristic reads and writes it through the shared `IO.Ref`. `BarycenterState` is
  `BarycenterHeuristic.BarycenterState` in Java/Rust; it is defined here because the resolver
  is the lower module.
- elk-rs reads node ids, layer indices and node types from the `CrossMinSnapshot` once one is
  set (`set_snapshot`, called by the barycenter heuristic after the `GraphInfoHolder` built it)
  and from the live graph otherwise (`LNode.id`, `Layer.id`, `LNode.type`); both are kept
  (`snapshot`). The `ArenaSync` property reads of elk-rs are plain arena reads.
- One `processConstraints` call runs on local copies of the resolver state (`ForsterData`)
  in `ExceptT String (StateM ForsterData)`; the arena is only read. A layer without any
  constraint (`unconstrained`) skips the passes, which would change neither the order nor a
  barycenter.
- `BarycenterState` keeps the barycenter unboxed (`barycenterValue`, `hasBarycenter`);
  `barycenter`/`setBarycenter` are the `Option` view.

Rust semantics kept where they differ from Java:
- `new` takes `constraintsBetweenNonDummies` as an argument (Java reads
  `IN_LAYER_SUCCESSOR_CONSTRAINTS_BETWEEN_NON_DUMMIES` from the first node's graph);
- `initAtLayerLevel` also sets `Layer.id := layerIndex`;
- `handleViolatedConstraint` inserts the merged group with `insert(index)` and revisits the
  merged group itself before the group that followed (Java's `ListIterator.add` skips it);
- `mergeGroups` tests `isEmpty` instead of `null` outgoing lists, decrements the incoming count
  saturating at `0`, and always stores the merged barycenter (`none` when both are unknown);
- a missing barycenter compares as `0.0` (Java would throw a `NullPointerException`);
- a missing constraint group throws `IllegalStateException: constraint group missing` (Rust
  `expect`).
The `ELK_TRACE` group dumps of elk-rs are not reproduced.
-/
namespace Elk.Alg.Layered.P3Order

open Elk.Core.Util Elk.Alg.Layered.Graph Elk.Alg.Layered.P3Order.Counting LayeredM

/-- `BarycenterHeuristic.BarycenterState`: the barycenter bookkeeping of one node. -/
structure BarycenterState where
  /-- `node`. -/
  node : LNodeId
  /-- `summedWeight`. -/
  summedWeight : Float := 0.0
  /-- `degree`. -/
  degree : Int := 0
  /-- `barycenter` (Java `Double`, `null` = unknown) when `hasBarycenter` (unboxed; see `barycenter`). -/
  barycenterValue : Float := 0.0
  /-- Whether the barycenter is known. -/
  hasBarycenter : Bool := false
  /-- `visited`. -/
  visited : Bool := false
  deriving Inhabited

/-- `BarycenterState::new(node)`. -/
def BarycenterState.new (node : LNodeId) : BarycenterState := { node }

/-- `barycenter` (`none` = unknown). -/
@[inline] def BarycenterState.barycenter (st : BarycenterState) : Option Float :=
  if st.hasBarycenter then some st.barycenterValue else none

/-- Whether state `(li, ni)` of a `barycenter_states[layer][node id]` table exists and has a
barycenter (without building an `Option`). -/
@[inline] def BarycenterState.knownIn (states : Array (Array (Option BarycenterState))) (li ni : Nat) : Bool :=
  if h : li < states.size then
    let row := states[li]
    if h2 : ni < row.size then
      match row[ni] with
      | some st => st.hasBarycenter
      | none => false
    else false
  else false

/-- The barycenter of state `(li, ni)` when `knownIn` (`0.0` without a state). -/
@[inline] def BarycenterState.valueIn (states : Array (Array (Option BarycenterState))) (li ni : Nat) : Float :=
  if h : li < states.size then
    let row := states[li]
    if h2 : ni < row.size then
      match row[ni] with
      | some st => st.barycenterValue
      | none => floatZero
    else floatZero
  else floatZero

/-- `barycenter = b`. -/
@[inline] def BarycenterState.setBarycenter (st : BarycenterState) (b : Option Float) : BarycenterState :=
  match b with
  | some v => { st with barycenterValue := v, hasBarycenter := true }
  | none => { st with hasBarycenter := false }

/-- Updates state `(li, ni)` of a `barycenter_states[layer][node id]` table (no-op without a
state). The row and the state are taken out before the update so that both change in place. -/
@[inline] def BarycenterState.updateIn (states : Array (Array (Option BarycenterState))) (li ni : Nat)
    (f : BarycenterState → BarycenterState) : Array (Array (Option BarycenterState)) :=
  if h : li < states.size then
    let row := states[li]
    let states := states.setIfInBounds li #[]
    let row := if h2 : ni < row.size then
        let o := row[ni]
        let row := row.setIfInBounds ni none
        match o with
        | some st => row.setIfInBounds ni (some (f st))
        | none => row
      else row
    states.setIfInBounds li row
  else states

/-- `ForsterConstraintResolver.ConstraintGroup`: nodes that must stay together, with the
constraint graph edges (group ids). -/
structure ConstraintGroup where
  /-- `summedWeight`. -/
  summedWeight : Float := 0.0
  /-- `degree`. -/
  degree : Int := 0
  /-- `nodes`. -/
  nodes : Array LNodeId := #[]
  /-- `outgoingConstraints` (group ids). -/
  outgoingConstraints : Array Nat := #[]
  /-- `incomingConstraints` (group ids). -/
  incomingConstraints : Array Nat := #[]
  /-- `incomingConstraintsCount` (Rust `usize`). -/
  incomingConstraintsCount : Nat := 0
  deriving Inhabited

namespace ConstraintGroup

/-- `ConstraintGroup::new(node)`. -/
def new (node : LNodeId) : ConstraintGroup := { nodes := #[node] }

/-- `ConstraintGroup::new_with_nodes(nodes)`. -/
def newWithNodes (nodes : Array LNodeId) : ConstraintGroup := { nodes }

/-- `has_outgoing_constraints()`. -/
@[inline] def hasOutgoingConstraints (g : ConstraintGroup) : Bool := !g.outgoingConstraints.isEmpty

/-- `single_node()`: the first node (groups are never empty; Rust would panic). -/
@[inline] def singleNode (g : ConstraintGroup) : LNodeId := g.nodes[0]?.getD default

end ConstraintGroup

/-- Rust `contains_group(list, target)`. -/
@[inline] def containsGroup (list : Array Nat) (target : Nat) : Bool := list.contains target

/-- Rust `remove_group(list, target)`: removes the first occurrence; whether one was removed. -/
def removeGroup (list : Array Nat) (target : Nat) : Array Nat × Bool :=
  match list.findIdx? (· == target) with
  | some i => (list.eraseIdxIfInBounds i, true)
  | none => (list, false)

/-- Grows `arr` with `v` to at least `n` entries (Rust `resize(n, v)` after a `>= len` check).
Sizes beyond `u32` (ids wrapped from negative values) are ignored instead of aborting. -/
def growTo {α : Type} (arr : Array α) (n : Nat) (v : α) : Array α :=
  -- `n > 2^32` as `(n - 1) >>> 32 != 0` (no big `Nat` literal at run time)
  if n <= arr.size || (n - 1) >>> 32 != 0 then arr else arr ++ Array.replicate (n - arr.size) v

/-- Mutable state of one resolver operation (the Rust fields that change). -/
structure ForsterData where
  /-- `layout_units`: layout unit node → its nodes in initialisation order. -/
  layoutUnits : Std.HashMap LNodeId (Array LNodeId) := {}
  /-- `barycenter_states[layer][node id]`. -/
  barycenterStates : Array (Array (Option BarycenterState)) := #[]
  /-- `constraint_groups[layer][node id]`: group id. -/
  constraintGroups : Array (Array (Option Nat)) := #[]
  /-- `constraint_group_arena`. -/
  constraintGroupArena : Array ConstraintGroup := #[]
  deriving Inhabited

namespace ForsterData

/-- Updates the barycenter states (fields taken out first, so the tables change in place). -/
@[inline] def updateBarycenterStates (d : ForsterData)
    (f : Array (Array (Option BarycenterState)) → Array (Array (Option BarycenterState))) : ForsterData :=
  match d with
  | ⟨lu, bs, cg, cga⟩ => ⟨lu, f bs, cg, cga⟩

/-- Updates the constraint group table. -/
@[inline] def updateConstraintGroups (d : ForsterData) (f : Array (Array (Option Nat)) → Array (Array (Option Nat))) :
    ForsterData :=
  match d with
  | ⟨lu, bs, cg, cga⟩ => ⟨lu, bs, f cg, cga⟩

/-- Updates the constraint group arena. -/
@[inline] def updateArena (d : ForsterData) (f : Array ConstraintGroup → Array ConstraintGroup) : ForsterData :=
  match d with
  | ⟨lu, bs, cg, cga⟩ => ⟨lu, bs, cg, f cga⟩

end ForsterData

/-- Read-only context: the arena and the snapshot (if set). -/
structure ForsterCtx where
  arena : LGraphArena
  snapshot : Option CrossMinSnapshot

/-- Rust `layer_index(node)`: `Layer.id as usize` of the node's layer, `0` without a layer. -/
def liveLayerIndex (a : LGraphArena) (n : LNodeId) : Nat :=
  match (a.node n).layer with
  | some l => asUsize (a.layer l).id
  | none => 0

namespace ForsterCtx

/-- `snap_node_id(node)`. -/
@[inline] def nodeId (c : ForsterCtx) (n : LNodeId) : Nat :=
  match c.snapshot with
  | some s => s.nodeId n
  | none => asUsize (c.arena.node n).id

/-- `snap_layer_index(node)`. -/
@[inline] def layerIndex (c : ForsterCtx) (n : LNodeId) : Nat :=
  match c.snapshot with
  | some s => s.nodeLayerIndex n
  | none => liveLayerIndex c.arena n

/-- `snap_node_type(node)`. -/
@[inline] def nodeType (c : ForsterCtx) (n : LNodeId) : NodeType :=
  match c.snapshot with
  | some s => s.nodeTypeOf (s.nodeFlatIndex n)
  | none => (c.arena.node n).type

end ForsterCtx

/-- The monad of the resolver internals. -/
abbrev ForsterM := ExceptT String (StateM ForsterData)

namespace ForsterM

/-- `group(group_id)`. -/
@[inline] def group (gid : Nat) : ForsterM (Option ConstraintGroup) := do
  return (← get).constraintGroupArena[gid]?

/-- `group_mut(group_id)` with an update. -/
@[inline] def modifyGroup (gid : Nat) (f : ConstraintGroup → ConstraintGroup) : ForsterM Unit :=
  modify fun d => d.updateArena (·.modify gid f)

/-- `add_group(group)`. -/
def addGroup (g : ConstraintGroup) : ForsterM Nat :=
  modifyGet fun d => (d.constraintGroupArena.size, d.updateArena (·.push g))

/-- `group_of(node)`. -/
def groupOf (c : ForsterCtx) (n : LNodeId) : ForsterM Nat := do
  let li := c.layerIndex n
  let ni := c.nodeId n
  match ((← get).constraintGroups[li]?).bind (·[ni]?) with
  | some (some g) => return g
  | _ => throw "java.lang.IllegalStateException: constraint group missing"

/-- The barycenter of a node's state (`none` without a state). -/
def nodeBarycenter (c : ForsterCtx) (n : LNodeId) : ForsterM (Option Float) := do
  let li := c.layerIndex n
  let ni := c.nodeId n
  return ((((← get).barycenterStates[li]?).bind (·[ni]?)).bind id).bind (·.barycenter)

/-- Sets the barycenter of a node's state (no-op without a state). -/
def setNodeBarycenter (c : ForsterCtx) (n : LNodeId) (b : Option Float) : ForsterM Unit := do
  let li := c.layerIndex n
  let ni := c.nodeId n
  modify fun d => d.updateBarycenterStates (BarycenterState.updateIn · li ni fun s => s.setBarycenter b)

/-- `group_barycenter(group)`: the barycenter of the group's first node. -/
def groupBarycenter (c : ForsterCtx) (gid : Nat) : ForsterM (Option Float) := do
  let some g ← group gid | return none
  nodeBarycenter c g.singleNode

/-- `set_group_barycenter(group, barycenter)`: for every node of the group. -/
def setGroupBarycenter (c : ForsterCtx) (gid : Nat) (b : Option Float) : ForsterM Unit := do
  let some g ← group gid | return
  for n in g.nodes do
    setNodeBarycenter c n b

/-- `init_node_level(node, full_init)`: a fresh single-node group; with `fullInit` also a fresh
barycenter state and the layout unit registration (`IN_LAYER_LAYOUT_UNIT`, read live). -/
def initNodeLevel (c : ForsterCtx) (node : LNodeId) (fullInit : Bool) : ForsterM Unit := do
  let li := c.layerIndex node
  let ni := c.nodeId node
  if li < (← get).constraintGroups.size then
    let gid ← addGroup (ConstraintGroup.new node)
    modify fun d => d.updateConstraintGroups (·.modify li fun l => (growTo l (ni + 1) none).setIfInBounds ni (some gid))
  if fullInit then
    if li < (← get).barycenterStates.size then
      modify fun d => d.updateBarycenterStates (·.modify li fun l =>
        (growTo l (ni + 1) none).setIfInBounds ni (some (BarycenterState.new node)))
    if let some unit := (c.arena.node node).internal.inLayerLayoutUnit then
      modify fun d => { d with layoutUnits := d.layoutUnits.insert unit ((d.layoutUnits.getD unit #[]).push node) }

/-- Adds the constraint `fromGroup → toGroup` (outgoing list and incoming count). -/
@[inline] private def addConstraint (fromGroup toGroup : Nat) : ForsterM Unit := do
  modifyGroup fromGroup fun g => { g with outgoingConstraints := g.outgoingConstraints.push toGroup }
  modifyGroup toGroup fun g => { g with incomingConstraintsCount := g.incomingConstraintsCount + 1 }

/-- The layout unit constraints between the previous normal node and `node`: every node of
the last unit precedes every node of the current unit. -/
private def addLayoutUnitConstraints (c : ForsterCtx) (units : Std.HashMap LNodeId (Array LNodeId))
    (lastNode node : LNodeId) : ForsterM Unit := do
  let lastUnitNodes := units.getD lastNode #[]
  let currentUnitNodes := units.getD node #[]
  for lastUnitNode in lastUnitNodes do
    for currentUnitNode in currentUnitNodes do
      let lastGroup ← groupOf c lastUnitNode
      let currentGroup ← groupOf c currentUnitNode
      addConstraint lastGroup currentGroup

/-- `build_constraints_graph(groups, only_between_normal_nodes)`. -/
def buildConstraintsGraph (c : ForsterCtx) (groups : Array Nat) (onlyBetweenNormalNodes : Bool) : ForsterM Unit := do
  for gid in groups do
    modifyGroup gid fun g => { g with outgoingConstraints := #[], incomingConstraintsCount := 0 }
  let units := (← get).layoutUnits
  let mut lastNonDummyNode : Option LNodeId := none
  for gid in groups do
    let some g ← group gid | continue
    let node := g.singleNode
    if onlyBetweenNormalNodes && c.nodeType node != .normal then continue
    for successor in (c.arena.node node).internal.inLayerSuccessorConstraints do
      if onlyBetweenNormalNodes && c.nodeType successor != .normal then continue
      let successorGroup ← groupOf c successor
      addConstraint gid successorGroup
    if !onlyBetweenNormalNodes && c.nodeType node == .normal then
      if let some lastNode := lastNonDummyNode then
        addLayoutUnitConstraints c units lastNode node
      lastNonDummyNode := some node

/-- The violation test of `find_violated_constraint` for one predecessor (Java compares the
`floatValue()`s for equality, then the doubles). -/
private def isViolated (predBary groupBary : Float) (predIndex groupIndex : Nat) : Bool :=
  if predBary.toF32 == groupBary.toF32 then predIndex > groupIndex
  else predBary > groupBary

/-- The index of the last occurrence of `gid` in `groups` (`0` when absent): the value of the Rust
`index_map` (filled in order, later entries win). -/
def lastIndexOf (groups : Array Nat) (gid : Nat) : Nat := Id.run do
  let mut k := groups.size
  while k > 0 do
    k := k - 1
    if groups[k]! == gid then return k
  return 0

/-- `find_violated_constraint(groups)`: a topological traversal of the constraint graph from its
sources (FIFO), returning the first `(predecessor, group)` pair in the wrong order. -/
def findViolatedConstraint (c : ForsterCtx) (groups : Array Nat) : ForsterM (Option (Nat × Nat)) := do
  let mut active : Array Nat := #[]
  for h : index in [0:groups.size] do
    let gid := groups[index]
    if let some g ← group gid then
      modifyGroup gid fun x => { x with incomingConstraints := #[] }
      if g.hasOutgoingConstraints && g.incomingConstraintsCount == 0 then
        active := active.push gid
  let mut head := 0
  while head < active.size do
    let gid := active[head]!
    head := head + 1
    let incoming := ((← group gid).map (·.incomingConstraints)).getD #[]
    for predecessor in incoming do
      let predBary := (← groupBarycenter c predecessor).getD 0.0
      let groupBary := (← groupBarycenter c gid).getD 0.0
      -- the group indices only break ties of the `f32` barycenters (Rust builds an index map)
      let violated := if predBary.toF32 == groupBary.toF32 then
          isViolated predBary groupBary (lastIndexOf groups predecessor) (lastIndexOf groups gid)
        else isViolated predBary groupBary 0 0
      if violated then
        return some (predecessor, gid)
    let outgoing := ((← group gid).map (·.outgoingConstraints)).getD #[]
    for successorId in outgoing do
      -- a missing group reads count `0` and list length `0` (Rust `unwrap_or(0)`)
      let (incomingCount, listLen) := match ← group successorId with
        | some successor => (successor.incomingConstraintsCount, successor.incomingConstraints.size + 1)
        | none => (0, 0)
      modifyGroup successorId fun x => { x with incomingConstraints := x.incomingConstraints.insertIdxIfInBounds 0 gid }
      if incomingCount == listLen then
        active := active.push successorId
  return none

/-- The outgoing constraints of a merged group (`merge_groups`). -/
private def mergedOutgoing (group1 group2 : Nat) (outgoing1 outgoing2 : Array Nat) : ForsterM (Array Nat) := do
  if !outgoing1.isEmpty then
    let mut outgoing := (removeGroup outgoing1 group2).1
    for candidate in outgoing2 do
      if candidate == group1 then continue
      if containsGroup outgoing candidate then
        modifyGroup candidate fun x => { x with incomingConstraintsCount := x.incomingConstraintsCount - 1 }
      else
        outgoing := outgoing.push candidate
    return outgoing
  else if !outgoing2.isEmpty then
    return (removeGroup outgoing2 group1).1
  else
    return #[]

/-- `merge_groups(group1, group2)`: a new group with the nodes of both, the union of their
outgoing constraints and the combined barycenter. -/
def mergeGroups (c : ForsterCtx) (group1 group2 : Nat) : ForsterM Nat := do
  let g1 := (← group group1).getD {}
  let g2 := (← group group2).getD {}
  let outgoing ← mergedOutgoing group1 group2 g1.outgoingConstraints g2.outgoingConstraints
  let newGroup : ConstraintGroup := { ConstraintGroup.newWithNodes (g1.nodes ++ g2.nodes) with
    summedWeight := g1.summedWeight + g2.summedWeight
    degree := g1.degree + g2.degree
    outgoingConstraints := outgoing }
  let barycenter ← if newGroup.degree > 0 then
      pure (some (newGroup.summedWeight / Float.ofInt newGroup.degree))
    else do
      let b1 ← groupBarycenter c group1
      let b2 ← groupBarycenter c group2
      pure (match b1, b2 with
        | some b1, some b2 => some ((b1 + b2) / 2.0)
        | some b1, none => some b1
        | none, some b2 => some b2
        | none, none => none)
  let newGroupId ← addGroup newGroup
  setGroupBarycenter c newGroupId barycenter
  return newGroupId

/-- `handle_violated_constraint(first, second, groups)`: replaces both groups by their merge,
inserted before the first group with a larger barycenter, and redirects constraints. -/
def handleViolatedConstraint (c : ForsterCtx) (first second : Nat) (groups : Array Nat) : ForsterM (Array Nat) := do
  let newGroup ← mergeGroups c first second
  let newBarycenter := (← groupBarycenter c newGroup).getD 0.0
  let mut groups := groups
  let mut alreadyInserted := false
  let mut index := 0
  while index < groups.size do
    let gid := groups[index]!
    if gid == first || gid == second then
      groups := groups.eraseIdxIfInBounds index
      continue
    let groupBarycenter := (← groupBarycenter c gid).getD 0.0
    if !alreadyInserted && groupBarycenter > newBarycenter then
      groups := groups.insertIdxIfInBounds index newGroup
      alreadyInserted := true
      continue
    if let some g ← group gid then
      if g.hasOutgoingConstraints then
        let (outgoing, firstRemoved) := removeGroup g.outgoingConstraints first
        let (outgoing, secondRemoved) := removeGroup outgoing second
        if firstRemoved || secondRemoved then
          modifyGroup gid fun x => { x with outgoingConstraints := outgoing.push newGroup }
          modifyGroup newGroup fun x => { x with incomingConstraintsCount := x.incomingConstraintsCount + 1 }
    index := index + 1
  if !alreadyInserted then
    groups := groups.push newGroup
  return groups

/-- `process_constraints_internal(nodes, only_between_normal_nodes)`. -/
def processConstraintsInternal (c : ForsterCtx) (nodes : Array LNodeId) (onlyBetweenNormalNodes : Bool) :
    ForsterM (Array LNodeId) := do
  let mut groups : Array Nat := #[]
  for node in nodes do
    groups := groups.push (← groupOf c node)
  buildConstraintsGraph c groups onlyBetweenNormalNodes
  while true do
    match ← findViolatedConstraint c groups with
    | some (first, second) => groups ← handleViolatedConstraint c first second groups
    | none => break
  let mut result : Array LNodeId := #[]
  for gid in groups do
    let groupNodes := ((← group gid).map (·.nodes)).getD #[]
    if groupNodes.size == 1 then
      -- the barycenter of a single-node group is the node's own: writing it back changes nothing
      result := result.push groupNodes[0]!
    else
      let groupBarycenter ← groupBarycenter c gid
      for node in groupNodes do
        result := result.push node
        setNodeBarycenter c node groupBarycenter
  return result

/-- `process_constraints(nodes)`: with `constraintsBetweenNonDummies` first between normal
nodes only (then the groups are re-initialised), then for all nodes. -/
def processConstraints (c : ForsterCtx) (constraintsBetweenNonDummies : Bool) (nodes : Array LNodeId) :
    ForsterM (Array LNodeId) := do
  let mut nodes := nodes
  if constraintsBetweenNonDummies then
    nodes ← processConstraintsInternal c nodes true
    for node in nodes do
      initNodeLevel c node false
  processConstraintsInternal c nodes false

end ForsterM

/-- `ForsterConstraintResolver`: mutable state behind `IO.Ref`s (shared with the barycenter
heuristic, which reads/writes `barycenterStates`). -/
structure ForsterConstraintResolver where
  /-- `constraints_between_non_dummies`. -/
  constraintsBetweenNonDummies : Bool
  /-- `layout_units` (Rust `FxHashMap` keyed by the unit node; only looked up, never iterated). -/
  layoutUnits : IO.Ref (Std.HashMap LNodeId (Array LNodeId))
  /-- `barycenter_states[layer][node id]`. -/
  barycenterStates : IO.Ref (Array (Array (Option BarycenterState)))
  /-- `constraint_groups[layer][node id]`. -/
  constraintGroups : IO.Ref (Array (Array (Option Nat)))
  /-- `constraint_group_arena`. -/
  constraintGroupArena : IO.Ref (Array ConstraintGroup)
  /-- `snapshot` (`set_snapshot`). -/
  snapshot : IO.Ref (Option CrossMinSnapshot)

namespace ForsterConstraintResolver

/-- `ForsterConstraintResolver::new(current_node_order, constraints_between_non_dummies)`
(the node order is not needed; the tables grow on initialisation). -/
def new (_currentNodeOrder : Array (Array LNodeId)) (constraintsBetweenNonDummies : Bool) :
    BaseIO ForsterConstraintResolver := do
  return {
    constraintsBetweenNonDummies
    layoutUnits := ← IO.mkRef {}
    barycenterStates := ← IO.mkRef #[]
    constraintGroups := ← IO.mkRef #[]
    constraintGroupArena := ← IO.mkRef #[]
    snapshot := ← IO.mkRef none }

/-- `set_snapshot(snapshot)`. -/
def setSnapshot (r : ForsterConstraintResolver) (s : CrossMinSnapshot) : BaseIO Unit := r.snapshot.set (some s)

/-- `barycenter_states` (a copy). -/
def getBarycenterStates (r : ForsterConstraintResolver) : BaseIO (Array (Array (Option BarycenterState))) :=
  r.barycenterStates.get

/-- Runs a `ForsterM` operation on the resolver state; the state is written back before a
failure is rethrown as `IO.userError`. -/
def runM {α : Type} (r : ForsterConstraintResolver) (x : ForsterCtx → ForsterM α) : LayeredM α := do
  let c : ForsterCtx := { arena := ← get, snapshot := ← r.snapshot.get }
  let d : ForsterData := {
    layoutUnits := ← r.layoutUnits.swap {}
    barycenterStates := ← r.barycenterStates.swap #[]
    constraintGroups := ← r.constraintGroups.swap #[]
    constraintGroupArena := ← r.constraintGroupArena.swap #[] }
  let (result, d) := Id.run ((x c).run.run d)
  r.layoutUnits.set d.layoutUnits
  r.barycenterStates.set d.barycenterStates
  r.constraintGroups.set d.constraintGroups
  r.constraintGroupArena.set d.constraintGroupArena
  match result with
  | .ok v => return v
  | .error msg => throw (IO.userError msg)

/-- Whether `process_constraints(nodes)` has no constraint to resolve: every node has a constraint
group (`group_of` would not fail), no node has `IN_LAYER_SUCCESSOR_CONSTRAINTS` and no node has
layout unit members. Then `build_constraints_graph` adds no constraint, `find_violated_constraint`
finds none, and every group (`group_of` only ever yields the single-node groups of
`init_node_level`) gives back its node: the order is unchanged and no barycenter is written. The
fields that `build_constraints_graph`/`find_violated_constraint` reset on the groups are reset
again before they are next read, so skipping the passes is not observable. -/
def unconstrained (c : ForsterCtx) (groups : Array (Array (Option Nat))) (units : Std.HashMap LNodeId (Array LNodeId))
    (nodes : Array LNodeId) : Bool :=
  nodes.all fun n =>
    (match (groups[c.layerIndex n]?).bind (·[c.nodeId n]?) with
      | some (some _) => true
      | _ => false) &&
    (c.arena.node n).internal.inLayerSuccessorConstraints.isEmpty &&
    (units.isEmpty || (units.getD n #[]).isEmpty)

/-- `process_constraints(nodes)`: the reordered nodes (Rust rewrites the vector in place); the
group barycenters are written to the nodes' states. Without constraints (`unconstrained`) the
passes are skipped; with `constraintsBetweenNonDummies` the groups are still re-initialised
between them (`init_node_level(node, false)`), as in Rust. -/
def processConstraints (r : ForsterConstraintResolver) (nodes : Array LNodeId) : LayeredM (Array LNodeId) := do
  let c : ForsterCtx := { arena := ← get, snapshot := ← r.snapshot.get }
  let groups ← r.constraintGroups.get
  let units ← r.layoutUnits.get
  if unconstrained c groups units nodes then
    if r.constraintsBetweenNonDummies then
      r.runM fun c => do
        for node in nodes do
          ForsterM.initNodeLevel c node false
        return nodes
    else return nodes
  else
    r.runM fun c => ForsterM.processConstraints c r.constraintsBetweenNonDummies nodes

/-- `init_at_layer_level(layer_index, node_order)`. -/
def initAtLayerLevel (r : ForsterConstraintResolver) (l : Nat) (order : Array (Array LNodeId)) : LayeredM Unit := do
  if l == 0 then
    r.layoutUnits.set {}
    r.constraintGroupArena.set #[]
  let layer := order[l]?.getD #[]
  r.barycenterStates.modify fun s => (growTo s (l + 1) #[]).setIfInBounds l (Array.replicate layer.size none)
  r.constraintGroups.modify fun s => (growTo s (l + 1) #[]).setIfInBounds l (Array.replicate layer.size none)
  if let some first := layer[0]? then
    if let some layerId := (← getNode first).layer then
      modifyLayer layerId fun x => { x with id := l }

/-- `init_at_node_level(layer_index, node_index, node_order)`: `node.id := nodeIndex`, then the
full node initialisation. -/
def initAtNodeLevel (r : ForsterConstraintResolver) (l n : Nat) (order : Array (Array LNodeId)) : LayeredM Unit := do
  let some node := (order[l]?).bind (·[n]?) | return
  modifyNode node fun x => { x with id := n }
  r.runM fun c => ForsterM.initNodeLevel c node true

/-- The `IInitializable` implementation (layer and node level). -/
def initializable (r : ForsterConstraintResolver) : Initializable where
  initAtLayerLevel := r.initAtLayerLevel
  initAtNodeLevel := r.initAtNodeLevel
  usesPortLevel := false
  usesEdgeLevel := false

end ForsterConstraintResolver

end Elk.Alg.Layered.P3Order
