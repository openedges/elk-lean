import Elk.Alg.Layered.Graph
import Elk.Alg.Layered.P3Order.CrossMinSnapshot
import Elk.Alg.Layered.P3Order.Counting.IInitializable
import Elk.Alg.Layered.P3Order.Counting.BinaryIndexedTree
import Elk.Alg.Layered.P3Order.Counting.CrossMinUtil
import Std.Data.HashMap
import Elk.Graph.ArrayModify
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
  modify fun d => d.updateArena (·.modifyIn gid f)

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

/-! ## Allocation-free `process_constraints` (Lean only)

`ForsterM.processConstraints` is the line-by-line port; `ForsterFast.processConstraints` computes
exactly the same: the same reads and writes of the group arena, the barycenter states and the group
table in the same order (so the same groups are created with the same ids and contents, the same
fields are left behind on the groups, and the same barycenters are written), the same result, and on
a missing constraint group the same state at the failure. It threads the three tables through tail
recursive loops instead of `ExceptT String (StateM ForsterData)`, reads groups and barycenters
without `Option`s (a missing barycenter reads `0.0` where the port reads `getD 0.0`), evaluates
`group_barycenter` only where its value is used (it is a pure read) and once per active group in
`find_violated_constraint` (nothing is written there), and only copies an outgoing list in
`handle_violated_constraint` when it contains one of the merged groups (`removeGroup` then changes
it). The differential test `forster fast = port` compares both on random constraint layers. -/

namespace ForsterFast

/-- The constraint group arena. -/
abbrev Arena := Array ConstraintGroup

/-- `barycenter_states[layer][node id]`. -/
abbrev States := Array (Array (Option BarycenterState))

/-- `constraint_groups[layer][node id]`. -/
abbrev Table := Array (Array (Option Nat))

/-- `group_of(node)` as `group id + 1` (`0`: no group, where `ForsterM.groupOf` throws). -/
@[inline] def groupIdx (c : ForsterCtx) (table : Table) (n : LNodeId) : Nat :=
  let li := c.layerIndex n
  let ni := c.nodeId n
  if h : li < table.size then
    let row := table[li]
    if h2 : ni < row.size then
      match row[ni] with
      | some g => g + 1
      | none => 0
    else 0
  else 0

/-- Whether a node type is `NORMAL` (a `match`, not the derived `BEq`). -/
@[inline] def isNormal : NodeType → Bool
  | .normal => true
  | _ => false

/-- `ConstraintGroup.singleNode` of group `gid` (`default` for a missing or empty group). -/
@[inline] def singleNodeOf (arena : Arena) (gid : Nat) : LNodeId :=
  if h : gid < arena.size then
    let nodes := arena[gid].nodes
    if h2 : 0 < nodes.size then nodes[0] else default
  else default

/-- `nodeBarycenter(node).getD 0.0`. -/
@[inline] def nodeBaryD (c : ForsterCtx) (states : States) (n : LNodeId) : Float :=
  let li := c.layerIndex n
  let ni := c.nodeId n
  if h : li < states.size then
    let row := states[li]
    if h2 : ni < row.size then
      match row[ni] with
      | some st => if st.hasBarycenter then st.barycenterValue else floatZero
      | none => floatZero
    else floatZero
  else floatZero

/-- Whether `nodeBarycenter(node)` is `some`. -/
@[inline] def nodeBaryKnown (c : ForsterCtx) (states : States) (n : LNodeId) : Bool :=
  BarycenterState.knownIn states (c.layerIndex n) (c.nodeId n)

/-- `groupBarycenter(gid).getD 0.0` (a missing group reads `0.0`). -/
@[inline] def groupBaryD (c : ForsterCtx) (arena : Arena) (states : States) (gid : Nat) : Float :=
  if gid < arena.size then nodeBaryD c states (singleNodeOf arena gid) else floatZero

/-- Whether `groupBarycenter(gid)` is `some`. -/
@[inline] def groupBaryKnown (c : ForsterCtx) (arena : Arena) (states : States) (gid : Nat) : Bool :=
  gid < arena.size && nodeBaryKnown c states (singleNodeOf arena gid)

/-- `setNodeBarycenter(node, known ? some value : none)`. -/
@[inline] def setNodeBary (c : ForsterCtx) (states : States) (n : LNodeId) (known : Bool) (value : Float) : States :=
  BarycenterState.updateIn states (c.layerIndex n) (c.nodeId n) fun st =>
    if known then { st with barycenterValue := value, hasBarycenter := true } else { st with hasBarycenter := false }

/-- `setNodeBary` for the nodes `nodes[i:]`. -/
partial def setNodesBary (c : ForsterCtx) (nodes : Array LNodeId) (i : Nat) (known : Bool) (value : Float)
    (states : States) : States :=
  if h : i < nodes.size then setNodesBary c nodes (i + 1) known value (setNodeBary c states nodes[i] known value)
  else states

/-- `outgoingConstraints.push g` on an unshared group (the fields are taken apart, so the list is
updated in place). -/
@[inline] def pushOutgoing (g : Nat) : ConstraintGroup → ConstraintGroup
  | ⟨sw, deg, nodes, out, inc, cnt⟩ => ⟨sw, deg, nodes, out.push g, inc, cnt⟩

/-- `incomingConstraints.insert(0, g)` (`insertIdxIfInBounds 0`) in place. -/
@[inline] def insertIncomingFront (g : Nat) : ConstraintGroup → ConstraintGroup
  | ⟨sw, deg, nodes, out, inc, cnt⟩ => ⟨sw, deg, nodes, out, inc.insertIdxIfInBounds 0 g, cnt⟩

/-- `incomingConstraints := #[]`, keeping the list's storage (`shrink 0` of the unshared list is the
same empty list). -/
@[inline] def clearIncoming : ConstraintGroup → ConstraintGroup
  | ⟨sw, deg, nodes, out, inc, cnt⟩ => ⟨sw, deg, nodes, out, inc.shrink 0, cnt⟩

/-- `outgoingConstraints := #[]`, `incomingConstraintsCount := 0`, keeping the list's storage. -/
@[inline] def clearOutgoing : ConstraintGroup → ConstraintGroup
  | ⟨sw, deg, nodes, out, inc, _⟩ => ⟨sw, deg, nodes, out.shrink 0, inc, 0⟩

/-- `addConstraint(from, to)`. -/
@[inline] def addConstraint (arena : Arena) (fromGroup toGroup : Nat) : Arena :=
  let arena := arena.modifyIn fromGroup (pushOutgoing toGroup)
  arena.modifyIn toGroup fun g => { g with incomingConstraintsCount := g.incomingConstraintsCount + 1 }

/-- The arena and whether no `group_of` failed (the arena is the state at the failure otherwise). -/
structure ArenaOk where
  arena : Arena
  ok : Bool
  deriving Inhabited

/-! ### `build_constraints_graph` -/

/-- The reset loop: no outgoing constraints and no incoming count for the groups `groups[i:]`. -/
partial def resetOutgoing (groups : Array Nat) (i : Nat) (arena : Arena) : Arena :=
  if h : i < groups.size then
    resetOutgoing groups (i + 1) (arena.modifyIn groups[i] clearOutgoing)
  else arena

/-- The successor loop of group `gid` over `succs[k:]`. -/
partial def addSuccessors (c : ForsterCtx) (table : Table) (onlyNormal : Bool) (gid : Nat) (succs : Array LNodeId)
    (k : Nat) (arena : Arena) : ArenaOk :=
  if h : k < succs.size then
    let s := succs[k]
    if onlyNormal && !isNormal (c.nodeType s) then addSuccessors c table onlyNormal gid succs (k + 1) arena
    else
      let sg := groupIdx c table s
      if sg == 0 then ⟨arena, false⟩
      else addSuccessors c table onlyNormal gid succs (k + 1) (addConstraint arena gid (sg - 1))
  else ⟨arena, true⟩

/-- The inner loop of `addLayoutUnitConstraints` (`groupOf lastUnitNode`, then `groupOf
currentUnitNode`, for every current unit node `cur[k:]`). -/
partial def addUnitInner (c : ForsterCtx) (table : Table) (lastUnitNode : LNodeId) (cur : Array LNodeId) (k : Nat)
    (arena : Arena) : ArenaOk :=
  if h : k < cur.size then
    let lg := groupIdx c table lastUnitNode
    if lg == 0 then ⟨arena, false⟩
    else
      let cg := groupIdx c table cur[k]
      if cg == 0 then ⟨arena, false⟩
      else addUnitInner c table lastUnitNode cur (k + 1) (addConstraint arena (lg - 1) (cg - 1))
  else ⟨arena, true⟩

/-- `addLayoutUnitConstraints` over the last unit's nodes `last[j:]`. -/
partial def addUnitOuter (c : ForsterCtx) (table : Table) (last cur : Array LNodeId) (j : Nat) (arena : Arena) : ArenaOk :=
  if h : j < last.size then
    let r := addUnitInner c table last[j] cur 0 arena
    if r.ok then addUnitOuter c table last cur (j + 1) r.arena else r
  else ⟨arena, true⟩

/-- The main loop of `build_constraints_graph` over `groups[i:]` (`hasLast`/`last`: the last
non-dummy node). -/
partial def buildLoop (c : ForsterCtx) (table : Table) (units : Std.HashMap LNodeId (Array LNodeId))
    (onlyNormal : Bool) (groups : Array Nat) (i : Nat) (hasLast : Bool) (last : LNodeId) (arena : Arena) : ArenaOk :=
  if h : i < groups.size then
    let gid := groups[i]
    if gid < arena.size then
      let node := singleNodeOf arena gid
      let normal := isNormal (c.nodeType node)
      if onlyNormal && !normal then buildLoop c table units onlyNormal groups (i + 1) hasLast last arena
      else
        let r := addSuccessors c table onlyNormal gid (c.arena.node node).internal.inLayerSuccessorConstraints 0 arena
        if !r.ok then r
        else if !onlyNormal && normal then
          if hasLast then
            let r2 := addUnitOuter c table (units.getD last #[]) (units.getD node #[]) 0 r.arena
            if r2.ok then buildLoop c table units onlyNormal groups (i + 1) true node r2.arena else r2
          else buildLoop c table units onlyNormal groups (i + 1) true node r.arena
        else buildLoop c table units onlyNormal groups (i + 1) hasLast last r.arena
    else buildLoop c table units onlyNormal groups (i + 1) hasLast last arena
  else ⟨arena, true⟩

/-- `build_constraints_graph(groups, only_between_normal_nodes)`. -/
def buildConstraintsGraph (c : ForsterCtx) (table : Table) (units : Std.HashMap LNodeId (Array LNodeId))
    (groups : Array Nat) (onlyNormal : Bool) (arena : Arena) : ArenaOk :=
  buildLoop c table units onlyNormal groups 0 false default (resetOutgoing groups 0 arena)

/-! ### `find_violated_constraint` -/

/-- The result of `find_violated_constraint`: the arena and, when `found`, the pair. -/
structure Found where
  arena : Arena
  found : Bool
  first : Nat
  second : Nat
  deriving Inhabited

/-- The reset loop: empty incoming lists, the sources with outgoing constraints are activated. -/
partial def findReset (groups : Array Nat) (i : Nat) (active : Array Nat) (arena : Arena) : Arena × Array Nat :=
  if h : i < groups.size then
    let gid := groups[i]
    if h2 : gid < arena.size then
      let g := arena[gid]
      let source := !g.outgoingConstraints.isEmpty && g.incomingConstraintsCount == 0
      let arena := arena.modifyIn gid clearIncoming
      findReset groups (i + 1) (if source then active.push gid else active) arena
    else findReset groups (i + 1) active arena
  else (arena, active)

/-- The predecessor loop of an active group (barycenter `groupBary`) over `incoming[k:]`: the first
violating predecessor `+ 1`, else `0`. -/
partial def findViolatingPred (c : ForsterCtx) (arena : Arena) (states : States) (groups : Array Nat) (gid : Nat)
    (groupBary : Float) (incoming : Array Nat) (k : Nat) : Nat :=
  if h : k < incoming.size then
    let pred := incoming[k]
    let predBary := groupBaryD c arena states pred
    let violated := if predBary.toF32 == groupBary.toF32 then
        ForsterM.lastIndexOf groups pred > ForsterM.lastIndexOf groups gid
      else predBary > groupBary
    if violated then pred + 1 else findViolatingPred c arena states groups gid groupBary incoming (k + 1)
  else 0

/-- The FIFO traversal: the successor loop of group `gid` over `outgoing[k:]`, then the next active
group `active[head]`. -/
partial def findLoop (c : ForsterCtx) (states : States) (groups : Array Nat) (active : Array Nat) (head gid : Nat)
    (outgoing : Array Nat) (k : Nat) (arena : Arena) : Found :=
  if h : k < outgoing.size then
    let succ := outgoing[k]
    let incomingCount := if h2 : succ < arena.size then arena[succ].incomingConstraintsCount else 0
    let listLen := if h2 : succ < arena.size then arena[succ].incomingConstraints.size + 1 else 0
    let arena := arena.modifyIn succ (insertIncomingFront gid)
    findLoop c states groups (if incomingCount == listLen then active.push succ else active) head gid outgoing (k + 1) arena
  else if h : head < active.size then
    let g := active[head]
    let incoming := if h2 : g < arena.size then arena[g].incomingConstraints else #[]
    let p := if incoming.isEmpty then 0
      else findViolatingPred c arena states groups g (groupBaryD c arena states g) incoming 0
    if p != 0 then ⟨arena, true, p - 1, g⟩
    else
      let outgoing := if h2 : g < arena.size then arena[g].outgoingConstraints else #[]
      findLoop c states groups active (head + 1) g outgoing 0 arena
  else ⟨arena, false, 0, 0⟩

/-- `find_violated_constraint(groups)`. -/
def findViolatedConstraint (c : ForsterCtx) (states : States) (groups : Array Nat) (arena : Arena) : Found :=
  let (arena, active) := findReset groups 0 #[] arena
  findLoop c states groups active 0 0 #[] 0 arena

/-! ### `handle_violated_constraint` -/

/-- The index of the first `target` in `xs[i:]` (`xs.size` when absent). -/
partial def indexOfFrom (xs : Array Nat) (target i : Nat) : Nat :=
  if h : i < xs.size then (if xs[i] == target then i else indexOfFrom xs target (i + 1)) else xs.size

/-- The candidate loop of `mergedOutgoing` over `outgoing2[k:]`. -/
partial def mergeCandidates (group1 : Nat) (outgoing2 : Array Nat) (k : Nat) (outgoing : Array Nat) (arena : Arena) :
    Array Nat × Arena :=
  if h : k < outgoing2.size then
    let cand := outgoing2[k]
    if cand == group1 then mergeCandidates group1 outgoing2 (k + 1) outgoing arena
    else if outgoing.contains cand then
      mergeCandidates group1 outgoing2 (k + 1) outgoing
        (arena.modifyIn cand fun x => { x with incomingConstraintsCount := x.incomingConstraintsCount - 1 })
    else mergeCandidates group1 outgoing2 (k + 1) (outgoing.push cand) arena
  else (outgoing, arena)

/-- `mergedOutgoing(group1, group2, outgoing1, outgoing2)`. -/
def mergedOutgoing (group1 group2 : Nat) (outgoing1 outgoing2 : Array Nat) (arena : Arena) : Array Nat × Arena :=
  if !outgoing1.isEmpty then mergeCandidates group1 outgoing2 0 (removeGroup outgoing1 group2).1 arena
  else if !outgoing2.isEmpty then ((removeGroup outgoing2 group1).1, arena)
  else (#[], arena)

/-- The arena and barycenter states after a merge, and the new group's id. -/
structure Merged where
  arena : Arena
  states : States
  newGroup : Nat
  deriving Inhabited

/-- `merge_groups(group1, group2)`. -/
def mergeGroups (c : ForsterCtx) (group1 group2 : Nat) (arena : Arena) (states : States) : Merged :=
  let g1 : ConstraintGroup := arena[group1]?.getD {}
  let g2 : ConstraintGroup := arena[group2]?.getD {}
  let (outgoing, arena) := mergedOutgoing group1 group2 g1.outgoingConstraints g2.outgoingConstraints arena
  let nodes := g1.nodes ++ g2.nodes
  let summedWeight := g1.summedWeight + g2.summedWeight
  let degree := g1.degree + g2.degree
  -- the barycenter (`b1`/`b2` are read after `mergedOutgoing`, which only changes counts)
  let (known, value) :=
    if degree > 0 then (true, summedWeight / Float.ofInt degree)
    else
      let k1 := groupBaryKnown c arena states group1
      let k2 := groupBaryKnown c arena states group2
      if k1 && k2 then (true, (groupBaryD c arena states group1 + groupBaryD c arena states group2) / floatTwo)
      else if k1 then (true, groupBaryD c arena states group1)
      else if k2 then (true, groupBaryD c arena states group2)
      else (false, floatZero)
  let newGroup : ConstraintGroup := { ConstraintGroup.newWithNodes nodes with summedWeight, degree, outgoingConstraints := outgoing }
  let newId := arena.size
  let arena := arena.push newGroup
  ⟨arena, setNodesBary c nodes 0 known value states, newId⟩

/-- The group loop of `handle_violated_constraint` from `groups[index]` on. -/
partial def handleLoop (c : ForsterCtx) (states : States) (first second newGroup : Nat) (newBary : Float)
    (inserted : Bool) (index : Nat) (groups : Array Nat) (arena : Arena) : Array Nat × Arena :=
  if h : index < groups.size then
    let gid := groups[index]
    if gid == first || gid == second then
      handleLoop c states first second newGroup newBary inserted index (groups.eraseIdxIfInBounds index) arena
    else if !inserted && groupBaryD c arena states gid > newBary then
      handleLoop c states first second newGroup newBary true index (groups.insertIdxIfInBounds index newGroup) arena
    else
      let og := if h2 : gid < arena.size then arena[gid].outgoingConstraints else #[]
      let i1 := indexOfFrom og first 0
      if !og.isEmpty && (i1 < og.size || og.contains second) then
        -- `removeGroup` of both merged groups: the list is taken out of the group first
        let arena := arena.modifyIn gid fun x => { x with outgoingConstraints := #[] }
        let og1 := if i1 < og.size then og.eraseIdxIfInBounds i1 else og
        let i2 := indexOfFrom og1 second 0
        let og2 := if i2 < og1.size then og1.eraseIdxIfInBounds i2 else og1
        let arena := arena.modifyIn gid fun x => { x with outgoingConstraints := og2.push newGroup }
        let arena := arena.modifyIn newGroup fun x => { x with incomingConstraintsCount := x.incomingConstraintsCount + 1 }
        handleLoop c states first second newGroup newBary inserted (index + 1) groups arena
      else handleLoop c states first second newGroup newBary inserted (index + 1) groups arena
  else ((if inserted then groups else groups.push newGroup), arena)

/-! ### `process_constraints` -/

/-- The tables of one `process_constraints` call. -/
structure Tables where
  arena : Arena
  states : States
  table : Table
  deriving Inhabited

/-- The violation loop of `process_constraints_internal`. -/
partial def resolveLoop (c : ForsterCtx) (groups : Array Nat) (arena : Arena) (states : States) :
    Array Nat × Arena × States :=
  let f := findViolatedConstraint c states groups arena
  if f.found then
    let m := mergeGroups c f.first f.second f.arena states
    let newBary := groupBaryD c m.arena m.states m.newGroup
    let (groups, arena) := handleLoop c m.states f.first f.second m.newGroup newBary false 0 groups m.arena
    resolveLoop c groups arena m.states
  else (groups, f.arena, states)

/-- The `group_of` of the nodes `nodes[i:]` pushed onto `out` (`none` when one is missing). -/
partial def groupsOf (c : ForsterCtx) (table : Table) (nodes : Array LNodeId) (i : Nat) (out : Array Nat) :
    Option (Array Nat) :=
  if h : i < nodes.size then
    let g := groupIdx c table nodes[i]
    if g == 0 then none else groupsOf c table nodes (i + 1) (out.push (g - 1))
  else some out

/-- The result loop of `process_constraints_internal`: the groups' nodes in order; the barycenter of
a multi-node group is written to its nodes. -/
partial def collectResult (c : ForsterCtx) (groups : Array Nat) (i : Nat) (arena : Arena) (out : Array LNodeId)
    (states : States) : Array LNodeId × States :=
  if h : i < groups.size then
    let gid := groups[i]
    let groupNodes := if h2 : gid < arena.size then arena[gid].nodes else #[]
    if h3 : groupNodes.size = 1 then
      collectResult c groups (i + 1) arena (out.push groupNodes[0]) states
    else
      let known := groupBaryKnown c arena states gid
      let value := groupBaryD c arena states gid
      collectResult c groups (i + 1) arena (out ++ groupNodes) (setNodesBary c groupNodes 0 known value states)
  else (out, states)

/-- `process_constraints_internal(nodes, only_between_normal_nodes)`: the result (`none` after a
missing constraint group) and the tables. -/
def processConstraintsInternal (c : ForsterCtx) (units : Std.HashMap LNodeId (Array LNodeId)) (nodes : Array LNodeId)
    (onlyNormal : Bool) (t : Tables) : Option (Array LNodeId) × Tables :=
  match t with
  | ⟨arena, states, table⟩ =>
    match groupsOf c table nodes 0 (Array.emptyWithCapacity nodes.size) with
    | none => (none, ⟨arena, states, table⟩)
    | some groups =>
      let b := buildConstraintsGraph c table units groups onlyNormal arena
      if !b.ok then (none, ⟨b.arena, states, table⟩)
      else
        let (groups, arena, states) := resolveLoop c groups b.arena states
        let (result, states) := collectResult c groups 0 arena (Array.emptyWithCapacity nodes.size) states
        (some result, ⟨arena, states, table⟩)

/-- `init_node_level(node, false)` for the nodes `nodes[i:]`: a fresh single-node group each. -/
partial def reinitNodes (c : ForsterCtx) (nodes : Array LNodeId) (i : Nat) (arena : Arena) (table : Table) : Arena × Table :=
  if h : i < nodes.size then
    let node := nodes[i]
    let li := c.layerIndex node
    let ni := c.nodeId node
    if li < table.size then
      let gid := arena.size
      reinitNodes c nodes (i + 1) (arena.push (ConstraintGroup.new node))
        (table.modify li fun l => (growTo l (ni + 1) none).setIfInBounds ni (some gid))
    else reinitNodes c nodes (i + 1) arena table
  else (arena, table)

/-- `process_constraints(nodes)` (see `ForsterM.processConstraints`). -/
def processConstraints (c : ForsterCtx) (units : Std.HashMap LNodeId (Array LNodeId)) (constraintsBetweenNonDummies : Bool)
    (nodes : Array LNodeId) (t : Tables) : Option (Array LNodeId) × Tables :=
  if constraintsBetweenNonDummies then
    match processConstraintsInternal c units nodes true t with
    | (none, t) => (none, t)
    | (some nodes, ⟨arena, states, table⟩) =>
      let (arena, table) := reinitNodes c nodes 0 arena table
      processConstraintsInternal c units nodes false ⟨arena, states, table⟩
  else processConstraintsInternal c units nodes false t

end ForsterFast

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
between them (`init_node_level(node, false)`), as in Rust. The passes run in `ForsterFast` (the
same reads and writes as `ForsterM.processConstraints`; the state is written back before a missing
constraint group is rethrown, like `runM`). -/
def processConstraints (r : ForsterConstraintResolver) (nodes : Array LNodeId) : LayeredM (Array LNodeId) := do
  let c : ForsterCtx := { arena := ← get, snapshot := ← r.snapshot.get }
  let units ← r.layoutUnits.get
  if unconstrained c (← r.constraintGroups.get) units nodes then
    if r.constraintsBetweenNonDummies then
      r.runM fun c => do
        for node in nodes do
          ForsterM.initNodeLevel c node false
        return nodes
    else return nodes
  else
    let t : ForsterFast.Tables := {
      arena := ← r.constraintGroupArena.swap #[], states := ← r.barycenterStates.swap #[]
      table := ← r.constraintGroups.swap #[] }
    let (result, t) := ForsterFast.processConstraints c units r.constraintsBetweenNonDummies nodes t
    r.constraintGroupArena.set t.arena
    r.barycenterStates.set t.states
    r.constraintGroups.set t.table
    match result with
    | some v => return v
    | none => throw (IO.userError "java.lang.IllegalStateException: constraint group missing")

/-- `process_constraints(nodes)` with the line-by-line port `ForsterM.processConstraints` (the
reference of the differential test). -/
def processConstraintsPort (r : ForsterConstraintResolver) (nodes : Array LNodeId) : LayeredM (Array LNodeId) := do
  let c : ForsterCtx := { arena := ← get, snapshot := ← r.snapshot.get }
  let units ← r.layoutUnits.get
  if unconstrained c (← r.constraintGroups.get) units nodes then
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
  -- `ForsterM.initNodeLevel c node true` (which cannot fail) on the refs directly
  let c : ForsterCtx := { arena := ← get, snapshot := ← r.snapshot.get }
  let li := c.layerIndex node
  let ni := c.nodeId node
  if li < (← r.constraintGroups.get).size then
    let gid ← r.constraintGroupArena.modifyGet fun arena => (arena.size, arena.push (ConstraintGroup.new node))
    r.constraintGroups.modify fun t => t.modify li fun row => (growTo row (ni + 1) none).setIfInBounds ni (some gid)
  if li < (← r.barycenterStates.get).size then
    r.barycenterStates.modify fun t => t.modify li fun row =>
      (growTo row (ni + 1) none).setIfInBounds ni (some (BarycenterState.new node))
  if let some unit := (c.arena.node node).internal.inLayerLayoutUnit then
    r.layoutUnits.modify fun units => units.insert unit ((units.getD unit #[]).push node)

/-- The `IInitializable` implementation (layer and node level). -/
def initializable (r : ForsterConstraintResolver) : Initializable where
  initAtLayerLevel := r.initAtLayerLevel
  initAtNodeLevel := r.initAtNodeLevel
  usesPortLevel := false
  usesEdgeLevel := false

end ForsterConstraintResolver

end Elk.Alg.Layered.P3Order
