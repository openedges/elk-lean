import Elk.Alg.Common.Compaction.OneD.OneDimensionalCompactor
import Elk.Alg.Layered.Graph.Ids
import Elk.Core.Options
import Elk.Core.Util.FloatConst
open Elk.Core.Util.FloatConst
/-!
# `org.eclipse.elk.alg.layered.compaction.components.OneDimensionalComponentsCompaction`

Port of `components/compaction/packing.rs` (elk-rs), which merges the Java classes
`ComponentsToCGraphTransformer` (building the `CGraph` of the components' hull rectangles and
external extensions) and `OneDimensionalComponentsCompaction` (the alternating horizontal /
vertical compaction rounds). The input types `Component` / `ComponentExtension` are the Java
`IComponent` / `IExternalExtension` as produced by `ComponentsCompactor`.

## Dynamic `CGraph` membership

The Rust code adds and removes extension nodes, placeholder nodes and placeholder groups to and
from `c_graph.c_nodes` / `c_graph.c_groups` between the compaction passes (`retain` / `push`), so
the member lists (and thus every iteration order of the compactor) change during the
compaction, while the removed elements keep their state. The `CGraph` of `alg.common` is an
arena whose arrays *are* the member lists. This port therefore keeps all nodes and groups in a
**master** `CGraph` (creation order) plus the current member lists (`Membership`, master ids in
Rust order) and hands the compactor a **projection**: a `CGraph` holding exactly the members in
Rust order, with all ids (`cGroup`, `constraints`, `cNodes`, `incomingConstraints`,
`reference`, `master`) renumbered. Before every membership change the projection is written
back into the master (`Packer.sync`) and afterwards rebuilt (`Packer.rebuild`).

References to non-members are dropped by the projection. In Rust such references (stale
constraints or group references of removed nodes) are never read before the next
`calculate_group_offsets` / constraint recalculation, so this is not observable.

The pointer-keyed Rust maps (`node_locks`, `Spacing.individual`) are master-indexed arrays;
the per-call lock snapshot (`frozen`) is indexed by projection ids.

## Moving the members (fast path)

The master graph is only read right after a `sync`. `rebuild` therefore *moves* the member
elements out of the master (`projectMove`: the master keeps `default` placeholders in their slots,
so the moved elements are unshared and their renumbering updates them in place) and `sync` moves
them back (`writeBackMove`, which takes the projection out of the compactor). Every element read
after a `sync` is the same as with the copying `project` / `writeBack`, which are kept as the
reference (`pack … (fastPath := false)`; differential test
`layered.components.packFastPath`). A membership listing an element twice (never produced by
`pack`) falls back to copying.

The vertical pass of `compactPass` repeats the constraint calculation right after
`changeDirection(UP)`, which has just calculated them from `LEFT`; the calculation is idempotent,
so the fast path skips the repetition (the reference keeps it).
-/

namespace Elk.Alg.Layered.Components.Compaction

open Elk.Graph Elk.Core Elk.Core.Math Elk.Core.Options Elk.Core.Util Elk.Alg.Common.Compaction.OneD
open Elk.Alg.Layered.Graph

/-- `IExternalExtension` (Rust `Extension` of `compaction/mod.rs`): the rectangle reaching
from the component hull to the border of the frame and the placeholder reserving the space of
the external port at the frame border. -/
structure ComponentExtension where
  rectangle : ElkRectangle
  placeholder : ElkRectangle
  side : PortSide
  deriving Inhabited

/-- `IComponent` (Rust `Component` of `compaction/mod.rs`). -/
structure Component where
  /-- Rectangles of the component's rectilinear convex hull. -/
  hull : Array ElkRectangle
  /-- `EXT_PORT_CONNECTIONS` of the component. -/
  sides : EnumSet PortSide
  /-- One extension per external side (in `sides` order). -/
  extensions : Array ComponentExtension
  /-- The edges connecting the component to external port dummies. -/
  externalEdges : Array LEdgeId
  deriving Inhabited

namespace OneDimensionalComponentsCompaction

/-- Rust `MAX_ITERATIONS`. -/
def MAX_ITERATIONS : Nat := 10
/-- Rust `EPSILON`. -/
def EPSILON : Float := 0.0001

/-- Rust `Extension` of `packing.rs` (master ids). -/
structure PackExtension where
  group : CGroupId
  node : CNodeId
  placeholder : CNodeId
  placeholderGroup : CGroupId
  side : PortSide
  deriving Inhabited

/-- The current Rust `c_nodes` / `c_groups` lists, as master ids in Rust order. -/
structure Membership where
  nodes : Array CNodeId := #[]
  groups : Array CGroupId := #[]
  deriving Inhabited

/-- Rust `locks(sides)`: the side-set mapping of Java's `LEFT, RIGHT, UP, DOWN` lock flags
(including the unspecified `NORTH/EAST/SOUTH` combination). -/
def locks (sides : EnumSet PortSide) : Array Bool :=
  let mask := sides.toArray.foldl (fun bits side => bits ||| (match side with
    | .north => 1 | .east => 2 | .south => 4 | .west => 8 | .undefined => 0)) 0
  match mask with
  | 0 | 5 | 10 | 11 | 13 | 14 | 15 => #[true, true, true, true]
  | 1 => #[true, true, true, false]
  | 2 => #[false, true, true, true]
  | 4 => #[true, true, false, true]
  | 8 => #[true, false, true, true]
  | 3 => #[false, true, true, false]
  | 6 => #[false, true, false, true]
  | 12 => #[true, false, false, true]
  | 9 => #[true, false, true, false]
  | _ => #[false, false, false, false]

/-- Rust `direction_index(direction)` (`unreachable!` for `UNDEFINED`, which the callers never
pass). -/
def directionIndex : Direction → Nat
  | .left => 0
  | .right => 1
  | .up => 2
  | .down => 3
  | .undefined => 0

/-- Rust `horizontal(side)`. -/
def horizontal (side : PortSide) : Bool := side == .west || side == .east

/-- The projection of the master graph onto the members (see the module doc). -/
def project (master : CGraph) (m : Membership) : CGraph := Id.run do
  let mut nodeIdx : Array (Option Nat) := Array.replicate master.cNodes.size none
  for i in [0:m.nodes.size] do
    nodeIdx := nodeIdx.set! m.nodes[i]!.idx (some i)
  let mut groupIdx : Array (Option Nat) := Array.replicate master.cGroups.size none
  for i in [0:m.groups.size] do
    groupIdx := groupIdx.set! m.groups[i]!.idx (some i)
  let nodeMap := nodeIdx
  let groupMap := groupIdx
  let rn : CNodeId → Option CNodeId := fun n => ((nodeMap[n.idx]?).bind id).map (⟨·⟩)
  let rg : CGroupId → Option CGroupId := fun g => ((groupMap[g.idx]?).bind id).map (⟨·⟩)
  let cNodes := m.nodes.map fun id =>
    let n := master.cNode id
    { n with cGroup := n.cGroup.bind rg, constraints := n.constraints.filterMap rn }
  let cGroups := m.groups.map fun id =>
    let g := master.cGroup id
    { g with master := g.master.bind rn, cNodes := g.cNodes.filterMap rn,
             incomingConstraints := g.incomingConstraints.filterMap rn, reference := g.reference.bind rn }
  return { master with cNodes, cGroups }

/-- Writes the state of a projection back into the master graph. -/
def writeBack (master : CGraph) (m : Membership) (phase : CGraph) : CGraph := Id.run do
  let bn : CNodeId → CNodeId := fun n => m.nodes[n.idx]?.getD n
  let bg : CGroupId → CGroupId := fun g => m.groups[g.idx]?.getD g
  let mut master := master
  for i in [0:m.nodes.size] do
    let n := phase.cNode ⟨i⟩
    let n := { n with cGroup := n.cGroup.map bg, constraints := n.constraints.map bn }
    master := master.modifyCNode m.nodes[i]! fun _ => n
  for i in [0:m.groups.size] do
    let g := phase.cGroup ⟨i⟩
    let g := { g with master := g.master.map bn, cNodes := g.cNodes.map bn,
                      incomingConstraints := g.incomingConstraints.map bn, reference := g.reference.map bn }
    master := master.modifyCGroup m.groups[i]! fun _ => g
  return master

/-- Takes the element at index `i` out of `a`, leaving `default` in its slot. -/
@[inline] private def takeAt {α : Type} [Inhabited α] (a : Array α) (i : Nat) : α × Array α :=
  if h : i < a.size then (a[i], a.set i default) else (default, a)

/-- Whether `ids` (indices into an arena of `size` elements) contains an index twice or an index
out of range. -/
private def hasDuplicates (ids : Array Nat) (size : Nat) : Bool := Id.run do
  let mut seen : Array Bool := Array.replicate size false
  for i in ids do
    if h : i < seen.size then
      if seen[i] then return true
      seen := seen.set i true
    else return true
  return false

/-- `project` that moves the member elements out of the master (see the module doc): returns the
master with `default` in the members' slots and the projection. -/
def projectMove (master : CGraph) (m : Membership) : CGraph × CGraph := Id.run do
  let mut nodeIdx : Array (Option Nat) := Array.replicate master.cNodes.size none
  for i in [0:m.nodes.size] do
    nodeIdx := nodeIdx.set! m.nodes[i]!.idx (some i)
  let mut groupIdx : Array (Option Nat) := Array.replicate master.cGroups.size none
  for i in [0:m.groups.size] do
    groupIdx := groupIdx.set! m.groups[i]!.idx (some i)
  let nodeMap := nodeIdx
  let groupMap := groupIdx
  let rn : CNodeId → Option CNodeId := fun n => ((nodeMap[n.idx]?).bind id).map (⟨·⟩)
  let rg : CGroupId → Option CGroupId := fun g => ((groupMap[g.idx]?).bind id).map (⟨·⟩)
  match master with
  | ⟨masterNodes, masterGroups, sd, ph, pv⟩ =>
    let mut masterNodes := masterNodes
    let mut cNodes : Array CNode := Array.mkEmpty m.nodes.size
    for id in m.nodes do
      let (n, rest) := takeAt masterNodes id.idx
      masterNodes := rest
      cNodes := cNodes.push { n with cGroup := n.cGroup.bind rg, constraints := n.constraints.filterMap rn }
    let mut masterGroups := masterGroups
    let mut cGroups : Array CGroup := Array.mkEmpty m.groups.size
    for id in m.groups do
      let (g, rest) := takeAt masterGroups id.idx
      masterGroups := rest
      let g := { g with master := g.master.bind rn, cNodes := g.cNodes.filterMap rn,
                        incomingConstraints := g.incomingConstraints.filterMap rn, reference := g.reference.bind rn }
      cGroups := cGroups.push g
    return (⟨masterNodes, masterGroups, sd, ph, pv⟩, ⟨cNodes, cGroups, sd, ph, pv⟩)

/-- `writeBack` that moves the projection's elements back into the master slots of the members
(see the module doc). -/
def writeBackMove (master : CGraph) (m : Membership) (phase : CGraph) : CGraph := Id.run do
  let bn : CNodeId → CNodeId := fun n => m.nodes[n.idx]?.getD n
  let bg : CGroupId → CGroupId := fun g => m.groups[g.idx]?.getD g
  match master, phase with
  | ⟨masterNodes, masterGroups, sd, ph, pv⟩, ⟨phaseNodes, phaseGroups, _, _, _⟩ =>
    let mut masterNodes := masterNodes
    let mut phaseNodes := phaseNodes
    for i in [0:m.nodes.size] do
      let (n, rest) := takeAt phaseNodes i
      phaseNodes := rest
      let n := { n with cGroup := n.cGroup.map bg, constraints := n.constraints.map bn }
      masterNodes := masterNodes.set! m.nodes[i]!.idx n
    let mut masterGroups := masterGroups
    let mut phaseGroups := phaseGroups
    for i in [0:m.groups.size] do
      let (g, rest) := takeAt phaseGroups i
      phaseGroups := rest
      let g := { g with master := g.master.map bn, cNodes := g.cNodes.map bn,
                        incomingConstraints := g.incomingConstraints.map bn, reference := g.reference.map bn }
      masterGroups := masterGroups.set! m.groups[i]!.idx g
    return ⟨masterNodes, masterGroups, sd, ph, pv⟩

/-- Rust `Spacing` (`ISpacingsHandler`): placeholders have the individual spacing `1.0`, all
other nodes the default; the spacing of a pair is the `f64::min` of both. Built per projection
(`isPlaceholder` is master-indexed). -/
def spacingsFor (isPlaceholder : Array Bool) (m : Membership) (default : Float) : SpacingsHandler :=
  .individualMin (m.nodes.foldl (fun acc n => acc.push (if isPlaceholder[n.idx]?.getD false then fl1p0 else default))
    (FloatArray.emptyWithCapacity m.nodes.size)) default

/-- The original `spacingsFor` with closures (reference of the `individualMin` form, differential test
`layered.components.packFastPath`). -/
def spacingsForReference (isPlaceholder : Array Bool) (m : Membership) (default : Float) : SpacingsHandler :=
  let flags := m.nodes.map fun n => isPlaceholder[n.idx]?.getD false
  let sp : CNodeId → Float := fun n => if flags[n.idx]?.getD false then fl1p0 else default
  .mk (fun _ a b => fmin (sp a) (sp b)) (fun _ a b => fmin (sp a) (sp b))

/-- The compaction state: master graph, current membership and the compactor (whose `cGraph`
is the projection of the membership). -/
structure Packer where
  master : CGraph
  members : Membership
  compactor : OneDimensionalCompactor
  isPlaceholder : Array Bool
  /-- Rust `node_locks` (master-indexed). -/
  nodeLocks : Array (Array Bool)
  spacing : Float
  /-- Fast path: `rebuild` / `sync` move the members out of / back into the master instead of
  copying them, and `compactPass` skips the repeated constraint calculation (see the module doc);
  `false` is the reference. -/
  fastPath : Bool := true

namespace Packer

/-- Writes the compactor's projection back into the master graph. -/
def sync (p : Packer) : IO Packer := do
  if p.compactor.cGraph.cNodes.size != p.members.nodes.size ||
      p.compactor.cGraph.cGroups.size != p.members.groups.size then
    throw (IO.userError "java.lang.IllegalStateException: compaction graph membership changed unexpectedly")
  if p.fastPath && !hasDuplicates (p.members.nodes.map (·.idx)) p.master.cNodes.size &&
      !hasDuplicates (p.members.groups.map (·.idx)) p.master.cGroups.size then
    match p with
    | ⟨master, members, compactor, isPlaceholder, nodeLocks, spacing, fastPath⟩ =>
      let phase := compactor.cGraph
      let compactor := { compactor with cGraph := {} }
      return ⟨writeBackMove master members phase, members, compactor, isPlaceholder, nodeLocks, spacing,
        fastPath⟩
  else
    return { p with master := writeBack p.master p.members p.compactor.cGraph }

/-- Hands the compactor the projection of the current membership. -/
def rebuild (p : Packer) : Packer :=
  let handler := (if p.fastPath then spacingsFor else spacingsForReference) p.isPlaceholder p.members p.spacing
  if p.fastPath && !hasDuplicates (p.members.nodes.map (·.idx)) p.master.cNodes.size &&
      !hasDuplicates (p.members.groups.map (·.idx)) p.master.cGroups.size then
    match p with
    | ⟨master, members, compactor, isPlaceholder, nodeLocks, spacing, fastPath⟩ =>
      let (master, g) := projectMove master members
      ⟨master, members, { compactor with cGraph := g, spacingsHandler := handler }, isPlaceholder,
        nodeLocks, spacing, fastPath⟩
  else
    let g := project p.master p.members
    { p with compactor := { p.compactor with cGraph := g, spacingsHandler := handler } }

/-- Rust `remove_node(graph, node)` on the membership. -/
def removeMember (p : Packer) (n : CNodeId) : Packer :=
  { p with members := { p.members with nodes := p.members.nodes.filter (· != n) } }

/-- Rust `c_groups.retain(|g| !Rc::ptr_eq(g, &group))` on the membership. -/
def removeGroupMember (p : Packer) (g : CGroupId) : Packer :=
  { p with members := { p.members with groups := p.members.groups.filter (· != g) } }

end Packer

/-- A group with zero deltas; out of line so that `Array.map` hands it the unshared group (PLAN 7.1
items 16, 59). -/
@[noinline] private def resetGroupDeltas (grp : CGroup) : CGroup := { grp with delta := fl0p0, deltaNormalized := fl0p0 }

/-- Rust `reset_deltas(graph)` on the projection. -/
def resetDeltas (g : CGraph) : CGraph :=
  { g with cGroups := g.cGroups.map resetGroupDeltas }

/-- Sum of `|delta_normalized|` over the groups of the projection (Rust `.map(abs).sum()`). -/
def deltaSum (g : CGraph) : Float :=
  g.cGroups.foldl (fun acc grp => acc + Float.abs grp.deltaNormalized) 0.0

private def addCNodeIO (g : CGraph) (group : CGroupId) (node : CNodeId) : IO CGraph :=
  match CGroup.addCNode g group node with
  | .ok g => pure g
  | .error e => throw (IO.userError e)

/-- One pass of `compact_round` (`isHorizontal` selects the extensions whose placeholders are
added; the others contribute their extension node). Returns the updated packer and the delta
contribution of the pass. -/
def compactPass (p : Packer) (extensions : Array PackExtension) (topLeft : KVector) (align : Bool)
    (isHorizontal : Bool) : IO (Packer × Float) := do
  let mut p ← p.sync
  for ext in extensions do
    if horizontal ext.side == isHorizontal then
      p := { p with members := { nodes := p.members.nodes.push ext.placeholder,
                                 groups := p.members.groups.push ext.placeholderGroup } }
    else
      p := { p with members := { p.members with nodes := p.members.nodes.push ext.node } }
      let master ← addCNodeIO p.master ext.group ext.node
      p := { p with master }
  p := p.rebuild
  let mut c := p.compactor.calculateGroupOffsets
  let mut delta := fl0p0
  if isHorizontal then
    c ← c.forceConstraintsRecalculation
  else
    delta := delta + deltaSum c.cGraph
    c := { c with cGraph := resetDeltas c.cGraph }
  let forward : Direction := if isHorizontal then .left else .up
  let backward : Direction := if isHorizontal then .right else .down
  let before := c.direction
  c ← c.changeDirection forward
  -- Rust recalculates the constraints right after `change_direction(UP)`. Coming from `LEFT`,
  -- `RIGHT` or `UNDEFINED`, `changeDirection` has just calculated them on the same state, and the
  -- calculation is idempotent (it clears and rebuilds the constraints, ids and group degrees from
  -- hitboxes and groups it does not change), so the repetition is skipped.
  let recalculated := match before with
    | .left | .right | .undefined => true
    | .up | .down => false
  if !isHorizontal && !(p.fastPath && recalculated) then
    c ← c.forceConstraintsRecalculation
  c ← (c.setLockFunction none).compact
  for direction in #[backward, forward] do
    c ← c.changeDirection direction
    -- Snapshot the Java reposition flags before the solver consumes degrees.
    let g := c.cGraph
    let frozen : Array Bool := g.cNodeIds.map fun n =>
      let reposition :=
        if align then
          let masterId := p.members.nodes[n.idx]?.getD n
          match p.nodeLocks[masterId.idx]? with
          | some flags => flags[directionIndex direction]?.getD false
          | none => false
        else
          match (g.cNode n).cGroup with
          | some grp => (g.cGroup grp).outDegree != 0
          | none => false
      !reposition
    let lock : LockFunction :=
      if p.fastPath then .flags frozen else .fn fun _ n _ => frozen[n.idx]?.getD false
    c ← (c.setLockFunction (some lock)).compact
  c ← (c.setLockFunction none).changeDirection .left
  p := { p with compactor := c }
  p ← p.sync
  for ext in extensions do
    if horizontal ext.side == isHorizontal then
      p := (p.removeMember ext.placeholder).removeGroupMember ext.placeholderGroup
    else
      p := p.removeMember ext.node
      p := { p with master := (CGroup.removeCNode p.master ext.group ext.node).1 }
  for ext in extensions do
    let movement := (p.master.cGroup ext.group).deltaNormalized
    if horizontal ext.side == isHorizontal then
      p := { p with master := p.master.modifyCNode ext.node fun n =>
        let rect := n.hitbox
        let rect := match ext.side with
          | .west => { rect with x := topLeft.x, width := fmax (rect.width + movement) fl1p0 }
          | .east => { rect with x := rect.x + movement, width := fmax (rect.width - movement) fl1p0 }
          | .north => { rect with y := topLeft.y, height := fmax (rect.height + movement) fl1p0 }
          | .south => { rect with y := rect.y + movement, height := fmax (rect.height - movement) fl1p0 }
          | .undefined => rect
        { n with hitbox := rect } }
    else
      p := { p with master := p.master.modifyCNode ext.placeholder fun n =>
        if isHorizontal then { n with hitbox := { n.hitbox with x := n.hitbox.x + movement } }
        else { n with hitbox := { n.hitbox with y := n.hitbox.y + movement } } }
  return (p.rebuild, delta)

/-- Rust `compact_round(compactor, extensions, top_left, node_locks, align)`: a horizontal and a
vertical pass; returns the summed normalized group movement. -/
def compactRound (p : Packer) (extensions : Array PackExtension) (topLeft : KVector) (align : Bool) :
    IO (Packer × Float) := do
  let mut p := { p with compactor := { p.compactor with cGraph := resetDeltas p.compactor.cGraph } }
  let mut delta := 0.0
  for isHorizontal in #[true, false] do
    let (p', d) ← compactPass p extensions topLeft align isHorizontal
    p := p'
    delta := delta + d
  let c ← p.compactor.forceConstraintsRecalculation
  p := { p with compactor := c }
  delta := delta + deltaSum c.cGraph
  return (p, delta)

/-- Rust `pack(components, spacing)`: compacts the components and returns the offset of every
component (input order) and the size of the compacted drawing. `fastPath := false` selects the
reference behaviour (copying projection, repeated constraint calculation; see the module doc). -/
def pack (components : Array Component) (spacing : Float) (fastPath : Bool := true) :
    IO (Array KVector × KVector) := do
  let mut graph := CGraph.allDirections
  let mut references : Array (CNodeId × ElkRectangle) := #[]
  let mut extensions : Array PackExtension := #[]
  let mut lockList : Array (CNodeId × Array Bool) := #[]
  let mut placeholders : Array CNodeId := #[]
  for component in components do
    let mut hullNodes : Array CNodeId := #[]
    for rect in component.hull do
      let (g, n) := CNode.create graph rect
      graph := g
      hullNodes := hullNodes.push n
    let some reference := hullNodes[0]?
      | throw (IO.userError "java.lang.IllegalStateException: a component has a hull")
    references := references.push (reference, (graph.cNode reference).hitbox)
    let (g, group) ← CGroup.createIO graph hullNodes
    graph := g
    let flags := locks component.sides
    for n in hullNodes do lockList := lockList.push (n, flags)
    for extension in component.extensions do
      let (g, node) := CNode.create graph extension.rectangle
      graph ← addCNodeIO g group node
      lockList := lockList.push (node, flags)
      let (g, placeholder) := CNode.create graph extension.placeholder
      lockList := lockList.push (placeholder, flags)
      let (g, placeholderGroup) ← CGroup.createIO g #[placeholder]
      graph := g
      placeholders := placeholders.push placeholder
      extensions := extensions.push { group, node, placeholder, placeholderGroup, side := extension.side }
  let mut nodeLocks : Array (Array Bool) := Array.replicate graph.cNodes.size #[]
  for (n, flags) in lockList do nodeLocks := nodeLocks.set! n.idx flags
  let mut isPlaceholder : Array Bool := Array.replicate graph.cNodes.size false
  for n in placeholders do isPlaceholder := isPlaceholder.set! n.idx true
  let placeholderGroups := extensions.map (·.placeholderGroup)
  -- Placeholders are added only while compacting in their associated direction.
  let members : Membership :=
    { nodes := graph.cNodeIds.filter (fun n => !(isPlaceholder[n.idx]?.getD false)),
      groups := graph.cGroupIds.filter (fun g => !placeholderGroups.contains g) }
  let mut topLeft : KVector := ⟨Float.posInf, Float.posInf⟩
  for n in members.nodes do
    let rect := (graph.cNode n).hitbox
    topLeft := ⟨fmin topLeft.x rect.x, fmin topLeft.y rect.y⟩
  let compactor := (OneDimensionalCompactor.new (project graph members)).setSpacingsHandler
    ((if fastPath then spacingsFor else spacingsForReference) isPlaceholder members spacing)
  let mut p : Packer :=
    { master := graph, members, compactor, isPlaceholder, nodeLocks, spacing, fastPath }
  p ← p.sync
  for extension in extensions do
    p := p.removeMember extension.node
    p := { p with master := (CGroup.removeCNode p.master extension.group extension.node).1 }
  p := p.rebuild
  for run in [0:MAX_ITERATIONS] do
    let (p', delta) ← compactRound p extensions topLeft false
    p := p'
    if run >= 1 && delta <= EPSILON then break
  let (p', _) ← compactRound p extensions topLeft true
  p := p'
  let c ← p.compactor.finish
  p := { p with compactor := c }
  p ← p.sync
  let mut minV : KVector := ⟨Float.posInf, Float.posInf⟩
  let mut maxV : KVector := ⟨Float.negInf, Float.negInf⟩
  for n in p.members.nodes ++ extensions.map (·.placeholder) do
    let rect := (p.master.cNode n).hitbox
    minV := ⟨fmin minV.x rect.x, fmin minV.y rect.y⟩
    maxV := ⟨fmax maxV.x (rect.x + rect.width), fmax maxV.y (rect.y + rect.height)⟩
  let offsets := references.map fun (reference, old) =>
    let rect := (p.master.cNode reference).hitbox
    (⟨rect.x - old.x - minV.x, rect.y - old.y - minV.y⟩ : KVector)
  let size : KVector := ⟨maxV.x - minV.x, maxV.y - minV.y⟩
  if !(size.x.isFinite && size.y.isFinite) then
    throw (IO.userError "java.lang.IllegalStateException: non-finite component compaction")
  return (offsets, size)

end OneDimensionalComponentsCompaction

end Elk.Alg.Layered.Components.Compaction
