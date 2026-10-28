import Elk.Alg.Layered.P4Nodes.BK.ThresholdStrategy
import Elk.Alg.Layered.P4Nodes.BK.ICompactor
import Std.Data.HashMap
/-!
# `org.eclipse.elk.alg.layered.p4nodes.bk.BKCompactor` (elk-rs `compactor.rs`)

Horizontal compaction of the Brandes & Köpf node placer: blocks are placed recursively (each
block after the block of its neighbor in the iteration direction), blocks of different classes
are connected by class edges with the required separation, the classes are placed by a
topological sweep, and the threshold strategy finally tries to straighten further edges.
For documentation see `BKNodePlacer`.

Order notes (Rust is followed where it differs from Java):
* the class graph (`sinkNodes`) is keyed by the sink's local id; class nodes are created in
  `sinkOrder` (first `addClassEdge` touching them), and `placeClasses` seeds its FIFO queue with
  the class nodes of in-degree 0 **in `sinkOrder`** (Java iterates a `HashMap`) and writes the
  shifts back in `sinkOrder` (only defined class shifts are written);
* `f64::min`/`f64::max` (`fmin`/`fmax`) instead of `Math.min`/`Math.max`.

Not ported: the `ELK_BK_REVERSE_SINK_QUEUE` debug switch of elk-rs (reverses the seed order).

The compactor state is the outermost `StateRefT` layer of `CompactM`, over the threshold strategy
(`ThresholdM`) and the layout (`BalM`).
-/
/-! Float literals as global constants (FL): inside branches, loops and specialised code the compiler
shares a literal's `Nat`/`Bool` arguments with unrelated variables (CSE) and then parses it on every
evaluation (`FastFloat.ofScientificImpl`); a top-level constant is a load (PLAN §7.1 items 17, 22). -/
private def fl0p0 : Float := 0.0

namespace Elk.Alg.Layered.P4Nodes.BK

open Elk.Graph Elk.Core.Math Elk.Core.Util Elk.Alg.Layered.Graph Elk.Alg.Layered.Options

/-- `BKCompactor.ClassEdge`: an edge of the class graph with the required separation between
the connected classes. -/
structure ClassEdge where
  /-- `target` (sink id of the target class). -/
  target : Nat
  /-- `separation`. -/
  separation : Float
  deriving Inhabited

/-- `BKCompactor.ClassNode`: a node of the class graph. -/
structure ClassNode where
  /-- `classShift` (`null` until placed). -/
  classShift : Option Float := none
  /-- `outgoing`. -/
  outgoing : Array ClassEdge := #[]
  /-- `indegree`. -/
  indegree : Nat := 0
  deriving Inhabited

/-- `BKCompactor`. -/
structure BKCompactor where
  /-- `spacingNodeNode` (`LayeredOptions.SPACING_NODE_NODE` of the graph). -/
  spacingNodeNode : Float
  /-- The threshold strategy chosen by `NODE_PLACEMENT_BK_EDGE_STRAIGHTENING`. -/
  thresholdKind : ThresholdStrategyKind
  /-- `sinkNodes`: the class graph, keyed by sink id. -/
  sinkNodes : Std.HashMap Nat ClassNode := {}
  /-- `sink_order` (Rust): creation order of the class nodes. -/
  sinkOrder : Array Nat := #[]
  deriving Inhabited

/-- Compaction computations: compactor state over the threshold strategy and the layout. -/
abbrev CompactM := StateRefT BKCompactor ThresholdM

namespace BKCompactor

/-- `new BKCompactor(layeredGraph, ni)`: reads `SPACING_NODE_NODE` and chooses the
`SimpleThresholdStrategy` for `IMPROVE_STRAIGHTNESS`, else the `NullThresholdStrategy`.
Throws when the graph has no `SPACINGS` (Rust panics). -/
def new (graph : LGraph) : IO BKCompactor := do
  if graph.internal.spacings.isNone then
    throw (IO.userError "java.lang.IllegalStateException: Missing spacings configuration for BK compactor")
  let spacingNodeNode := (graph.props.get LayeredOptions.SPACING_NODE_NODE).getD 0.0
  let edgeStraightening := (graph.props.get LayeredOptions.NODE_PLACEMENT_BK_EDGE_STRAIGHTENING).getD .improveStraightness
  let thresholdKind := match edgeStraightening with
    | .improveStraightness => ThresholdStrategyKind.simple
    | .none => ThresholdStrategyKind.null
  return { spacingNodeNode, thresholdKind }

/-- The neighbor of `node` (in-layer index `index`) in the compaction direction: the next node
for `UP`, the previous one for `DOWN`. -/
private def neighborInLayer (ctx : BKContext) (vdir : VDirection) (node : LNodeId) (index : Nat) : Option LNodeId := do
  let l ← (ctx.arena.node node).layer
  let nodes := (ctx.arena.layer l).nodes
  match vdir with
  | .up => if index + 1 < nodes.size then nodes[index + 1]? else none
  | .down => if index > 0 then nodes[index - 1]? else none

/-- The new position of the block of `root` that keeps `current` clear of `neighbor` (same
class): `UP` places `current` above the neighbor, `DOWN` below it. -/
private def sameClassPosition (ctx : BKContext) (bal : BKAlignedLayout) (vdir : VDirection) (current : Nat)
    (neighbor : LNodeId) (neighborId neighborRoot : Nat) (spacing : Float) : Float :=
  let currentNode := ctx.nodeOf current
  match vdir with
  | .up =>
    bal.yOf neighborRoot + bal.innerShiftOf neighborId - ctx.marginTop neighbor - spacing
      - ctx.marginBottom currentNode - ctx.sizeY currentNode - bal.innerShiftOf current
  | .down =>
    bal.yOf neighborRoot + bal.innerShiftOf neighborId + ctx.sizeY neighbor + ctx.marginBottom neighbor
      + spacing + ctx.marginTop currentNode - bal.innerShiftOf current

/-- The separation required between the class of `root` and the class of `neighbor`
(`requiredSpace`, with `SPACING_NODE_NODE`). -/
private def requiredClassSpace (ctx : BKContext) (bal : BKAlignedLayout) (vdir : VDirection) (rootId current : Nat)
    (neighbor : LNodeId) (neighborId neighborRoot : Nat) (spacingNodeNode : Float) : Float :=
  let currentNode := ctx.nodeOf current
  match vdir with
  | .up =>
    bal.yOf rootId + bal.innerShiftOf current + ctx.sizeY currentNode + ctx.marginBottom currentNode
      + spacingNodeNode - (bal.yOf neighborRoot + bal.innerShiftOf neighborId - ctx.marginTop neighbor)
  | .down =>
    bal.yOf rootId + bal.innerShiftOf current - ctx.marginTop currentNode - bal.yOf neighborRoot
      - bal.innerShiftOf neighborId - ctx.sizeY neighbor - ctx.marginBottom neighbor - spacingNodeNode

/-- `getOrCreateClassNode` + `ClassNode.addEdge`: adds a class edge `source → target` (class nodes
are created on first use and appended to `sinkOrder`). -/
private def addClassEdge (sourceId targetId : Nat) (separation : Float) : CompactM Unit :=
  modifyThe BKCompactor fun c => Id.run do
    let mut c := c
    if !c.sinkNodes.contains sourceId then
      c := { c with sinkNodes := c.sinkNodes.insert sourceId {}, sinkOrder := c.sinkOrder.push sourceId }
    if !c.sinkNodes.contains targetId then
      c := { c with sinkNodes := c.sinkNodes.insert targetId {}, sinkOrder := c.sinkOrder.push targetId }
    c := { c with sinkNodes := c.sinkNodes.modify targetId fun t => { t with indegree := t.indegree + 1 } }
    c := { c with sinkNodes := c.sinkNodes.modify sourceId fun s =>
      { s with outgoing := s.outgoing.push { target := targetId, separation } } }
    return c

/-- Trace line of `place_block` for a same-class `DOWN` placement (`ELK_TRACE_BK_PLACE_BLOCK`). -/
private def traceDown (ctx : BKContext) (bal : BKAlignedLayout) (rootId current : Nat) (neighbor : LNodeId)
    (neighborId neighborRoot : Nat) (newPosition thresh updated spacing : Float) : IO Unit := do
  let currentNode := ctx.nodeOf current
  IO.eprintln (s!"bk-place-block: root={rootId} current={current}({ctx.designation currentNode}) " ++
    s!"neighbor_id={neighborId}({ctx.designation neighbor}) neighbor_root={neighborRoot} new={fmt3 newPosition} " ++
    s!"thresh={fmt3 thresh} updated={fmt3 updated} spacing={fmt3 spacing} down comp=(y_nr={fmt3 (bal.yOf neighborRoot)}," ++
    s!"inner_n={fmt3 (bal.innerShiftOf neighborId)},size_n={fmt3 (ctx.sizeY neighbor)}," ++
    s!"mb_n={fmt3 (ctx.marginBottom neighbor)},mt_c={fmt3 (ctx.marginTop currentNode)}," ++
    s!"inner_c={fmt3 (bal.innerShiftOf current)})")

/-- The same-class branch of `placeBlock`: moves the block of `root` such that `current` keeps
the vertical spacing to `neighbor` (bounded by the threshold). Returns the new
`isInitialAssignment` flag. -/
private def placeSameClass (ctx : BKContext) (vdir : VDirection) (rootId current : Nat) (neighbor : LNodeId)
    (neighborId neighborRoot : Nat) (thresh : Float) (isInitialAssignment : Bool) : CompactM Bool := do
  let tracePB := ElkTrace.global.bkPlaceBlock
  let bal ← getThe BKAlignedLayout
  if tracePB then
    IO.eprintln s!"bk-place-block: root={rootId} same-class neighbor_root={neighborRoot} sink={bal.sinkOf rootId}"
  let spacing ← ctx.verticalSpacing (ctx.nodeOf current) neighbor
  let newPosition := sameClassPosition ctx bal vdir current neighbor neighborId neighborRoot spacing
  let currentPosition := bal.yOf rootId
  let updated := match vdir with
    | .up => if isInitialAssignment then fmin newPosition thresh else fmin currentPosition (fmin newPosition thresh)
    | .down => if isInitialAssignment then fmax newPosition thresh else fmax currentPosition (fmax newPosition thresh)
  if tracePB then
    match vdir with
    | .up =>
      IO.eprintln s!"bk-place-block: root={rootId} current={current} neighbor_root={neighborRoot} new={fmt3 newPosition} thresh={fmt3 thresh} updated={fmt3 updated} spacing={fmt3 spacing} up"
    | .down => traceDown ctx bal rootId current neighbor neighborId neighborRoot newPosition thresh updated spacing
  modifyThe BKAlignedLayout (·.setY rootId updated)
  return false

/-- The different-class branch of `placeBlock`: records the separation required between the
two classes as a class edge. -/
private def placeOtherClass (ctx : BKContext) (vdir : VDirection) (rootId current : Nat) (neighbor : LNodeId)
    (neighborId neighborRoot : Nat) : CompactM Unit := do
  let tracePB := ElkTrace.global.bkPlaceBlock
  let spacingNodeNode := (← getThe BKCompactor).spacingNodeNode
  let bal ← getThe BKAlignedLayout
  let sinkId := bal.sinkOf rootId
  let neighborSinkId := bal.sinkOf neighborRoot
  if tracePB then
    IO.eprintln s!"bk-place-block: root={rootId} different-class sink={sinkId} neighbor_root={neighborRoot} neighbor_sink={neighborSinkId}"
  let requiredSpace := requiredClassSpace ctx bal vdir rootId current neighbor neighborId neighborRoot spacingNodeNode
  addClassEdge sinkId neighborSinkId requiredSpace
  if tracePB then
    let dir := if vdir == .up then "up" else "down"
    IO.eprintln s!"bk-place-block: class-edge root={rootId} sink={sinkId} neighbor_root={neighborRoot} neighbor_sink={neighborSinkId} required={fmt3 requiredSpace} {dir}"

mutual

/-- `placeBlock(root)`: places the block of `root` (if not placed yet) by going through all its
nodes (the `align` ring, bounded by `max(align.len(), 1)` steps like Rust); before each node's
neighbor in the compaction direction is considered, the neighbor's block is placed
(recursively). Blocks of the same class are moved as far as necessary to keep the vertical
spacing; for blocks of different classes a class edge is recorded. -/
partial def placeBlock (ctx : BKContext) (ni : NeighborhoodInformation) (rootId : Nat) : CompactM Unit := do
  let tracePB := ElkTrace.global.bkPlaceBlock
  if (← getThe BKAlignedLayout).isYDefined rootId then return
  let some vdir := (← getThe BKAlignedLayout).vdir
    | throw (IO.userError "java.lang.IllegalStateException: BK compactor requires a vertical direction")
  modifyThe BKAlignedLayout (·.setY rootId fl0p0)
  if tracePB then
    IO.eprintln s!"bk-place-block: start root={rootId} vdir={if vdir == .up then "Up" else "Down"}"
  let thresh := if vdir == .down then Float.negInf else Float.posInf
  let maxSteps := max (← getThe BKAlignedLayout).size 1
  placeBlockSteps ctx ni vdir rootId maxSteps rootId thresh true 0
  if tracePB then
    IO.eprintln s!"bk-place-block: done root={rootId} final_y={fmt3 ((← getThe BKAlignedLayout).yOf rootId)}"
  ThresholdStrategy.finishBlock rootId

/-- The loop of `placeBlock` over the block ring of `rootId` from `current` (`steps` taken so far,
bounded by `maxSteps` like Rust), tail recursive so that the threshold and the flags stay
unboxed. -/
partial def placeBlockSteps (ctx : BKContext) (ni : NeighborhoodInformation) (vdir : VDirection) (rootId maxSteps : Nat)
    (current : Nat) (thresh : Float) (isInitialAssignment : Bool) (steps : Nat) : CompactM Unit := do
  let currentNode := ctx.nodeOf current
  match neighborInLayer ctx vdir currentNode (ni.nodeIndexOf current) with
  | some neighbor =>
    let neighborId := ctx.nodeId neighbor
    let neighborRoot := (← getThe BKAlignedLayout).rootOf neighborId
    placeBlock ctx ni neighborRoot
    let thresh ← ThresholdStrategy.calculateThreshold ctx thresh rootId current
    if (← getThe BKAlignedLayout).sinkOf rootId == rootId then
      modifyThe BKAlignedLayout fun b => { b with sink := b.sink.set! rootId (b.sinkOf neighborRoot) }
      if ElkTrace.global.bkPlaceBlock then
        IO.eprintln s!"bk-place-block: root={rootId} adopt-sink from neighbor_root={neighborRoot} sink={(← getThe BKAlignedLayout).sinkOf rootId}"
    let sameClass := (← getThe BKAlignedLayout) |> fun b => b.sinkOf rootId == b.sinkOf neighborRoot
    if sameClass then
      let isInitialAssignment ←
        placeSameClass ctx vdir rootId current neighbor neighborId neighborRoot thresh isInitialAssignment
      placeBlockNext ctx ni vdir rootId maxSteps current thresh isInitialAssignment steps
    else
      placeOtherClass ctx vdir rootId current neighbor neighborId neighborRoot
      placeBlockNext ctx ni vdir rootId maxSteps current thresh isInitialAssignment steps
  | none =>
    let thresh ← ThresholdStrategy.calculateThreshold ctx thresh rootId current
    placeBlockNext ctx ni vdir rootId maxSteps current thresh isInitialAssignment steps

/-- The end of one `placeBlockSteps` step: moves to the next node of the block ring and stops at
the root (or after `maxSteps` steps). -/
partial def placeBlockNext (ctx : BKContext) (ni : NeighborhoodInformation) (vdir : VDirection) (rootId maxSteps : Nat)
    (current : Nat) (thresh : Float) (isInitialAssignment : Bool) (steps : Nat) : CompactM Unit := do
  let current := (← getThe BKAlignedLayout).alignOf current
  if current == rootId || steps ≥ maxSteps then
    if steps ≥ maxSteps && ElkTrace.global.bkGuard then
      IO.eprintln s!"bk-guard: place_block loop hit max_steps root_id={rootId} current={current} max_steps={maxSteps}"
    return
  placeBlockSteps ctx ni vdir rootId maxSteps current thresh isInitialAssignment (steps + 1)

end

/-- The topological sweep of `placeClasses` over the class graph: FIFO queue seeded with the
class nodes of in-degree 0 in `sinkOrder`; each class gets the minimal (`DOWN`) / maximal (`UP`)
shift over its incoming class edges. -/
private def sweepClasses (vdir : VDirection) (sinkNodes : Std.HashMap Nat ClassNode) (sinkOrder : Array Nat) :
    Std.HashMap Nat ClassNode := Id.run do
  let mut nodes := sinkNodes
  let mut queue : Array Nat := sinkOrder.filter fun id => (nodes.get? id).any (·.indegree == 0)
  let mut head := 0
  while head < queue.size do
    let nodeId := queue[head]!
    head := head + 1
    let some node := nodes.get? nodeId | continue
    let classShift := node.classShift.getD fl0p0
    if node.classShift.isNone then
      nodes := nodes.insert nodeId { node with classShift := some fl0p0 }
    for edge in node.outgoing do
      if let some target := nodes.get? edge.target then
        let candidate := classShift + edge.separation
        let shift := match target.classShift with
          | none => candidate
          | some s => if vdir == .down then fmin s candidate else fmax s candidate
        let indegree := if target.indegree > 0 then target.indegree - 1 else target.indegree
        nodes := nodes.insert edge.target { target with classShift := some shift, indegree }
        if indegree == 0 then queue := queue.push edge.target
  return nodes

/-- `placeClasses(bal)`: places the classes and stores each class shift at its sink
(`bal.shift`). -/
private def placeClasses (vdir : VDirection) : CompactM Unit := do
  -- take the class graph out of the state so that the sweep updates it in place
  let (sinkNodes, order) ← modifyGetThe BKCompactor fun c => ((c.sinkNodes, c.sinkOrder), { c with sinkNodes := {} })
  if ElkTrace.global.bkClasses then
    for id in order do
      if let some node := sinkNodes.get? id then
        IO.eprintln s!"bk-classes: sink={id} indegree={node.indegree} outgoing={node.outgoing.size}"
  let nodes := sweepClasses vdir sinkNodes order
  modifyThe BKCompactor fun c => { c with sinkNodes := nodes }
  modifyThe BKAlignedLayout fun b => Id.run do
    let mut b := b
    for id in order do
      if let some shift := (nodes.get? id).bind (·.classShift) then
        b := { b with shift := b.shift.set! id shift }
    return b

/-- `apply_final_coordinates`: every node gets the y coordinate of its root; roots are
additionally moved by their class shift (if finite in the compaction direction). Nodes are
visited in layer order, so the root of a block (in the first visited layer of the block) is
moved before its other nodes copy its position. -/
private def applyFinalCoordinates (ctx : BKContext) (vdir : VDirection) (nodes : Array LNodeId)
    (bal : BKAlignedLayout) : BKAlignedLayout :=
  -- the y arrays are taken out of the layout and updated in place by an unboxed loop
  let y := bal.y
  let yDefined := bal.yDefined
  let bal := { bal with y := FloatArray.empty, yDefined := #[] }
  let isUp := match vdir with | .up => true | .down => false
  let (y, yDefined) := go bal isUp 0 y yDefined
  { bal with y, yDefined }
where
  /-- Node `i` of `nodes`; `y`/`yDefined` are the layout's arrays (`yOf`/`setY` on them). -/
  go (bal : BKAlignedLayout) (isUp : Bool) (i : Nat) (y : FloatArray) (yDefined : Array Bool) :
      FloatArray × Array Bool :=
    if h : i < nodes.size then
      let idx := ctx.nodeId nodes[i]
      let rootId := bal.rootOf idx
      let rootY := if yDefined.getD rootId false then y.get! rootId else fl0p0
      let y := y.set! idx rootY
      let yDefined := yDefined.set! idx true
      if idx == rootId then
        let sinkShift := bal.shiftOf (bal.sinkOf idx)
        if (isUp && sinkShift > Float.negInf) || (!isUp && sinkShift < Float.posInf) then
          go bal isUp (i + 1) (y.set! idx (rootY + sinkShift)) yDefined
        else go bal isUp (i + 1) y yDefined
      else go bal isUp (i + 1) y yDefined
    else (y, yDefined)
  termination_by nodes.size - i

/-- `horizontalCompaction(bal)`: resets sinks and shifts, places all blocks (layers reversed
for `LEFT`, nodes of a layer reversed for `UP`; only roots start a placement), places the
classes, computes the final coordinates (same layer order, nodes in layer order) and lets the
threshold strategy post-process the layout. -/
def horizontalCompaction (ctx : BKContext) (ni : NeighborhoodInformation) : CompactM Unit := do
  let some vdir := (← getThe BKAlignedLayout).vdir
    | throw (IO.userError "java.lang.IllegalStateException: BK compactor requires a vertical direction")
  let some hdir := (← getThe BKAlignedLayout).hdir
    | throw (IO.userError "java.lang.IllegalStateException: BK compactor requires a horizontal direction")
  let shiftInit := if vdir == .up then Float.negInf else Float.posInf
  modifyThe BKAlignedLayout fun b => Id.run do
    let mut b := b
    for id in [0:b.sink.size] do
      b := { b with sink := b.sink.set! id id, shift := b.shift.set! id shiftInit }
    return b
  modifyThe BKCompactor fun c => { c with sinkNodes := {}, sinkOrder := #[] }
  let layers := if hdir == .left then ctx.layers.reverse else ctx.layers
  ThresholdStrategy.init
  modifyThe BKAlignedLayout fun b => { b with yDefined := Array.replicate b.yDefined.size false }
  for l in layers do
    let mut nodes := (ctx.arena.layer l).nodes
    if vdir == .up then nodes := nodes.reverse
    for n in nodes do
      let id := ctx.nodeId n
      if (← getThe BKAlignedLayout).rootOf id == id then
        placeBlock ctx ni id
  placeClasses vdir
  for l in layers do
    let nodes := (ctx.arena.layer l).nodes
    modifyThe BKAlignedLayout (applyFinalCoordinates ctx vdir nodes)
  ThresholdStrategy.postProcess ctx ni

/-- Runs `horizontalCompaction` on one layout with a fresh threshold strategy of the chosen
kind (equivalent to the Rust compactor reused across layouts: `init()` resets the strategy
and the class graph is cleared at the start of every compaction). -/
def run (c : BKCompactor) (ctx : BKContext) (bal : BKAlignedLayout) (ni : NeighborhoodInformation) :
    IO BKAlignedLayout := do
  let ((), bal) ← (((horizontalCompaction ctx ni).run' c).run' (ThresholdStrategy.create c.thresholdKind)).run bal
  return bal

/-- The compactor as an `ICompactor`. -/
def toICompactor (c : BKCompactor) (ctx : BKContext) : ICompactor :=
  { horizontalCompaction := c.run ctx }

end BKCompactor

end Elk.Alg.Layered.P4Nodes.BK
