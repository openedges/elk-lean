import Elk.Alg.Layered.LayeredPhases
import Elk.Alg.Layered.P4Nodes.BK.BKAligner
import Elk.Alg.Layered.P4Nodes.BK.BKCompactor
import Elk.Core.Util.ProgressMonitor
import Elk.Core.Util.FloatConst
open Elk.Core.Util.FloatConst
/-!
# `org.eclipse.elk.alg.layered.p4nodes.bk.BKNodePlacer` (elk-rs `node_placer.rs`)

Node placement (phase 4 of ELK Layered) inspired by Ulrik Brandes and Boris Köpf, *Fast and
simple horizontal coordinate assignment* (GD'01, LNCS 2265, pp. 33-36, 2002), extended to cope
with ports, node sizes and node margins:

1. type 1 conflicts (short edges crossing inner segments of long edges) are marked;
2. for each of the four iteration directions (`RIGHTDOWN`, `RIGHTUP`, `LEFTDOWN`, `LEFTUP`, in
   this order) nodes are grouped into blocks (`BKAligner.verticalAlignment`),
3. nodes are shifted inside their blocks to straighten the block edges
   (`BKAligner.insideBlockShift`),
4. y coordinates are assigned to blocks (`BKCompactor`);
5. a balanced (median) layout or the smallest of the computed layouts that respects the node
   order is chosen (`fixedAlignment`, `favorStraightEdges`).

Lean structure: `NeighborhoodInformation.buildFor` assigns the node/layer ids in the arena (like
Java/Rust); everything else works on a snapshot of the arena (`BKContext`, Rust `ArenaSync`) and
returns the new node y positions, which are written with `LayeredM.modifyNode` after the
snapshot is released. The layouts are local values (Rust `Vec<BKAlignedLayout>`), indexed by
local node ids (see `BKUtil`). Iteration orders: `graph.layers` in order and each layer's
`nodes` in order, unless stated otherwise.

Rust deviations from Java that are followed: the balanced layout's `min`/`max` start at `±∞`
(Java `Integer.MAX_VALUE`/`MIN_VALUE`), `f64::min/max`, the class debug output keyed by sink id.
The `ELK_TRACE_BK*` diagnostics are printed to stderr like elk-rs (`{:.3}` via `fmt3`).
-/

namespace Elk.Alg.Layered.P4Nodes.BK

open Elk.Graph Elk.Core.Math Elk.Core.Util Elk.Core.Alg Elk.Alg.Layered Elk.Alg.Layered.Graph
  Elk.Alg.Layered.Options Elk.Alg.Layered.Intermediate

namespace BKNodePlacer

/-- `HIERARCHY_PROCESSING_ADDITIONS`: additional processor dependencies for graphs with
hierarchical ports. -/
def HIERARCHY_PROCESSING_ADDITIONS : LayeredProcessorConfiguration :=
  LayoutProcessorConfiguration.create.addBefore .p5EdgeRouting .hierarchicalPortPositionProcessor

/-- `getLayoutProcessorConfiguration(graph)`: `HIERARCHY_PROCESSING_ADDITIONS` if the graph has
external ports, else none. -/
def getLayoutProcessorConfiguration (graph : LGraphId) : LayeredM (Option LayeredProcessorConfiguration) := do
  if (← LayeredM.getGraph graph).internal.graphProperties.contains .externalPorts then
    return some (LayoutProcessorConfiguration.createFrom HIERARCHY_PROCESSING_ADDITIONS)
  return none

/-- `MIN_LAYERS_FOR_CONFLICTS`: the minimum number of layers needed to have conflicts. -/
def MIN_LAYERS_FOR_CONFLICTS : Nat := 3

/-- `build_nodes_by_id(layers, node_count)`: local id → node (throws for a missing id). -/
private def buildNodesById (a : LGraphArena) (layers : Array LayerId) (nodeCount : Nat) : IO (Array LNodeId) := do
  let mut nodes : Array (Option LNodeId) := Array.replicate nodeCount none
  for l in layers do
    for n in (a.layer l).nodes do
      let id := BKContext.idAsUsize (a.node n).id
      if id < nodes.size then nodes := nodes.set! id (some n)
  nodes.mapM fun
    | some n => pure n
    | none => throw (IO.userError "java.lang.IllegalStateException: Missing node for id")

/-- `incidentToInnerSegment(node, layer1, layer2)`: whether `node` (in layer `layer1`) is a long
edge dummy with an incoming edge from a long edge dummy in layer `layer2`. -/
private def incidentToInnerSegment (a : LGraphArena) (ni : NeighborhoodInformation) (node : LNodeId)
    (layer1 layer2 : Nat) : Bool := Id.run do
  let nd := a.node node
  if nd.type != .longEdge then return false
  let layerId (l : Option LayerId) : Nat := (l.map fun l => BKContext.idAsUsize (a.layer l).id).getD 0
  for e in a.nodeIncomingEdges node do
    let some source := (a.edge e).source.bind (fun p => (a.port p).owner) | continue
    let src := a.node source
    if src.type != .longEdge then continue
    if ni.layerIndexOf (layerId src.layer) == layer2 && ni.layerIndexOf (layerId nd.layer) == layer1 then
      return true
  return false

/-- The `ELK_TRACE_BK_CONFLICTS` line for a marked edge. -/
private def traceConflict (a : LGraphArena) (e : LEdgeId) (k k0 k1 : Nat) : IO Unit := do
  let ed := a.edge e
  let endInfo (p : Option LPortId) : String × String :=
    match p.bind (fun p => (a.port p).owner) with
    | some n => (toString (BKContext.idAsUsize (a.node n).id), a.nodeDesignation n)
    | none => ("18446744073709551615", "<none>")
  let (srcId, srcName) := endInfo ed.source
  let (tgtId, tgtName) := endInfo ed.target
  IO.eprintln s!"bk-conflict: mark edge {srcId}({srcName})->{tgtId}({tgtName}) k={k} k0={k0} k1={k1}"

/-- Marks the left-neighbor edges of the nodes `nodes[l..=l1]` (layer `i + 1`) that are not
incident to an inner segment and whose neighbor index lies outside `[k0, k1]`. -/
private def markRange (a : LGraphArena) (ni : NeighborhoodInformation) (nodes : Array LNodeId) (i : Nat)
    (l l1 k0 k1 : Nat) (marked : Std.HashSet LEdgeId) : IO (Std.HashSet LEdgeId × Nat) := do
  let traceConflicts := ElkTrace.global.bkConflicts
  let mut marked := marked
  let mut l := l
  while l ≤ l1 do
    let vl := nodes[l]!
    if !incidentToInnerSegment a ni vl (i + 1) i then
      for (neighborId, edge) in ni.leftNeighbors.getD (BKContext.idAsUsize (a.node vl).id) #[] do
        let k := ni.nodeIndexOf neighborId
        if k < k0 || k > k1 then
          marked := marked.insert edge
          if traceConflicts then traceConflict a edge k k0 k1
    l := l + 1
  return (marked, l)

/-- `markConflicts(layeredGraph)`: marks type 1 conflicts, i.e. non-inner segments crossing
inner segments (segments between two long edge dummies) between the layers `i` and `i + 1`
(`1 ≤ i < layers − 1`). The markers are later used to resolve conflicts in favour of long
edges. -/
def markConflicts (a : LGraphArena) (layers : Array LayerId) (ni : NeighborhoodInformation) :
    IO (Std.HashSet LEdgeId) := do
  let mut marked : Std.HashSet LEdgeId := {}
  if layers.size < MIN_LAYERS_FOR_CONFLICTS then return marked
  let layerSize := layers.map fun l => (a.layer l).nodes.size
  for i in [1:layers.size - 1] do
    let nodes := (a.layer layers[i + 1]!).nodes
    let mut k0 := 0
    let mut l := 0
    for l1 in [0:layerSize[i + 1]!] do
      let vli := nodes[l1]!
      let incident := incidentToInnerSegment a ni vli (i + 1) i
      if l1 == layerSize[i + 1]! - 1 || incident then
        let mut k1 := layerSize[i]! - 1
        if incident then
          if let some (neighborId, _) := (ni.leftNeighbors.getD (BKContext.idAsUsize (a.node vli).id) #[])[0]? then
            k1 := ni.nodeIndexOf neighborId
        let (marked', l') ← markRange a ni nodes i l l1 k0 k1 marked
        marked := marked'
        l := l'
        k0 := k1
  return marked

/-- `createBalancedLayout(layouts, nodeCount)`: the median of the given layouts. The smallest
layout (first one of minimal `layoutSize`) is the reference: every layout is shifted to align
its top (`DOWN`) or bottom (`UP`) with it, and each node gets the average of the two middle
values of its shifted positions (inner shifts included; the balanced inner shifts are `0`). -/
def createBalancedLayout (ctx : BKContext) (layouts : Array BKAlignedLayout) : BKAlignedLayout := Id.run do
  let noOfLayouts := layouts.size
  let mut balanced := BKAlignedLayout.new ctx.nodeCount none none
  let mut width : Array Float := Array.replicate noOfLayouts fl0p0
  let mut mn : Array Float := Array.replicate noOfLayouts Float.posInf
  let mut mx : Array Float := Array.replicate noOfLayouts Float.negInf
  let mut minWidthLayout := 0
  for i in [0:noOfLayouts] do
    let layout := layouts[i]!
    width := width.set! i (layout.layoutSize ctx)
    if width[i]! < width[minWidthLayout]! then minWidthLayout := i
    for l in ctx.layers do
      for n in (ctx.arena.layer l).nodes do
        let id := ctx.nodeId n
        let nodePos := layout.yOf id + layout.innerShiftOf id
        mn := mn.set! i (fmin mn[i]! nodePos)
        mx := mx.set! i (fmax mx[i]! (nodePos + ctx.sizeY n))
  let mut shift : Array Float := Array.replicate noOfLayouts fl0p0
  for i in [0:noOfLayouts] do
    if layouts[i]!.vdir == some .down then
      shift := shift.set! i (mn[minWidthLayout]! - mn[i]!)
    else
      shift := shift.set! i (mx[minWidthLayout]! - mx[i]!)
  for l in ctx.layers do
    for n in (ctx.arena.layer l).nodes do
      let id := ctx.nodeId n
      let calculated := (Array.range noOfLayouts).map fun i =>
        let layout := layouts[i]!
        layout.yOf id + layout.innerShiftOf id + shift[i]!
      let calculated := stableSort calculated Float.comparePartial
      if noOfLayouts ≥ 3 then
        balanced := balanced.setY id ((calculated[1]! + calculated[2]!) / fl2p0)
      else if noOfLayouts > 0 then
        balanced := balanced.setY id calculated[noOfLayouts / 2]!
      balanced := balanced.setInnerShift id fl0p0
  return balanced

/-- `checkOrderConstraint(layeredGraph, bal)`: whether all nodes are placed in the order of
their layers without overlapping (top and bottom border, with margins, beyond the previous
node's bottom). -/
def checkOrderConstraint (ctx : BKContext) (bal : BKAlignedLayout) (monitor : ProgressMonitor) : IO Bool := do
  let mut feasible := true
  for l in ctx.layers do
    let nodes := (ctx.arena.layer l).nodes
    let i := firstOrderViolation ctx bal nodes 0 Float.negInf
    if h : i < nodes.size then
      feasible := false
      if ← monitor.isLoggingEnabled then
        -- every node before the violating one passed, the last of them is Java's `previous`
        let prevStr := if i == 0 then "<none>" else ctx.nodeToString nodes[i - 1]!
        monitor.log s!"bk node placement breaks on {ctx.nodeToString nodes[i]} which should have been after {prevStr}"
      break
  if ← monitor.isLoggingEnabled then
    monitor.log s!"{bal} is feasible: {feasible}"
  return feasible
where
  /-- The inner loop of `checkOrderConstraint` over the nodes of one layer from `i` on with the bottom
  `pos` of the last node: the index of the first node that is not below `pos` (`nodes.size` if all
  are). A pure tail loop, so that `pos` stays an unboxed `Float` and `previous` needs no `some`
  per node (PLAN 7.1 items 3, 49); `pos` becomes `bottom`, the same sum Java assigns. -/
  firstOrderViolation (ctx : BKContext) (bal : BKAlignedLayout) (nodes : Array LNodeId) (i : Nat)
      (pos : Float) : Nat :=
    if h : i < nodes.size then
      let n := nodes[i]
      let id := ctx.nodeId n
      let top := bal.yOf id + bal.innerShiftOf id - ctx.marginTop n
      let bottom := bal.yOf id + bal.innerShiftOf id + ctx.sizeY n + ctx.marginBottom n
      if top > pos && bottom > pos then firstOrderViolation ctx bal nodes (i + 1) bottom else i
    else nodes.size
  termination_by nodes.size - i

/-- `getClasses(bal)` (debug output): the block roots of each class, keyed by sink (ascending);
the roots of a class in order of first appearance in `bal.root` (Java `LinkedHashSet`; Rust
drains a `HashSet`). Empty for the balanced layout. -/
def getClasses (ctx : BKContext) (bal : BKAlignedLayout) (monitor : ProgressMonitor) : IO (Array (Nat × Array LNodeId)) := do
  if bal.vdir.isNone then
    if ← monitor.isLoggingEnabled then
      monitor.log "There are no classes in a balanced layout."
    return #[]
  let mut seen : Array Bool := Array.replicate bal.size false
  let mut bySink : Array (Array LNodeId) := Array.replicate bal.size #[]
  for r in bal.root do
    if r < bal.size && !seen[r]! then
      seen := seen.set! r true
      let s := bal.sinkOf r
      bySink := bySink.modify s (·.push (ctx.nodeOf r))
  let mut result : Array (Nat × Array LNodeId) := #[]
  for s in [0:bal.size] do
    if !bySink[s]!.isEmpty then result := result.push (s, bySink[s]!)
  return result

/-- Rust `{:?}` of an `Option<String>` label. -/
private def debugLabel (label : Option String) : String :=
  match label with
  | some s => s!"Some(\"{s}\")"
  | none => "None"

/-- The `ELK_TRACE_BK_LAYOUTS` output. -/
private def traceLayouts (ctx : BKContext) (layouts : Array BKAlignedLayout) : IO Unit := do
  for bal in layouts do
    IO.eprintln s!"bk-layout: {bal}"
    for l in ctx.layers do
      for n in (ctx.arena.layer l).nodes do
        let id := ctx.nodeId n
        IO.eprintln s!"bk-layout-node: layout={bal} id={id} y={fmt3 (bal.yOf id)} inner={fmt3 (bal.innerShiftOf id)} final={fmt3 (bal.yOf id + bal.innerShiftOf id)}"

/-- The `ELK_TRACE_BK_NODE_STATE` output for the chosen layout. -/
private def traceNodeState (ctx : BKContext) (chosen : BKAlignedLayout) : IO Unit := do
  let filter := ElkTrace.global.bkNodeFilter
  for l in ctx.layers do
    for n in (ctx.arena.layer l).nodes do
      let id := ctx.nodeId n
      let name := ctx.designation n
      let label := ((ctx.arena.node n).labels[0]?).map fun lb => (ctx.arena.label lb).text
      if let some f := filter then
        if !(name.contains f) && !(label.any (·.contains f)) then continue
      let rootId := chosen.rootOf id
      IO.eprintln (s!"bk-node-state: node={name} label={debugLabel label} id={id} root={rootId} " ++
        s!"align={chosen.alignOf id} sink={chosen.sinkOf id} y_root={fmt3 (chosen.yOf rootId)} " ++
        s!"y_node={fmt3 (chosen.yOf id)} inner={fmt3 (chosen.innerShiftOf id)} block_size={fmt3 (chosen.blockSizeOf rootId)}")

/-- Chooses the layout: the balanced layout if requested and feasible, else the first feasible
layout of minimal `layoutSize`, else the first layout. -/
private def chooseLayout (ctx : BKContext) (layouts : Array BKAlignedLayout) (produceBalancedLayout : Bool)
    (monitor : ProgressMonitor) : IO BKAlignedLayout := do
  let trace := ElkTrace.global.bk
  let mut chosen : Option BKAlignedLayout := none
  if produceBalancedLayout then
    let balanced := createBalancedLayout ctx layouts
    let balancedOk ← checkOrderConstraint ctx balanced monitor
    if trace then
      IO.eprintln s!"bk: balanced candidate={balanced} size={(balanced.layoutSize ctx).toRustDisplay} order_ok={balancedOk}"
    if balancedOk then chosen := some balanced
  if trace then IO.eprintln "bk: balanced layout checked"
  if chosen.isNone then
    -- `layoutSize` is pure: every layout's size is computed once (Java recomputes it per comparison)
    let mut chosenSize : Float := 0.0
    for bal in layouts do
      let orderOk ← checkOrderConstraint ctx bal monitor
      let size := bal.layoutSize ctx
      if trace then
        IO.eprintln s!"bk: candidate={bal} size={size.toRustDisplay} order_ok={orderOk}"
      let smaller : Bool := if chosen.isSome then chosenSize > size else true
      if orderOk && smaller then
        chosen := some bal
        chosenSize := size
  if trace then
    match chosen with
    | some c => IO.eprintln s!"bk: layout chosen={c} size={(c.layoutSize ctx).toRustDisplay}"
    | none => IO.eprintln "bk: layout chosen=<none>"
  match chosen, layouts[0]? with
  | some c, _ => return c
  | none, some first => return first
  | none, none => throw (IO.userError "java.lang.IllegalStateException: At least one BK layout must exist")

/-- The four (or one, for a fixed alignment) layouts in the Java/Rust order `RIGHTDOWN`,
`RIGHTUP`, `LEFTDOWN`, `LEFTUP`. -/
private def initialLayouts (nodeCount : Nat) (align : FixedAlignment) : Array BKAlignedLayout :=
  let mk (v : VDirection) (h : HDirection) := BKAlignedLayout.new nodeCount (some v) (some h)
  match align with
  | .leftDown => #[mk .down .left]
  | .leftUp => #[mk .up .left]
  | .rightDown => #[mk .down .right]
  | .rightUp => #[mk .up .right]
  | _ => #[mk .down .right, mk .up .right, mk .down .left, mk .up .left]

/-- Steps 1–5 on a snapshot of the arena; returns the new y position of every node (layers in
order, nodes in layer order) and writes the debug log of the chosen layout. -/
private def computePositions (graph : LGraphId) (ni : NeighborhoodInformation) (monitor : ProgressMonitor) :
    LayeredM (Array (LNodeId × Float)) := do
  let trace := ElkTrace.global.bk
  let a ← get
  let g := a.graph graph
  let layers := g.layers
  let nodesById ← buildNodesById a layers ni.nodeCount
  let align := (g.props.get LayeredOptions.NODE_PLACEMENT_BK_FIXED_ALIGNMENT).getD .none
  let favorStraightEdges := (g.props.get LayeredOptions.NODE_PLACEMENT_FAVOR_STRAIGHT_EDGES).getD false
  let produceBalancedLayout := (align == .none && !favorStraightEdges) || align == .balanced
  let markedEdges ← markConflicts a layers ni
  if trace then IO.eprintln "bk: conflicts marked"
  let some spacings := g.internal.spacings
    | throw (IO.userError "java.lang.IllegalStateException: Missing spacings configuration for BK node placement")
  let ctx : BKContext := { arena := a, layers, nodesById, spacings }
  let layouts ← (initialLayouts ni.nodeCount align).mapM fun bal => do
    let bal ← BKAligner.verticalAlignment ctx ni markedEdges bal
    BKAligner.insideBlockShift ctx bal
  if trace then IO.eprintln "bk: alignment done"
  let compactor := (← BKCompactor.new g).toICompactor ctx
  let layouts ← layouts.mapM fun bal => compactor.horizontalCompaction bal ni
  if trace then IO.eprintln "bk: compaction done"
  if ElkTrace.global.bkLayouts then traceLayouts ctx layouts
  if ← monitor.isLoggingEnabled then
    for bal in layouts do
      monitor.log s!"{bal} size is {(bal.layoutSize ctx).toRustDisplay}"
  let chosen ← chooseLayout ctx layouts produceBalancedLayout monitor
  if ElkTrace.global.bkNodeState then traceNodeState ctx chosen
  let mut positions : Array (LNodeId × Float) := #[]
  for l in layers do
    for n in (a.layer l).nodes do
      let id := ctx.nodeId n
      positions := positions.push (n, chosen.yOf id + chosen.innerShiftOf id)
  if ← monitor.isLoggingEnabled then
    monitor.log s!"Chosen node placement: {chosen}"
    monitor.log s!"Blocks: {formatBlocks ctx (chosen.getBlocks ctx)}"
    let classes ← getClasses ctx chosen monitor
    monitor.log s!"Classes: {formatBlocks ctx classes}"
    monitor.log s!"Marked edges: {markedEdges.size}"
  return positions

/-- `process(layeredGraph, monitor)`: Brandes & Köpf node placement of `graph`. -/
def process (graph : LGraphId) (monitor : ProgressMonitor) : LayeredM Unit := do
  let _ ← monitor.begin "Brandes & Koepf node placement" 1.0
  let trace := ElkTrace.global.bk
  if trace then IO.eprintln "bk: start"
  let ni ← NeighborhoodInformation.buildFor graph
  let positions ← computePositions graph ni monitor
  for (n, y) in positions do
    LayeredM.modifyNode n fun x => { x with position := { x.position with y := y } }
  if trace then IO.eprintln "bk: positions applied"
  monitor.done

/-- The `BKNodePlacer` phase (`NodePlacementStrategy.BRANDES_KOEPF`). -/
def phase : LayeredPhase :=
  { name := "BKNodePlacer"
    process := process
    getLayoutProcessorConfiguration := getLayoutProcessorConfiguration }

end BKNodePlacer

/-- Registers `BKNodePlacer` as the phase of `NodePlacementStrategy.BRANDES_KOEPF`. -/
builtin_initialize registerBKNodePlacer : Unit ←
  LayeredPhases.registerPhase .p4NodePlacement (ElkEnum.ordinal NodePlacementStrategy.brandesKoepf) (pure BKNodePlacer.phase)

end Elk.Alg.Layered.P4Nodes.BK
