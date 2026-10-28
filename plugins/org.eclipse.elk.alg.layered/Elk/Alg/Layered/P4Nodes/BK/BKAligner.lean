import Elk.Alg.Layered.P4Nodes.BK.BKAlignedLayout
import Std.Data.HashSet
/-!
# `org.eclipse.elk.alg.layered.p4nodes.bk.BKAligner` (elk-rs `aligner.rs`)

Block building (`verticalAlignment`) and inner shifting (`insideBlockShift`) of the Brandes &
Köpf node placer. For documentation see `BKNodePlacer`.

Both steps take the layout by value and return the updated layout (the arrays are updated in
place while the layout is unshared).
-/
namespace Elk.Alg.Layered.P4Nodes.BK

open Elk.Graph Elk.Core.Math Elk.Core.Util Elk.Alg.Layered.Graph Elk.Alg.Layered.Options

namespace BKAligner

/-- Rust `{:?}` of a `VDirection`. -/
private def vdirDebug : VDirection → String
  | .down => "Down"
  | .up => "Up"

/-- Rust `{:?}` of an `HDirection`. -/
private def hdirDebug : HDirection → String
  | .right => "Right"
  | .left => "Left"

/-- Rust `isize::MAX` (initial `r` for `UP`; Java `Integer.MAX_VALUE`). -/
private def ISIZE_MAX : Int := 9223372036854775807

/-- Tries to append `node` (local id `id`) to the block of its median neighbor(s): the
neighbor indices `ms` (`low..=high`, reversed for `UP`) are tried while `node` is still
unaligned; a neighbor is taken if its edge is not marked and its in-layer index is beyond `r`
(`r < index` for `DOWN`, `r > index` for `UP`). Returns the updated layout and `r`. -/
private def alignNode (ctx : BKContext) (ni : NeighborhoodInformation) (markedEdges : Std.HashSet LEdgeId)
    (vdir : VDirection) (node : LNodeId) (id : Nat) (neighbors : Array (Nat × LEdgeId)) (ms : Array Nat)
    (bal : BKAlignedLayout) (r : Int) : IO (BKAlignedLayout × Int) := do
  let traceAlign := ElkTrace.global.bkAlign
  let mut bal := bal
  let mut r := r
  for m in ms do
    if bal.alignOf id == id then
      let (neighborId, edge) := neighbors[m]!
      if neighborId ≥ bal.size then continue
      let neighborIndex : Int := ni.nodeIndexOf neighborId
      let edgeMarked := markedEdges.contains edge
      if traceAlign then
        let neighborName := ctx.designation (ctx.nodeOf neighborId)
        IO.eprintln s!"bk-align: try node={id} neighbor={neighborId}({neighborName}) idx={neighborIndex} r={r} marked={edgeMarked}"
      let beyond := if vdir == .up then r > neighborIndex else r < neighborIndex
      if !edgeMarked && beyond then
        bal := { bal with align := bal.align.set! neighborId id }
        let root := bal.rootOf neighborId
        bal := { bal with root := bal.root.set! id root }
        bal := { bal with align := bal.align.set! id root }
        let od := bal.od[root]! && ctx.nodeType node == .longEdge
        bal := { bal with od := bal.od.set! root od }
        r := neighborIndex
        if traceAlign then
          IO.eprintln s!"bk-align: align-set node={id} neighbor={neighborId} root={root} new_r={r}"
  return (bal, r)

/-- `verticalAlignment(bal, markedEdges)`: the graph is traversed in the layout's directions
(layers reversed for `LEFT`, nodes of a layer reversed for `UP`) and nodes are grouped into
blocks with their median left (`RIGHT`) or right (`LEFT`) neighbors. The nodes of a block will
be placed such that the edges connecting them are straight. Type 1 conflicts (`markedEdges`)
are resolved in favour of long edges. -/
def verticalAlignment (ctx : BKContext) (ni : NeighborhoodInformation) (markedEdges : Std.HashSet LEdgeId)
    (bal : BKAlignedLayout) : IO BKAlignedLayout := do
  let traceAlign := ElkTrace.global.bkAlign
  let mut bal := bal
  for l in ctx.layers do
    for n in (ctx.arena.layer l).nodes do
      let id := ctx.nodeId n
      bal := { bal with root := bal.root.set! id id }
      bal := { bal with align := bal.align.set! id id }
      bal := bal.setInnerShift id 0.0
  let some hdir := bal.hdir
    | throw (IO.userError "java.lang.IllegalStateException: BK aligner requires a horizontal direction")
  let some vdir := bal.vdir
    | throw (IO.userError "java.lang.IllegalStateException: BK aligner requires a vertical direction")
  let layers := if hdir == .left then ctx.layers.reverse else ctx.layers
  for l in layers do
    let mut r : Int := -1
    let mut nodes := (ctx.arena.layer l).nodes
    if vdir == .up then
      r := ISIZE_MAX
      nodes := nodes.reverse
    for node in nodes do
      let id := ctx.nodeId node
      if id ≥ bal.size then continue
      let neighbors := (if hdir == .left then ni.rightNeighbors else ni.leftNeighbors).getD id #[]
      if neighbors.isEmpty then continue
      let d := neighbors.size
      let low := (d - 1) / 2
      let high := d / 2
      if traceAlign then
        IO.eprintln s!"bk-align: node={id}({ctx.designation node}) neighbors={d} low={low} high={high} vdir={vdirDebug vdir} hdir={hdirDebug hdir}"
      let ms := (Array.range (high + 1 - low)).map (· + low)
      let ms := if vdir == .up then ms.reverse else ms
      let (bal', r') ← alignNode ctx ni markedEdges vdir node id neighbors ms bal r
      bal := bal'
      r := r'
  return bal

/-- Number of connected edges of `current` between the nodes `currentId` and `nextId` (the
multi-edge diagnostic of `ELK_TRACE_BK_INNER`). -/
private def candidateCount (ctx : BKContext) (current : LNodeId) (currentId nextId : Nat) : Nat :=
  let a := ctx.arena
  (a.nodeConnectedEdges current).foldl (init := 0) fun acc e =>
    let ed := a.edge e
    match ed.source.bind (fun p => (a.port p).owner), ed.target.bind (fun p => (a.port p).owner) with
    | some s, some t =>
      let sId := ctx.nodeId s
      let tId := ctx.nodeId t
      if (sId == currentId && tId == nextId) || (sId == nextId && tId == currentId) then acc + 1 else acc
    | _, _ => acc

/-- The first loop of `insideBlockShift` for one block: walks the block ring from the root and
sets each node's inner shift such that the edge to the previous node is straight; returns the
inner shifts and the space required above and below the root's top border. `bal` is read for the
block ring only; its inner shifts are `innerShift` (taken out of the layout by the caller). The
loop is tail recursive with unboxed accumulators (bounded by `maxSteps` like Rust). -/
private partial def shiftBlockNodes (ctx : BKContext) (hdir : HDirection) (rootId maxSteps : Nat)
    (bal : BKAlignedLayout) (innerShift : FloatArray) (current steps : Nat) (spaceAbove spaceBelow : Float) :
    IO (FloatArray × Float × Float) := do
  let next := bal.alignOf current
  if next == rootId || steps ≥ maxSteps then
    if steps ≥ maxSteps && ElkTrace.global.bkGuard then
      IO.eprintln s!"bk-guard: inside_block_shift loop1 hit max_steps root_id={rootId} current={current} next={next} max_steps={maxSteps}"
    return (innerShift, spaceAbove, spaceBelow)
  let currentNode := ctx.nodeOf current
  let nextNode := ctx.nodeOf next
  let some edge := ctx.edgeBetween currentNode nextNode
    | throw (IO.userError "java.lang.IllegalStateException: edge between block nodes is missing")
  if ElkTrace.global.bkInner then
    let count := candidateCount ctx currentNode current next
    if count > 1 then
      IO.eprintln s!"bk-inner: root={rootId} multi-edge current={current} next={next} candidates={count}"
  let ed := ctx.arena.edge edge
  let (some sourcePort, some targetPort) := (ed.source, ed.target)
    | throw (IO.userError "java.lang.IllegalStateException: block edge without source or target port")
  let portPosDiff :=
    if hdir == .left then ctx.portOffsetY targetPort - ctx.portOffsetY sourcePort
    else ctx.portOffsetY sourcePort - ctx.portOffsetY targetPort
  let nextInnerShift := innerShift.get! current + portPosDiff
  let innerShift := innerShift.set! next nextInnerShift
  if ElkTrace.global.bkInner then
    IO.eprintln s!"bk-inner: root={rootId} step current={current}({ctx.designation currentNode}) next={next}({ctx.designation nextNode}) port_diff={fmt3 portPosDiff} next_inner={fmt3 nextInnerShift}"
  shiftBlockNodes ctx hdir rootId maxSteps bal innerShift next (steps + 1)
    (fmax spaceAbove (ctx.marginTop nextNode - nextInnerShift))
    (fmax spaceBelow (nextInnerShift + ctx.sizeY nextNode + ctx.marginBottom nextNode))

/-- The second loop of `insideBlockShift` for one block: adds `spaceAbove` to the inner shift of
every node of the block ring starting at the root (bounded by `maxSteps` like Rust). -/
private partial def applySpaceAbove (ctx : BKContext) (rootId maxSteps : Nat) (bal : BKAlignedLayout)
    (spaceAbove : Float) (innerShift : FloatArray) (current steps : Nat) : IO FloatArray := do
  let innerShift := innerShift.set! current (innerShift.get! current + spaceAbove)
  if ElkTrace.global.bkInner then
    IO.eprintln s!"bk-inner: root={rootId} apply current={current}({ctx.designation (ctx.nodeOf current)}) inner={fmt3 (innerShift.get! current)}"
  let current := bal.alignOf current
  if current == rootId || steps ≥ maxSteps then
    if steps ≥ maxSteps && ElkTrace.global.bkGuard then
      IO.eprintln s!"bk-guard: inside_block_shift loop2 hit max_steps root_id={rootId} current={current} max_steps={maxSteps}"
    return innerShift
  applySpaceAbove ctx rootId maxSteps bal spaceAbove innerShift current (steps + 1)

/-- The block roots of `getBlocks` (ascending root id, only roots of nodes in the layers),
without collecting the blocks' nodes. -/
private def blockRoots (ctx : BKContext) (bal : BKAlignedLayout) : Array Nat := Id.run do
  let mut seen : Array Bool := Array.replicate bal.size false
  for l in ctx.layers do
    for n in (ctx.arena.layer l).nodes do
      seen := seen.set! (bal.rootOf (ctx.nodeId n)) true
  let mut result : Array Nat := #[]
  for r in [0:bal.size] do
    if seen[r]! then result := result.push r
  return result

/-- `insideBlockShift(bal)`: moves the nodes inside each block (in ascending root id order,
Rust `BTreeMap`) such that all edges inside the block are straight, then shifts the whole
block down by the space required above the root and records the block size
(`spaceAbove + spaceBelow`). Not part of the original algorithm; adds port and node size
handling. The inner shifts and block sizes are taken out of the layout while the blocks are
processed (updated in place) and written back at the end. -/
def insideBlockShift (ctx : BKContext) (bal : BKAlignedLayout) : IO BKAlignedLayout := do
  let roots := blockRoots ctx bal
  let some hdir := bal.hdir
    | throw (IO.userError "java.lang.IllegalStateException: BK aligner requires a horizontal direction")
  let traceInner := ElkTrace.global.bkInner
  let maxSteps := max bal.size 1
  let mut innerShift := bal.innerShift
  let mut blockSize := bal.blockSize
  let bal := { bal with innerShift := FloatArray.empty, blockSize := FloatArray.empty }
  for rootId in roots do
    let rootNode := ctx.nodeOf rootId
    if traceInner then
      IO.eprintln s!"bk-inner: root={rootId}({ctx.designation rootNode}) start hdir={hdirDebug hdir}"
    let spaceAbove := ctx.marginTop rootNode
    let spaceBelow := ctx.sizeY rootNode + ctx.marginBottom rootNode
    innerShift := innerShift.set! rootId 0.0
    let (innerShift', spaceAbove, spaceBelow) ←
      shiftBlockNodes ctx hdir rootId maxSteps bal innerShift rootId 0 spaceAbove spaceBelow
    innerShift ← applySpaceAbove ctx rootId maxSteps bal spaceAbove innerShift' rootId 0
    blockSize := blockSize.set! rootId (spaceAbove + spaceBelow)
    if traceInner then
      IO.eprintln s!"bk-inner: root={rootId} done space_above={fmt3 spaceAbove} space_below={fmt3 spaceBelow} block_size={fmt3 (blockSize.get! rootId)}"
  return { bal with innerShift, blockSize }

end BKAligner

end Elk.Alg.Layered.P4Nodes.BK
