import Elk.Alg.Layered.P4Nodes.BK.NeighborhoodInformation
import Elk.Core.Util.ElkTrace
/-!
# `org.eclipse.elk.alg.layered.p4nodes.bk.BKAlignedLayout` (elk-rs `aligned_layout.rs`)

One of the four (or the balanced) layouts computed by the Brandes & Köpf node placer: the
block structure (`root`, `align`), the inner shifts and block sizes, the classes (`sink`,
`shift`) and the resulting y coordinates. All arrays are indexed by local node ids (see
`BKUtil`); Java uses `LNode` references, Rust `usize` ids.

`y` is `Vec<Option<f64>>` in Rust; here it is an unboxed `FloatArray` plus the `yDefined`
flags (`y[i].unwrap_or(0.0)` = `yOf i`). The read-only parts of the Rust struct (`layers`,
`nodes_by_id`, `spacings`, `sync`) live in `BKContext`.

The algorithms that update a layout incrementally (aligner, compactor, threshold strategies)
run in `BalM := StateRefT BKAlignedLayout IO`.
-/
/-! Float literals as global constants (FL): inside branches, loops and specialised code the compiler
shares a literal's `Nat`/`Bool` arguments with unrelated variables (CSE) and then parses it on every
evaluation (`FastFloat.ofScientificImpl`); a top-level constant is a load (PLAN §7.1 items 17, 22). -/
private def fl0p0 : Float := 0.0

namespace Elk.Alg.Layered.P4Nodes.BK

open Elk.Graph Elk.Core.Math Elk.Core.Util Elk.Alg.Layered.Graph Elk.Alg.Layered.Options

/-- `BKAlignedLayout.VDirection`: `DOWN` = iteration top-down, `UP` = bottom-up. -/
elk_enum VDirection := down up

/-- `BKAlignedLayout.HDirection`: `RIGHT` = iterating the layers from left to right, `LEFT` =
from right to left. -/
elk_enum HDirection := right left

/-- `BKAlignedLayout`. -/
structure BKAlignedLayout where
  /-- `root`: the root node of each node's block. -/
  root : Array Nat
  /-- `blockSize`: the size of a block (indexed by its root). -/
  blockSize : FloatArray
  /-- `align`: the next node in a block, or the root if the node is the last, forming a ring. -/
  align : Array Nat
  /-- `innerShift`: the value by which a node must be shifted to stay straight inside its block. -/
  innerShift : FloatArray
  /-- `sink`: the root node of a class, mapped from block root nodes to class root nodes. -/
  sink : Array Nat
  /-- `shift`: the value by which a class must be shifted for a more compact placement. -/
  shift : FloatArray
  /-- `y`: the y coordinate of every node (meaningful where `yDefined`). -/
  y : FloatArray
  /-- `y[i].is_some()`. -/
  yDefined : Array Bool
  /-- `vdir`: the vertical direction (`none` for the balanced layout). -/
  vdir : Option VDirection
  /-- `hdir`: the horizontal direction (`none` for the balanced layout). -/
  hdir : Option HDirection
  /-- `su`: flags blocks (by root) that are part of a straightened edge. -/
  su : Array Bool
  /-- `od`: flags blocks (by root) that consist solely of dummy nodes. -/
  od : Array Bool
  deriving Inhabited

/-- The layout monad of the aligner/compactor/threshold strategies. -/
abbrev BalM := StateRefT BKAlignedLayout IO

namespace BKAlignedLayout

/-- `BKAlignedLayout::new(…, vdir, hdir, …)`: every node is its own block, root and sink; all
shifts and sizes `0`, no y coordinates, `su = false`, `od = true`. -/
def new (nodeCount : Nat) (vdir : Option VDirection) (hdir : Option HDirection) : BKAlignedLayout :=
  let ids := Array.range nodeCount
  { root := ids, align := ids, sink := ids
    blockSize := ⟨Array.replicate nodeCount 0.0⟩, innerShift := ⟨Array.replicate nodeCount 0.0⟩
    shift := ⟨Array.replicate nodeCount 0.0⟩, y := ⟨Array.replicate nodeCount 0.0⟩
    yDefined := Array.replicate nodeCount false
    vdir, hdir
    su := Array.replicate nodeCount false, od := Array.replicate nodeCount true }

/-- Number of entries of the per-node arrays (`align.len()`). -/
@[inline] def size (bal : BKAlignedLayout) : Nat := bal.align.size

/-- `y[i].unwrap_or(0.0)`. -/
@[inline] def yOf (bal : BKAlignedLayout) (i : Nat) : Float :=
  if bal.yDefined.getD i false then bal.y.get! i else fl0p0

/-- `y[i].is_some()`. -/
@[inline] def isYDefined (bal : BKAlignedLayout) (i : Nat) : Bool := bal.yDefined.getD i false

/-- `y[i] = Some(v)`. -/
@[inline] def setY (bal : BKAlignedLayout) (i : Nat) (v : Float) : BKAlignedLayout :=
  { bal with y := bal.y.set! i v, yDefined := bal.yDefined.set! i true }

/-- `inner_shift[i]`. -/
@[inline] def innerShiftOf (bal : BKAlignedLayout) (i : Nat) : Float := bal.innerShift.get! i

/-- `inner_shift[i] = v`. -/
@[inline] def setInnerShift (bal : BKAlignedLayout) (i : Nat) (v : Float) : BKAlignedLayout :=
  { bal with innerShift := bal.innerShift.set! i v }

/-- `root[i]`. -/
@[inline] def rootOf (bal : BKAlignedLayout) (i : Nat) : Nat := bal.root[i]!

/-- `align[i]`. -/
@[inline] def alignOf (bal : BKAlignedLayout) (i : Nat) : Nat := bal.align[i]!

/-- `sink[i]`. -/
@[inline] def sinkOf (bal : BKAlignedLayout) (i : Nat) : Nat := bal.sink[i]!

/-- `blockSize[i]`. -/
@[inline] def blockSizeOf (bal : BKAlignedLayout) (i : Nat) : Float := bal.blockSize.get! i

/-- `shift[i]`. -/
@[inline] def shiftOf (bal : BKAlignedLayout) (i : Nat) : Float := bal.shift.get! i

/-- `toString()`: `RIGHTDOWN`, `LEFTUP`, …, or `BALANCED` without directions. -/
def toString (bal : BKAlignedLayout) : String :=
  let h := match bal.hdir with
    | some .right => "RIGHT"
    | some .left => "LEFT"
    | none => ""
  let v := match bal.vdir with
    | some .down => "DOWN"
    | some .up => "UP"
    | none => "BALANCED"
  h ++ v

instance : ToString BKAlignedLayout := ⟨BKAlignedLayout.toString⟩

/-- `layoutSize()`: the extent between the minimal y coordinate of any node and the maximal y
coordinate plus the size of the node's block (`f64::min/max`, layers then nodes in order). -/
def layoutSize (ctx : BKContext) (bal : BKAlignedLayout) : Float :=
  layoutSizeGo 0 #[] 0 Float.posInf Float.negInf
where
  /-- The node loop with unboxed accumulators: node `ni` of `nodes` (the nodes of layer `li`). -/
  layoutSizeGo (li : Nat) (nodes : Array LNodeId) (ni : Nat) (mn mx : Float) : Float :=
    if h : ni < nodes.size then
      let id := ctx.nodeId nodes[ni]
      let yMin := bal.yOf id
      let yMax := yMin + bal.blockSizeOf (bal.rootOf id)
      layoutSizeGo li nodes (ni + 1) (fmin mn yMin) (fmax mx yMax)
    else if h' : li < ctx.layers.size then
      layoutSizeGo (li + 1) (ctx.arena.layer ctx.layers[li]).nodes 0 mn mx
    else mx - mn
  termination_by (ctx.layers.size + 1 - li, nodes.size - ni)

/-- `calculateDelta(src, tgt)`: target port position minus source port position (each
`y + innerShift + (port.y + anchor.y)`); `> 0` means the target has to move up to straighten
the edge. -/
def calculateDelta (ctx : BKContext) (bal : BKAlignedLayout) (src tgt : LPortId) : Float :=
  let srcNodeId := ctx.portNodeId src
  let tgtNodeId := ctx.portNodeId tgt
  let srcPos := bal.yOf srcNodeId + bal.innerShiftOf srcNodeId + ctx.portOffsetY src
  let tgtPos := bal.yOf tgtNodeId + bal.innerShiftOf tgtNodeId + ctx.portOffsetY tgt
  tgtPos - srcPos

/-- `getMinY(n)`: `y[root[n]] + innerShift[n] - margin.top`. -/
def minY (ctx : BKContext) (bal : BKAlignedLayout) (id : Nat) : Float :=
  bal.yOf (bal.rootOf id) + bal.innerShiftOf id - ctx.marginTop (ctx.nodeOf id)

/-- `getMaxY(n)`: `y[root[n]] + innerShift[n] + size.y + margin.bottom`. -/
def maxY (ctx : BKContext) (bal : BKAlignedLayout) (id : Nat) : Float :=
  let n := ctx.nodeOf id
  bal.yOf (bal.rootOf id) + bal.innerShiftOf id + ctx.sizeY n + ctx.marginBottom n

/-- `getUpperNeighbor(n)`: the node before `n` in its layer. -/
def upperNeighbor (ctx : BKContext) (ni : NeighborhoodInformation) (id : Nat) : Option LNodeId := do
  let n ← ctx.nodesById[id]?
  let l ← (ctx.arena.node n).layer
  let index ← ni.nodeIndex[id]?
  if index > 0 then (ctx.arena.layer l).nodes[index - 1]? else none

/-- `getLowerNeighbor(n)`: the node after `n` in its layer. -/
def lowerNeighbor (ctx : BKContext) (ni : NeighborhoodInformation) (id : Nat) : Option LNodeId := do
  let n ← ctx.nodesById[id]?
  let l ← (ctx.arena.node n).layer
  let index ← ni.nodeIndex[id]?
  let nodes := (ctx.arena.layer l).nodes
  if index + 1 < nodes.size then nodes[index + 1]? else none

/-- Shared loop of `checkSpaceAbove`/`checkSpaceBelow`: visits the block ring starting after
`blockNode` until it wraps around (bounded by `max(align.len(), 1)` steps like Rust). -/
private def checkSpace (ctx : BKContext) (ni : NeighborhoodInformation) (bal : BKAlignedLayout)
    (blockNode : Nat) (delta : Float) (above : Bool) : IO Float := do
  let mut availableSpace := delta
  let root := blockNode
  let mut current := root
  let maxSteps := max bal.size 1
  let mut steps := 0
  while true do
    current := bal.alignOf current
    if above then
      let minYCurrent := minY ctx bal current
      if let some neighbor := upperNeighbor ctx ni current then
        let maxYNeighbor := maxY ctx bal (ctx.nodeId neighbor)
        let spacing ← ctx.verticalSpacing (ctx.nodeOf current) neighbor
        availableSpace := fmin availableSpace (minYCurrent - (maxYNeighbor + spacing))
    else
      let maxYCurrent := maxY ctx bal current
      if let some neighbor := lowerNeighbor ctx ni current then
        let minYNeighbor := minY ctx bal (ctx.nodeId neighbor)
        let spacing ← ctx.verticalSpacing (ctx.nodeOf current) neighbor
        availableSpace := fmin availableSpace (minYNeighbor - (maxYCurrent + spacing))
    if current == root then break
    steps := steps + 1
    if steps ≥ maxSteps then
      if ElkTrace.global.bkGuard then
        let which := if above then "check_space_above" else "check_space_below"
        IO.eprintln s!"bk-guard: {which} loop hit max_steps root={root} current={current} max_steps={maxSteps}"
      break
  return availableSpace

/-- `checkSpaceAbove(blockRoot, delta)`: the maximal distance (`≤ delta`) the block containing
`blockNode` can be moved upward without overlapping any upper neighbor (plus spacing). -/
def checkSpaceAbove (ctx : BKContext) (ni : NeighborhoodInformation) (bal : BKAlignedLayout)
    (blockNode : Nat) (delta : Float) : IO Float :=
  checkSpace ctx ni bal blockNode delta true

/-- `checkSpaceBelow(blockRoot, delta)`: like `checkSpaceAbove` for moving downward. -/
def checkSpaceBelow (ctx : BKContext) (ni : NeighborhoodInformation) (bal : BKAlignedLayout)
    (blockNode : Nat) (delta : Float) : IO Float :=
  checkSpace ctx ni bal blockNode delta false

/-- `shiftBlock(rootNode, delta)`: adds `delta` to the y coordinate of every node of the block
ring starting at `blockNode` (bounded by `max(align.len(), 1)` steps like Rust). -/
def shiftBlock (blockNode : Nat) (delta : Float) : BalM Unit := do
  let maxSteps := max (← getThe BKAlignedLayout).size 1
  let root := blockNode
  let mut current := root
  let mut steps := 0
  while true do
    let c := current
    modifyThe BKAlignedLayout fun b => b.setY c (b.yOf c + delta)
    current := (← getThe BKAlignedLayout).alignOf current
    if current == root || steps ≥ maxSteps then
      if steps ≥ maxSteps && ElkTrace.global.bkGuard then
        IO.eprintln s!"bk-guard: shift_block loop hit max_steps root={root} current={current} max_steps={maxSteps}"
      break
    steps := steps + 1

/-- `util::get_blocks(bal)` (Java `BKNodePlacer.getBlocks`): the nodes of every block, keyed by
the block root. Rust collects them in a `BTreeMap`, so the blocks are ordered by root id; the
nodes of a block are in layer order. -/
def getBlocks (ctx : BKContext) (bal : BKAlignedLayout) : Array (Nat × Array LNodeId) := Id.run do
  let mut byRoot : Array (Array LNodeId) := Array.replicate bal.size #[]
  let mut seen : Array Bool := Array.replicate bal.size false
  for l in ctx.layers do
    for n in (ctx.arena.layer l).nodes do
      let r := bal.rootOf (ctx.nodeId n)
      byRoot := byRoot.modify r (·.push n)
      seen := seen.set! r true
  let mut result : Array (Nat × Array LNodeId) := #[]
  for r in [0:bal.size] do
    if seen[r]! then result := result.push (r, byRoot[r]!)
  return result

/-- `cleanup()`: releases the arrays. -/
def cleanup (bal : BKAlignedLayout) : BKAlignedLayout :=
  { bal with root := #[], blockSize := ⟨#[]⟩, align := #[], innerShift := ⟨#[]⟩, sink := #[],
             shift := ⟨#[]⟩, y := ⟨#[]⟩, yDefined := #[], su := #[], od := #[] }

end BKAlignedLayout

/-- `format_blocks`: `{root:[n, …], …}` (debug output). -/
def formatBlocks (ctx : BKContext) (blocks : Array (Nat × Array LNodeId)) : String :=
  let entries := blocks.toList.map fun (r, ns) =>
    s!"{r}:[{", ".intercalate (ns.toList.map ctx.nodeToString)}]"
  "{" ++ ", ".intercalate entries ++ "}"

end Elk.Alg.Layered.P4Nodes.BK
