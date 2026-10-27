import Elk.Graph
import Elk.Core.Util.Java
import Elk.Graph.ArrayModify
/-!
# Rectangle packing arena (`util::{Block, BlockRow, BlockStack, RectRow}` data and `RectPackingM`)

elk-rs keeps the packing structures as an `Rc<RefCell<…>>` object graph: a `RectRow` owns its
blocks (`Vec<BlockRef>`) and stacks (`Vec<BlockStackRef>`), a `BlockStack` owns its blocks, and a
`Block` points back to its parent row and stack through `Weak` references. elk-lean stores the
three shared kinds in one local arena with typed indices (`BlockId`, `BlockStackId`, `RectRowId`);
`BlockRow` is a plain value inside its `Block` (`Vec<BlockRow>` in Rust). The rectangles
themselves are the child nodes of the laid-out `ElkGraph` node (`NodeId`), so all geometry updates
of rectangles go through `ElkM`.

The algorithm monad is `RectPackingM := StateRefT RectPackingArena ElkM`: arena state on top of
the `ElkGraph` state. `ElkM` actions lift automatically. Arena elements are read with
`getBlock`/`getStack`/`getRow` (value copies) and updated in place with
`modifyBlock`/`modifyStack`/`modifyRow`; never bind the whole arena across a write.

This module holds the data of the four Java classes (one structure each, Java/Rust field order)
because their methods reference each other through the arena; the methods live in
`Util/BlockRow.lean`, `Util/Block.lean`, `Util/BlockStack.lean` and `Util/RectRow.lean`.
`RectRow.notifyAboutNodeChange` is defined here because `Block` calls it and `RectRow.lean`
depends on `Block.lean`.

Rust reference semantics reproduced explicitly:
* **`Weak` liveness.** `Block.stack()` / `Block.parent_row()` upgrade a `Weak`; they return `None`
  once the last strong reference is gone. Stacks are owned by `RectRow.stacks` only, so clearing a
  row's stacks (`calculate_block_stacks`, `reset_stacks`) drops them: `BlockStack.alive` is set to
  `false` for every cleared stack that no other row lists (`releaseStacks`). Rows are owned by the
  phase's `rows` vector and `rows_storage`; the packing phases (F8b) call `RectRow.drop` when Rust
  drops the last strong reference to a row. `Block.stackOf` / `Block.parentRowOf` honour these
  flags.
* **`RefCell` borrows in `notify_about_node_change`.** A block's mutating method runs under
  `borrow_mut()` of that block; the row reads the other children with `try_borrow()`, uses the
  notifying block's `(width, height)` for the first child it cannot borrow, and returns without
  updating ("defer") when a second child is borrowed. The notifying block is passed as `self?`;
  additional blocks that a caller keeps mutably borrowed in Rust can be listed in
  `RectPackingArena.borrowedBlocks` to reproduce the deferral.
-/
namespace Elk.Alg.RectPacking.Util

open Elk.Graph Elk.Core.Util

/-- Index of a `Block` in `RectPackingArena.blocks` (Rust `BlockRef`). -/
structure BlockId where
  idx : Nat
  deriving BEq, Hashable, Repr, Inhabited, DecidableEq

/-- Index of a `BlockStack` in `RectPackingArena.stacks` (Rust `BlockStackRef`). -/
structure BlockStackId where
  idx : Nat
  deriving BEq, Hashable, Repr, Inhabited, DecidableEq

/-- Index of a `RectRow` in `RectPackingArena.rows` (Rust `RectRowRef`). -/
structure RectRowId where
  idx : Nat
  deriving BEq, Hashable, Repr, Inhabited, DecidableEq

/-- `org.eclipse.elk.alg.rectpacking.util.BlockRow` (Rust `block_row.rs`): a row of rectangles
inside a block. A plain value owned by its `Block`. -/
structure BlockRow where
  x : Float
  y : Float
  width : Float := 0.0
  height : Float := 0.0
  nodeNodeSpacing : Float
  /-- `rects`: the rectangles (child nodes of the laid-out graph) in the row. -/
  rects : Array NodeId := #[]
  deriving Inhabited, Repr

/-- `org.eclipse.elk.alg.rectpacking.util.Block` (Rust `block.rs`): rectangles of similar height
placed in block rows. -/
structure Block where
  smallestRectWidth : Float := Float.posInf
  minWidth : Float := 0.0
  width : Float := 0.0
  minHeight : Float := 0.0
  smallestRectHeight : Float := Float.posInf
  averageHeight : Float := 0.0
  maxHeight : Float := 0.0
  height : Float := 0.0
  children : Array NodeId := #[]
  rows : Array BlockRow := #[]
  x : Float := 0.0
  y : Float := 0.0
  /-- `parent_row` (`Weak`): see `Block.parentRowOf` for the liveness check. -/
  parentRow : Option RectRowId := none
  /-- `stack` (`Weak`): see `Block.stackOf` for the liveness check. -/
  stack : Option BlockStackId := none
  nodeNodeSpacing : Float := 0.0
  fixed : Bool := false
  positionFixed : Bool := false
  deriving Inhabited, Repr

/-- `org.eclipse.elk.alg.rectpacking.util.BlockStack` (Rust `block_stack.rs`): blocks stacked
on top of each other inside a row. -/
structure BlockStack where
  blocks : Array BlockId := #[]
  x : Float
  y : Float
  width : Float := 0.0
  height : Float := 0.0
  nodeNodeSpacing : Float
  /-- `false` once Rust would have dropped the last `Rc` (see the module doc). -/
  alive : Bool := true
  deriving Inhabited, Repr

/-- `org.eclipse.elk.alg.rectpacking.util.RectRow` (Rust `rect_row.rs`): a row of blocks. -/
structure RectRow where
  height : Float := 0.0
  width : Float := 0.0
  y : Float
  nodeNodeSpacing : Float
  children : Array BlockId := #[]
  stacks : Array BlockStackId := #[]
  potentialAdditionalWidthToGetLastBlock : Float := 0.0
  /-- `false` once Rust would have dropped the last `Rc` (see the module doc). -/
  alive : Bool := true
  deriving Inhabited, Repr

/-- The arena of one rectangle packing run. -/
structure RectPackingArena where
  blocks : Array Block := #[]
  stacks : Array BlockStack := #[]
  rows : Array RectRow := #[]
  /-- Blocks a caller keeps mutably borrowed in Rust while another block notifies its row (see
  `RectRow.notifyAboutNodeChange`); normally empty. -/
  borrowedBlocks : Array BlockId := #[]
  /-- `rows_storage` (thread-local `HashMap<usize, Vec<RectRowRef>>`), insertion ordered. -/
  storedRows : Array (Int × Array RectRowId) := #[]
  deriving Inhabited

/-- The rectangle packing monad: arena state over `ElkM`. -/
abbrev RectPackingM := StateRefT RectPackingArena ElkM

namespace RectPackingM

/-- Runs a `RectPackingM` computation on an arena (default: empty). -/
@[inline] def run {α : Type} (x : RectPackingM α) (arena : RectPackingArena := {}) :
    ElkM (α × RectPackingArena) :=
  StateRefT'.run x arena

/-- Runs a `RectPackingM` computation on an empty arena and drops the arena. -/
@[inline] def run' {α : Type} (x : RectPackingM α) : ElkM α := StateRefT'.run' x {}

@[inline] def getBlock (b : BlockId) : RectPackingM Block := do
  return (← getThe RectPackingArena).blocks[b.idx]!
@[inline] def getStack (s : BlockStackId) : RectPackingM BlockStack := do
  return (← getThe RectPackingArena).stacks[s.idx]!
@[inline] def getRow (r : RectRowId) : RectPackingM RectRow := do
  return (← getThe RectPackingArena).rows[r.idx]!

@[inline] def modifyBlock (b : BlockId) (f : Block → Block) : RectPackingM Unit :=
  modifyThe RectPackingArena fun a => { a with blocks := a.blocks.modifyIn b.idx f }
@[inline] def modifyStack (s : BlockStackId) (f : BlockStack → BlockStack) : RectPackingM Unit :=
  modifyThe RectPackingArena fun a => { a with stacks := a.stacks.modifyIn s.idx f }
@[inline] def modifyRow (r : RectRowId) (f : RectRow → RectRow) : RectPackingM Unit :=
  modifyThe RectPackingArena fun a => { a with rows := a.rows.modifyIn r.idx f }

@[inline] def setBlock (b : BlockId) (v : Block) : RectPackingM Unit := modifyBlock b fun _ => v
@[inline] def setStack (s : BlockStackId) (v : BlockStack) : RectPackingM Unit := modifyStack s fun _ => v
@[inline] def setRow (r : RectRowId) (v : RectRow) : RectPackingM Unit := modifyRow r fun _ => v

/-- Adds a block to the arena (`Rc::new(RefCell::new(block))`). -/
def addBlock (b : Block) : RectPackingM BlockId :=
  modifyGetThe RectPackingArena fun a => (⟨a.blocks.size⟩, { a with blocks := a.blocks.push b })
/-- Adds a stack to the arena. -/
def addStack (s : BlockStack) : RectPackingM BlockStackId :=
  modifyGetThe RectPackingArena fun a => (⟨a.stacks.size⟩, { a with stacks := a.stacks.push s })
/-- Adds a row to the arena. -/
def addRow (r : RectRow) : RectPackingM RectRowId :=
  modifyGetThe RectPackingArena fun a => (⟨a.rows.size⟩, { a with rows := a.rows.push r })

/-- Blocks listed as mutably borrowed by the caller (`RectPackingArena.borrowedBlocks`). -/
@[inline] def borrowedBlocks : RectPackingM (Array BlockId) := do
  return (← getThe RectPackingArena).borrowedBlocks

/-- Runs `x` with `blocks` additionally marked as mutably borrowed (Rust: a `borrow_mut()` guard
of those blocks is alive while `x` runs). -/
def withBorrowed {α : Type} (blocks : Array BlockId) (x : RectPackingM α) : RectPackingM α := do
  let saved ← borrowedBlocks
  modifyThe RectPackingArena fun a => { a with borrowedBlocks := a.borrowedBlocks ++ blocks }
  try x finally
    modifyThe RectPackingArena fun a => { a with borrowedBlocks := saved }

end RectPackingM

open RectPackingM

namespace RectRow

/-- `RectRow::new(y, node_node_spacing)`. -/
def new (y nodeNodeSpacing : Float) : RectRow := { y, nodeNodeSpacing }

/-- `notify_about_node_change(locked_child_fallback)`: recomputes the row width (sum of the child
widths plus spacing) and height (maximum child height, `0` without children) from its blocks, in
child order. `self?` is the notifying block (mutably borrowed in Rust) and `lockedChildFallback`
its `(width, height)`: the first borrowed child (the notifying block or one of
`RectPackingArena.borrowedBlocks`) takes the fallback values; a second borrowed child aborts the
update (Rust "defer"). -/
def notifyAboutNodeChange (row : RectRowId) (lockedChildFallback : Option (Float × Float))
    (self? : Option BlockId := none) : RectPackingM Unit := do
  let a ← getThe RectPackingArena
  let r := a.rows[row.idx]!
  let (hasFallback, fallbackWidth, fallbackHeight) := match lockedChildFallback with
    | some (w, h) => (true, w, h)
    | none => (false, 0.0, 0.0)
  let (hasSelf, selfIdx) := match self? with
    | some b => (true, b.idx)
    | none => (false, 0)
  let res := notifyLoop a.blocks r.children a.borrowedBlocks hasSelf selfIdx r.nodeNodeSpacing 0
    hasFallback fallbackWidth fallbackHeight 0.0 Float.negInf
  match res with
  | none => return
  | some (totalStackWidth, newMaxHeight) =>
    let newMaxHeight := if newMaxHeight == Float.negInf then 0.0 else newMaxHeight
    modifyRow row fun x => { x with width := totalStackWidth, height := newMaxHeight }
where
  /-- The child loop (tail recursive, unboxed state; the arena is not modified while it runs).
  `none` is the Rust "defer" (a second borrowed child). -/
  notifyLoop (blocks : Array Block) (children borrowed : Array BlockId) (hasSelf : Bool) (selfIdx : Nat)
      (nodeNodeSpacing : Float) (index : Nat) (hasFallback : Bool) (fallbackWidth fallbackHeight : Float)
      (totalStackWidth newMaxHeight : Float) : Option (Float × Float) :=
    if h : index < children.size then
      let child := children[index]
      let spacing := if index > 0 then nodeNodeSpacing else 0.0
      if (hasSelf && child.idx == selfIdx) || borrowed.contains child then
        if hasFallback then
          notifyLoop blocks children borrowed hasSelf selfIdx nodeNodeSpacing (index + 1) false
            fallbackWidth fallbackHeight (totalStackWidth + (fallbackWidth + spacing))
            (fmax newMaxHeight fallbackHeight)
        else none
      else
        let b := blocks[child.idx]!
        notifyLoop blocks children borrowed hasSelf selfIdx nodeNodeSpacing (index + 1) hasFallback
          fallbackWidth fallbackHeight (totalStackWidth + (b.width + spacing)) (fmax newMaxHeight b.height)
    else some (totalStackWidth, newMaxHeight)
  termination_by children.size - index

/-- Rust drops the last strong reference to the row (it leaves the phase's `rows` vector and
`rows_storage`): `Weak` upgrades of `Block.parent_row` fail from now on. -/
def drop (row : RectRowId) : RectPackingM Unit := modifyRow row fun r => { r with alive := false }

end RectRow

namespace Block

/-- `parent_row()`: the parent row if it is still alive (`Weak::upgrade`). -/
def parentRowOf (b : BlockId) : RectPackingM (Option RectRowId) := do
  match (← getBlock b).parentRow with
  | some r => return if (← getRow r).alive then some r else none
  | none => return none

/-- `stack()`: the stack if it is still alive (`Weak::upgrade`). -/
def stackOf (b : BlockId) : RectPackingM (Option BlockStackId) := do
  match (← getBlock b).stack with
  | some s => return if (← getStack s).alive then some s else none
  | none => return none

/-- `notify_parent()`: `parent_row.notify_about_node_change(Some((width, height)))` if the
parent row is alive. -/
def notifyParent (b : BlockId) : RectPackingM Unit := do
  let blk ← getBlock b
  if let some row ← parentRowOf b then
    RectRow.notifyAboutNodeChange row (some (blk.width, blk.height)) (some b)

end Block

namespace BlockStack

/-- Drops the stacks just removed from `row.stacks` (`stacks.clear()`): every stack that no other
row lists any more becomes dead (`Weak` upgrades in `Block.stack()` fail). -/
def releaseStacks (row : RectRowId) (old : Array BlockStackId) : RectPackingM Unit := do
  let rows := (← getThe RectPackingArena).rows
  for s in old do
    let mut stillOwned := false
    for i in [0:rows.size] do
      if i != row.idx && rows[i]!.stacks.contains s then
        stillOwned := true
        break
    if !stillOwned then
      modifyStack s fun x => { x with alive := false }

end BlockStack

end Elk.Alg.RectPacking.Util
