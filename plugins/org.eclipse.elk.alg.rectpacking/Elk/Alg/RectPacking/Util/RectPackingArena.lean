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

Java reference semantics (ELK Java is the reference; elk-rs used `Weak`/`RefCell` and differed):
* **Strong references.** A block keeps its parent row and its stack (`Block.getParentRow()`,
  `getStack()`) after the row left the phase's row list or the row's stacks were reset; elk-rs held
  them as `Weak` and treated a dropped row/stack as absent (`None`). Java's stale references matter:
  a block placed beside its block from a removed next row still has that row as parent, so the
  repeated compaction of the row sees it as coming from the next row (`wasFromNextRow`) and adds it
  to the row a second time.
* **No borrows.** `RectRow.notifyAboutNodeChange` recomputes the row from all its blocks; elk-rs
  skipped the update ("defer") when a block was listed twice (a second `RefCell` borrow).
-/
/-! Float literals as global constants (FL): inside branches, loops and specialised code the compiler
shares a literal's `Nat`/`Bool` arguments with unrelated variables (CSE) and then parses it on every
evaluation (`FastFloat.ofScientificImpl`); a top-level constant is a load (PLAN §7.1 items 17, 22). -/
private def fl0p0 : Float := 0.0

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
  width : Float := fl0p0
  height : Float := fl0p0
  nodeNodeSpacing : Float
  /-- `rects`: the rectangles (child nodes of the laid-out graph) in the row. -/
  rects : Array NodeId := #[]
  deriving Inhabited, Repr

/-- `org.eclipse.elk.alg.rectpacking.util.Block` (Rust `block.rs`): rectangles of similar height
placed in block rows. -/
structure Block where
  smallestRectWidth : Float := Float.posInf
  minWidth : Float := fl0p0
  width : Float := fl0p0
  minHeight : Float := fl0p0
  smallestRectHeight : Float := Float.posInf
  averageHeight : Float := fl0p0
  maxHeight : Float := fl0p0
  height : Float := fl0p0
  children : Array NodeId := #[]
  rows : Array BlockRow := #[]
  x : Float := fl0p0
  y : Float := fl0p0
  /-- `parentRow` (a strong reference, see the module doc). -/
  parentRow : Option RectRowId := none
  /-- `stack` (a strong reference, see the module doc). -/
  stack : Option BlockStackId := none
  nodeNodeSpacing : Float := fl0p0
  fixed : Bool := false
  positionFixed : Bool := false
  deriving Inhabited, Repr

/-- `org.eclipse.elk.alg.rectpacking.util.BlockStack` (Rust `block_stack.rs`): blocks stacked
on top of each other inside a row. -/
structure BlockStack where
  blocks : Array BlockId := #[]
  x : Float
  y : Float
  width : Float := fl0p0
  height : Float := fl0p0
  nodeNodeSpacing : Float
  deriving Inhabited, Repr

/-- `org.eclipse.elk.alg.rectpacking.util.RectRow` (Rust `rect_row.rs`): a row of blocks. -/
structure RectRow where
  height : Float := fl0p0
  width : Float := fl0p0
  y : Float
  nodeNodeSpacing : Float
  children : Array BlockId := #[]
  stacks : Array BlockStackId := #[]
  potentialAdditionalWidthToGetLastBlock : Float := fl0p0
  deriving Inhabited, Repr

/-- The arena of one rectangle packing run. -/
structure RectPackingArena where
  blocks : Array Block := #[]
  stacks : Array BlockStack := #[]
  rows : Array RectRow := #[]
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

end RectPackingM

open RectPackingM

namespace RectRow

/-- `RectRow::new(y, node_node_spacing)`. -/
def new (y nodeNodeSpacing : Float) : RectRow := { y, nodeNodeSpacing }

/-- `notifyAboutNodeChange()`: recomputes the row width (sum of the block widths plus spacing) and
height (`Math.max` from `Double.NEGATIVE_INFINITY`: `-∞` without blocks) from its blocks, in list
order (a block listed twice counts twice). -/
def notifyAboutNodeChange (row : RectRowId) : RectPackingM Unit := do
  let a ← getThe RectPackingArena
  let r := a.rows[row.idx]!
  let (totalStackWidth, newMaxHeight) := notifyLoop a.blocks r.children r.nodeNodeSpacing 0 fl0p0 Float.negInf
  modifyRow row fun x => { x with width := totalStackWidth, height := newMaxHeight }
where
  /-- The block loop (tail recursive, unboxed state). -/
  notifyLoop (blocks : Array Block) (children : Array BlockId) (nodeNodeSpacing : Float) (index : Nat)
      (totalStackWidth newMaxHeight : Float) : Float × Float :=
    if h : index < children.size then
      let b := blocks[children[index].idx]!
      let spacing := if index > 0 then nodeNodeSpacing else fl0p0
      notifyLoop blocks children nodeNodeSpacing (index + 1) (totalStackWidth + (b.width + spacing))
        (javaMax newMaxHeight b.height)
    else (totalStackWidth, newMaxHeight)
  termination_by children.size - index

end RectRow

namespace Block

/-- `getParentRow()`. -/
def parentRowOf (b : BlockId) : RectPackingM (Option RectRowId) := do
  return (← getBlock b).parentRow

/-- `getStack()`. -/
def stackOf (b : BlockId) : RectPackingM (Option BlockStackId) := do
  return (← getBlock b).stack

/-- `parentRow.notifyAboutNodeChange()`. -/
def notifyParent (b : BlockId) : RectPackingM Unit := do
  if let some row ← parentRowOf b then
    RectRow.notifyAboutNodeChange row

end Block

end Elk.Alg.RectPacking.Util
