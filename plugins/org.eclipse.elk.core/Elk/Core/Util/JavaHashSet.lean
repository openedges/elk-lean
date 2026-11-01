import Elk.Core.Util.Java
/-!
# `java.util.HashSet` (iteration order of `java.util.HashMap`, JDK 21)

ELK iterates `HashSet`s of value-hashed objects (`KVector`, `TEdge`, `TTriangle`: `hashCode()` is
computed from the coordinates) and its results depend on that iteration order, which is a pure
function of the hash codes and of the sequence of insertions and removals. `JavaHashSet` reproduces
it exactly: the table of bins (`table[(n - 1) & hash]`, `hash = h ^ (h >>> 16)`), lazy allocation
with 16 bins, doubling when `size` exceeds `0.75 · capacity` (a resize keeps the relative order of
the entries of a bin and splits it into the bins `j` and `j + oldCap`), new entries at the end of
their bin, `clear()` keeping the capacity, and the **tree bins** (`HashMap.TreeNode`): a bin that
reaches 9 entries in a table of at least 64 bins (smaller tables are resized instead) becomes a
red-black tree ordered by hash whose `next` list — the iteration order — is the insertion list with
the tree root moved to the front after every structural change (`moveRootToFront`); new entries are
linked right after their tree parent; removals unlink the entry, rebalance (the CLR deletion with
linkage swapping) and turn the bin back into a plain list when the tree gets too small; a resize
splits a tree bin and untreeifies a half with at most 6 entries. Iterator removal
(`Iterator.remove`, `removeIf`) is `removeNode(…, movable = false)`: no untreeify and no
`moveRootToFront`.

Not reproduced: the order of tree-bin entries with **equal** hash codes but unequal keys, which Java
decides with `System.identityHashCode` (`TreeNode.tieBreakOrder`); here such an entry goes left
(`dir = -1`). The element types are not `Comparable` (`comparableClassFor` is `null`). `equals` is
the Lean `BEq` instance, called as Java calls it: `newKey == existingKey`. Java's identity shortcut
(`p.key == key`) only matters for keys that are not equal to themselves (NaN coordinates).

Checked against `java.util.HashSet` with `scripts/java/HashSetOrder.java` (random operation sequences
of `scripts/gen_hashset_ops.py` with up to six tree bins; one of them is the `lake test` suite
`spv.javaHashSet`).
-/
namespace Elk.Core.Util

/-- Java `Double.hashCode(value)`: `(int) (bits ^ (bits >>> 32))` of `Double.doubleToLongBits`
(canonical NaN). -/
def Float.javaHashCode (x : Float) : UInt32 :=
  let bits : UInt64 := if x.isNaN then 0x7ff8000000000000 else x.toBits
  (bits ^^^ (bits >>> 32)).toUInt32

/-- Java `Integer.reverse(int)`: the bits in reverse order. -/
def UInt32.javaReverse (x : UInt32) : UInt32 :=
  let m1 : UInt32 := 0x55555555
  let m2 : UInt32 := 0x33333333
  let m4 : UInt32 := 0x0F0F0F0F
  let m8 : UInt32 := 0x00FF00FF
  let x := ((x >>> 1) &&& m1) ||| ((x &&& m1) <<< 1)
  let x := ((x >>> 2) &&& m2) ||| ((x &&& m2) <<< 2)
  let x := ((x >>> 4) &&& m4) ||| ((x &&& m4) <<< 4)
  let x := ((x >>> 8) &&& m8) ||| ((x &&& m8) <<< 8)
  (x >>> 16) ||| (x <<< 16)

/-- `hashCode()` of a Java class whose hash is computed from its value (an `int`, as `UInt32`). -/
class JavaHashCode (α : Type) where
  /-- `hashCode()`. -/
  javaHashCode : α → UInt32
  /-- Stands in for Java's identity test `p.key == key` in removals (`HashMap.removeNode`): values
  that are the same object in Java (bitwise equal representation). It only matters for keys that are
  not `equals` to themselves (NaN coordinates); `add` never uses it (distinct Java objects with
  NaN coordinates are distinct set elements). -/
  javaSame : α → α → Bool := fun _ _ => false

/-- `HashMap.TreeNode`: an entry of a tree bin; links are indices into the bin's node array. -/
structure JavaTreeNode (α : Type) where
  /-- The spread hash (`HashMap.hash(key)`). -/
  hash : UInt32
  /-- The key. -/
  key : α
  /-- Red-black tree links. -/
  parent : Option Nat := none
  left : Option Nat := none
  right : Option Nat := none
  /-- The bin list (`next` = iteration order). -/
  prev : Option Nat := none
  next : Option Nat := none
  /-- Node colour. -/
  red : Bool := false
  deriving Inhabited

/-- A bin of the table (`table[i]`). -/
inductive JavaHashBin (α : Type) where
  /-- A plain bin: the `Node` list in `next` order with the spread hashes (`#[]` = `null`). -/
  | chain (entries : Array (UInt32 × α))
  /-- A tree bin: the `TreeNode`s (unlinked ones stay in the array) and the bin head `table[i]`. -/
  | tree (nodes : Array (JavaTreeNode α)) (first : Nat)

instance {α : Type} : Inhabited (JavaHashBin α) := ⟨.chain #[]⟩

namespace JavaTreeBin

variable {α : Type} [Inhabited α]

/-- The node array of a tree bin. -/
abbrev Nodes (α : Type) := Array (JavaTreeNode α)

/-- Java `int` comparison `a > b` of two hashes. -/
@[inline] private def hashGt (a b : UInt32) : Bool := a.toInt32 > b.toInt32

/-! The link setters update a node through an out-of-line updater (PLAN 7.1 items 16, 59): an
inlined record-update lambda in `Array.modify` tests the node's exclusivity before the slot is
cleared and so reallocated the node on every link change; the `@[noinline]` updater runs on the
unshared node and reuses it. -/
@[noinline] private def withParent (v : Option Nat) (n : JavaTreeNode α) : JavaTreeNode α := { n with parent := v }
@[noinline] private def withLeft (v : Option Nat) (n : JavaTreeNode α) : JavaTreeNode α := { n with left := v }
@[noinline] private def withRight (v : Option Nat) (n : JavaTreeNode α) : JavaTreeNode α := { n with right := v }
@[noinline] private def withPrev (v : Option Nat) (n : JavaTreeNode α) : JavaTreeNode α := { n with prev := v }
@[noinline] private def withNext (v : Option Nat) (n : JavaTreeNode α) : JavaTreeNode α := { n with next := v }
@[noinline] private def withRed (v : Bool) (n : JavaTreeNode α) : JavaTreeNode α := { n with red := v }

@[inline] private def setParent (ns : Nodes α) (i : Nat) (v : Option Nat) : Nodes α := ns.modify i (withParent v)
@[inline] private def setLeft (ns : Nodes α) (i : Nat) (v : Option Nat) : Nodes α := ns.modify i (withLeft v)
@[inline] private def setRight (ns : Nodes α) (i : Nat) (v : Option Nat) : Nodes α := ns.modify i (withRight v)
@[inline] private def setPrev (ns : Nodes α) (i : Nat) (v : Option Nat) : Nodes α := ns.modify i (withPrev v)
@[inline] private def setNext (ns : Nodes α) (i : Nat) (v : Option Nat) : Nodes α := ns.modify i (withNext v)
@[inline] private def setRed (ns : Nodes α) (i : Nat) (v : Bool) : Nodes α := ns.modify i (withRed v)
@[inline] private def isRed (ns : Nodes α) : Option Nat → Bool
  | some i => ns[i]!.red
  | none => false

/-- `TreeNode.root()`: follows the parent links. -/
partial def rootOf (ns : Nodes α) (i : Nat) : Nat :=
  match ns[i]!.parent with
  | some p => rootOf ns p
  | none => i

/-- `rotateLeft(root, p)`. -/
def rotateLeft (ns : Nodes α) (root : Option Nat) (p : Option Nat) : Nodes α × Option Nat := Id.run do
  let some p := p | return (ns, root)
  let some r := ns[p]!.right | return (ns, root)
  let mut ns := ns
  let mut root := root
  let rl := ns[r]!.left
  ns := setRight ns p rl
  if let some rl := rl then ns := setParent ns rl (some p)
  let pp := ns[p]!.parent
  ns := setParent ns r pp
  match pp with
  | none => root := some r; ns := setRed ns r false
  | some pp => ns := if ns[pp]!.left == some p then setLeft ns pp (some r) else setRight ns pp (some r)
  ns := setLeft ns r (some p)
  ns := setParent ns p (some r)
  return (ns, root)

/-- `rotateRight(root, p)`. -/
def rotateRight (ns : Nodes α) (root : Option Nat) (p : Option Nat) : Nodes α × Option Nat := Id.run do
  let some p := p | return (ns, root)
  let some l := ns[p]!.left | return (ns, root)
  let mut ns := ns
  let mut root := root
  let lr := ns[l]!.right
  ns := setLeft ns p lr
  if let some lr := lr then ns := setParent ns lr (some p)
  let pp := ns[p]!.parent
  ns := setParent ns l pp
  match pp with
  | none => root := some l; ns := setRed ns l false
  | some pp => ns := if ns[pp]!.right == some p then setRight ns pp (some l) else setLeft ns pp (some l)
  ns := setRight ns l (some p)
  ns := setParent ns p (some l)
  return (ns, root)

/-- The `for (;;)` loop of `balanceInsertion`. -/
private partial def balanceInsertionLoop (ns : Nodes α) (root : Option Nat) (x : Nat) :
    Nodes α × Option Nat := Id.run do
  let mut ns := ns
  let mut root := root
  let some xp := ns[x]!.parent | return (setRed ns x false, some x)
  if !ns[xp]!.red then return (ns, root)
  let some xpp := ns[xp]!.parent | return (ns, root)
  let xppl := ns[xpp]!.left
  if xppl == some xp then
    let xppr := ns[xpp]!.right
    if isRed ns xppr then
      ns := setRed ns xppr.get! false
      ns := setRed ns xp false
      ns := setRed ns xpp true
      return balanceInsertionLoop ns root xpp
    let mut x := x
    let mut xp : Option Nat := some xp
    let mut xpp : Option Nat := some xpp
    if ns[xp.get!]!.right == some x then
      x := xp.get!
      (ns, root) := rotateLeft ns root (some x)
      xp := ns[x]!.parent
      xpp := xp.bind fun i => ns[i]!.parent
    if let some xp' := xp then
      ns := setRed ns xp' false
      if let some xpp' := xpp then
        ns := setRed ns xpp' true
        (ns, root) := rotateRight ns root (some xpp')
    return balanceInsertionLoop ns root x
  else
    if isRed ns xppl then
      ns := setRed ns xppl.get! false
      ns := setRed ns xp false
      ns := setRed ns xpp true
      return balanceInsertionLoop ns root xpp
    let mut x := x
    let mut xp : Option Nat := some xp
    let mut xpp : Option Nat := some xpp
    if ns[xp.get!]!.left == some x then
      x := xp.get!
      (ns, root) := rotateRight ns root (some x)
      xp := ns[x]!.parent
      xpp := xp.bind fun i => ns[i]!.parent
    if let some xp' := xp then
      ns := setRed ns xp' false
      if let some xpp' := xpp then
        ns := setRed ns xpp' true
        (ns, root) := rotateLeft ns root (some xpp')
    return balanceInsertionLoop ns root x

/-- `balanceInsertion(root, x)`: returns the new root. -/
def balanceInsertion (ns : Nodes α) (root : Option Nat) (x : Nat) : Nodes α × Option Nat :=
  balanceInsertionLoop (setRed ns x true) root x

/-- `balanceDeletion(root, x)`: returns the new root. -/
partial def balanceDeletion (ns : Nodes α) (root : Option Nat) (x : Option Nat) :
    Nodes α × Option Nat := Id.run do
  let some xi := x | return (ns, root)
  if x == root then return (ns, root)
  let mut ns := ns
  let mut root := root
  let some xp0 := ns[xi]!.parent | return (setRed ns xi false, some xi)
  if ns[xi]!.red then return (setRed ns xi false, root)
  let mut xp : Option Nat := some xp0
  if ns[xp0]!.left == some xi then
    let mut xpr := ns[xp0]!.right
    if isRed ns xpr then
      ns := setRed ns xpr.get! false
      ns := setRed ns xp0 true
      (ns, root) := rotateLeft ns root (some xp0)
      xp := ns[xi]!.parent
      xpr := xp.bind fun i => ns[i]!.right
    match xpr with
    | none => return balanceDeletion ns root xp
    | some s =>
      let sl := ns[s]!.left
      let sr := ns[s]!.right
      if !isRed ns sr && !isRed ns sl then
        ns := setRed ns s true
        return balanceDeletion ns root xp
      let mut xpr2 : Option Nat := some s
      if !isRed ns sr then
        if let some sl := sl then ns := setRed ns sl false
        ns := setRed ns s true
        (ns, root) := rotateRight ns root (some s)
        xp := ns[xi]!.parent
        xpr2 := xp.bind fun i => ns[i]!.right
      if let some r := xpr2 then
        ns := setRed ns r (match xp with | none => false | some p => ns[p]!.red)
        if let some sr := ns[r]!.right then ns := setRed ns sr false
      if let some p := xp then
        ns := setRed ns p false
        (ns, root) := rotateLeft ns root (some p)
      return balanceDeletion ns root root
  else
    let mut xpl := ns[xp0]!.left
    if isRed ns xpl then
      ns := setRed ns xpl.get! false
      ns := setRed ns xp0 true
      (ns, root) := rotateRight ns root (some xp0)
      xp := ns[xi]!.parent
      xpl := xp.bind fun i => ns[i]!.left
    match xpl with
    | none => return balanceDeletion ns root xp
    | some s =>
      let sl := ns[s]!.left
      let sr := ns[s]!.right
      if !isRed ns sl && !isRed ns sr then
        ns := setRed ns s true
        return balanceDeletion ns root xp
      let mut xpl2 : Option Nat := some s
      if !isRed ns sl then
        if let some sr := sr then ns := setRed ns sr false
        ns := setRed ns s true
        (ns, root) := rotateLeft ns root (some s)
        xp := ns[xi]!.parent
        xpl2 := xp.bind fun i => ns[i]!.left
      if let some l := xpl2 then
        ns := setRed ns l (match xp with | none => false | some p => ns[p]!.red)
        if let some sl := ns[l]!.left then ns := setRed ns sl false
      if let some p := xp then
        ns := setRed ns p false
        (ns, root) := rotateRight ns root (some p)
      return balanceDeletion ns root root

/-- `moveRootToFront(tab, root)`: the root becomes the bin head; returns the new head. -/
def moveRootToFront (ns : Nodes α) (first : Nat) (root : Option Nat) : Nodes α × Nat := Id.run do
  let some root := root | return (ns, first)
  if root == first then return (ns, first)
  let mut ns := ns
  let rp := ns[root]!.prev
  let rn := ns[root]!.next
  if let some rn := rn then ns := setPrev ns rn rp
  if let some rp := rp then ns := setNext ns rp rn
  ns := setPrev ns first (some root)
  ns := setNext ns root (some first)
  ns := setPrev ns root none
  return (ns, root)

/-- The keys of a tree bin in `next` order (with their hashes). -/
partial def entries (ns : Nodes α) (first : Nat) : Array (UInt32 × α) :=
  let rec go (i : Option Nat) (acc : Array (UInt32 × α)) : Array (UInt32 × α) :=
    match i with
    | none => acc
    | some i => go ns[i]!.next (acc.push (ns[i]!.hash, ns[i]!.key))
  go (some first) #[]

/-- `treeify(tab)` of the list starting at `head` (the `next`/`prev` links are set): builds the tree
in list order and moves its root to the front; returns the new head. -/
partial def treeify (ns : Nodes α) (head : Nat) : Nodes α × Nat := Id.run do
  let mut ns := ns
  let mut root : Option Nat := none
  let mut x : Option Nat := some head
  while true do
    let some xi := x | break
    let next := ns[xi]!.next
    ns := setLeft (setRight ns xi none) xi none
    match root with
    | none =>
      ns := setRed (setParent ns xi none) xi false
      root := some xi
    | some r =>
      let h := ns[xi]!.hash
      let mut p := r
      while true do
        let ph := ns[p]!.hash
        -- equal hashes: `tieBreakOrder` (identity hash codes) is not reproducible; go left
        let dirLeft := hashGt ph h || !(hashGt h ph)
        let child := if dirLeft then ns[p]!.left else ns[p]!.right
        match child with
        | some c => p := c
        | none =>
          ns := setParent ns xi (some p)
          ns := if dirLeft then setLeft ns p (some xi) else setRight ns p (some xi)
          (ns, root) := balanceInsertion ns root xi
          break
    x := next
  return moveRootToFront ns head root

/-- `find(h, k, null)` from node `p`; `same` is the key test (`pk == k || k.equals(pk)`). -/
partial def findWith (same : α → α → Bool) (ns : Nodes α) (p : Option Nat) (h : UInt32) (k : α) :
    Option Nat :=
  match p with
  | none => none
  | some pi =>
    let n := ns[pi]!
    if hashGt n.hash h then findWith same ns n.left h k
    else if hashGt h n.hash then findWith same ns n.right h k
    else if same k n.key then some pi
    else if n.left.isNone then findWith same ns n.right h k
    else if n.right.isNone then findWith same ns n.left h k
    else match findWith same ns n.right h k with
      | some q => some q
      | none => findWith same ns n.left h k

/-- `find(h, k, null)` with `equals` only. -/
@[inline] def find [BEq α] (ns : Nodes α) (p : Option Nat) (h : UInt32) (k : α) : Option Nat :=
  findWith (· == ·) ns p h k

/-- The node indices of a tree bin in `next` order. -/
def order (ns : Nodes α) (first : Nat) : Array Nat := Id.run do
  let mut out := #[]
  let mut i : Option Nat := some first
  for _ in [0:ns.size] do
    let some j := i | break
    out := out.push j
    i := ns[j]!.next
  return out

/-- `putTreeVal(map, tab, h, k, v)`: returns the bin and whether the key was added. -/
def putTreeVal [BEq α] (ns : Nodes α) (first : Nat) (h : UInt32) (k : α) :
    Nodes α × Nat × Bool := Id.run do
  let mut ns := ns
  let root := rootOf ns first
  let mut searched := false
  let mut p := root
  while true do
    let n := ns[p]!
    let mut dirLeft := false
    if hashGt n.hash h then dirLeft := true
    else if hashGt h n.hash then dirLeft := false
    else if k == n.key then return (ns, first, false)
    else
      if !searched then
        searched := true
        if (find ns n.left h k).isSome || (find ns n.right h k).isSome then
          return (ns, first, false)
      -- `tieBreakOrder` (identity hash codes): not reproducible, go left
      dirLeft := true
    let child := if dirLeft then n.left else n.right
    match child with
    | some c => p := c
    | none =>
      let xpn := n.next
      let x := ns.size
      ns := ns.push { hash := h, key := k, next := xpn, parent := some p, prev := some p }
      ns := if dirLeft then setLeft ns p (some x) else setRight ns p (some x)
      ns := setNext ns p (some x)
      if let some xpn := xpn then ns := setPrev ns xpn (some x)
      let (ns', root') := balanceInsertion ns (some root) x
      let (ns', first') := moveRootToFront ns' first root'
      return (ns', first', true)
  return (ns, first, false)

/-- A plain bin with the keys of the list starting at `first` (`untreeify`). -/
def untreeify (ns : Nodes α) (first : Option Nat) : JavaHashBin α :=
  match first with
  | none => .chain #[]
  | some f => .chain (entries ns f)

/-- `removeTreeNode(map, tab, movable)` of node `p` of the bin with head `first0`. -/
def removeTreeNode (ns : Nodes α) (first0 : Nat) (p : Nat) (movable : Bool) : JavaHashBin α := Id.run do
  let mut ns := ns
  let succ := ns[p]!.next
  let pred := ns[p]!.prev
  let mut first : Option Nat := some first0
  match pred with
  | none => first := succ
  | some pr => ns := setNext ns pr succ
  if let some s := succ then ns := setPrev ns s pred
  let some firstI := first | return .chain #[]
  let mut root : Option Nat := some (rootOf ns first0)
  let r0 := root.get!
  if movable && (ns[r0]!.right.isNone || ns[r0]!.left.isNone ||
      ns[ns[r0]!.left.get!]!.left.isNone) then
    return untreeify ns first
  let pl := ns[p]!.left
  let pr := ns[p]!.right
  let mut replacement := p
  match pl, pr with
  | some pl, some pr =>
    let mut s := pr
    while true do
      match ns[s]!.left with
      | some sl => s := sl
      | none => break
    let c := ns[s]!.red
    ns := setRed ns s ns[p]!.red
    ns := setRed ns p c
    let sr := ns[s]!.right
    let pp := ns[p]!.parent
    if s == pr then
      ns := setParent ns p (some s)
      ns := setRight ns s (some p)
    else
      let sp := ns[s]!.parent
      ns := setParent ns p sp
      if let some sp := sp then
        ns := if ns[sp]!.left == some s then setLeft ns sp (some p) else setRight ns sp (some p)
      ns := setRight ns s (some pr)
      ns := setParent ns pr (some s)
    ns := setLeft ns p none
    ns := setRight ns p sr
    if let some sr := sr then ns := setParent ns sr (some p)
    ns := setLeft ns s (some pl)
    ns := setParent ns pl (some s)
    ns := setParent ns s pp
    match pp with
    | none => root := some s
    | some pp => ns := if ns[pp]!.left == some p then setLeft ns pp (some s) else setRight ns pp (some s)
    replacement := sr.getD p
  | some pl, none => replacement := pl
  | none, some pr => replacement := pr
  | none, none => replacement := p
  if replacement != p then
    let pp := ns[p]!.parent
    ns := setParent ns replacement pp
    match pp with
    | none =>
      root := some replacement
      ns := setRed ns replacement false
    | some pp =>
      ns := if ns[pp]!.left == some p then setLeft ns pp (some replacement)
        else setRight ns pp (some replacement)
    ns := setParent (setRight (setLeft ns p none) p none) p none
  let mut r := root
  if !ns[p]!.red then
    (ns, r) := balanceDeletion ns root (some replacement)
  if replacement == p then
    let pp := ns[p]!.parent
    ns := setParent ns p none
    if let some pp := pp then
      if ns[pp]!.left == some p then ns := setLeft ns pp none
      else if ns[pp]!.right == some p then ns := setRight ns pp none
  let mut firstI := firstI
  if movable then
    (ns, firstI) := moveRootToFront ns firstI r
  return .tree ns firstI

/-- `split(map, tab, index, bit)` of a tree bin: the lower and the upper bin. -/
def split (ns : Nodes α) (first : Nat) (bit : UInt32) : JavaHashBin α × JavaHashBin α := Id.run do
  let order := order ns first
  let lo := order.filter fun i => ns[i]!.hash &&& bit == 0
  let hi := order.filter fun i => ns[i]!.hash &&& bit != 0
  let mkBin (part : Array Nat) (other : Array Nat) : JavaHashBin α := Id.run do
    if part.isEmpty then return .chain #[]
    if part.size ≤ 6 then return .chain (part.map fun i => (ns[i]!.hash, ns[i]!.key))
    if other.isEmpty then return .tree ns first  -- whole bin on this side: tree kept as is
    -- relink the part (fresh nodes in list order) and treeify it
    let mut nodes : Nodes α := #[]
    for k in [0:part.size] do
      let n := ns[part[k]!]!
      nodes := nodes.push {
        hash := n.hash, key := n.key,
        prev := if k == 0 then none else some (k - 1),
        next := if k + 1 < part.size then some (k + 1) else none }
    let (nodes', head) := treeify nodes 0
    return .tree nodes' head
  return (mkBin lo hi, mkBin hi lo)

end JavaTreeBin

/-- `java.util.HashSet<E>` (a `java.util.HashMap<E, Object>` with the default load factor 0.75):
the bins in table order; see the module doc. -/
structure JavaHashSet (α : Type) where
  /-- `table` (`#[]` while unallocated). -/
  table : Array (JavaHashBin α) := #[]
  /-- `size`. -/
  size : Nat := 0
  /-- `threshold` (resize when `size` exceeds it). -/
  threshold : Nat := 0
  deriving Inhabited

namespace JavaHashSet

variable {α : Type} [Inhabited α] [BEq α] [JavaHashCode α]

/-- `HashMap.hash(key)`: `h ^ (h >>> 16)`. -/
@[inline] def spread (h : UInt32) : UInt32 := h ^^^ (h >>> 16)

/-- `new HashSet<>()`. -/
def empty : JavaHashSet α := {}

/-- `isEmpty()`. -/
@[inline] def isEmpty (s : JavaHashSet α) : Bool := s.size == 0

/-- The elements in iteration order (`iterator()`, `toArray()`, `new ArrayList<>(set)`). -/
def toArray (s : JavaHashSet α) : Array α := Id.run do
  let mut out : Array α := Array.mkEmpty s.size
  for b in s.table do
    match b with
    | .chain es => for e in es do out := out.push e.2
    | .tree ns first => for e in JavaTreeBin.entries ns first do out := out.push e.2
  return out

/-- `resize()`: allocates 16 bins or doubles the table (`DEFAULT_LOAD_FACTOR = 0.75`). -/
def resize (s : JavaHashSet α) : JavaHashSet α := Id.run do
  let oldCap := s.table.size
  if oldCap == 0 then
    return { s with table := Array.replicate 16 (.chain #[]), threshold := 12 }
  let newCap := oldCap * 2
  let newThr := if oldCap ≥ 16 then s.threshold * 2 else (newCap * 3) / 4
  let mut tab : Array (JavaHashBin α) := Array.replicate newCap (.chain #[])
  let bit : UInt32 := oldCap.toUInt32
  for j in [0:oldCap] do
    match s.table[j]! with
    | .chain es =>
      if es.isEmpty then continue
      tab := tab.set! j (.chain (es.filter fun e => e.1 &&& bit == 0))
      tab := tab.set! (j + oldCap) (.chain (es.filter fun e => e.1 &&& bit != 0))
    | .tree ns first =>
      if ns[first]!.next.isNone then
        -- a single entry (`e.next == null`) moves as it is, still a tree node
        let k := if ns[first]!.hash &&& bit == 0 then j else j + oldCap
        tab := tab.set! k (.tree ns first)
      else
        let (lo, hi) := JavaTreeBin.split ns first bit
        tab := tab.set! j lo
        tab := tab.set! (j + oldCap) hi
  return { s with table := tab, threshold := newThr }

/-- `treeifyBin(tab, hash)`: resizes a table with fewer than 64 bins, else turns bin `i` into a tree. -/
private def treeifyBin (s : JavaHashSet α) (i : Nat) : JavaHashSet α :=
  if s.table.size < 64 then s.resize
  else
    match s.table[i]! with
    | .chain es =>
      let nodes : JavaTreeBin.Nodes α := Id.run do
        let mut nodes := #[]
        for k in [0:es.size] do
          nodes := nodes.push {
            hash := es[k]!.1, key := es[k]!.2,
            prev := if k == 0 then none else some (k - 1),
            next := if k + 1 < es.size then some (k + 1) else none }
        return nodes
      let (nodes, head) := JavaTreeBin.treeify nodes 0
      { s with table := s.table.set! i (.tree nodes head) }
    | .tree .. => s

/-- `add(e)`: `true` if the element was not yet in the set (`putVal`). -/
def add (s : JavaHashSet α) (k : α) : JavaHashSet α × Bool := Id.run do
  let h := spread (JavaHashCode.javaHashCode k)
  let mut s := if s.table.isEmpty then s.resize else s
  let n := s.table.size
  let i := (h &&& (n - 1).toUInt32).toNat
  match s.table[i]! with
  | .chain es =>
    if es.any fun e => e.1 == h && k == e.2 then return (s, false)
    let len := es.size + 1
    s := { s with table := s.table.modify i fun b => match b with
      | .chain es => .chain (es.push (h, k))
      | b => b }
    if len ≥ 9 then s := treeifyBin s i
  | .tree ns first =>
    s := { s with table := s.table.set! i default }
    let (ns, first, added) := JavaTreeBin.putTreeVal ns first h k
    s := { s with table := s.table.set! i (.tree ns first) }
    if !added then return (s, false)
  s := { s with size := s.size + 1 }
  if s.size > s.threshold then s := s.resize
  return (s, true)

/-- `addAll(c)`: `add` of every element in order. -/
def addAll (s : JavaHashSet α) (c : Array α) : JavaHashSet α :=
  c.foldl (fun s k => (s.add k).1) s

/-- `contains(o)` (`getNode`). -/
def contains (s : JavaHashSet α) (k : α) : Bool :=
  if s.table.isEmpty then false
  else
    let h := spread (JavaHashCode.javaHashCode k)
    let i := (h &&& (s.table.size - 1).toUInt32).toNat
    match s.table[i]! with
    | .chain es => es.any fun e => e.1 == h && k == e.2
    | .tree ns first =>
      let f := ns[first]!
      (f.hash == h && k == f.key) ||
        (JavaTreeBin.find ns (some (JavaTreeBin.rootOf ns first)) h k).isSome

/-- `removeNode(hash(k), k, null, false, movable)`: the key test is Java's
`p.key == key || key.equals(p.key)` (`javaSame` for the identity). -/
def removeNode (s : JavaHashSet α) (k : α) (movable : Bool) : JavaHashSet α × Bool := Id.run do
  if s.table.isEmpty then return (s, false)
  let h := spread (JavaHashCode.javaHashCode k)
  let i := (h &&& (s.table.size - 1).toUInt32).toNat
  let same (a b : α) : Bool := JavaHashCode.javaSame b a || a == b
  match s.table[i]! with
  | .chain es =>
    match es.findIdx? fun e => e.1 == h && same k e.2 with
    | none => return (s, false)
    | some j =>
      let s := { s with table := s.table.set! i default }
      let bin : JavaHashBin α := .chain (es.eraseIdxIfInBounds j)
      return ({ s with table := s.table.set! i bin, size := s.size - 1 }, true)
  | .tree ns first =>
    let f := ns[first]!
    let node :=
      if f.hash == h && same k f.key then some first
      else if f.next.isSome then JavaTreeBin.findWith same ns (some (JavaTreeBin.rootOf ns first)) h k
      else none
    let some p := node | return (s, false)
    let s := { s with table := s.table.set! i default }
    let bin := JavaTreeBin.removeTreeNode ns first p movable
    return ({ s with table := s.table.set! i bin, size := s.size - 1 }, true)

/-- `remove(o)`. -/
@[inline] def remove (s : JavaHashSet α) (k : α) : JavaHashSet α × Bool := s.removeNode k true

/-- `removeIf(filter)` / `Iterator.remove()` in iteration order: removes the elements satisfying
`p`, each at its own position (`removeNode(…, movable = false)` of the iterator's current node: no
untreeify, no `moveRootToFront`). -/
def removeIf (s : JavaHashSet α) (p : α → Bool) : JavaHashSet α := Id.run do
  let mut s := s
  for i in [0:s.table.size] do
    match s.table[i]! with
    | .chain es =>
      if es.any (p ·.2) then
        let kept := es.filter fun e => !p e.2
        s := { s with table := s.table.set! i default }
        s := { s with table := s.table.set! i (.chain kept), size := s.size - (es.size - kept.size) }
    | .tree ns first =>
      let order := JavaTreeBin.order ns first
      if order.any fun j => p ns[j]!.key then
        s := { s with table := s.table.set! i default }
        let mut bin : JavaHashBin α := .tree ns first
        let mut removed := 0
        for j in order do
          match bin with
          | .tree ns' first' =>
            if p ns'[j]!.key then
              bin := JavaTreeBin.removeTreeNode ns' first' j false
              removed := removed + 1
          | .chain _ => pure ()
        s := { s with table := s.table.set! i bin, size := s.size - removed }
  return s

/-- `AbstractSet.removeAll(c)` for a list `c` (`List.contains` = `equals`): if the set is larger,
`remove` of every element of `c`; otherwise iterator removal of the elements contained in `c`. -/
def removeAll (s : JavaHashSet α) (c : Array α) : JavaHashSet α :=
  if s.size > c.size then c.foldl (fun s k => (s.remove k).1) s
  else s.removeIf fun k => c.any fun x => k == x

/-- `clear()`: empties the bins, keeps the capacity. -/
def clear (s : JavaHashSet α) : JavaHashSet α :=
  if s.size > 0 then { s with table := Array.replicate s.table.size (.chain #[]), size := 0 } else s

end JavaHashSet

end Elk.Core.Util
