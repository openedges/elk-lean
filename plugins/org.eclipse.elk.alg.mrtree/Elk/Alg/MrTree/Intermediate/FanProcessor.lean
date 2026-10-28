import Std.Data.HashMap
import Elk.Alg.MrTree.Graph.TArena
/-!
# `org.eclipse.elk.alg.mrtree.intermediate.FanProcessor`

Port of `intermediate/fan_processor.rs` (elk-rs) / Java `FanProcessor`: computes the `FAN` (maximal
number of descendants of a node on one level) and `DESCENDANTS` (number of nodes in the subtree, the
node included) of every node.

## The Java/Rust computation (`processStrings`)

Java derives both values from hierarchical identifier strings (`ID`). Level by level, starting at
the first `ROOT` node, every node gets the identifier `<parent id><index>` where the index within
the sibling group is zero padded to `floor(log10(level size)) + 1` digits; the children temporarily
carry the parent's identifier. The prefixes of all identifiers of a level are counted (Rust iterates
only `0 .. last_id.len() - digits` prefix lengths, using the last identifier of the level) and merged
into the global fan (maximum) and descendant (sum) maps; every node of the graph finally looks its
values up under its own identifier. This costs `O(level size × id length²)` per level — cubic in the
depth (a chain of 2,000 nodes took 80 s). `processStrings` keeps that computation verbatim.

## The array computation (`process`)

When the breadth-first walk from the root reaches every node at most once (the graph below the
root is a tree, which `DFSTreeifyer` + `RootProcessor` guarantee unless the search order is `BFS`,
whose search can keep two edges into one node), the identifiers are unique, have the same length on
a level and the identifier of a level-`k` ancestor is the length-`k` prefix of its descendants'
identifiers, so the maps hold exactly:

* `DESCENDANTS(v) = 1 + |subtree(v) \ {v}|`;
* `FAN(v) = max over d ≥ 1 of |descendants of v at depth d below v|` (0 for a leaf);

(prefixes that end inside a digit block are never the identifier of a node). `process` computes
these in one pass per tree: the depth profiles of the subtrees are merged bottom-up along the
breadth-first order, every node inheriting the profile array of its tallest child and adding the
other children's profiles into it (long-path merging, linear in the number of nodes). It falls back
to `processStrings` whenever the walk reaches a node twice (DAG, cycle back to the root), a child's
`id` is outside the graph's node index range (the duplicate test is indexed by `id`, which
`DFSTreeifyer.init` sets to the node's list index; the `SUPER_ROOT`/`DUMMY_ROOT` with id 0 is the
root and tested by identity), or a node of the graph already carries an identifier (only a previous
run would leave one), so both functions write the same `FAN`/`DESCENDANTS` for every input. The
identifier strings themselves are only written by `processStrings`; nothing else reads them.
-/
namespace Elk.Alg.MrTree.Intermediate

open Elk.Core.Util Elk.Alg.MrTree.Graph

namespace FanProcessor

/-- `FanProcessor::format_right(value, len)`: `value` left padded with `0` to `len` characters. -/
def formatRight (value : Int) (len : Nat) : String := Id.run do
  let mut s := toString value
  while s.length < len do
    s := "0" ++ s
  return s

/-- One level of `calculate_fan`: assigns the identifiers of the level, returns the next level and
the updated global fan and descendant maps. -/
private def calculateFanLevel (currentLevel : Array TNodeId) (gloFan gloDesc : Std.HashMap String Int) :
    MrTreeM (Array TNodeId × Std.HashMap String Int × Std.HashMap String Int) := do
  let mut nextLevel : Array TNodeId := #[]
  let digits := (Float.ofNat currentLevel.size).log10.floor.toUInt64.toNat + 1
  let mut lastParentId : Option String := none
  let mut index : Int := 0
  let mut lastId := ""
  let mut cachedIds : Array String := #[]
  for node in currentLevel do
    let parentId := (← MrTreeM.getNode node).internal.idString
    if lastParentId != some parentId then
      lastParentId := some parentId
      index := 0
    let id := if parentId.isEmpty then formatRight index digits else parentId ++ formatRight index digits
    index := index + 1
    lastId := id
    cachedIds := cachedIds.push id
    MrTreeM.modifyNode node fun n => { n with internal.idString := id }
    for child in (← MrTreeM.children node) do
      MrTreeM.modifyNode child fun n => { n with internal.idString := lastId }
      nextLevel := nextLevel.push child
  -- prefix computation
  let mut localFan : Std.HashMap String Int := {}
  if digits > 0 && lastId.length >= digits then
    for i in [0:lastId.length - digits] do
      for id in cachedIds do
        let pre := String.ofList (id.toList.take (i + 1))
        localFan := localFan.insert pre (localFan.getD pre 0 + 1)
  let (gloFan, gloDesc) := localFan.fold (init := (gloFan, gloDesc)) fun (fan, desc) key value =>
    let desc := desc.insert key (desc.getD key 0 + value)
    let fan := if fan.getD key 0 < value then fan.insert key value else fan
    (fan, desc)
  return (nextLevel, gloFan, gloDesc)

/-- The identifier-string computation of Java/Rust `FanProcessor::process` (see the module doc);
`process` uses it for the graphs below whose root the breadth-first walk is not a tree. -/
def processStrings (graph : TGraphId) : MrTreeM Unit := do
  let nodes := (← MrTreeM.getGraph graph).nodes
  let a ← get
  let root := nodes.find? fun n => (a.node n).internal.root
  let mut gloFan : Std.HashMap String Int := {}
  let mut gloDesc : Std.HashMap String Int := {}
  let mut currentLevel : Array TNodeId := match root with
    | some r => #[r]
    | none => #[]
  while !currentLevel.isEmpty do
    let (next, fan, desc) ← calculateFanLevel currentLevel gloFan gloDesc
    currentLevel := next
    gloFan := fan
    gloDesc := desc
  for node in (← MrTreeM.getGraph graph).nodes do
    MrTreeM.modifyNode node fun n =>
      let key := n.internal.idString
      { n with internal.fan := gloFan.getD key 0, internal.descendants := gloDesc.getD key 0 + 1 }

/-- The breadth-first walk from the root (entry 0): the entries in visiting order (the Java levels
concatenated), the position of the first child entry of every entry (the children of entry `i` are
the entries `childStart[i] ..< childStart[i + 1]`, the last ones end at the entry count) and, by
`id`, `1 +` the entry of every reached non-root node (0 = not reached). `none` when the walk reaches
a node twice or a child's `id` is outside `0 ..< size`. -/
private def treeWalk (a : TArena) (root : TNodeId) (size : Nat) :
    Option (Array TNodeId × Array Nat × Array Nat) := Id.run do
  let mut entryOf : Array Nat := Array.replicate size 0
  let mut order : Array TNodeId := #[root]
  let mut childStart : Array Nat := #[]
  let mut head := 0
  while h : head < order.size do
    let v := order[head]
    head := head + 1
    childStart := childStart.push order.size
    for c in (a.node v).directChildren do
      if c == root then return none
      let id := (a.node c).id
      if id < 0 then return none
      let k := id.toNat
      if hk : k < entryOf.size then
        if entryOf[k] != 0 then return none
        entryOf := entryOf.set k (order.size + 1)
        order := order.push c
      else return none
  return some (order, childStart, entryOf)

/-- Adds the profile `q` into `p` aligned at their ends (`p[off + k] += q[k]` from `k` on); returns
`p` and the maximum of `best` and the new entries. -/
private def addProfile (p q : Array Nat) (off k best : Nat) : Array Nat × Nat :=
  if h : k < q.size then
    let v := p[off + k]! + q[k]
    addProfile (p.set! (off + k) v) q off (k + 1) (if v > best then v else best)
  else (p, best)
  termination_by q.size - k

/-- `FAN` and `DESCENDANTS - 1` of every entry of a tree walk (see the module doc): bottom-up over
the entries, the depth profile of an entry (counts by depth, deepest first, the entry itself last)
is the profile of its tallest child plus the other children's profiles, then `1` appended. -/
private def fanAndDescendants (childStart : Array Nat) : Array Nat × Array Nat := Id.run do
  let m := childStart.size
  let mut prof : Array (Array Nat) := Array.replicate m #[]
  let mut fan : Array Nat := Array.replicate m 0
  let mut desc : Array Nat := Array.replicate m 0
  for j in [0:m] do
    let i := m - 1 - j
    let cs := childStart[i]!
    let ce := if i + 1 < m then childStart[i + 1]! else m
    if cs == ce then
      prof := prof.set! i #[1]
    else
      let mut tall := cs
      for c in [cs + 1:ce] do
        if prof[c]!.size > prof[tall]!.size then tall := c
      let (p, prof') := prof.swapAt! tall #[]
      prof := prof'
      let mut p := p
      let mut best := max 1 fan[tall]!
      let mut d := desc[tall]! + 1
      for c in [cs:ce] do
        if c != tall then
          let (q, prof') := prof.swapAt! c #[]
          prof := prof'
          d := d + desc[c]! + 1
          let (p', best') := addProfile p q (p.size - q.size) 0 best
          p := p'
          best := best'
      fan := fan.set! i best
      desc := desc.set! i d
      prof := prof.set! i (p.push 1)
  return (fan, desc)

/-- The `(FAN, DESCENDANTS - 1)` of every node of the graph by the array computation, `none` when
`processStrings` must run (see the module doc). Nodes the walk does not reach get `(0, 0)`, like
the missing map entries of Java. -/
private def treeValues (a : TArena) (nodes : Array TNodeId) : Option (Array (Nat × Nat)) := Id.run do
  if nodes.any fun n => !(a.node n).internal.idString.isEmpty then return none
  let some root := nodes.find? fun n => (a.node n).internal.root
    | return some (nodes.map fun _ => (0, 0))
  let some (order, childStart, entryOf) := treeWalk a root nodes.size | return none
  let (fan, desc) := fanAndDescendants childStart
  return some <| nodes.map fun n =>
    let e := if n == root then some 0 else
      let id := (a.node n).id
      if id < 0 then none else
        match entryOf[id.toNat]? with
        | some k => if k != 0 && order[k - 1]? == some n then some (k - 1) else none
        | none => none
    match e with
    | some e => (fan[e]!, desc[e]!)
    | none => (0, 0)

/-- `FanProcessor::process` (see the module doc for the two computations). -/
def process (graph : TGraphId) (monitor : ProgressMonitor) : MrTreeM Unit := do
  discard <| monitor.begin "Processor compute fanout" 1.0
  let nodes := (← MrTreeM.getGraph graph).nodes
  let result := treeValues (← get) nodes
  match result with
  | some values =>
    modify fun a => Id.run do
      let mut a := a
      for h : i in [0:nodes.size] do
        let (f, d) := values[i]?.getD (0, 0)
        a := a.modifyNode nodes[i] fun x =>
          { x with internal.fan := (f : Int), internal.descendants := (d : Int) + 1 }
      return a
  | none => processStrings graph
  monitor.done

/-- The `FanProcessor` (`IntermediateProcessorStrategy.FAN_PROC`). -/
def processor : TreeProcessor := { name := "FanProcessor", process }

end FanProcessor

end Elk.Alg.MrTree.Intermediate
