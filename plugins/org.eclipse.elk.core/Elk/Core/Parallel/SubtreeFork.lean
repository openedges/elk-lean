import Elk.Graph
import Elk.Core.Options.CoreOptions
import Elk.Core.Parallel.Settings
/-!
# Sub-tree forks of the `ElkGraph` arena (elk-lean addition, agent PAR)

The data side of the parallel sibling layout (`Elk.Core.Parallel.SiblingLayout`,
`docs/parallel-layout.md`): which arena elements belong to which sibling sub-graph, whether a sibling
is independent of the others, and how the arenas of the parallel chunks are checked and merged.

A task gets the whole arena value (`ElkGraph`, five persistent arrays); the first write to an array
or an element copies it (Lean's reference counting), so the original arena stays intact and every
chunk sees exactly the state before the sibling loop.

## Domains and the eligibility test
For the units (the children `C₀ … Cₖ` of the node whose sibling loop is parallelised) the
`Ownership` tables give every element its unit (`u + 1`) or `0`:
* nodes: `sub(Cᵤ)` = `Cᵤ` and its descendants; ports: their ports;
* edges: contained in a node of `sub(Cᵤ)`, or with all end points (nodes, or ports by their parent
  node) in `sub(Cᵤ)` and at least one end point — this includes the inside self loops of `Cᵤ`,
  contained in its parent;
* labels (recursively, labels of labels): of owned nodes, ports and edges; sections: of owned edges.
A unit is *closed* (eligible) when every edge contained in `sub(Cᵤ)` or with an end point strictly
inside `Cᵤ` (a descendant or a descendant's port) has all its end points in `sub(Cᵤ)`: no
hierarchy-crossing edge leaves the sub-tree. Edges at `Cᵤ` itself or its own ports may lead anywhere
(they belong to the parent's layout). Domains of distinct units are disjoint (see the doc).

The algorithms laying out the sub-tree matter as well (`algorithmClass`, from the audit in
`docs/parallel-layout.md`): the tree walks of radial and vertiflex follow every outgoing edge and map
ports to their node without a hierarchy check, so an edge between a descendant of `Cᵤ` and `Cᵤ` (or
one of its ports) lets them walk out of the sub-tree through `Cᵤ` (to siblings and the parent); disco
and spore delegate to such algorithms. A sub-tree with one of them is eligible only without such an
edge (`rootLinked`). A sub-tree with an algorithm that is not in either list (e.g. one registered by a
test) is never eligible.

## Check and merge
`checkChunk` / `mergeChunk` compare the chunk's result arena with the original element by element:
an element outside the chunk's domains must still be the *same object* (`withPtrEq`; the fallback
compares a lossless fingerprint, only evaluated when the pointers differ). Any other write makes the
caller fall back to the sequential loop on the untouched original arena. Elements of the chunk's
domains are copied into the merged arena; elements the chunk created (appended, e.g. edge
sections) are appended in chunk order and renumbered (`Remap`): in the sequential run they would
have been created after those of the earlier chunks.
-/
namespace Elk.Core.Parallel

open Elk.Graph Elk.Core.Math

/-! ## Ownership -/

/-- Owner tables of one sibling loop: `0` = no unit, `u + 1` = unit `u`; per unit the eligibility
test (`closed`). The element tables have the sizes of the arena they were computed on. -/
structure Ownership where
  nodes : Array Nat
  ports : Array Nat
  edges : Array Nat
  labels : Array Nat
  sections : Array Nat
  closed : Array Bool
  deriving Inhabited

/-- The owner of an edge end point. -/
@[inline] def Ownership.ownerOf (nodes ports : Array Nat) : ConnectableId → Nat
  | .node n => nodes[n.idx]?.getD 0
  | .port p => ports[p.idx]?.getD 0

/-- The node of an edge end point (a port's parent). -/
@[inline] def endPointNode (g : ElkGraph) : ConnectableId → Option NodeId
  | .node n => some n
  | .port p => (g.ports[p.idx]?).bind (·.parent)

/-- Per-edge end point summary: owner of the first end point, whether all have that owner, the
number of end points and the owners that have an end point strictly inside their unit root. -/
private structure EndPointScan where
  first : Nat := 0
  same : Bool := true
  count : Nat := 0
  inside : Array Nat := #[]
  /-- Owners with an end point at their unit root (the root node or one of its ports). -/
  atRoot : Array Nat := #[]

private def scanEndPoints (g : ElkGraph) (units : Array NodeId) (nodes ports : Array Nat)
    (eps : Array ConnectableId) (s : EndPointScan) : EndPointScan := Id.run do
  let mut s := s
  for c in eps do
    let o := Ownership.ownerOf nodes ports c
    if s.count == 0 then s := { s with first := o }
    else if o != s.first then s := { s with same := false }
    s := { s with count := s.count + 1 }
    if o != 0 then
      let strictlyInside := match endPointNode g c with
        | some n => some n != units[o - 1]?
        | none => false
      if strictlyInside && !s.inside.contains o then s := { s with inside := s.inside.push o }
      if !strictlyInside && !s.atRoot.contains o then s := { s with atRoot := s.atRoot.push o }
  return s

/-- Algorithms whose layout of a node stays inside the node's sub-tree for every eligible unit (audit). -/
def subtreeLocalAlgorithms : Array String :=
  #["org.eclipse.elk.layered", "org.eclipse.elk.force", "org.eclipse.elk.stress", "org.eclipse.elk.mrtree",
    "org.eclipse.elk.rectpacking", "org.eclipse.elk.topdownpacking", "org.eclipse.elk.box",
    "org.eclipse.elk.fixed", "org.eclipse.elk.random"]

/-- Algorithms whose tree walks leave the sub-tree through an edge between a descendant and the
unit root (radial, vertiflex) or that delegate to any algorithm (disco, spore). -/
def rootWalkingAlgorithms : Array String :=
  #["org.eclipse.elk.radial", "org.eclipse.elk.vertiflex", "org.eclipse.elk.disco",
    "org.eclipse.elk.sporeOverlap", "org.eclipse.elk.sporeCompaction"]

/-- `0` = only sub-tree local algorithms, `1` = also root-walking ones, `2` = an unknown one. -/
def algorithmClass (id : String) : Nat :=
  if subtreeLocalAlgorithms.contains id then 0
  else if rootWalkingAlgorithms.contains id then 1
  else 2

/-- Assigns `owner` to the labels in `todo` and, recursively, to their labels. -/
private def ownLabels (g : ElkGraph) (labels : Array Nat) (owner : Nat) (todo : Array LabelId) : Array Nat := Id.run do
  let mut labels := labels
  let mut stack := todo
  while !stack.isEmpty do
    let l := stack.back!
    stack := stack.pop
    if h : l.idx < labels.size then
      if labels[l.idx] == 0 then
        labels := labels.set l.idx owner
        stack := stack ++ (g.labels[l.idx]?.map (·.labels)).getD #[]
  return labels

/-- The owner tables of the units `units` (sibling nodes, in loop order) on the arena `g`. -/
def computeOwnership (g : ElkGraph) (units : Array NodeId) : Ownership := Id.run do
  -- nodes: the sub-trees (a node already owned is not entered twice, which also stops on a
  -- malformed cyclic parent structure)
  let mut nodes : Array Nat := Array.replicate g.nodes.size 0
  for h : u in [0:units.size] do
    let mut stack : Array NodeId := #[units[u]]
    while !stack.isEmpty do
      let n := stack.back!
      stack := stack.pop
      if h' : n.idx < nodes.size then
        if nodes[n.idx] == 0 then
          nodes := nodes.set n.idx (u + 1)
          stack := stack ++ (g.nodes[n.idx]?.map (·.children)).getD #[]
  -- ports of owned nodes
  let mut ports : Array Nat := Array.replicate g.ports.size 0
  for h : i in [0:g.nodes.size] do
    let o := nodes[i]?.getD 0
    if o != 0 then
      for p in g.nodes[i].ports do
        if p.idx < ports.size then ports := ports.set! p.idx o
  -- algorithms of the sub-trees (resolved algorithm of every owned node)
  let mut algClass : Array Nat := Array.replicate units.size 0
  for h : i in [0:g.nodes.size] do
    let o := nodes[i]?.getD 0
    if o != 0 then
      if let some id := g.nodes[i].props.get Elk.Core.Options.CoreOptions.RESOLVED_ALGORITHM then
        let c := algorithmClass id
        if c > (algClass[o - 1]?.getD 0) then algClass := algClass.set! (o - 1) c
  -- edges and the eligibility test
  let mut edges : Array Nat := Array.replicate g.edges.size 0
  let mut closed : Array Bool := algClass.map (· < 2)
  let mut rootLinked : Array Bool := Array.replicate units.size false
  for h : e in [0:g.edges.size] do
    let ed := g.edges[e]
    let cont := match ed.containingNode with
      | some c => nodes[c.idx]?.getD 0
      | none => 0
    let s := scanEndPoints g units nodes ports ed.targets (scanEndPoints g units nodes ports ed.sources {})
    let allIn (u : Nat) : Bool := s.same && (s.count == 0 || s.first == u)
    if cont != 0 && !allIn cont then closed := closed.set! (cont - 1) false
    for u in s.inside do
      if !allIn u then closed := closed.set! (u - 1) false
      if s.atRoot.contains u then rootLinked := rootLinked.set! (u - 1) true
    let owner :=
      if cont != 0 then cont
      else if s.count > 0 && s.same then s.first
      else 0
    if owner != 0 then edges := edges.set! e owner
  -- labels of owned nodes, ports and edges
  let mut labels : Array Nat := Array.replicate g.labels.size 0
  for h : i in [0:g.nodes.size] do
    let o := nodes[i]?.getD 0
    if o != 0 then labels := ownLabels g labels o g.nodes[i].labels
  for h : i in [0:g.ports.size] do
    let o := ports[i]?.getD 0
    if o != 0 then labels := ownLabels g labels o g.ports[i].labels
  -- sections of owned edges
  let mut sections : Array Nat := Array.replicate g.sections.size 0
  for h : i in [0:g.edges.size] do
    let o := edges[i]?.getD 0
    if o != 0 then
      labels := ownLabels g labels o g.edges[i].labels
      for s in g.edges[i].sections do
        if s.idx < sections.size then sections := sections.set! s.idx o
  let mut eligible : Array Bool := Array.mkEmpty units.size
  for u in [0:units.size] do
    eligible := eligible.push ((closed[u]?.getD false) && !((algClass[u]?.getD 0) == 1 && (rootLinked[u]?.getD false)))
  return { nodes, ports, edges, labels, sections, closed := eligible }

/-- Work estimate of a sibling sub-tree: its nodes, their ports and their contained edges. -/
def subtreeWork (g : ElkGraph) (root : NodeId) : Nat := Id.run do
  let mut stack : Array NodeId := #[root]
  let mut work := 0
  let mut steps := 0
  while !stack.isEmpty && steps ≤ g.nodes.size do
    let n := stack.back!
    stack := stack.pop
    steps := steps + 1
    if let some nd := g.nodes[n.idx]? then
      work := work + 1 + nd.ports.size + nd.containedEdges.size
      stack := stack ++ nd.children
  return work

/-! ## Renumbering of created elements -/

/-- Element counts of an arena. -/
structure Sizes where
  nodes : Nat
  ports : Nat
  edges : Nat
  labels : Nat
  sections : Nat
  deriving Inhabited

/-- The element counts of `g`. -/
def Sizes.of (g : ElkGraph) : Sizes :=
  ⟨g.nodes.size, g.ports.size, g.edges.size, g.labels.size, g.sections.size⟩

/-- Renumbering of the elements a chunk created: an id below the fork size is kept, a created one
moves by the number of elements the earlier chunks created (`off`). -/
structure Remap where
  base : Sizes
  off : Sizes
  deriving Inhabited

namespace Remap

/-- No created element moves. -/
@[inline] def isId (r : Remap) : Bool :=
  r.off.nodes == 0 && r.off.ports == 0 && r.off.edges == 0 && r.off.labels == 0 && r.off.sections == 0

@[inline] def node (r : Remap) (n : NodeId) : NodeId := if n.idx < r.base.nodes then n else ⟨n.idx + r.off.nodes⟩
@[inline] def port (r : Remap) (p : PortId) : PortId := if p.idx < r.base.ports then p else ⟨p.idx + r.off.ports⟩
@[inline] def edge (r : Remap) (e : EdgeId) : EdgeId := if e.idx < r.base.edges then e else ⟨e.idx + r.off.edges⟩
@[inline] def label (r : Remap) (l : LabelId) : LabelId := if l.idx < r.base.labels then l else ⟨l.idx + r.off.labels⟩
@[inline] def sec (r : Remap) (s : SectionId) : SectionId :=
  if s.idx < r.base.sections then s else ⟨s.idx + r.off.sections⟩

def connectable (r : Remap) : ConnectableId → ConnectableId
  | .node n => .node (r.node n)
  | .port p => .port (r.port p)

def element (r : Remap) : ElementId → ElementId
  | .node n => .node (r.node n)
  | .port p => .port (r.port p)
  | .edge e => .edge (r.edge e)
  | .label l => .label (r.label l)

/-- Renumbers the references of a node. -/
def elkNode (r : Remap) (n : ElkNode) : ElkNode :=
  if r.isId then n else
  { n with labels := n.labels.map r.label, parent := n.parent.map r.node,
           children := n.children.map r.node, ports := n.ports.map r.port,
           containedEdges := n.containedEdges.map r.edge, outgoingEdges := n.outgoingEdges.map r.edge,
           incomingEdges := n.incomingEdges.map r.edge }

/-- Renumbers the references of a port. -/
def elkPort (r : Remap) (p : ElkPort) : ElkPort :=
  if r.isId then p else
  { p with labels := p.labels.map r.label, parent := p.parent.map r.node,
           outgoingEdges := p.outgoingEdges.map r.edge, incomingEdges := p.incomingEdges.map r.edge }

/-- Renumbers the references of an edge. -/
def elkEdge (r : Remap) (e : ElkEdge) : ElkEdge :=
  if r.isId then e else
  { e with labels := e.labels.map r.label, containingNode := e.containingNode.map r.node,
           sources := e.sources.map r.connectable, targets := e.targets.map r.connectable,
           sections := e.sections.map r.sec }

/-- Renumbers the references of a label. -/
def elkLabel (r : Remap) (l : ElkLabel) : ElkLabel :=
  if r.isId then l else
  { l with labels := l.labels.map r.label, parent := l.parent.map r.element }

/-- Renumbers the references of an edge section. -/
def elkSection (r : Remap) (s : ElkEdgeSection) : ElkEdgeSection :=
  if r.isId then s else
  { s with parent := s.parent.map r.edge, outgoingShape := s.outgoingShape.map r.connectable,
           incomingShape := s.incomingShape.map r.connectable,
           outgoingSections := s.outgoingSections.map r.sec,
           incomingSections := s.incomingSections.map r.sec }

end Remap

/-! ## Unchanged-element test

`withPtrEq` returns `true` when both values are the same object; otherwise it evaluates the
continuation, which must be `true` for equal values (its proof obligation). The continuations compare
lossless fingerprints (floats by their bits, strings length-prefixed), so an element rebuilt with
equal content counts as unchanged. They only run when a chunk replaced an element outside its
domains, i.e. on the way to the sequential fallback. `Dynamic` property values are compared by their
type name only (no `DecidableEq`); no layout writes them. -/

private def fpStr (acc s : String) : String := acc ++ toString s.utf8ByteSize ++ ":" ++ s ++ ";"
private def fpNat (acc : String) (n : Nat) : String := acc ++ toString n ++ ";"
private def fpFloat (acc : String) (x : Float) : String := acc ++ toString x.toBits ++ ";"
private def fpVec (acc : String) (v : KVector) : String := fpFloat (fpFloat acc v.x) v.y
private def fpArr {α : Type} (acc : String) (xs : Array α) (f : String → α → String) : String :=
  xs.foldl f (fpNat acc xs.size)
private def fpOpt {α : Type} (acc : String) (x : Option α) (f : String → α → String) : String :=
  match x with
  | some v => f (acc ++ "s") v
  | none => acc ++ "n;"

private partial def fpValue (acc : String) : PropValue → String
  | .bool b => acc ++ (if b then "b1;" else "b0;")
  | .int i => acc ++ "i" ++ toString i ++ ";"
  | .double d => fpFloat (acc ++ "d") d
  | .string s => fpStr (acc ++ "s") s
  | .enum o => fpNat (acc ++ "e") o
  | .enumSet b => acc ++ "E" ++ toString b ++ ";"
  | .vector v => fpVec (acc ++ "v") v
  | .vectorChain c => fpArr (acc ++ "c") c fpVec
  | .padding p => fpFloat (fpFloat (fpFloat (fpFloat (acc ++ "p") p.top) p.right) p.bottom) p.left
  | .margins m => fpFloat (fpFloat (fpFloat (fpFloat (acc ++ "m") m.top) m.right) m.bottom) m.left
  | .individualSpacings es => fpArr (acc ++ "I") es fun a (k, v) => fpValue (fpStr a k.id) v
  | .intList xs => fpArr (acc ++ "l") xs fun a i => a ++ toString i ++ ";"
  | .stringList xs => fpArr (acc ++ "L") xs fpStr
  | .doubleList xs => fpArr (acc ++ "D") xs fpFloat
  | .proxy raw => fpStr (acc ++ "x") raw
  | .dynamic d => fpStr (acc ++ "y") (toString d.typeName)

private def fpProps (acc : String) (m : PropertyMap) : String :=
  fpArr acc m.entries fun a (k, v) => fpValue (fpStr a k.id) v

private def fpConn (acc : String) : ConnectableId → String
  | .node n => fpNat (acc ++ "N") n.idx
  | .port p => fpNat (acc ++ "P") p.idx

private def fpElem (acc : String) : ElementId → String
  | .node n => fpNat (acc ++ "N") n.idx
  | .port p => fpNat (acc ++ "P") p.idx
  | .edge e => fpNat (acc ++ "E") e.idx
  | .label l => fpNat (acc ++ "L") l.idx

private def fpNode (n : ElkNode) : String :=
  let a := fpOpt "" n.identifier fpStr
  let a := fpFloat (fpFloat (fpFloat (fpFloat a n.x) n.y) n.width) n.height
  let a := fpProps a n.props
  let a := fpArr a n.labels fun a l => fpNat a l.idx
  let a := fpOpt a n.parent fun a p => fpNat a p.idx
  let a := fpArr a n.children fun a c => fpNat a c.idx
  let a := fpArr a n.ports fun a p => fpNat a p.idx
  let a := fpArr a n.containedEdges fun a e => fpNat a e.idx
  let a := fpArr a n.outgoingEdges fun a e => fpNat a e.idx
  fpArr a n.incomingEdges fun a e => fpNat a e.idx

private def fpPort (p : ElkPort) : String :=
  let a := fpOpt "" p.identifier fpStr
  let a := fpFloat (fpFloat (fpFloat (fpFloat a p.x) p.y) p.width) p.height
  let a := fpProps a p.props
  let a := fpArr a p.labels fun a l => fpNat a l.idx
  let a := fpOpt a p.parent fun a n => fpNat a n.idx
  let a := fpArr a p.outgoingEdges fun a e => fpNat a e.idx
  fpArr a p.incomingEdges fun a e => fpNat a e.idx

private def fpEdge (e : ElkEdge) : String :=
  let a := fpOpt "" e.identifier fpStr
  let a := fpProps a e.props
  let a := fpArr a e.labels fun a l => fpNat a l.idx
  let a := fpOpt a e.containingNode fun a n => fpNat a n.idx
  let a := fpArr a e.sources fpConn
  let a := fpArr a e.targets fpConn
  fpArr a e.sections fun a s => fpNat a s.idx

private def fpLabel (l : ElkLabel) : String :=
  let a := fpOpt "" l.identifier fpStr
  let a := fpFloat (fpFloat (fpFloat (fpFloat a l.x) l.y) l.width) l.height
  let a := fpProps a l.props
  let a := fpArr a l.labels fun a l => fpNat a l.idx
  let a := fpOpt a l.parent fpElem
  fpStr a l.text

private def fpSection (s : ElkEdgeSection) : String :=
  let a := fpOpt "" s.identifier fpStr
  let a := fpProps a s.props
  let a := fpFloat (fpFloat (fpFloat (fpFloat a s.startX) s.startY) s.endX) s.endY
  let a := fpArr a s.bendPoints fpVec
  let a := fpOpt a s.parent fun a e => fpNat a e.idx
  let a := fpOpt a s.outgoingShape fpConn
  let a := fpOpt a s.incomingShape fpConn
  let a := fpArr a s.outgoingSections fun a s => fpNat a s.idx
  fpArr a s.incomingSections fun a s => fpNat a s.idx

/-- `a` and `b` are the same node object, or equal. -/
@[inline] def sameNode (a b : ElkNode) : Bool :=
  withPtrEq a b (fun _ => decide (fpNode a = fpNode b)) (fun h => by subst h; exact decide_eq_true rfl)
/-- `a` and `b` are the same port object, or equal. -/
@[inline] def samePort (a b : ElkPort) : Bool :=
  withPtrEq a b (fun _ => decide (fpPort a = fpPort b)) (fun h => by subst h; exact decide_eq_true rfl)
/-- `a` and `b` are the same edge object, or equal. -/
@[inline] def sameEdge (a b : ElkEdge) : Bool :=
  withPtrEq a b (fun _ => decide (fpEdge a = fpEdge b)) (fun h => by subst h; exact decide_eq_true rfl)
/-- `a` and `b` are the same label object, or equal. -/
@[inline] def sameLabel (a b : ElkLabel) : Bool :=
  withPtrEq a b (fun _ => decide (fpLabel a = fpLabel b)) (fun h => by subst h; exact decide_eq_true rfl)
/-- `a` and `b` are the same section object, or equal. -/
@[inline] def sameSection (a b : ElkEdgeSection) : Bool :=
  withPtrEq a b (fun _ => decide (fpSection a = fpSection b)) (fun h => by subst h; exact decide_eq_true rfl)

/-! ## Check and merge -/

/-- Whether `res` (a chunk result forked from `orig`) left every element outside `inChunk`'s domains
untouched (`owner` = the owner table of the kind, sized like `orig`). -/
@[specialize] def checkKind {α : Type} [Inhabited α] (orig res : Array α) (owner : Array Nat)
    (inChunk : Nat → Bool) (same : α → α → Bool) : Bool := Id.run do
  if res.size < orig.size then return false
  for h : j in [0:orig.size] do
    let o := owner[j]?.getD 0
    if o != 0 && inChunk (o - 1) then continue
    if !same orig[j] res[j]! then return false
  return true

/-- Copies the chunk's own and created elements of one kind from `res` into `merged`, renumbering
them (`remap`); `none` when an element outside the chunk's domains changed. -/
@[specialize] def mergeKind {α : Type} [Inhabited α] (orig res merged : Array α) (owner : Array Nat)
    (inChunk : Nat → Bool) (same : α → α → Bool) (remap : α → α) : Option (Array α) := Id.run do
  if res.size < orig.size then return none
  let mut m := merged
  for h : j in [0:orig.size] do
    let o := owner[j]?.getD 0
    if o != 0 && inChunk (o - 1) then
      m := m.set! j (remap res[j]!)
    else if !same orig[j] res[j]! then return none
  for h : k in [orig.size:res.size] do
    m := m.push (remap res[k]!)
  return some m

/-- Whether the first chunk's result `res` only changed its own domains (it becomes the merge base). -/
def checkChunk (orig res : ElkGraph) (own : Ownership) (inChunk : Nat → Bool) : Bool :=
  checkKind orig.nodes res.nodes own.nodes inChunk sameNode &&
  checkKind orig.ports res.ports own.ports inChunk samePort &&
  checkKind orig.edges res.edges own.edges inChunk sameEdge &&
  checkKind orig.labels res.labels own.labels inChunk sameLabel &&
  checkKind orig.sections res.sections own.sections inChunk sameSection

/-- Merges a later chunk's result `res` (forked from `orig`) into `merged`; returns the merged arena
and the renumbering applied to the chunk's created elements, or `none` on a write outside the
chunk's domains. -/
def mergeChunk (orig res merged : ElkGraph) (own : Ownership) (inChunk : Nat → Bool) :
    Option (ElkGraph × Remap) := do
  let base := Sizes.of orig
  let cur := Sizes.of merged
  let r : Remap := { base, off := ⟨cur.nodes - base.nodes, cur.ports - base.ports, cur.edges - base.edges,
                                   cur.labels - base.labels, cur.sections - base.sections⟩ }
  let ⟨mn, mp, me, ml, ms⟩ := merged
  let nodes ← mergeKind orig.nodes res.nodes mn own.nodes inChunk sameNode r.elkNode
  let ports ← mergeKind orig.ports res.ports mp own.ports inChunk samePort r.elkPort
  let edges ← mergeKind orig.edges res.edges me own.edges inChunk sameEdge r.elkEdge
  let labels ← mergeKind orig.labels res.labels ml own.labels inChunk sameLabel r.elkLabel
  let sections ← mergeKind orig.sections res.sections ms own.sections inChunk sameSection r.elkSection
  return ({ nodes, ports, edges, labels, sections }, r)

end Elk.Core.Parallel
