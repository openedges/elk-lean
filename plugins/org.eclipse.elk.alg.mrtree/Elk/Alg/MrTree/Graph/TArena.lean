import Elk.Core.Alg.LayoutProcessor
import Elk.Alg.MrTree.Graph.TGraph
import Elk.Alg.MrTree.Graph.TNode
import Elk.Alg.MrTree.Graph.TEdge
import Elk.Alg.MrTree.Graph.TLabel
/-!
# The tree graph arena (`TArena`) and the `MrTreeM` monad

There is no Java/Rust class of this name: elk-rs holds the tree graph as `Arc<Mutex<_>>` objects that
reference each other (`TGraphRef`, `TNodeRef`, `TEdgeRef`, `TLabelRef`). Following `PORTING.md`
section 14 all elements live in the arrays of one `TArena` and refer to each other by typed ids. One
arena holds every `TGraph` of a layout run (the imported graph, its components and the packed result
share their nodes and edges, like the shared references of Rust).

This module also hosts the methods of `TNode`, `TEdge` and `TLabel` that update other elements, with
the Rust semantics:

* `TNode::new(id, graph)` / `new_with_label` → `TArena.createNode` (appends the node to `graph`);
* `TEdge::new(source, target)` → `TArena.createEdge` (`set_target` first, then `set_source`, so that
  `add_outgoing` sees the target for the `direct_children` cache; the edge is *not* added to a graph);
* `TEdge::set_source`/`set_target` → `setEdgeSource`/`setEdgeTarget`;
* `TNode::add_outgoing`/`add_incoming`/`remove_outgoing`/`remove_incoming`/`replace_outgoing_edges`;
* `TNode::parent` (source of the first incoming edge), `children` (`direct_children`), `add_child`
  (a `DUMMY` edge appended to the edges of the node's own graph);
* `TLabel::new(edge, text)` → `createLabel`;
* the `Display` implementations → `nodeToString`, `edgeToString`, `labelToString` (an edge without both
  end points prints `e_<arena index>` instead of Rust's pointer `e_0x…`).

The algorithm monad is `MrTreeM := StateRefT TArena IO`; the importer and the layout provider, which
also read and write the `ElkGraph`, run in `ElkM` and carry the arena as a value (see
`Elk.Alg.MrTree.ElkGraphImporter`). Processors are `LayoutProcessor MrTreeM TGraphId`: the graph
argument is the id of the processed graph (Rust `&mut TGraphRef`).
-/
namespace Elk.Alg.MrTree.Graph

open Elk.Graph Elk.Core.Math Elk.Core.Alg

/-- Arena of all tree graph elements. -/
structure TArena where
  graphs : Array TGraph := #[]
  nodes : Array TNode := #[]
  edges : Array TEdge := #[]
  labels : Array TLabel := #[]
  deriving Inhabited

namespace TArena

/-! ### Element access -/

@[inline] def graph (a : TArena) (g : TGraphId) : TGraph := a.graphs[g.idx]!
@[inline] def node (a : TArena) (n : TNodeId) : TNode := a.nodes[n.idx]!
@[inline] def edge (a : TArena) (e : TEdgeId) : TEdge := a.edges[e.idx]!
@[inline] def label (a : TArena) (l : TLabelId) : TLabel := a.labels[l.idx]!

@[inline] def modifyGraph (a : TArena) (g : TGraphId) (f : TGraph → TGraph) : TArena :=
  { a with graphs := a.graphs.modify g.idx f }
@[inline] def modifyNode (a : TArena) (n : TNodeId) (f : TNode → TNode) : TArena :=
  { a with nodes := a.nodes.modify n.idx f }
@[inline] def modifyEdge (a : TArena) (e : TEdgeId) (f : TEdge → TEdge) : TArena :=
  { a with edges := a.edges.modify e.idx f }
@[inline] def modifyLabel (a : TArena) (l : TLabelId) (f : TLabel → TLabel) : TArena :=
  { a with labels := a.labels.modify l.idx f }

/-! ### Creation -/

/-- `TGraph::new()`: a new empty graph. -/
def createGraph (a : TArena) : TArena × TGraphId :=
  (({ a with graphs := a.graphs.push {} } : TArena), ⟨a.graphs.size⟩)

/-- `TNode::new(id, graph)` / `TNode::new_with_label(id, graph, label)`: a new node with zero
geometry, appended to the nodes of `graph` (if any). -/
def createNode (a : TArena) (id : Int) (graph : Option TGraphId) (label : Option String := none) :
    TArena × TNodeId :=
  let n : TNodeId := ⟨a.nodes.size⟩
  let a := { a with nodes := a.nodes.push { id, graph, label } }
  let a := match graph with
    | some g => a.modifyGraph g fun x => { x with nodes := x.nodes.push n }
    | none => a
  (a, n)

/-- `TNode::add_outgoing(edge)`: ignored if the edge is already outgoing; otherwise the edge's current
target is appended to the `direct_children` cache and the edge to the outgoing edges. -/
def addOutgoing (a : TArena) (n : TNodeId) (e : TEdgeId) : TArena :=
  if (a.node n).outgoingEdges.contains e then a
  else
    let target := (a.edge e).target
    a.modifyNode n fun x =>
      let dc := match target with
        | some t => x.directChildren.push t
        | none => x.directChildren
      { x with directChildren := dc, outgoingEdges := x.outgoingEdges.push e }

/-- `TNode::add_incoming(edge)`: ignored if the edge is already incoming. -/
def addIncoming (a : TArena) (n : TNodeId) (e : TEdgeId) : TArena :=
  if (a.node n).incomingEdges.contains e then a
  else a.modifyNode n fun x => { x with incomingEdges := x.incomingEdges.push e }

/-- `TNode::remove_outgoing(edge)`: removes the edge and the first occurrence of its target in the
`direct_children` cache. -/
def removeOutgoing (a : TArena) (n : TNodeId) (e : TEdgeId) : TArena :=
  match (a.node n).outgoingEdges.idxOf? e with
  | none => a
  | some i =>
    let target := (a.edge e).target
    a.modifyNode n fun x =>
      let out := x.outgoingEdges.eraseIdx! i
      let dc := match target with
        | some t => match x.directChildren.idxOf? t with
          | some ci => x.directChildren.eraseIdx! ci
          | none => x.directChildren
        | none => x.directChildren
      { x with outgoingEdges := out, directChildren := dc }

/-- `TNode::remove_incoming(edge)`. -/
def removeIncoming (a : TArena) (n : TNodeId) (e : TEdgeId) : TArena :=
  match (a.node n).incomingEdges.idxOf? e with
  | none => a
  | some i => a.modifyNode n fun x => { x with incomingEdges := x.incomingEdges.eraseIdx! i }

/-- `TNode::replace_outgoing_edges(edges)`: replaces the outgoing edges and rebuilds the
`direct_children` cache from their targets. -/
def replaceOutgoingEdges (a : TArena) (n : TNodeId) (edges : Array TEdgeId) : TArena :=
  let dc := edges.filterMap fun e => (a.edge e).target
  a.modifyNode n fun x => { x with outgoingEdges := edges, directChildren := dc }

/-- `TEdge::set_source(edge, source)`: no-op if the source does not change; otherwise the edge leaves
the outgoing edges of the old source and joins those of the new one. -/
def setEdgeSource (a : TArena) (e : TEdgeId) (source : Option TNodeId) : TArena :=
  let current := (a.edge e).source
  match current, source with
  | some c, some s => if c == s then a else go current source
  | _, _ => go current source
where
  go (current source : Option TNodeId) : TArena :=
    let a := match current with
      | some c => a.removeOutgoing c e
      | none => a
    let a := match source with
      | some s => a.addOutgoing s e
      | none => a
    a.modifyEdge e fun x => { x with source }

/-- `TEdge::set_target(edge, target)`: no-op if the target does not change; otherwise the edge leaves
the incoming edges of the old target and joins those of the new one. -/
def setEdgeTarget (a : TArena) (e : TEdgeId) (target : Option TNodeId) : TArena :=
  let current := (a.edge e).target
  match current, target with
  | some c, some t => if c == t then a else go current target
  | _, _ => go current target
where
  go (current target : Option TNodeId) : TArena :=
    let a := match current with
      | some c => a.removeIncoming c e
      | none => a
    let a := match target with
      | some t => a.addIncoming t e
      | none => a
    a.modifyEdge e fun x => { x with target }

/-- `TEdge::new(source, target)`: a new edge (not added to any graph); the target is set before the
source (see the module doc). -/
def createEdge (a : TArena) (source target : TNodeId) : TArena × TEdgeId :=
  let e : TEdgeId := ⟨a.edges.size⟩
  let a := { a with edges := a.edges.push {} }
  let a := a.setEdgeTarget e (some target)
  let a := a.setEdgeSource e (some source)
  (a, e)

/-- `TLabel::new(edge, text)`: a new label, appended to the labels of the edge. -/
def createLabel (a : TArena) (e : TEdgeId) (text : String) : TArena × TLabelId :=
  let l : TLabelId := ⟨a.labels.size⟩
  let a := { a with labels := a.labels.push { edge := some e, text := some text } }
  (a.modifyEdge e fun x => { x with labels := x.labels.push l }, l)

/-! ### Tree navigation -/

/-- `TNode::parent()`: the source of the first incoming edge. -/
def parent (a : TArena) (n : TNodeId) : Option TNodeId :=
  (a.node n).incomingEdges[0]?.bind fun e => (a.edge e).source

/-- `TNode::children()` / `children_copy()`. -/
@[inline] def children (a : TArena) (n : TNodeId) : Array TNodeId := (a.node n).directChildren

/-- `TNode::add_child(node, child)`: a new `DUMMY` edge `node -> child`, appended to the edges of the
graph the node was created in. -/
def addChild (a : TArena) (node child : TNodeId) : TArena × TEdgeId :=
  let (a, e) := a.createEdge node child
  let a := a.modifyEdge e fun x => { x with internal.dummy := true }
  match (a.node node).graph with
  | some g => (a.modifyGraph g fun x => { x with edges := x.edges.push e }, e)
  | none => (a, e)

/-! ### `Display` -/

/-- `impl Display for TNode`: `n_<label>`, or `n_<id>` without a (non-empty) label. -/
def nodeToString (a : TArena) (n : TNodeId) : String :=
  let x := a.node n
  match x.label with
  | some l => if l.isEmpty then s!"n_{x.id}" else s!"n_{l}"
  | none => s!"n_{x.id}"

/-- `impl Display for TEdge`: `<source>-><target>`. -/
def edgeToString (a : TArena) (e : TEdgeId) : String :=
  match (a.edge e).source, (a.edge e).target with
  | some s, some t => s!"{a.nodeToString s}->{a.nodeToString t}"
  | _, _ => s!"e_{e.idx}"

/-- `impl Display for TLabel`: `l_<text>`, or `l[<edge>]` without a (non-empty) text. -/
def labelToString (a : TArena) (l : TLabelId) : String :=
  let x := a.label l
  let ofEdge : String := match x.edge with
    | some e => s!"l[{a.edgeToString e}]"
    | none => "l[]"
  match x.text with
  | some t => if t.isEmpty then ofEdge else s!"l_{t}"
  | none => ofEdge

end TArena

/-- The state monad of the tree layout algorithm. -/
abbrev MrTreeM := StateRefT TArena IO

/-- `ILayoutProcessor<TGraph>`: the graph argument is the id of the processed graph. -/
abbrev TreeProcessor := LayoutProcessor MrTreeM TGraphId

namespace MrTreeM

/-- Runs a tree layout action on an arena: the result and the final arena. -/
@[inline] def run {α : Type} (x : MrTreeM α) (a : TArena) : IO (α × TArena) := StateRefT'.run x a

@[inline] def getGraph (g : TGraphId) : MrTreeM TGraph := do return (← get).graph g
@[inline] def getNode (n : TNodeId) : MrTreeM TNode := do return (← get).node n
@[inline] def getEdge (e : TEdgeId) : MrTreeM TEdge := do return (← get).edge e
@[inline] def getLabel (l : TLabelId) : MrTreeM TLabel := do return (← get).label l

@[inline] def modifyGraph (g : TGraphId) (f : TGraph → TGraph) : MrTreeM Unit := modify (·.modifyGraph g f)
@[inline] def modifyNode (n : TNodeId) (f : TNode → TNode) : MrTreeM Unit := modify (·.modifyNode n f)
@[inline] def modifyEdge (e : TEdgeId) (f : TEdge → TEdge) : MrTreeM Unit := modify (·.modifyEdge e f)
@[inline] def modifyLabel (l : TLabelId) (f : TLabel → TLabel) : MrTreeM Unit := modify (·.modifyLabel l f)

/-- `TGraph::new()`. -/
@[inline] def createGraph : MrTreeM TGraphId := modifyGet fun a => let (a, g) := a.createGraph; (g, a)
/-- `TNode::new(id, graph)` / `new_with_label`. -/
@[inline] def createNode (id : Int) (graph : Option TGraphId) (label : Option String := none) : MrTreeM TNodeId :=
  modifyGet fun a => let (a, n) := a.createNode id graph label; (n, a)
/-- `TEdge::new(source, target)`. -/
@[inline] def createEdge (source target : TNodeId) : MrTreeM TEdgeId :=
  modifyGet fun a => let (a, e) := a.createEdge source target; (e, a)
/-- `TLabel::new(edge, text)`. -/
@[inline] def createLabel (e : TEdgeId) (text : String) : MrTreeM TLabelId :=
  modifyGet fun a => let (a, l) := a.createLabel e text; (l, a)

@[inline] def setEdgeSource (e : TEdgeId) (s : Option TNodeId) : MrTreeM Unit := modify (·.setEdgeSource e s)
@[inline] def setEdgeTarget (e : TEdgeId) (t : Option TNodeId) : MrTreeM Unit := modify (·.setEdgeTarget e t)
@[inline] def addOutgoing (n : TNodeId) (e : TEdgeId) : MrTreeM Unit := modify (·.addOutgoing n e)
@[inline] def addIncoming (n : TNodeId) (e : TEdgeId) : MrTreeM Unit := modify (·.addIncoming n e)
@[inline] def removeOutgoing (n : TNodeId) (e : TEdgeId) : MrTreeM Unit := modify (·.removeOutgoing n e)
@[inline] def removeIncoming (n : TNodeId) (e : TEdgeId) : MrTreeM Unit := modify (·.removeIncoming n e)
@[inline] def replaceOutgoingEdges (n : TNodeId) (edges : Array TEdgeId) : MrTreeM Unit :=
  modify (·.replaceOutgoingEdges n edges)
/-- `TNode::add_child(node, child)`. -/
@[inline] def addChild (node child : TNodeId) : MrTreeM TEdgeId :=
  modifyGet fun a => let (a, e) := a.addChild node child; (e, a)

@[inline] def parent (n : TNodeId) : MrTreeM (Option TNodeId) := do return (← get).parent n
@[inline] def children (n : TNodeId) : MrTreeM (Array TNodeId) := do return (← get).children n

/-- `graph.get_property(p)` (stored value, else the property default). -/
@[inline] def getGraphProp {α : Type} [PropCodec α] (g : TGraphId) (p : Property α) : MrTreeM (Option α) :=
  do return ((← get).graph g).props.get p
/-- `node.get_property(p)` (stored value, else the property default). -/
@[inline] def getNodeProp {α : Type} [PropCodec α] (n : TNodeId) (p : Property α) : MrTreeM (Option α) :=
  do return ((← get).node n).props.get p
/-- `graph.set_property(p, Some(v))`. -/
@[inline] def setGraphProp {α : Type} [PropCodec α] (g : TGraphId) (p : Property α) (v : α) : MrTreeM Unit :=
  modifyGraph g fun x => { x with props := x.props.set p v }
/-- `node.set_property(p, Some(v))`. -/
@[inline] def setNodeProp {α : Type} [PropCodec α] (n : TNodeId) (p : Property α) (v : α) : MrTreeM Unit :=
  modifyNode n fun x => { x with props := x.props.set p v }

end MrTreeM

end Elk.Alg.MrTree.Graph
