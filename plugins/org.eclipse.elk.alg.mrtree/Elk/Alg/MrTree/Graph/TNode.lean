import Elk.Alg.MrTree.Graph.TShape
import Elk.Alg.MrTree.Options.InternalProperties
/-!
# `org.eclipse.elk.alg.mrtree.graph.TNode`

Port of `graph/t_node.rs` (elk-rs): a tree node. The structure holds the fields; the methods that
touch other elements (`new`, `add_outgoing`, `remove_outgoing`, `parent`, `add_child`, `Display`)
live in `Elk.Alg.MrTree.Graph.TArena`.

Rust keeps a `direct_children` cache next to `outgoing_edges`: `add_outgoing` appends the target of
the edge, `remove_outgoing` removes the *first occurrence* of the edge's target and
`replace_outgoing_edges` rebuilds it. With multi-edges the cache order can differ from the targets of
`outgoing_edges` (Java `getChildren()`), so the cache is kept as the field `directChildren` and
`children()` returns it, exactly like Rust.
-/
namespace Elk.Alg.MrTree.Graph

open Elk.Core.Math Elk.Alg.MrTree.Options

/-- The internal properties of a `TNode` (`InternalProperties`, Rust defaults). -/
structure TNodeInternals where
  /-- `ORIGIN`. -/
  origin : Option Origin := none
  /-- `DEPTH`. -/
  depth : Int := 0
  /-- `FAN`. -/
  fan : Int := 0
  /-- `DESCENDANTS`. -/
  descendants : Int := 0
  /-- `ROOT`. -/
  root : Bool := false
  /-- `LEFTNEIGHBOR`. -/
  leftNeighbor : Option TNodeId := none
  /-- `RIGHTNEIGHBOR`. -/
  rightNeighbor : Option TNodeId := none
  /-- `LEFTSIBLING`. -/
  leftSibling : Option TNodeId := none
  /-- `RIGHTSIBLING`. -/
  rightSibling : Option TNodeId := none
  /-- `DUMMY`. -/
  dummy : Bool := false
  /-- `LEVEL` (never used by elk-rs). -/
  level : Int := 0
  /-- `XCOOR`. -/
  xcoor : Int := 0
  /-- `YCOOR`. -/
  ycoor : Int := 0
  /-- `LEVELHEIGHT`. -/
  levelHeight : Float := 0.0
  /-- `LEVELMIN`. -/
  levelMin : Float := 0.0
  /-- `LEVELMAX`. -/
  levelMax : Float := 0.0
  /-- `COMPACT_LEVEL_ASCENSION`. -/
  compactLevelAscension : Bool := false
  /-- `COMPACT_CONSTRAINTS` (Rust `unwrap_or_default` = empty). -/
  compactConstraints : Array TNodeId := #[]
  /-- `ID`: the fan identifier string of `FanProcessor`. -/
  idString : String := ""
  /-- `POSITION`: the order index of `NodeOrderer`. -/
  position : Int := 0
  /-- `PRELIM`. -/
  prelim : Float := 0.0
  /-- `MODIFIER`. -/
  modifier : Float := 0.0
  deriving Inhabited

/-- `org.eclipse.elk.alg.mrtree.graph.TNode`. -/
structure TNode extends TShape where
  /-- The graph the node was created in (Rust `Weak<TGraph>`; used by `add_child`). -/
  graph : Option TGraphId := none
  /-- `getLabel()`. -/
  label : Option String := none
  /-- `getOutgoingEdges()`. -/
  outgoingEdges : Array TEdgeId := #[]
  /-- `getIncomingEdges()`. -/
  incomingEdges : Array TEdgeId := #[]
  /-- Rust `direct_children` (see the module doc). -/
  directChildren : Array TNodeId := #[]
  /-- Internal properties. -/
  internal : TNodeInternals := {}
  deriving Inhabited

namespace TNode

/-- `isLeaf()`: no outgoing edges. -/
@[inline] def isLeaf (n : TNode) : Bool := n.outgoingEdges.isEmpty

/-- `children()` / `children_copy()`: the `direct_children` cache. -/
@[inline] def children (n : TNode) : Array TNodeId := n.directChildren

end TNode

end Elk.Alg.MrTree.Graph
