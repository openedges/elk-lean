import Elk.Graph.Enum
/-!
# `org.eclipse.elk.alg.layered.options.NodeFlexibility`

Port of `options/node_flexibility.rs` (elk-rs) and `NodeFlexibility.java`.

The static `NodeFlexibility.getNodeFlexibility(LNode)` needs the layered graph model; elk-rs
implements it as `get_node_flexibility` in `network_simplex_placer.rs`, so it is ported with
`P4Nodes.NetworkSimplexPlacer`.
-/
namespace Elk.Alg.Layered.Options

/-- `org.eclipse.elk.alg.layered.options.NodeFlexibility`: Represents the flexibility of a node
during node placement with the `NetworkSimplexPlacer`. Here, flexibility means that either the ports
are allowed to move on a node's border or that the node's size may change. Both points have the goal
to further reduce the overall edge length, possibly straightening a larger number of edges. -/
elk_enum NodeFlexibility := none portPosition nodeSizeWhereSpacePermits nodeSize

namespace NodeFlexibility

/-- `NodeFlexibility.isFlexibleSize()`: only `NODE_SIZE`. -/
def isFlexibleSize : NodeFlexibility → Bool
  | .nodeSize => true
  | _ => false

/-- `NodeFlexibility.isFlexibleSizeWhereSpacePermits()`: `NODE_SIZE_WHERE_SPACE_PERMITS` or
`NODE_SIZE`. -/
def isFlexibleSizeWhereSpacePermits : NodeFlexibility → Bool
  | .nodeSizeWhereSpacePermits | .nodeSize => true
  | _ => false

/-- `NodeFlexibility.isFlexiblePorts()`: every value except `NONE`. -/
def isFlexiblePorts : NodeFlexibility → Bool
  | .portPosition | .nodeSizeWhereSpacePermits | .nodeSize => true
  | _ => false

/-- `NodeFlexibility.isAtLeast(nf)` (Java only; elk-rs has no counterpart). The Java `switch`
lacks a `return` in the `NODE_SIZE_WHERE_SPACE_PERMITS` branch and falls through to the
`PORT_POSITION` branch; this fall-through is reproduced (`nf.isFlexiblePorts`). -/
def isAtLeast (self nf : NodeFlexibility) : Bool :=
  match self with
  | .nodeSize => nf.isFlexibleSize
  | .nodeSizeWhereSpacePermits => nf.isFlexiblePorts
  | .portPosition => nf.isFlexiblePorts
  | .none => true

end NodeFlexibility

end Elk.Alg.Layered.Options
