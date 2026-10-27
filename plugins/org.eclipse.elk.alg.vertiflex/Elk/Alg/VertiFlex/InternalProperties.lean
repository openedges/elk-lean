import Elk.Graph
import Elk.Alg.VertiFlex.P2Relative.OutlineNode
/-!
# `org.eclipse.elk.alg.vertiflex.InternalProperties`

Port of `internal_properties.rs` (elk-rs). The Rust properties are stored in the property map of
each `ElkNode`; here they are typed fields of a per-node record (`NodeProps`) kept in a side
table that is indexed by `NodeId.idx` (`VertiFlexState`), so the layout never writes them into
the `ElkGraph` (they are never exported anyway).

| Rust `InternalProperties` | Lean `NodeProps` field | type |
|---|---|---|
| `LEFT_OUTLINE` / `RIGHT_OUTLINE` | `leftOutline` / `rightOutline` | `Option OutlineNode` |
| `OUTLINE_MAX_DEPTH` | `outlineMaxDepth` | `Option Float` |
| `MIN_X` `MAX_X` `MIN_Y` `MAX_Y` | `minX` `maxX` `minY` `maxY` | `Option Float` |
| `EDGE_BEND_HEIGHT` | `edgeBendHeight` | `Option Float` |
| `NODE_MODEL_ORDER` | `nodeModelOrder` | `Option Int` (`i32`) |
| `ROOT_NODE` | not stored (never read or written in Rust) | |

`none` is an unset property; the algorithm reads them with Rust's `unwrap_or(..)` defaults.
-/
namespace Elk.Alg.VertiFlex

open Elk.Graph Elk.Alg.VertiFlex.P2Relative

/-- The `InternalProperties` of one `ElkNode`. -/
structure NodeProps where
  /-- `LEFT_OUTLINE`. -/
  leftOutline : Option OutlineNode := none
  /-- `RIGHT_OUTLINE`. -/
  rightOutline : Option OutlineNode := none
  /-- `OUTLINE_MAX_DEPTH`. -/
  outlineMaxDepth : Option Float := none
  /-- `MIN_X`. -/
  minX : Option Float := none
  /-- `MAX_X`. -/
  maxX : Option Float := none
  /-- `MIN_Y`. -/
  minY : Option Float := none
  /-- `MAX_Y`. -/
  maxY : Option Float := none
  /-- `EDGE_BEND_HEIGHT`. -/
  edgeBendHeight : Option Float := none
  /-- `NODE_MODEL_ORDER` (`"Node Model Order"`). -/
  nodeModelOrder : Option Int := none
  deriving Inhabited

/-- The side table of internal node properties of one layout run. -/
structure VertiFlexState where
  /-- `NodeProps` indexed by `NodeId.idx` (sized to the node count of the graph). -/
  nodes : Array NodeProps := #[]

/-- The monad of the VertiFlex phases: internal properties on top of the `ElkGraph` monad. -/
abbrev VertiFlexM := StateRefT VertiFlexState ElkM

namespace VertiFlexM

/-- `node.get_property(InternalProperties::..)` for all properties of a node at once. -/
def getProps (n : NodeId) : VertiFlexM NodeProps := do
  return (← getThe VertiFlexState).nodes.getD n.idx {}

/-- `node.set_property(InternalProperties::.., ..)`: updates the record of a node in place. -/
def modifyProps (n : NodeId) (f : NodeProps → NodeProps) : VertiFlexM Unit :=
  modifyThe VertiFlexState fun s => { s with nodes := s.nodes.modify n.idx f }

/-- Rust `.expect(msg)` on a property that must be present: the panic message is the plain `msg`. -/
def expectSome {α : Type} (value : Option α) (msg : String) : VertiFlexM α :=
  match value with
  | some v => pure v
  | none => throw (IO.userError msg)

end VertiFlexM

end Elk.Alg.VertiFlex
