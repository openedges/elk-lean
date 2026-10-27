import Elk.Graph
/-!
# `org.eclipse.elk.alg.mrtree.options.InternalProperties`

Port of `options/internal_properties.rs` (elk-rs). As required by `PORTING.md` sections 5 and 14 the
internal (non-option) properties are typed fields of the `TGraph` arena structures instead of
property map entries. Every field has the Rust property default; properties without a default whose
absence is observable (`Option` in Rust) are `Option` fields.

| Java / Rust `InternalProperties` | element | Lean field |
|---|---|---|
| `ORIGIN` | graph, node, edge | `TGraph.internal.origin`, `TNode.internal.origin`, `TEdge.internal.origin` |
| `RANDOM` | graph | not ported: never read or written by elk-rs |
| `DEPTH` (0) | node | `TNode.internal.depth` |
| `FAN` (0) | node | `TNode.internal.fan` |
| `DESCENDANTS` (0) | node | `TNode.internal.descendants` |
| `ROOT` (false) | node | `TNode.internal.root` |
| `LEFTNEIGHBOR`, `RIGHTNEIGHBOR` | node | `TNode.internal.leftNeighbor`, `rightNeighbor` (`Option TNodeId`) |
| `LEFTSIBLING`, `RIGHTSIBLING` | node | `TNode.internal.leftSibling`, `rightSibling` (`Option TNodeId`) |
| `DUMMY` (false) | node, edge | `TNode.internal.dummy`, `TEdge.internal.dummy` |
| `LEVEL` (0) | node | `TNode.internal.level` (unused by elk-rs) |
| `REMOVABLE_EDGES` | graph | `TGraph.internal.removableEdges` (`Array TEdgeId`, Rust `unwrap_or_default`) |
| `XCOOR`, `YCOOR` (0) | node | `TNode.internal.xcoor`, `ycoor` (`Int`, Rust `i32`) |
| `LEVELHEIGHT`, `LEVELMIN`, `LEVELMAX` (0.0) | node | `TNode.internal.levelHeight`, `levelMin`, `levelMax` |
| `GRAPH_XMIN`, `GRAPH_YMIN`, `GRAPH_XMAX`, `GRAPH_YMAX` (0.0) | graph | `TGraph.internal.graphXmin`, `graphYmin`, `graphXmax`, `graphYmax` |
| `COMPACT_LEVEL_ASCENSION` (false) | node | `TNode.internal.compactLevelAscension` |
| `COMPACT_CONSTRAINTS` | node | `TNode.internal.compactConstraints` (`Array TNodeId`, Rust `unwrap_or_default`) |
| `ID` ("") | node | `TNode.internal.idString` |
| `POSITION` (0) | node | `TNode.internal.position` |
| `PRELIM`, `MODIFIER` (0.0) | node | `TNode.internal.prelim`, `modifier` |
| `BB_UPLEFT`, `BB_LOWRIGHT` | graph | `TGraph.internal.bbUpleft`, `bbLowright` (`Option KVector`) |

Rust stores the origin as a pointer-derived `OriginId` into hash maps of the importer; the Lean origin
is the typed `ElkGraph` id itself, so the importer needs no maps.
-/
namespace Elk.Alg.MrTree.Options

open Elk.Graph

/-- elk-rs `Origin` (`InternalProperties.ORIGIN`): the `ElkGraph` element a `TGraph` element was
created from. -/
inductive Origin where
  | elkNode (n : NodeId)
  | elkEdge (e : EdgeId)
  | elkLabel (l : LabelId)
  deriving BEq, Inhabited, Repr

end Elk.Alg.MrTree.Options
