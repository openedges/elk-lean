import Elk.Graph
import Elk.Core.Math.KVector
import Elk.Core.Util.Random
/-!
# `org.eclipse.elk.alg.force.options.InternalProperties`

The internal (non-option) properties of the force algorithms. As required by `PORTING.md` section 5
they are typed fields of the algorithm's own graph structures instead of property map entries:

| Java / Rust `InternalProperties` | Lean |
|---|---|
| `ORIGIN` (on graph, node, edge, label) | `FGraph.origin`, `FArena.nodeOrigin`, `edgeOrigin`, `labelOrigin` |
| `RANDOM` | `FGraph.random` |
| `BB_UPLEFT` | `FGraph.bbUpleft` |
| `BB_LOWRIGHT` | `FGraph.bbLowright` |

Rust stores the origin as a pointer-derived `OriginId` into per-importer hash maps; the Lean origin is
the typed `ElkGraph` id itself, so no maps are needed.
-/
namespace Elk.Alg.Force.Options

open Elk.Graph

/-- elk-rs `Origin`: the `ElkGraph` element an `FGraph` element was created from. -/
inductive Origin where
  | elkNode (n : NodeId)
  | elkEdge (e : EdgeId)
  | elkLabel (l : LabelId)
  deriving BEq, Inhabited, Repr

end Elk.Alg.Force.Options
