import Elk.Core.Math.KVector
import Elk.Alg.MrTree.Graph.TGraphElement
/-!
# `org.eclipse.elk.alg.mrtree.graph.TShape`

Port of `graph/t_shape.rs` (elk-rs): a graph element with a position and a size (both zero
initially). `TNode` and `TLabel` extend it.
-/
namespace Elk.Alg.MrTree.Graph

open Elk.Core.Math

/-- `org.eclipse.elk.alg.mrtree.graph.TShape`. -/
structure TShape extends TGraphElement where
  /-- `getPosition()`. -/
  position : KVector := {}
  /-- `getSize()`. -/
  size : KVector := {}
  deriving Inhabited

end Elk.Alg.MrTree.Graph
