import Elk.Graph
/-!
# `org.eclipse.elk.alg.layered.graph.LNode.NodeType`
-/
namespace Elk.Alg.Layered.Graph

/-- `LNode.NodeType` (Java ordinal order). -/
elk_enum NodeType := normal longEdge externalPort northSouthPort label breakingPoint placeholder nonshiftingPlaceholder

namespace NodeType

/-- `NodeType.getColor()` (debug graph output). -/
def color : NodeType → String
  | .externalPort => "#cc99cc"
  | .longEdge => "#eaed00"
  | .northSouthPort => "#0034de"
  | .label => "#75c3c3"
  | .breakingPoint => "#eeeeff"
  | _ => "#eeeeee"

/-- Java constant name (`name()`), e.g. `LONG_EDGE`. -/
def name (t : NodeType) : String := ElkEnum.javaName t

/-- Number of constants (`NodeType.values().length`). -/
def COUNT : Nat := ElkEnum.count (α := NodeType)

end NodeType

end Elk.Alg.Layered.Graph
