import Elk.Graph
import Elk.Core.Util.Java
import Elk.Alg.Radial.RadialUtil
import Elk.Alg.Radial.P1Position.Wedge.IAnnulusWedgeCriteria
/-!
# `org.eclipse.elk.alg.radial.p1position.wedge.AnnulusWedgeByNodeSpace`

Port of `annulus_wedge_by_node_space.rs` (elk-rs): the wedge space of a node is the maximum of
its own diagonal and the sum of the wedge spaces of its successors.
-/
namespace Elk.Alg.Radial.P1Position.Wedge

open Elk.Graph Elk.Core.Util

namespace AnnulusWedgeByNodeSpace

/-- `calculate_wedge_space(node)` on the arena. -/
partial def calculateWedgeSpacePure (g : ElkGraph) (node : NodeId) : Float :=
  let successors := RadialUtil.successorsPure g node
  let n := g.node node
  let nodeSize := Float.sqrt (n.width * n.width + n.height * n.height)
  let childSpace := successors.foldl (fun acc child => acc + calculateWedgeSpacePure g child) 0.0
  fmax childSpace nodeSize

/-- `calculate_wedge_space(node)`. -/
def calculateWedgeSpace (node : NodeId) : ElkM Float :=
  ElkM.withGraph fun g => calculateWedgeSpacePure g node

/-- The `IAnnulusWedgeCriteria` of this class. -/
def criteria : IAnnulusWedgeCriteria := { calculateWedgeSpace := calculateWedgeSpace }

end AnnulusWedgeByNodeSpace

end Elk.Alg.Radial.P1Position.Wedge
