import Elk.Graph
import Elk.Alg.Radial.RadialUtil
import Elk.Alg.Radial.P1Position.Wedge.IAnnulusWedgeCriteria
/-!
# `org.eclipse.elk.alg.radial.p1position.wedge.AnnulusWedgeByLeafs`

Port of `annulus_wedge_by_leafs.rs` (elk-rs): the wedge space is the number of leaves of the subtree.
-/
namespace Elk.Alg.Radial.P1Position.Wedge

open Elk.Graph

namespace AnnulusWedgeByLeafs

/-- `calculate_wedge_space(node)`. -/
def calculateWedgeSpace (node : NodeId) : ElkM Float := RadialUtil.getNumberOfLeaves node

/-- The `IAnnulusWedgeCriteria` of this class. -/
def criteria : IAnnulusWedgeCriteria := { calculateWedgeSpace := calculateWedgeSpace }

end AnnulusWedgeByLeafs

end Elk.Alg.Radial.P1Position.Wedge
