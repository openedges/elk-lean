import Elk.Graph
/-!
# `org.eclipse.elk.alg.radial.p1position.wedge.IAnnulusWedgeCriteria`

Port of `i_annulus_wedge_criteria.rs` (elk-rs).
-/
namespace Elk.Alg.Radial.P1Position.Wedge

open Elk.Graph

/-- `IAnnulusWedgeCriteria`: the space a node (with its subtree) needs in its annulus wedge. -/
structure IAnnulusWedgeCriteria where
  /-- `calculate_wedge_space(node)`. -/
  calculateWedgeSpace : NodeId → ElkM Float

end Elk.Alg.Radial.P1Position.Wedge
