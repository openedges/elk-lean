import Elk.Graph
import Elk.Alg.Radial.InternalProperties
/-!
# `org.eclipse.elk.alg.radial.intermediate.rotation.IRadialRotator`

Port of `i_radial_rotator.rs` (elk-rs).
-/
namespace Elk.Alg.Radial.Intermediate.Rotation

open Elk.Graph

/-- `IRadialRotator`. -/
structure IRadialRotator where
  /-- `rotate(graph)`. -/
  rotate : NodeId → RadialM Unit

end Elk.Alg.Radial.Intermediate.Rotation
