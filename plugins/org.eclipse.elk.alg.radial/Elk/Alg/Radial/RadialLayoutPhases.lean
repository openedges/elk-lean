import Elk.Graph.Enum
/-!
# `org.eclipse.elk.alg.radial.RadialLayoutPhases`

Port of `radial_layout_phases.rs` (elk-rs). The factory half of the Rust enum (`create_phase`:
`P1_NODE_PLACEMENT` -> `EadesRadial`, `P2_EDGE_ROUTING` -> `StraightLineEdgeRouter`) lives in
`Elk.Alg.Radial.RadialLayoutProvider` (`RadialLayoutPhases.phaseFactory`), because the phases refer
to this enumeration as their phase type.
-/
namespace Elk.Alg.Radial

/-- `RadialLayoutPhases`: `P1_NODE_PLACEMENT`, `P2_EDGE_ROUTING`. -/
elk_enum RadialLayoutPhases := p1NodePlacement p2EdgeRouting

end Elk.Alg.Radial
