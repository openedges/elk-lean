import Elk.Graph.Enum
/-!
# `org.eclipse.elk.alg.radial.options.AnnulusWedgeCriteria`

Port of `annulus_wedge_criteria.rs` (elk-rs). The factory half of the Rust enum (`create`, which
builds the `IAnnulusWedgeCriteria`) lives in `Elk.Alg.Radial.P1Position.EadesRadial`, the only
user, because the wedge implementations depend on the options.
-/
namespace Elk.Alg.Radial.Options

/-- `AnnulusWedgeCriteria`: how the wedge of a node in the annulus is calculated
(Java default of the option: `NODE_SIZE`). -/
elk_enum AnnulusWedgeCriteria := leafNumber nodeSize

end Elk.Alg.Radial.Options
