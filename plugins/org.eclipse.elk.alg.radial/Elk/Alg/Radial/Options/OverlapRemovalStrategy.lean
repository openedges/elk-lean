import Elk.Graph.Enum
/-!
# `org.eclipse.elk.alg.radial.options.OverlapRemovalStrategy`

Port of `overlap_removal_strategy.rs` (elk-rs). The factory half of the Rust enum (`create`, which
builds the `IOverlapRemoval`) lives in
`Elk.Alg.Radial.Intermediate.Overlaps.RadiusExtensionOverlapRemoval`.
-/
namespace Elk.Alg.Radial.Options

/-- `OverlapRemovalStrategy`: the overlap removal implementations. -/
elk_enum OverlapRemovalStrategy := extentRadii

end Elk.Alg.Radial.Options
