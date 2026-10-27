import Elk.Graph.Enum
/-!
# `org.eclipse.elk.alg.radial.options.RadialTranslationStrategy`

Port of `radial_translation_strategy.rs` (elk-rs). The factory half of the Rust enum (`create`,
which builds the optional `IEvaluation`) lives in `Elk.Alg.Radial.P1Position.EadesRadial`, the
only user, because the evaluations depend on the options.
-/
namespace Elk.Alg.Radial.Options

/-- `RadialTranslationStrategy`: the criterion used to find the optimal translation (rotation
offset) of the first radii. -/
elk_enum RadialTranslationStrategy := none edgeLength edgeLengthByPosition crossingMinimizationByPosition

end Elk.Alg.Radial.Options
