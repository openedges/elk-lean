import Elk.Graph.Enum
/-!
# `org.eclipse.elk.alg.rectpacking.options.OptimizationGoal`

Port of `options/optimization_goal.rs` (elk-rs): the optimization goal of the first width
approximation iteration (`AreaApproximation`). Declaration order (= ordinal) as in Java/Rust.
-/
namespace Elk.Alg.RectPacking.Options

/-- `OptimizationGoal`: `ASPECT_RATIO_DRIVEN`, `MAX_SCALE_DRIVEN` (default), `AREA_DRIVEN`. -/
elk_enum OptimizationGoal := aspectRatioDriven maxScaleDriven areaDriven

end Elk.Alg.RectPacking.Options
