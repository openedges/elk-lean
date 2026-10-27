import Elk.Graph
/-!
# `org.eclipse.elk.alg.force.stress.Dimension`

The dimensions that the stress layout may alter (`StressOptions.DIMENSION`). In elk-rs the enum is
declared next to `StressMajorization`; Java has it as its own class, so it gets its own module here.
-/
namespace Elk.Alg.Force.Stress

/-- `Dimension`: `XY` (both), `X` (only x) or `Y` (only y). -/
elk_enum Dimension := xy x y

end Elk.Alg.Force.Stress
