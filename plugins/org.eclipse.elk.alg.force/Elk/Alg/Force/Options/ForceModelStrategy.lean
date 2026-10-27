import Elk.Graph
/-!
# `org.eclipse.elk.alg.force.options.ForceModelStrategy`

The force model used by the force layout (`ForceOptions.MODEL`).
-/
namespace Elk.Alg.Force.Options

/-- `ForceModelStrategy`: `EADES` (Eades' spring embedder) or `FRUCHTERMAN_REINGOLD`. -/
elk_enum ForceModelStrategy := eades fruchtermanReingold

end Elk.Alg.Force.Options
