import Elk.Core.Math
/-! `org.eclipse.elk.alg.layered.graph.LMargin`: an `ElkMargin` (the Java subclass adds no state). -/
namespace Elk.Alg.Layered.Graph

/-- `LMargin` = `ElkMargin` (top/right/bottom/left, all `0.0` by default). -/
abbrev LMargin := Elk.Core.Math.ElkMargin

end Elk.Alg.Layered.Graph
