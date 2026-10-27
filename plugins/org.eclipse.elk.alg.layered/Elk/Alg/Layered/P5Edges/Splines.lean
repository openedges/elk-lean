import Elk.Alg.Layered.P5Edges.Splines.SplinesMath
import Elk.Alg.Layered.P5Edges.Splines.Rectangle
import Elk.Alg.Layered.P5Edges.Splines.NubSpline
import Elk.Alg.Layered.P5Edges.Splines.NubsSelfLoop
import Elk.Alg.Layered.P5Edges.Splines.SplineSegment
import Elk.Alg.Layered.P5Edges.Splines.SplineEdgeRouter
/-!
# `org.eclipse.elk.alg.layered.p5edges.splines`

Aggregator of the spline edge routing package: `SplineEdgeRouter` (the `EdgeRouting.SPLINES` phase,
registered with `LayeredPhases.registerPhase .p5EdgeRouting`), the segment data (`SplineSegment`),
`NubSpline`/`NubsSelfLoop` (NURBS without weights → Bezier control points), `Rectangle` and
`SplinesMath`.
-/
