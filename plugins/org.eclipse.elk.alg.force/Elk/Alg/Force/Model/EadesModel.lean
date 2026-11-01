import Elk.Alg.Force.Model.AbstractForceModel
import Elk.Core.Util.FloatConst
open Elk.Core.Util.FloatConst
/-!
# `org.eclipse.elk.alg.force.model.EadesModel`

Port of `eades_model.rs` (elk-rs): Eades' spring embedder. Attractive forces grow logarithmically with
the distance (`ln(d / springLength)`) between connected particles, repulsive forces fall off with the
square of the distance. Uses the generic `ForceModel.layout`, which (like Java's `calcDisplacement`)
separates particles at the same position with `avoidSamePosition` before the force is computed (elk-rs
skipped the separation, so coinciding particles exerted no force on each other and the random
generator was not advanced).
-/

namespace Elk.Alg.Force.Model

open Elk.Graph Elk.Core.Math Elk.Core.Util Elk.Alg.Force.Graph Elk.Alg.Force.Options

/-- `ZERO_FACTOR`: force factor used when two particles touch (distance 0). -/
def EADES_ZERO_FACTOR : Float := 100.0

/-- elk-rs `EadesModel`: the model state read in `initialize_model`. -/
structure EadesModel where
  maxIterations : Int := 0
  springLength : Float := fl0p0
  repulsionFactor : Float := fl0p0

namespace EadesModel

/-- `EadesModel::repulsive(d, r)`. -/
def repulsive (d r : Float) : Float :=
  if d > 0.0 then r / (d * d) else r * EADES_ZERO_FACTOR

/-- `EadesModel.attractive(d, s)`: Java `Math.log` is `javaLog` (fdlibm; the C library's `log`
differs by an ulp now and then). -/
def attractive (d s : Float) : Float :=
  if d > 0.0 then javaLog (d / s) else -EADES_ZERO_FACTOR

/-- `initialize_model`: iterations (300), spring length (`SPACING_NODE_NODE`, 80 if the property has no
default) and repulsion factor (5.0) from the graph's options. -/
def initializeModel (g : FGraph) : EadesModel :=
  { maxIterations := g.props.getD ForceOptions.ITERATIONS 300
    springLength := g.props.getD ForceOptions.SPACING_NODE_NODE fl80p0
    repulsionFactor := g.props.getD ForceOptions.REPULSION fl5p0 }

/-- `EadesModel.calcDisplacement(forcer, forcee)` after `avoidSamePosition` (run by the generic
`ForceModel.layout`): Java divides by the distance unguarded and uses `Math.max(0, ...)` (NaN
propagates). -/
def calcDisplacement (m : EadesModel) (g : FGraph) (forcer forcee : FParticleId) : Option KVector :=
  let forceePos := g.arena.particlePosition forcee
  let forcerPos := g.arena.particlePosition forcer
  let displacement := forceePos - forcerPos
  let length := displacement.length
  let forcerRadius := g.arena.particleRadius forcer
  let forceeRadius := g.arena.particleRadius forcee
  let d := javaMax fl0p0 (length - forcerRadius - forceeRadius)
  let connection := g.getConnection forcer forcee
  let force :=
    if connection > 0 then
      -(attractive d m.springLength) * (Float.ofInt connection)
    else
      let priority := (g.arena.particleProperties forcer).getD ForceOptions.PRIORITY 1
      repulsive d m.repulsionFactor * (Float.ofInt priority)
  some (displacement.scale (force / length))

/-- The Eades model as a `ForceModel` strategy. -/
def model : ForceModel EadesModel where
  initializeModel := initializeModel
  moreIterations := fun m count => count < m.maxIterations
  calcDisplacement := calcDisplacement

/-- `EadesModel::layout(graph, monitor)` (the trait default). -/
def layout (monitor : ProgressMonitor) : FM Unit := ForceModel.layout model monitor

end EadesModel

end Elk.Alg.Force.Model
