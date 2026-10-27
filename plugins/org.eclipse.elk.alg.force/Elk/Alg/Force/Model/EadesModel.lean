import Elk.Alg.Force.Model.AbstractForceModel
/-!
# `org.eclipse.elk.alg.force.model.EadesModel`

Port of `eades_model.rs` (elk-rs): Eades' spring embedder. Attractive forces grow logarithmically with
the distance (`ln(d / springLength)`) between connected particles, repulsive forces fall off with the
square of the distance. Uses the generic `ForceModel.layout`; like in Rust `avoid_same_position` is not
used, particles at the same position simply exert no force on each other.
-/
namespace Elk.Alg.Force.Model

open Elk.Graph Elk.Core.Math Elk.Core.Util Elk.Alg.Force.Graph Elk.Alg.Force.Options

/-- `ZERO_FACTOR`: force factor used when two particles touch (distance 0). -/
def EADES_ZERO_FACTOR : Float := 100.0

/-- elk-rs `EadesModel`: the model state read in `initialize_model`. -/
structure EadesModel where
  maxIterations : Int := 0
  springLength : Float := 0.0
  repulsionFactor : Float := 0.0

namespace EadesModel

/-- `EadesModel::repulsive(d, r)`. -/
def repulsive (d r : Float) : Float :=
  if d > 0.0 then r / (d * d) else r * EADES_ZERO_FACTOR

/-- `EadesModel::attractive(d, s)`. -/
def attractive (d s : Float) : Float :=
  if d > 0.0 then Float.log (d / s) else -EADES_ZERO_FACTOR

/-- `initialize_model`: iterations (300), spring length (`SPACING_NODE_NODE`, 80 if the property has no
default) and repulsion factor (5.0) from the graph's options. -/
def initializeModel (g : FGraph) : EadesModel :=
  { maxIterations := g.props.getD ForceOptions.ITERATIONS 300
    springLength := g.props.getD ForceOptions.SPACING_NODE_NODE 80.0
    repulsionFactor := g.props.getD ForceOptions.REPULSION 5.0 }

/-- `calc_displacement(graph, forcer, forcee)`. -/
def calcDisplacement (m : EadesModel) (g : FGraph) (forcer forcee : FParticleId) : Option KVector :=
  let forceePos := g.arena.particlePosition forcee
  let forcerPos := g.arena.particlePosition forcer
  let displacement := forceePos - forcerPos
  let length := displacement.length
  if length == 0.0 then none
  else
    let forcerRadius := g.arena.particleRadius forcer
    let forceeRadius := g.arena.particleRadius forcee
    let d := fmax (length - forcerRadius - forceeRadius) 0.0
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
