import Elk.Graph
import Elk.Core.Math.KVector
import Elk.Core.Util.Random
import Elk.Core.Util.Java
import Elk.Core.Util.ProgressMonitor
import Elk.Alg.Force.Graph.FGraph
import Elk.Alg.Force.Options.ForceOptions
/-!
# `org.eclipse.elk.alg.force.model.AbstractForceModel`

Port of `abstract_force_model.rs` (elk-rs): the shared part of the force models. The Rust trait
`ForceModel` (`initialize_model`, `more_iterations`, `calc_displacement`, `iteration_done` and the
default `layout`) becomes the strategy record `ForceModel` with the generic `layout` below;
the model specific state `σ` is threaded explicitly. `AbstractForceModel` itself keeps the random
generator and the displacement bound.

Iteration order of the generic `layout` (identical to Rust): for every particle `v` (nodes, labels,
bend points of the graph lists) and every other particle `u` the displacement `calc_displacement(u, v)`
is added to the displacement of `v`; all positions are updated afterwards, so the pairwise forces of
one iteration are computed from the positions at the start of the iteration. The accumulation therefore
happens in a local array (starting from the arena displacement, which is zero).

`KVector.wiggle` is re-implemented as `wiggle` because Rust (`x += r * a - a / 2`) and Java add the
whole offset to the coordinate, while `Elk.Core.Math.KVector.wiggle` adds the two terms one after the
other, which rounds differently.
-/
namespace Elk.Alg.Force.Model

open Elk.Graph Elk.Core.Math Elk.Core.Util Elk.Alg.Force.Graph Elk.Alg.Force.Options

/-- `DISP_BOUND_FACTOR`. -/
def DISP_BOUND_FACTOR : Float := 16.0

/-- elk-rs `AbstractForceModel`: the random generator of the layout and the displacement bound. -/
structure AbstractForceModel where
  random : Random := {}
  dispBound : Float := 0.0

/-- `KVector::wiggle(random, amount)` with the Rust/Java rounding: `x + (r * amount - amount / 2)`. -/
def wiggle (v : KVector) (random : Random) (amount : Float) : KVector × Random :=
  let (dx, random) := random.nextDouble
  let (dy, random) := random.nextDouble
  (⟨v.x + (dx * amount - amount / 2.0), v.y + (dy * amount - amount / 2.0)⟩, random)

namespace AbstractForceModel

/-- `AbstractForceModel::initialize(graph)` (named `initializeBase`, `initialize` is a Lean keyword): fetches the random generator (seed 1 if the graph has
none), computes the adjacency matrix and the displacement bound, places the nodes at random positions
unless the layout is interactive, and adds `REPULSIVE_POWER` bend points to every edge. -/
def initializeBase : FM AbstractForceModel := do
  let mut random := ((← get).random).getD (Random.ofInt 1)
  modify (·.calcAdjacency)
  let nodes := (← get).nodes
  let edgeCount := (← get).edges.size
  let dispBound := fmax (nodes.size.toFloat * DISP_BOUND_FACTOR + edgeCount.toFloat)
    (DISP_BOUND_FACTOR * DISP_BOUND_FACTOR)
  let interactive := ((← get).props).getD ForceOptions.INTERACTIVE false
  if !interactive then
    let posScale := nodes.size.toFloat
    for nid in nodes do
      let (x, r1) := random.nextDouble
      let (y, r2) := r1.nextDouble
      random := r2
      modify fun g => { g with arena := { g.arena with
        nodePosition := g.arena.nodePosition.set! nid.idx ⟨x * posScale, y * posScale⟩ } }
  for eid in (← get).edges do
    let count := ((← get).arena.edgeProperties[eid.idx]!).getD ForceOptions.REPULSIVE_POWER 0
    if count > 0 then
      for _ in [0:count.toNat] do
        modify fun g =>
          let (a, bid) := g.arena.addBendpoint eid
          { g with arena := a, bendpoints := g.bendpoints.push bid }
      modify (·.distributeBendpoints eid)
  return { random, dispBound }

/-- Stores the (advanced) random generator in the graph. In Rust the generator of the graph property
`RANDOM` is shared by reference (`Random` clones share their state, like the Java object), so the
draws of one component continue the sequence of the previous one; the providers hand the generator
of a finished component to the next, which is what storing it here enables. -/
def storeRandom (random : Random) : FM Unit :=
  modify fun g => { g with random := some random }

/-- `AbstractForceModel::iteration_done(graph)`: refreshes the label positions and redistributes the
bend points of every edge. -/
def iterationDone : FM Unit := do
  for eid in (← get).edges do
    for lid in (← get).arena.edgeLabels[eid.idx]! do
      modify (·.refreshLabelPosition lid)
    modify (·.distributeBendpoints eid)

/-- `AbstractForceModel::avoid_same_position(random, graph, u, v)`: while `u` and `v` have the same
position, moves them apart. Two bend points of (different) edges are moved by the orthogonal vectors
of their edges; any other pair is wiggled randomly. Like in Rust this loops forever if the bend point
branch cannot separate the particles (zero-length edges). -/
partial def avoidSamePosition (random : Random) (u v : FParticleId) : FM Random := do
  let mut random := random
  while true do
    let pu := (← get).arena.particlePosition u
    let pv := (← get).arena.particlePosition v
    if pu.x != pv.x || pu.y != pv.y then return random
    let mut triedForBendpoints := false
    if let (.bend b1, .bend b2) := (u, v) then
      let uEdge := (← get).arena.bendEdge[b1.idx]!
      let vEdge := (← get).arena.bendEdge[b2.idx]!
      if let (some uEid, some vEid) := (uEdge, vEdge) then
        let g ← get
        let uSource := g.edgeSourcePoint uEid
        let uTarget := g.edgeTargetPoint uEid
        let vSource := g.edgeSourcePoint vEid
        let vTarget := g.edgeTargetPoint vEid
        let (some us, some ut, some vs, some vt) := (uSource, uTarget, vSource, vTarget)
          | return random
        let uVec := KVector.fromPoints us ut
        let orthogonalU : KVector :=
          if uVec.length > 0.0 then
            ⟨(uVec.x / uVec.length) * 2.0, (-(uVec.y / uVec.length)) * 2.0⟩
          else {}
        let vVec := KVector.fromPoints vs vt
        let orthogonalV : KVector :=
          if vVec.length > 0.0 then
            ⟨(vVec.x / vVec.length) * 2.0, (-(vVec.y / vVec.length)) * 2.0⟩
          else {}
        let moved := (pu + orthogonalU) + orthogonalV
        modify fun g => { g with arena := g.arena.setParticlePosition u moved }
        triedForBendpoints := true
    if !triedForBendpoints then
      let (pu', r1) := wiggle pu random 1.0
      let (pv', r2) := wiggle pv r1 1.0
      random := r2
      modify fun g => { g with arena := (g.arena.setParticlePosition u pu').setParticlePosition v pv' }
  return random

end AbstractForceModel

/-- The Rust trait `ForceModel`: what a concrete model contributes to the generic `layout`. `σ` is the
model state (`max_iterations`, `temperature`, ...). -/
structure ForceModel (σ : Type) where
  /-- `initialize_model(graph)`. -/
  initializeModel : FGraph → σ
  /-- `more_iterations(count)`. -/
  moreIterations : σ → Int → Bool
  /-- `calc_displacement(graph, forcer, forcee)`: the displacement `forcer` causes on `forcee`. -/
  calcDisplacement : σ → FGraph → FParticleId → FParticleId → Option KVector
  /-- `iteration_done()` (default: nothing). -/
  iterationDone : σ → σ := id

namespace ForceModel

/-- Displacement of every particle caused by all other particles (the pair loops of `layout`). -/
private def pairDisplacements {σ : Type} (model : ForceModel σ) (st : σ) (g : FGraph)
    (particles : Array FParticleId) : Array KVector := Id.run do
  let n := particles.size
  let mut disp : Array KVector := particles.map g.arena.particleDisplacement
  for vi in [0:n] do
    let v := particles[vi]!
    for ui in [0:n] do
      let u := particles[ui]!
      if u == v then continue
      match model.calcDisplacement st g u v with
      | some d => disp := disp.modify vi (· + d)
      | none => pure ()
  return disp

/-- Applies the bounded displacements to the particle positions and resets the displacements. -/
private def applyDisplacements (g : FGraph) (particles : Array FParticleId) (disp : Array KVector)
    (dispBound : Float) : FGraph := Id.run do
  let mut arena := g.arena
  for vi in [0:particles.size] do
    let v := particles[vi]!
    let bounded := (disp[vi]!).bound (-dispBound) (-dispBound) dispBound dispBound
    arena := arena.setParticlePosition v (arena.particlePosition v + bounded)
    arena := arena.setParticleDisplacement v {}
  return { g with arena }

/-- `ForceModel::layout(graph, monitor)`: the generic force layout loop. -/
def layout {σ : Type} (model : ForceModel σ) (monitor : ProgressMonitor) : FM Unit := do
  let _ ← monitor.begin "Component Layout" 1.0
  let base ← AbstractForceModel.initializeBase
  AbstractForceModel.storeRandom base.random
  let mut st := model.initializeModel (← get)
  let mut iterations : Int := 0
  while model.moreIterations st iterations && !(← monitor.isCanceled) do
    AbstractForceModel.iterationDone
    st := model.iterationDone st
    let particles := (← get).particleIds
    let disp := pairDisplacements model st (← get) particles
    modify (applyDisplacements · particles disp base.dispBound)
    iterations := iterations + 1
  monitor.done

end ForceModel

end Elk.Alg.Force.Model
