import Std.Data.HashMap
import Elk.Graph
import Elk.Core.Math.KVector
import Elk.Core.Util.Random
import Elk.Core.Util.Java
import Elk.Core.Util.ProgressMonitor
import Elk.Alg.Force.Graph.FGraph
import Elk.Alg.Force.Options.ForceOptions
import Elk.Core.Util.FloatConst
open Elk.Core.Util.FloatConst
/-!
# `org.eclipse.elk.alg.force.model.AbstractForceModel`

Port of `abstract_force_model.rs` (elk-rs): the shared part of the force models. The Rust trait
`ForceModel` (`initialize_model`, `more_iterations`, `calc_displacement`, `iteration_done` and the
default `layout`) becomes the strategy record `ForceModel` with the generic `layout` below;
the model specific state `σ` is threaded explicitly. `AbstractForceModel` itself keeps the random
generator and the displacement bound.

Iteration order of the generic `layout` (Java `AbstractForceModel.layout`, used by the Eades model):
for every particle `v` (nodes, labels, bend points of the graph lists) and every other particle `u`,
`avoidSamePosition(u, v)` separates the two if they share a position (elk-rs skipped this) and the
displacement `calcDisplacement(u, v)` is added to the displacement of `v`; all positions are updated
afterwards. The accumulation happens in a local array indexed by the first entry of each particle
(`ParticleIdentity`: a label listed twice is one Java object, see `ComponentsProcessor`).

`wiggle` delegates to `Elk.Core.Math.KVector.wiggle` (Rust/Java rounding `x + (r * a - a / 2)`).
-/

namespace Elk.Alg.Force.Model

open Elk.Graph Elk.Core.Math Elk.Core.Util Elk.Alg.Force.Graph Elk.Alg.Force.Options

/-- `DISP_BOUND_FACTOR`. -/
def DISP_BOUND_FACTOR : Float := 16.0

/-- elk-rs `AbstractForceModel`: the random generator of the layout and the displacement bound. -/
structure AbstractForceModel where
  random : Random := {}
  dispBound : Float := fl0p0

/-- `KVector::wiggle(random, amount)` (`Elk.Core.Math.KVector.wiggle`, Rust/Java rounding
`x + (r * amount - amount / 2)`). -/
@[inline] def wiggle (v : KVector) (random : Random) (amount : Float) : KVector × Random :=
  KVector.wiggle v random amount

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
of their edges; any other pair is wiggled randomly. Java semantics: the loop test is
`pu.x - pv.x == 0 && pu.y - pv.y == 0` and the orthogonal vectors divide by the edge length unguarded,
so a zero-length edge yields NaN coordinates and ends the loop (elk-rs looped forever there). -/
partial def avoidSamePosition (random : Random) (u v : FParticleId) : FM Random := do
  let mut random := random
  while true do
    let pu := (← get).arena.particlePosition u
    let pv := (← get).arena.particlePosition v
    -- Java `while (pu.x - pv.x == 0 && pu.y - pv.y == 0)` (infinite or NaN coordinates end the loop)
    if !(pu.x - pv.x == fl0p0 && pu.y - pv.y == fl0p0) then return random
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
        -- Java divides by the edge length unguarded: a zero-length edge gives NaN coordinates,
        -- which end the loop (elk-rs skipped the move and looped forever)
        let uVec := KVector.fromPoints us ut
        let orthogonalU : KVector := ⟨uVec.x / uVec.length * fl2p0, -uVec.y / uVec.length * fl2p0⟩
        let vVec := KVector.fromPoints vs vt
        let orthogonalV : KVector := ⟨vVec.x / vVec.length * fl2p0, -(vVec.y / vVec.length) * fl2p0⟩
        let moved := (pu + orthogonalU) + orthogonalV
        modify fun g => { g with arena := g.arena.setParticlePosition u moved }
        triedForBendpoints := true
    if !triedForBendpoints then
      let (pu', r1) := wiggle pu random fl1p0
      let (pv', r2) := wiggle pv r1 fl1p0
      random := r2
      modify fun g => { g with arena := (g.arena.setParticlePosition u pu').setParticlePosition v pv' }
  return random

end AbstractForceModel

/-- Java object identity of the entries of a particle list. Java's lists hold objects: a label whose
edge is listed twice in a component (see `ComponentsProcessor.buildComponent`) is the same `FLabel`
twice in `getParticles()`. `first[i]` is the index of the first entry of the particle at `i` (nodes
and bend points are never repeated, so `first[i] = i` for them); `groups` lists the entries of every
repeated particle (first entry first) and `groupOf[i]` is the group of entry `i` (`groups.size` for an
entry that is not repeated). -/
structure ParticleIdentity where
  first : Array USize
  groupOf : Array Nat
  groups : Array (Array Nat)
  deriving Inhabited

namespace ParticleIdentity

/-- The identity table of a particle list (`FGraph.particleIds`). -/
def ofParticles (particles : Array FParticleId) : ParticleIdentity := Id.run do
  let n := particles.size
  let mut first : Array USize := Array.mkEmpty n
  let mut seen : Std.HashMap Nat Nat := {}
  let mut repeated : Array Nat := #[]
  for i in [0:n] do
    match particles[i]! with
    | .label l =>
      match seen[l.idx]? with
      | some f =>
        first := first.push f.toUSize
        repeated := repeated.push i
      | none =>
        seen := seen.insert l.idx i
        first := first.push i.toUSize
    | _ => first := first.push i.toUSize
  if repeated.isEmpty then
    return { first, groupOf := #[], groups := #[] }
  let mut groupOf : Array Nat := Array.replicate n n
  let mut groups : Array (Array Nat) := #[]
  for i in repeated do
    let f := (first[i]!).toNat
    let gi := groupOf[f]!
    if gi < groups.size then
      groups := groups.modify gi (·.push i)
      groupOf := groupOf.set! i gi
    else
      groupOf := (groupOf.set! f groups.size).set! i groups.size
      groups := groups.push #[f, i]
  -- `n` marks the entries without repetition
  groupOf := groupOf.map fun g => if g == n then groups.size else g
  return { first, groupOf, groups }

/-- Whether some particle is listed more than once. -/
@[inline] def hasRepeats (t : ParticleIdentity) : Bool := !t.groups.isEmpty

/-- The other entries of the particle at entry `i` (empty if it is listed once). -/
@[inline] def others (t : ParticleIdentity) (i : Nat) : Array Nat :=
  match t.groupOf[i]? with
  | some g => match t.groups[g]? with
    | some es => es.filter (· != i)
    | none => #[]
  | none => #[]

end ParticleIdentity

/-- The Rust trait `ForceModel`: what a concrete model contributes to the generic `layout`. `σ` is the
model state (`max_iterations`, `temperature`, ...). -/
structure ForceModel (σ : Type) where
  /-- `initialize_model(graph)`. -/
  initializeModel : FGraph → σ
  /-- `more_iterations(count)`. -/
  moreIterations : σ → Int → Bool
  /-- `calcDisplacement(forcer, forcee)` after `avoidSamePosition`: the displacement `forcer` causes on
  `forcee` (`none` = Java `null`, no displacement). -/
  calcDisplacement : σ → FGraph → FParticleId → FParticleId → Option KVector
  /-- `iteration_done()` (default: nothing). -/
  iterationDone : σ → σ := id

namespace ForceModel

/-- The pair loop of particle `v` (entry `vi`) from entry `ui` on, with the graph unchanged:
`calcDisplacement(u, v)` of every other particle `u` is added to `acc` in list order. Stops at the
first `u` that shares the position of `v` (Java's `avoidSamePosition` test
`pu.x - pv.x == 0 && pu.y - pv.y == 0`), which the caller separates in the monad; returns the sum
and that entry (`particles.size` when the row is done). -/
private partial def scanRow {σ : Type} (model : ForceModel σ) (st : σ) (g : FGraph)
    (particles : Array FParticleId) (v : FParticleId) (ui : Nat) (acc : KVector) : KVector × Nat :=
  if h : ui < particles.size then
    let u := particles[ui]
    if u == v then scanRow model st g particles v (ui + 1) acc
    else
      let pu := g.arena.particlePosition u
      let pv := g.arena.particlePosition v
      if pu.x - pv.x == 0.0 && pu.y - pv.y == 0.0 then (acc, ui)
      else
        let acc := match model.calcDisplacement st g u v with
          | some d => acc + d
          | none => acc
        scanRow model st g particles v (ui + 1) acc
  else (acc, particles.size)

/-- `AbstractForceModel.layout(fgraph, monitor)`: the generic force layout loop of Java. Every
iteration calls `iterationDone`, then for every particle `v` of `getParticles()` and every other
particle `u` (object identity: repeated entries of `v` itself are skipped) separates the two if they
share a position (`avoidSamePosition`, which may move them and advances the random generator) and adds
`calcDisplacement(u, v)` to the displacement of `v`; afterwards every entry's displacement is bounded,
added to its position and reset. The displacement belongs to the particle, so a particle listed twice
accumulates both passes and moves once (its second entry adds the reset zero vector). -/
def layout {σ : Type} (model : ForceModel σ) (monitor : ProgressMonitor) : FM Unit := do
  let _ ← monitor.begin "Component Layout" 1.0
  let base ← AbstractForceModel.initializeBase
  let mut random := base.random
  let mut st := model.initializeModel (← get)
  let particles := (← get).particleIds
  let ident := ParticleIdentity.ofParticles particles
  let n := particles.size
  let zero : KVector := {}
  let mut iterations : Int := 0
  while model.moreIterations st iterations && !(← monitor.isCanceled) do
    AbstractForceModel.iterationDone
    st := model.iterationDone st
    let mut disp : Array KVector := Array.replicate n zero
    for vi in [0:n] do
      let v := particles[vi]!
      let slot := (ident.first[vi]!).toNat
      let mut acc := disp[slot]!
      let mut ui := 0
      while ui < n do
        let (acc', stop) := scanRow model st (← get) particles v ui acc
        acc := acc'
        if stop >= n then break
        -- `u` shares the position of `v`: separate them, then the pair's displacement
        let u := particles[stop]!
        random ← AbstractForceModel.avoidSamePosition random u v
        if let some d := model.calcDisplacement st (← get) u v then acc := acc + d
        ui := stop + 1
      disp := disp.set! slot acc
    for vi in [0:n] do
      let v := particles[vi]!
      let slot := (ident.first[vi]!).toNat
      let bounded := (disp[slot]!).bound (-base.dispBound) (-base.dispBound) base.dispBound base.dispBound
      modify fun g => { g with arena := g.arena.setParticlePosition v (g.arena.particlePosition v + bounded) }
      disp := disp.set! slot zero
    iterations := iterations + 1
  AbstractForceModel.storeRandom random
  monitor.done

end ForceModel

end Elk.Alg.Force.Model
