import Elk.Alg.Force.Model.AbstractForceModel
/-!
# `org.eclipse.elk.alg.force.model.FruchtermanReingoldModel`

Port of `fruchterman_reingold_model.rs` (elk-rs): the Fruchterman-Reingold model with a linearly
decreasing temperature. elk-rs overrides the generic `layout` of the trait with a flat-array version
(the "SoA-optimized" layout); this port follows that version exactly, because it differs from the
generic loop: it calls `avoid_same_position`/wiggles particles at identical positions, it cools the
temperature before computing the forces of an iteration, and the trait's `calc_displacement` is never
used for this model (so it is not ported).

Iteration structure of one iteration (Rust order):
1. positions are written back to the arena, `AbstractForceModel.iterationDone` refreshes labels and
   bend points, the temperature is lowered by `threshold`, positions are read again;
2. for every particle `v` (index order nodes, labels, bend points) and every other particle `u`: if both
   are at the same position they are separated (bend points through the arena and
   `avoidSamePosition`, other particles by wiggling the local copies until they differ), then
   `force = repulsive(d, k) * priority(u) - attractive(d, k) * connection(u, v)` scaled by
   `temperature / length` is added to the displacement of `v` (`d` = distance minus both radii, at
   least 0);
3. displacements are bounded by `dispBound` and added to the positions.
-/
namespace Elk.Alg.Force.Model

open Elk.Graph Elk.Core.Math Elk.Core.Util Elk.Alg.Force.Graph Elk.Alg.Force.Options

/-- `SPACING_FACTOR`. -/
def FR_SPACING_FACTOR : Float := 0.01
/-- `ZERO_FACTOR`: force factor used when two particles touch (distance 0). -/
def FR_ZERO_FACTOR : Float := 100.0

/-- elk-rs `FruchtermanReingoldModel`: temperature, its decrement per iteration and the ideal edge
length `k`. -/
structure FruchtermanReingoldModel where
  temperature : Float := 0.0
  threshold : Float := 0.0
  k : Float := 0.0

namespace FruchtermanReingoldModel

/-- `FruchtermanReingoldModel::repulsive(d, k)`. -/
def repulsive (d k : Float) : Float :=
  if d > 0.0 then k * k / d else k * k * FR_ZERO_FACTOR

/-- `FruchtermanReingoldModel::attractive(d, k)`. -/
def attractive (d k : Float) : Float := d * d / k

/-- `initialize_model`: temperature (0.001), threshold (`temperature / iterations`) and `k`
(`sqrt(area / (2 n)) * spacing * 0.01`, `spacing` = `SPACING_NODE_NODE`). -/
def initializeModel (g : FGraph) : FruchtermanReingoldModel := Id.run do
  let temperature := g.props.getD ForceOptions.TEMPERATURE 0.001
  let iterations := g.props.getD ForceOptions.ITERATIONS 300
  let threshold := if iterations > 0 then temperature / Float.ofInt iterations else temperature
  let n := g.nodes.size.toFloat
  let mut totalWidth := 0.0
  let mut totalHeight := 0.0
  for nid in g.nodes do
    totalWidth := totalWidth + (g.arena.nodeSize[nid.idx]!).x
    totalHeight := totalHeight + (g.arena.nodeSize[nid.idx]!).y
  let area := totalWidth * totalHeight
  let spacing := g.props.getD ForceOptions.SPACING_NODE_NODE 80.0
  let c := spacing * FR_SPACING_FACTOR
  let k := if n > 0.0 then Float.sqrt (area / (2.0 * n)) * c else 0.0
  return { temperature, threshold, k }

/-- Particle data extracted from the arena for the flat-array loops. -/
private structure Flat where
  particles : Array FParticleId
  radii : FloatArray
  priorities : Array Int
  /-- Row-major `n x n` connection weights (`FGraph::get_connection`), diagonal 0. -/
  connections : Array Int

private def extractFlat (g : FGraph) : Flat := Id.run do
  let particles := g.particleIds
  let n := particles.size
  let mut radii := FloatArray.emptyWithCapacity n
  let mut priorities : Array Int := Array.mkEmpty n
  for p in particles do
    radii := radii.push (g.arena.particleRadius p)
    priorities := priorities.push ((g.arena.particleProperties p).getD ForceOptions.PRIORITY 1)
  let mut connections : Array Int := Array.replicate (n * n) 0
  for i in [0:n] do
    for j in [0:n] do
      if i == j then continue
      connections := connections.set! (i * n + j) (g.getConnection particles[i]! particles[j]!)
  return { particles, radii, priorities, connections }

/-- Particle positions as flat coordinate arrays. -/
private def readPositions (g : FGraph) (particles : Array FParticleId) : FloatArray × FloatArray := Id.run do
  let mut px := FloatArray.emptyWithCapacity particles.size
  let mut py := FloatArray.emptyWithCapacity particles.size
  for p in particles do
    let pos := g.arena.particlePosition p
    px := px.push pos.x
    py := py.push pos.y
  return (px, py)

/-- Writes flat positions back to the arena. -/
private def writePositions (g : FGraph) (particles : Array FParticleId) (px py : FloatArray) : FGraph :=
  Id.run do
    let mut arena := g.arena
    for i in [0:particles.size] do
      arena := arena.setParticlePosition particles[i]! ⟨px.get! i, py.get! i⟩
    return { g with arena }

/-- Stores the positions of two particles in the arena. -/
private def setTwoPositions (g : FGraph) (a b : FParticleId) (pa pb : KVector) : FGraph :=
  { g with arena := (g.arena.setParticlePosition a pa).setParticlePosition b pb }

/-- `isBend`. -/
private def isBend : FParticleId → Bool
  | .bend _ => true
  | _ => false

/-- `FruchtermanReingoldModel::layout(graph, monitor)` (the flat-array version of elk-rs). -/
def layout (monitor : ProgressMonitor) : FM Unit := do
  let _ ← monitor.begin "Component Layout" 1.0
  let base ← AbstractForceModel.initializeBase
  let mut st := initializeModel (← get)
  let flat := extractFlat (← get)
  let particles := flat.particles
  let n := particles.size
  let radii := flat.radii
  let priorities := flat.priorities
  let connections := flat.connections
  let (px0, py0) := readPositions (← get) particles
  let mut px := px0
  let mut py := py0
  let dispBound := base.dispBound
  let mut random := base.random
  let mut dx := FloatArray.mk (Array.replicate n 0.0)
  let mut dy := FloatArray.mk (Array.replicate n 0.0)
  while st.temperature > 0.0 && !(← monitor.isCanceled) do
    -- write positions back for the label / bend point refresh, cool down, read them again
    modify (writePositions · particles px py)
    AbstractForceModel.iterationDone
    st := { st with temperature := st.temperature - st.threshold }
    let (px', py') := readPositions (← get) particles
    px := px'
    py := py'
    for i in [0:n] do
      dx := dx.set! i 0.0
      dy := dy.set! i 0.0
    -- O(n^2) force computation
    for vi in [0:n] do
      for ui in [0:n] do
        if ui == vi then continue
        if px.get! ui == px.get! vi && py.get! ui == py.get! vi then
          if isBend particles[ui]! || isBend particles[vi]! then
            -- bend points: edge aware separation through the arena
            modify (setTwoPositions · particles[ui]! particles[vi]! ⟨px.get! ui, py.get! ui⟩
              ⟨px.get! vi, py.get! vi⟩)
            random ← AbstractForceModel.avoidSamePosition random particles[ui]! particles[vi]!
            let pu := (← get).arena.particlePosition particles[ui]!
            let pv := (← get).arena.particlePosition particles[vi]!
            px := px.set! ui pu.x
            py := py.set! ui pu.y
            px := px.set! vi pv.x
            py := py.set! vi pv.y
          else
            let mut separated := false
            while !separated do
              let (nu, r1) := wiggle ⟨px.get! ui, py.get! ui⟩ random 1.0
              let (nv, r2) := wiggle ⟨px.get! vi, py.get! vi⟩ r1 1.0
              random := r2
              px := px.set! ui nu.x
              py := py.set! ui nu.y
              px := px.set! vi nv.x
              py := py.set! vi nv.y
              if nu.x != nv.x || nu.y != nv.y then separated := true
        -- displacement of vi caused by ui
        let ddx := px.get! vi - px.get! ui
        let ddy := py.get! vi - py.get! ui
        let length := Float.sqrt (ddx * ddx + ddy * ddy)
        if length == 0.0 then continue
        let d := fmax (length - radii.get! ui - radii.get! vi) 0.0
        let mut force := repulsive d st.k * Float.ofInt priorities[ui]!
        let connection := connections[ui * n + vi]!
        if connection > 0 then
          force := force - attractive d st.k * Float.ofInt connection
        let s := force * st.temperature / length
        dx := dx.set! vi (dx.get! vi + ddx * s)
        dy := dy.set! vi (dy.get! vi + ddy * s)
    -- apply the displacements with bounds
    for vi in [0:n] do
      let bounded := (KVector.mk (dx.get! vi) (dy.get! vi)).bound (-dispBound) (-dispBound) dispBound dispBound
      px := px.set! vi (px.get! vi + bounded.x)
      py := py.set! vi (py.get! vi + bounded.y)
  -- final write-back of the positions, displacements are reset
  modify fun g =>
    let g := writePositions g particles px py
    { g with arena := particles.foldl (fun a p => a.setParticleDisplacement p {}) g.arena }
  AbstractForceModel.storeRandom random
  monitor.done

end FruchtermanReingoldModel

end Elk.Alg.Force.Model
