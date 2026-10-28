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

Java's lists hold objects (FEL): a label of an edge that `ComponentsProcessor.split` lists twice is the
same particle at two entries of `getParticles()` (`ParticleIdentity`). Its entries share one position
(a separation of one entry moves all), the pair loop skips the other entries (Java `u != v`), the rows
of all entries accumulate one displacement (stored at the first entry), and the update moves it once
(the later entries add the reset zero vector).

Known deviations from Java's `calcDisplacement`, all for degenerate coordinates only (kept because the
Java forms cost about 10% of the force layout in the inner loop): a pair whose distance underflows to
0 exerts no force (Java divides by 0), `d` is 0 for a NaN distance (Java `Math.max(0, NaN)` is NaN),
and the scan's same-position test is `==` (equal infinite coordinates are tested again with Java's
`pu.x - pv.x == 0` before they are wiggled).
-/
/-! Float literals as global constants (FL): inside branches, loops and specialised code the compiler
shares a literal's `Nat`/`Bool` arguments with unrelated variables (CSE) and then parses it on every
evaluation (`FastFloat.ofScientificImpl`); a top-level constant is a load (PLAN §7.1 items 17, 22). -/
private def fl0p0 : Float := 0.0
private def fl0p001 : Float := 0.001
private def fl1p0 : Float := 1.0
private def fl2p0 : Float := 2.0
private def fl80p0 : Float := 80.0

namespace Elk.Alg.Force.Model

open Elk.Graph Elk.Core.Math Elk.Core.Util Elk.Alg.Force.Graph Elk.Alg.Force.Options

/-- `SPACING_FACTOR`. -/
def FR_SPACING_FACTOR : Float := 0.01
/-- `ZERO_FACTOR`: force factor used when two particles touch (distance 0). -/
def FR_ZERO_FACTOR : Float := 100.0

/-- elk-rs `FruchtermanReingoldModel`: temperature, its decrement per iteration and the ideal edge
length `k`. -/
structure FruchtermanReingoldModel where
  temperature : Float := fl0p0
  threshold : Float := fl0p0
  k : Float := fl0p0

namespace FruchtermanReingoldModel

/-- `FruchtermanReingoldModel::repulsive(d, k)`. -/
def repulsive (d k : Float) : Float :=
  if d > 0.0 then k * k / d else k * k * FR_ZERO_FACTOR

/-- `FruchtermanReingoldModel::attractive(d, k)`. -/
def attractive (d k : Float) : Float := d * d / k

/-- `initialize_model`: temperature (0.001), threshold (`temperature / iterations`) and `k`
(`sqrt(area / (2 n)) * spacing * 0.01`, `spacing` = `SPACING_NODE_NODE`). -/
def initializeModel (g : FGraph) : FruchtermanReingoldModel := Id.run do
  let temperature := g.props.getD ForceOptions.TEMPERATURE fl0p001
  let iterations := g.props.getD ForceOptions.ITERATIONS 300
  let threshold := if iterations > 0 then temperature / Float.ofInt iterations else temperature
  let n := g.nodes.size.toFloat
  let mut totalWidth := fl0p0
  let mut totalHeight := fl0p0
  for nid in g.nodes do
    totalWidth := totalWidth + (g.arena.nodeSize[nid.idx]!).x
    totalHeight := totalHeight + (g.arena.nodeSize[nid.idx]!).y
  let area := totalWidth * totalHeight
  let spacing := g.props.getD ForceOptions.SPACING_NODE_NODE fl80p0
  let c := spacing * FR_SPACING_FACTOR
  let k := if n > fl0p0 then Float.sqrt (area / (fl2p0 * n)) * c else fl0p0
  return { temperature, threshold, k }

/-- Particle data extracted from the arena for the flat-array loops. -/
private structure Flat where
  particles : Array FParticleId
  radii : FloatArray
  /-- `PRIORITY` of every particle as a float (`priority as f64`, converted once). -/
  priorities : FloatArray
  /-- Connection weights (`FGraph::get_connection as f64`, diagonal 0) by row of the affected
  particle: `connections[v][u] = get_connection(u, v)`, so the pair loop of `v` reads one row. -/
  connections : Array FloatArray

private def extractFlat (g : FGraph) : Flat := Id.run do
  let particles := g.particleIds
  let n := particles.size
  let mut radii := FloatArray.emptyWithCapacity n
  let mut priorities := FloatArray.emptyWithCapacity n
  for p in particles do
    radii := radii.push (g.arena.particleRadius p)
    priorities := priorities.push (Float.ofInt ((g.arena.particleProperties p).getD ForceOptions.PRIORITY 1))
  let mut connections : Array FloatArray := Array.mkEmpty n
  for j in [0:n] do
    let mut row := FloatArray.emptyWithCapacity n
    for i in [0:n] do
      row := row.push (if i == j then fl0p0 else Float.ofInt (g.getConnection particles[i]! particles[j]!))
    connections := connections.push row
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

/-- `isBend`. -/
private def isBend : FParticleId → Bool
  | .bend _ => true
  | _ => false

/-- Whether `AbstractForceModel.iterationDone` can move anything: some edge of the graph has labels or
bend points. Without them it leaves the arena unchanged, so the write-back and re-read of the
positions around it are skipped (they would read back the written values). -/
private def needsRefresh (g : FGraph) : Bool :=
  g.edges.any fun e =>
    !(g.arena.edgeLabels[e.idx]!).isEmpty || !(g.arena.edgeBendpoints[e.idx]!).isEmpty

/-- Result of `scanForces`: where it stopped (`n` = done) and the accumulated displacement. The scalar
fields are stored unboxed in the constructor, so a scan allocates one small object. -/
private structure ScanResult where
  stop : USize
  ax : Float
  ay : Float
  deriving Inhabited

/-- The displacement of particle `vi` caused by the particles `ui, ui + 1, …, n - 1` (the inner pair
loop of `layout`), accumulated onto `(ax, ay)` in loop order. Stops at the first particle at the same
position as `vi` (returned as `stop`, `n` when there is none) so the caller can separate the two before
continuing; `check = false` skips that test for `ui` itself (the pair the caller has just separated,
whose force is computed unconditionally like in Rust).

The loop invariants are parameters (`pxv`, `pyv`, `rv`: position and radius of `vi`; `crow`: the
connection row of `vi`; `kk = k * k` and `kk0 = k * k * ZERO_FACTOR`, the two possible values of
`repulsive`; `zero = 0.0`), so the body has no calls, literals or `Nat` arithmetic. Every float
operation is the one of `repulsive`/`attractive`/`fmax` in the same order: `fmax (length - ru - rv) 0.0`
is `d0` if `d0 > 0` and `0.0` otherwise (also for NaN), and `repulsive d k` is `k * k / d` exactly when
`d > 0`. A tail-recursive function with unboxed parameters: a `for` loop would box the accumulators in
its state tuple. The size equalities make every load unchecked (`n` is `px.usize`). -/
private partial def scanForcesU (px py radii priorities crow : FloatArray) (hy : py.size = px.size)
    (hr : radii.size = px.size) (hp : priorities.size = px.size) (hc : crow.size = px.size)
    (vi : USize) (pxv pyv rv k kk kk0 temperature zero : Float) (ui : USize) (check : Bool)
    (ax ay : Float) : ScanResult :=
  if h : ui < px.usize then
    have hx : ui.toNat < px.size := FloatArray.usize_lt_size h
    if ui == vi then
      scanForcesU px py radii priorities crow hy hr hp hc vi pxv pyv rv k kk kk0 temperature zero
        (ui + 1) true ax ay
    else
      let pxu := px.uget ui hx
      let pyu := py.uget ui (by omega)
      if check && pxu == pxv && pyu == pyv then ⟨ui, ax, ay⟩
      else
        let ddx := pxv - pxu
        let ddy := pyv - pyu
        let length := Float.sqrt (ddx * ddx + ddy * ddy)
        if length == zero then
          scanForcesU px py radii priorities crow hy hr hp hc vi pxv pyv rv k kk kk0 temperature zero
            (ui + 1) true ax ay
        else
          let d0 := length - radii.uget ui (by omega) - rv
          let d := if d0 > zero then d0 else zero
          let repulsive := if d > zero then kk / d else kk0
          let force := repulsive * priorities.uget ui (by omega)
          let connection := crow.uget ui (by omega)
          let force := if connection > zero then force - d * d / k * connection else force
          let s := force * temperature / length
          scanForcesU px py radii priorities crow hy hr hp hc vi pxv pyv rv k kk kk0 temperature zero
            (ui + 1) true (ax + ddx * s) (ay + ddy * s)
  else ⟨px.usize, ax, ay⟩

/-- `scanForcesU` with checked loads (`0.0` out of bounds, like `get!`), for arrays of different
sizes; the layout never builds those (all particle arrays have `n` entries). -/
private partial def scanForcesChecked (px py radii priorities crow : FloatArray) (n vi : USize)
    (pxv pyv rv k kk kk0 temperature zero : Float) (ui : USize) (check : Bool) (ax ay : Float) :
    ScanResult :=
  if ui >= n then ⟨n, ax, ay⟩
  else if ui == vi then
    scanForcesChecked px py radii priorities crow n vi pxv pyv rv k kk kk0 temperature zero
      (ui + 1) true ax ay
  else
    let pxu := fgetU px ui zero
    let pyu := fgetU py ui zero
    if check && pxu == pxv && pyu == pyv then ⟨ui, ax, ay⟩
    else
      let ddx := pxv - pxu
      let ddy := pyv - pyu
      let length := Float.sqrt (ddx * ddx + ddy * ddy)
      if length == zero then
        scanForcesChecked px py radii priorities crow n vi pxv pyv rv k kk kk0 temperature zero
          (ui + 1) true ax ay
      else
        let d0 := length - fgetU radii ui zero - rv
        let d := if d0 > zero then d0 else zero
        let repulsive := if d > zero then kk / d else kk0
        let force := repulsive * fgetU priorities ui zero
        let connection := fgetU crow ui zero
        let force := if connection > zero then force - d * d / k * connection else force
        let s := force * temperature / length
        scanForcesChecked px py radii priorities crow n vi pxv pyv rv k kk kk0 temperature zero
          (ui + 1) true (ax + ddx * s) (ay + ddy * s)

/-- The pair loop of `vi` from `ui` on (`scanForcesU` when all arrays have `n` entries). -/
@[inline] private def scanForces (px py radii priorities crow : FloatArray) (n vi : USize)
    (pxv pyv rv k kk kk0 temperature zero : Float) (ui : USize) (check : Bool) (ax ay : Float) :
    ScanResult :=
  if h : py.size = px.size ∧ radii.size = px.size ∧ priorities.size = px.size ∧ crow.size = px.size
      ∧ px.usize = n then
    scanForcesU px py radii priorities crow h.1 h.2.1 h.2.2.1 h.2.2.2.1 vi pxv pyv rv k kk kk0
      temperature zero ui check ax ay
  else
    scanForcesChecked px py radii priorities crow n vi pxv pyv rv k kk kk0 temperature zero ui check
      ax ay

/-- Result of `forceRows`: the displacement arrays and, if a pair at the same position interrupted
the rows, the particle `vi` whose row stopped together with its partial scan. -/
private structure RowsResult where
  dx : FloatArray
  dy : FloatArray
  /-- The interrupted row (`n` = all rows done). -/
  vi : USize
  stop : USize
  ax : Float
  ay : Float
  deriving Inhabited

/-- The rows `vi, vi + 1, …, n - 1` of the pair loop while no particle shares the position of the
row's particle: the displacement of each `vi` (accumulated from zero, the reset displacement) is
stored in `dx`/`dy`. Returns at the first row that needs a separation, which the caller handles in
the monad (bend points go through the arena) before resuming at the next row. -/
private partial def forceRows (px py radii priorities : FloatArray) (connections : Array FloatArray)
    (first : Array USize) (n : USize) (k kk kk0 temperature zero : Float) (vi : USize)
    (dx dy : FloatArray) : RowsResult :=
  if vi >= n then ⟨dx, dy, n, n, zero, zero⟩
  else
    -- the displacement belongs to the particle: a repeated entry continues the sum of its first
    -- entry (Java adds to `v.getDisplacement()`, reset after the previous iteration's update)
    let f := first[vi.toNat]?.getD vi
    let ax0 := if f == vi then zero else fgetU dx f zero
    let ay0 := if f == vi then zero else fgetU dy f zero
    let r := scanForces px py radii priorities connections[vi.toNat]! n vi (fgetU px vi zero)
      (fgetU py vi zero) (fgetU radii vi zero) k kk kk0 temperature zero 0 true ax0 ay0
    if r.stop >= n then
      forceRows px py radii priorities connections first n k kk kk0 temperature zero (vi + 1)
        (fsetU dx f r.ax) (fsetU dy f r.ay)
    else ⟨dx, dy, vi, r.stop, r.ax, r.ay⟩

/-- `FruchtermanReingoldModel::layout(graph, monitor)` (the flat-array version of elk-rs). -/
def layout (monitor : ProgressMonitor) : FM Unit := do
  let _ ← monitor.begin "Component Layout" fl1p0
  let base ← AbstractForceModel.initializeBase
  let mut st := initializeModel (← get)
  let flat := extractFlat (← get)
  let refresh := needsRefresh (← get)
  let particles := flat.particles
  let n := particles.size
  let nu := n.toUSize
  let radii := flat.radii
  let priorities := flat.priorities
  let connections := flat.connections
  let ident := ParticleIdentity.ofParticles particles
  let first := ident.first
  let repeats := ident.hasRepeats
  let (px0, py0) := readPositions (← get) particles
  let mut px := px0
  let mut py := py0
  let dispBound := base.dispBound
  let zero : Float := fl0p0
  let mut random := base.random
  let mut dx := FloatArray.mk (Array.replicate n fl0p0)
  let mut dy := FloatArray.mk (Array.replicate n fl0p0)
  while st.temperature > fl0p0 && !(← monitor.isCanceled) do
    if refresh then
      -- write positions back for the label / bend point refresh
      modify (writePositions · particles px py)
      AbstractForceModel.iterationDone
    st := { st with temperature := st.temperature - st.threshold }
    if refresh then
      -- read them again (bend points and labels may have moved)
      let (px', py') := readPositions (← get) particles
      px := px'
      py := py'
    let k := st.k
    let kk := k * k
    let kk0 := k * k * FR_ZERO_FACTOR
    let temperature := st.temperature
    -- O(n^2) force computation: `forceRows` runs the pair loops up to the next particle at the same
    -- position as the row's particle, which is separated here (monadic: bend points go through the
    -- arena) before the row continues with that pair; every row overwrites its displacement
    let mut vi : USize := 0
    while vi < nu do
      let rows := forceRows px py radii priorities connections first nu k kk kk0 temperature zero vi dx dy
      dx := rows.dx
      dy := rows.dy
      if rows.vi >= nu then
        vi := nu
      else
        let v := rows.vi.toNat
        let mut ax := rows.ax
        let mut ay := rows.ay
        let mut stopU := rows.stop
        while stopU < nu do
          let stop := stopU.toNat
          if particles[stop]! == particles[v]! then
            -- another entry of the same particle (Java `u != v` is object identity): no force
            let r := scanForces px py radii priorities connections[v]! nu rows.vi
              (px.get! v) (py.get! v) (radii.get! v) k kk kk0 temperature zero (stopU + 1) true ax ay
            ax := r.ax
            ay := r.ay
            stopU := r.stop
            continue
          if isBend particles[stop]! || isBend particles[v]! then
            -- bend points: edge aware separation through the arena (Java reads the live positions,
            -- so all of them are written back first)
            modify (writePositions · particles px py)
            random ← AbstractForceModel.avoidSamePosition random particles[stop]! particles[v]!
            let pu := (← get).arena.particlePosition particles[stop]!
            let pv := (← get).arena.particlePosition particles[v]!
            px := px.set! stop pu.x
            py := py.set! stop pu.y
            px := px.set! v pv.x
            py := py.set! v pv.y
          else
            -- Java's loop test `pu.x - pv.x == 0 && pu.y - pv.y == 0` (false for equal infinite
            -- coordinates, which the scan's `==` test stops at)
            let mut separated :=
              !(px.get! stop - px.get! v == zero && py.get! stop - py.get! v == zero)
            while !separated do
              let (nu', r1) := wiggle ⟨px.get! stop, py.get! stop⟩ random fl1p0
              let (nv, r2) := wiggle ⟨px.get! v, py.get! v⟩ r1 fl1p0
              random := r2
              px := px.set! stop nu'.x
              py := py.set! stop nu'.y
              px := px.set! v nv.x
              py := py.set! v nv.y
              if !(nu'.x - nv.x == zero && nu'.y - nv.y == zero) then separated := true
          if repeats then
            -- the other entries of a moved particle share its position
            for j in ident.others stop do
              px := px.set! j (px.get! stop)
              py := py.set! j (py.get! stop)
            for j in ident.others v do
              px := px.set! j (px.get! v)
              py := py.set! j (py.get! v)
          -- the separated pair's force is computed without a second same-position test
          let r := scanForces px py radii priorities connections[v]! nu rows.vi
            (px.get! v) (py.get! v) (radii.get! v) k kk kk0 temperature zero stopU false ax ay
          ax := r.ax
          ay := r.ay
          stopU := r.stop
        let f := (first[v]!).toNat
        dx := dx.set! f ax
        dy := dy.set! f ay
        vi := rows.vi + 1
    -- apply the displacements with bounds
    for i in [0:n] do
      let bounded := (KVector.mk (dx.get! i) (dy.get! i)).bound (-dispBound) (-dispBound) dispBound dispBound
      px := px.set! i (px.get! i + bounded.x)
      py := py.set! i (py.get! i + bounded.y)
    if repeats then
      -- Java moves a repeated particle at its first entry and resets its displacement, so its later
      -- entries add the zero vector: position `p + bound(d) + 0.0`, shared by all entries
      for grp in ident.groups do
        let f := grp[0]!
        let mut x := px.get! f
        let mut y := py.get! f
        for _ in [1:grp.size] do
          x := x + zero
          y := y + zero
        for j in grp do
          px := px.set! j x
          py := py.set! j y
  -- final write-back of the positions, displacements are reset
  modify fun g =>
    let g := writePositions g particles px py
    { g with arena := particles.foldl (fun a p => a.setParticleDisplacement p {}) g.arena }
  AbstractForceModel.storeRandom random
  monitor.done

end FruchtermanReingoldModel

end Elk.Alg.Force.Model
