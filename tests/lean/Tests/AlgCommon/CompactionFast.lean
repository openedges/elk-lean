import Tests.Framework
import Elk.Alg.Common.Compaction
/-! Differential tests of the compaction fast paths (round 13, CMP) against the kept reference
implementations:

* `core.util.sort.stableSortTR`: the tail-recursive `stableSort` against the former `while`
  formulation `stableSortReference`, for consistent and for inconsistent (pair-hash) comparators
  (same comparison sequence ⇒ same permutation);
* `alg.common.compaction.scanlineFast`: `ScanlineConstraintCalculator.sweep` (precomputed keys,
  pure handler kernel) against `sweepReference` on random hitbox sets (duplicate y values,
  zero-height and zero-width boxes, NaN coordinates, groups);
* `alg.common.compaction.longestPathFast`: `LongestPathCompaction.compact` (pure) against
  `compactReference`, with lock functions reading the graph, `flags` locks, closure and
  `individualMin` spacings handlers, and the `flags`/`individualMin` forms against equivalent closures;
* `alg.common.compaction.cgraphFast`: `CGraph.calculateGroupOffsets` and
  `calculateConstraintsForCGroups` against their `…Reference`, including empty groups, nodes in
  several groups, out-of-range ids and self constraints.

Every comparison is on the full element state (floats by bit pattern) and on the exception text. -/
namespace Tests.AlgCommon.CompactionFast

open Tests Elk.Core.Util Elk.Core.Math Elk.Core.Options Elk.Alg.Common.Compaction.OneD

/-- splitmix64 step: returns the next state and a pseudo-random value. -/
def next (s : UInt64) : UInt64 × UInt64 :=
  let s := s + 0x9E3779B97F4A7C15
  let z := (s ^^^ (s >>> 30)) * 0xBF58476D1CE4E5B9
  let z := (z ^^^ (z >>> 27)) * 0x94D049BB133111EB
  (s, z ^^^ (z >>> 31))

/-- A pseudo-random number below `n` (`n > 0`). -/
def below (s : UInt64) (n : Nat) : UInt64 × Nat :=
  let (s, z) := next s
  (s, (z % n.toUInt64).toNat)

/-- A coordinate from a small set (many ties), occasionally NaN. -/
def coord (s : UInt64) (nan : Bool) : UInt64 × Float :=
  let (s, k) := below s 40
  if nan && k == 39 then (s, 0.0 / 0.0) else (s, (k.toFloat - 10.0) * 2.5)

/-- An extent from a small set including zero. -/
def extent (s : UInt64) : UInt64 × Float :=
  let (s, k) := below s 8
  (s, if k < 2 then 0.0 else k.toFloat * 3.0)

/-- A random graph of `n` nodes; nodes are put into random groups (`groups` of them, some nodes
stay without group). -/
def randomGraph (seed : UInt64) (n groups : Nat) (nan : Bool) : CGraph := Id.run do
  let mut s := seed
  let mut g := CGraph.allDirections
  for _ in [0:n] do
    let (s1, x) := coord s nan
    let (s2, y) := coord s1 nan
    let (s3, w) := extent s2
    let (s4, h) := extent s3
    s := s4
    g := (CNode.create g (ElkRectangle.ofValues x y w h)).1
  let mut members : Array (Array CNodeId) := Array.replicate groups #[]
  for i in [0:n] do
    let (s1, k) := below s (groups + 1)
    s := s1
    if k < groups then members := members.modify k (·.push ⟨i⟩)
  for ms in members do
    match CGroup.create g ms with
    | .ok (g', _) => g := g'
    | .error _ => pure ()
  return g

/-- Bit pattern of a float (NaN payloads compared exactly). -/
def fb (x : Float) : UInt64 := x.toBits

def rectKey (r : ElkRectangle) : List UInt64 := [fb r.x, fb r.y, fb r.width, fb r.height]

/-- The full state of a node. -/
def nodeKey (c : CNode) : String :=
  s!"{c.id}|{c.cGroup.map (·.idx)}|{rectKey c.hitbox}|{c.hitboxPreCompaction.map rectKey}|{fb c.cGroupOffset.x},{fb c.cGroupOffset.y}|{c.constraints.map (·.idx)}|{fb c.startPos}"

/-- The full state of a group. -/
def groupKey (c : CGroup) : String :=
  s!"{c.id}|{c.master.map (·.idx)}|{c.cNodes.map (·.idx)}|{fb c.startPos}|{c.incomingConstraints.map (·.idx)}|{c.outDegree}|{c.outDegreeReal}|{c.reference.map (·.idx)}|{fb c.delta}|{fb c.deltaNormalized}"

/-- The full state of a graph. -/
def graphKey (g : CGraph) : String :=
  String.intercalate ";" (g.cNodes.toList.map nodeKey) ++ "#" ++ String.intercalate ";" (g.cGroups.toList.map groupKey)

/-- Runs a strategy on a state and renders the outcome (graph state or exception text). -/
def outcome (act : CompactM Unit) (st : CompactorState) : IO String := do
  try
    let (_, st) ← act.run st
    return graphKey st.cGraph
  catch e => return s!"error: {e}"

/-- A comparator that ignores its arguments' order consistency: a hash of the pair. -/
def hashCmp (seed : UInt64) (a b : Nat) : Ordering :=
  let (_, z) := next (seed ^^^ (a.toUInt64 * (1000003 : UInt64)) ^^^ (b.toUInt64 <<< (20 : UInt64)))
  match z % 3 with
  | 0 => .lt
  | 1 => .eq
  | _ => .gt

def stableSortTR : Suite := suite "core.util.sort.stableSortTR" do
  let mut s : UInt64 := 7
  let mut same := 0
  let mut total := 0
  for size in [0, 1, 2, 3, 15, 16, 17, 31, 32, 33, 47, 64, 100, 257, 1000] do
    for round in [0:6] do
      let mut xs : Array Nat := #[]
      for _ in [0:size] do
        let (s1, k) := below s (if round % 2 == 0 then 10 else 1000)
        s := s1
        xs := xs.push k
      -- consistent comparator on keys (the index is carried to see the permutation)
      let keyed := (Array.range xs.size).map fun i => (xs[i]!, i)
      let a := stableSort keyed fun p q => compare p.1 q.1
      let b := stableSortReference keyed fun p q => compare p.1 q.1
      total := total + 1
      if a == b then same := same + 1
      -- inconsistent comparator
      let seed := s
      let a := stableSort xs (hashCmp seed)
      let b := stableSortReference xs (hashCmp seed)
      total := total + 1
      if a == b then same := same + 1
  checkEq "stableSort = stableSortReference" same total

/-- The nodes in a pseudo-random order with a repeated id dropped (sweeps take arbitrary lists). -/
def sweepNodes (g : CGraph) (seed : UInt64) : Array CNodeId :=
  if seed % 3 == 0 then g.cNodeIds
  else
    let ids := g.cNodeIds
    stableSort ids fun a b => hashCmp seed a.idx b.idx

def scanlineFast : Suite := suite "alg.common.compaction.scanlineFast" do
  let mut same := 0
  let mut total := 0
  let mut errors := 0
  for seed in [1:301] do
    let n := seed % 23 + 1
    let g := randomGraph (seed.toUInt64 * 7919) n (seed % 5 + 1) (seed % 7 == 0)
    let nodes := sweepNodes g seed.toUInt64
    let st : CompactorState := { cGraph := g }
    let a ← outcome (ScanlineConstraintCalculator.sweep nodes) st
    let b ← outcome (ScanlineConstraintCalculator.sweepReference nodes) st
    if a.startsWith "error" then errors := errors + 1
    total := total + 1
    if a == b then same := same + 1 else IO.println s!"scanline mismatch seed {seed}"
    -- the whole constraint calculation (predefined constraints, group degrees)
    let c := (OneDimensionalCompactor.new g).setConstraintAlgorithm ScanlineConstraintCalculator
    let ref := c.setConstraintAlgorithm ⟨ScanlineConstraintCalculator.sweepReference =<< CompactM.cNodeIds⟩
    for dir in #[Direction.left, .right, .up, .down] do
      let ra ← (try return graphKey (← c.changeDirection dir).cGraph catch e => return s!"error: {e}")
      let rb ← (try return graphKey (← ref.changeDirection dir).cGraph catch e => return s!"error: {e}")
      total := total + 1
      if ra == rb then same := same + 1 else IO.println s!"scanline compactor mismatch seed {seed} {dir}"
  checkEq "sweep = sweepReference" same total
  report "scanline sweeps mostly succeed" (errors * 4 <= 300) s!"{errors} errors"

/-- A lock function that reads the graph (group degree, node position) and the direction. -/
def readingLock (seed : Nat) : LockFunction := .fn fun g n dir =>
  let c := g.cNode n
  let byGroup := match c.cGroup with
    | some gr => (g.cGroup gr).outDegreeReal % 2 == 0
    | none => false
  match seed % 4 with
  | 0 => byGroup
  | 1 => (n.idx + seed) % 3 == 0
  | 2 => c.hitbox.x > 0.0 && dir == .left
  | _ => byGroup || c.startPos > 5.0

/-- A spacing handler depending on the node ids. -/
def idSpacing : SpacingsHandler :=
  .mk (fun _ a b => (a.idx % 3).toFloat + (b.idx % 2).toFloat * 0.5) (fun _ a b => ((a.idx + b.idx) % 4).toFloat)

/-- Individual node spacings (some nodes beyond the table: default) for an `individualMin` handler. -/
def individualSpacings (seed n : Nat) : FloatArray × Float :=
  let sp := (Array.range (n * 2 / 3)).foldl (fun acc i => acc.push (((i * 7 + seed) % 5).toFloat * 1.5)) FloatArray.empty
  (sp, ((seed % 3).toFloat + 0.25))

/-- The closures equivalent to `SpacingsHandler.individualMin sp d`. -/
def individualClosures (sp : FloatArray) (d : Float) : SpacingsHandler :=
  let f : CNodeId → Float := fun c => if h : c.idx < sp.size then sp[c.idx] else d
  .mk (fun _ a b => fmin (f a) (f b)) (fun _ a b => fmin (f a) (f b))

/-- Random per-node lock flags (shorter than the node list: the rest is unlocked). -/
def randomFlags (seed n : Nat) : Array Bool :=
  (Array.range (n * 3 / 4)).map fun i => (i * 5 + seed) % 3 == 0

def longestPathFast : Suite := suite "alg.common.compaction.longestPathFast" do
  let mut same := 0
  let mut total := 0
  let mut moved := 0
  for seed in [1:301] do
    let n := seed % 19 + 1
    let g := randomGraph (seed.toUInt64 * 104729) n (seed % 4 + 1) (seed % 11 == 0)
    for dir in #[Direction.left, .right, .up, .down] do
      -- constraints from the (reference) quadratic calculation in this direction
      let c := ((OneDimensionalCompactor.new g).setConstraintAlgorithm QuadraticConstraintCalculation).setSpacingsHandler
        (if seed % 2 == 0 then idSpacing else SpacingsHandler.default)
      let c ← (try c.changeDirection dir catch _ => pure c)
      let (isp, idflt) := individualSpacings seed n
      let flags := randomFlags seed n
      for lockKind in [0:5] do
        let lockFun : Option LockFunction := match lockKind with
          | 0 => none
          | 3 => some (.flags flags)
          | 4 => some (.fn fun _ m _ => flags[m.idx]?.getD false)
          | _ => some (readingLock (seed + lockKind))
        for spKind in [0:3] do
          let sh := match spKind with
            | 0 => c.spacingsHandler
            | 1 => SpacingsHandler.individualMin isp idflt
            | _ => individualClosures isp idflt
          let st : CompactorState := { c.toCompactorState with lockFun, spacingsHandler := sh }
          -- start positions as `compact` sets them
          let a ← outcome LongestPathCompaction.compact st
          let b ← outcome LongestPathCompaction.compactReference st
          if a != graphKey st.cGraph then moved := moved + 1
          total := total + 1
          if a == b then same := same + 1 else IO.println s!"longest path mismatch seed {seed} {dir} {lockKind} {spKind}"
          -- the `flags`/`individualMin` forms against the equivalent closures (both on the fast path)
          if lockKind == 3 || spKind == 1 then
            let lockFun' : Option LockFunction :=
              if lockKind == 3 then some (.fn fun _ m _ => flags[m.idx]?.getD false) else lockFun
            let sh' := if spKind == 1 then individualClosures isp idflt else sh
            let b' ← outcome LongestPathCompaction.compact { st with lockFun := lockFun', spacingsHandler := sh' }
            total := total + 1
            if a == b' then same := same + 1 else IO.println s!"longest path form mismatch seed {seed} {dir} {lockKind} {spKind}"
  checkEq "compact = compactReference" same total
  report "longest path changes the graph" (moved * 2 >= total) s!"{moved}/{total}"

/-- A graph whose groups list nodes arbitrarily (duplicates, nodes of several groups, out-of-range
ids, empty groups). -/
def messyGroups (seed : UInt64) (n : Nat) : CGraph := Id.run do
  let mut g := randomGraph seed n 0 (seed % 3 == 0)
  let mut s := seed
  let (s1, groups) := below s 5
  s := s1
  for _ in [0:groups] do
    let (s2, size) := below s 5
    s := s2
    let mut ms : Array CNodeId := #[]
    for _ in [0:size] do
      let (s3, k) := below s (n + 2)
      s := s3
      ms := ms.push ⟨k⟩
    g := { g with cGroups := g.cGroups.push { cNodes := ms, reference := if size % 2 == 0 then some ⟨0⟩ else none } }
  return g

def cgraphFast : Suite := suite "alg.common.compaction.cgraphFast" do
  let mut same := 0
  let mut total := 0
  for seed in [1:401] do
    let n := seed % 17 + 1
    let g := if seed % 2 == 0 then randomGraph (seed.toUInt64 * 31337) n (seed % 4 + 1) (seed % 5 == 0)
      else messyGroups (seed.toUInt64 * 31337) n
    let a := graphKey g.calculateGroupOffsets
    let b := graphKey g.calculateGroupOffsetsReference
    total := total + 1
    if a == b then same := same + 1 else IO.println s!"calculateGroupOffsets mismatch seed {seed}"
    -- group degrees from random constraints (including out-of-range targets and self loops)
    let mut gc := g
    let mut s := seed.toUInt64 * 911
    for i in [0:gc.cNodes.size] do
      let (s1, k) := below s 4
      s := s1
      let mut cs : Array CNodeId := #[]
      for _ in [0:k] do
        let (s2, t) := below s (gc.cNodes.size + 1)
        s := s2
        cs := cs.push ⟨t⟩
      gc := gc.modifyCNode ⟨i⟩ fun c => { c with constraints := cs }
    let a := graphKey gc.calculateConstraintsForCGroups
    let b := graphKey gc.calculateConstraintsForCGroupsReference
    total := total + 1
    if a == b then same := same + 1 else IO.println s!"calculateConstraintsForCGroups mismatch seed {seed}"
  checkEq "CGraph fast paths = references" same total

def suites : Array Tests.Suite := #[stableSortTR, scanlineFast, longestPathFast, cgraphFast]

end Tests.AlgCommon.CompactionFast
