import Tests.Framework
import Elk.Api
/-!
Tests of the parallel sibling layout (`Elk.Core.Parallel`, agent PAR, `docs/parallel-layout.md`).

* `parallel.ownership`: domains and the eligibility test of `computeOwnership` on an imported graph
  (closed sub-trees, a hierarchy-crossing edge, inside self loops and edges between sibling ports,
  the root-walking algorithms), `balancedCuts`.
* `parallel.merge`: `checkChunk`/`mergeChunk` renumber the sections two chunks create exactly like the
  sequential run, accept an element rebuilt with equal content and reject a write outside the chunk's
  domains.
* `parallel.differential`: random hierarchical graphs (separate children with layered, mrtree, force,
  stress, rectpacking, box, fixed, radial and nested levels, sibling port edges, root-linked radial
  children as barriers) and multi-component graphs, laid out with thread cap 1 and 4 at work threshold
  0: identical outputs, and the parallel path was taken.
* `parallel.failures`: throwing children in every position and in pairs: the parallel layout reports the
  exception of the first throwing child in sibling order, like the sequential one, and leaves the same
  arena behind (engine run caught inside `ElkM`).
-/
namespace Tests.Api.ParallelLayout

open Tests Elk Elk.Graph Elk.Api Elk.Json Elk.Core.Parallel

/-- Lays `json` out with the thread cap `threads` and the work threshold `minW` (both restored). -/
private def layoutWith (threads minW : Nat) (json : String) : IO (Except String String) := do
  let previous ← minWorkRef.get
  minWorkRef.set minW
  try withThreads threads (layoutJson json "" (sortKeys := true)) finally minWorkRef.set previous

/-- Imports `json` like `Elk.Api.layoutValue` (algorithms resolved by a dry engine run would also
work; the resolver alone is enough here). -/
private def importJson (json : String) : IO (NodeId × ElkGraph) := do
  let .ok v := Elk.Json.parse json | throw (IO.userError "not JSON")
  ensureInitialized
  let defaults ← match ← GlobalOptions.parse "{}" with
    | .ok g => pure g
    | .error e => throw (IO.userError e)
  let ((root, _), g) ← (ImportM.run (JsonImporter.transform v) { defaults := some defaults }).run {}
  -- resolve the algorithms (the engine's first step), so that `RESOLVED_ALGORITHM` is set
  let ((), g) ← (do
      let resolver ← Elk.Core.Data.LayoutAlgorithmResolver.new
      Elk.Core.Util.ElkUtil.applyVisitors root #[resolver.toVisitor] : ElkM Unit).run g
  return (root, g)

private def nodeByIdentifier (g : ElkGraph) (id : String) : NodeId :=
  ⟨(g.nodes.findIdx? (·.identifier == some id)).getD 0⟩

private def edgeByIdentifier (g : ElkGraph) (id : String) : EdgeId :=
  ⟨(g.edges.findIdx? (·.identifier == some id)).getD 0⟩

/-- `a` (edges inside and an edge from an inner node to its own port, but entered by `ec`), `b` (closed,
an inside self loop contained in the root), `c` (open: an edge from inside `c` to inside `a`), `d` (radial with
an edge from a child to `d` itself: root-linked, not eligible), `e` (radial without one: eligible),
edges between the ports of `a` and `b` at the root. -/
private def ownershipGraph : String := "{\"id\":\"root\",\"children\":[
  {\"id\":\"a\",\"ports\":[{\"id\":\"ap\"}],\"children\":[{\"id\":\"a1\",\"width\":10,\"height\":10},{\"id\":\"a2\",\"width\":10,\"height\":10}],
   \"edges\":[{\"id\":\"ea\",\"sources\":[\"a1\"],\"targets\":[\"a2\"]},{\"id\":\"eap\",\"sources\":[\"a2\"],\"targets\":[\"ap\"]}]},
  {\"id\":\"b\",\"ports\":[{\"id\":\"bp\"}],\"children\":[{\"id\":\"b1\",\"width\":10,\"height\":10}]},
  {\"id\":\"c\",\"children\":[{\"id\":\"c1\",\"width\":10,\"height\":10}],
   \"edges\":[{\"id\":\"ec\",\"sources\":[\"c1\"],\"targets\":[\"a1\"]}]},
  {\"id\":\"d\",\"layoutOptions\":{\"elk.algorithm\":\"radial\"},\"children\":[{\"id\":\"d1\",\"width\":10,\"height\":10},{\"id\":\"d2\",\"width\":10,\"height\":10}],
   \"edges\":[{\"id\":\"ed\",\"sources\":[\"d1\"],\"targets\":[\"d2\"]},{\"id\":\"edr\",\"sources\":[\"d2\"],\"targets\":[\"d\"]}]},
  {\"id\":\"e\",\"layoutOptions\":{\"elk.algorithm\":\"radial\"},\"children\":[{\"id\":\"e1\",\"width\":10,\"height\":10},{\"id\":\"e2\",\"width\":10,\"height\":10}],
   \"edges\":[{\"id\":\"ee\",\"sources\":[\"e1\"],\"targets\":[\"e2\"]}]}],
 \"edges\":[{\"id\":\"eab\",\"sources\":[\"ap\"],\"targets\":[\"bp\"]},{\"id\":\"ebb\",\"sources\":[\"b\"],\"targets\":[\"b\"]}]}"

def ownership : Suite := suite "parallel.ownership" do
  let (root, g) ← importJson ownershipGraph
  let units := (g.node root).children
  let own := computeOwnership g units
  checkEq "units" units.size 5
  -- `ec` (declared in `c`, contained in the root after the import's containment update) enters `a`
  -- from outside: both `a` and `c` are open
  checkEq "closed" (toString own.closed.toList) (toString [false, true, false, false, true])
  let ownerOfNode (id : String) := own.nodes[(nodeByIdentifier g id).idx]!
  let ownerOfEdge (id : String) := own.edges[(edgeByIdentifier g id).idx]!
  checkEq "node a1" (ownerOfNode "a1") 1
  checkEq "node b" (ownerOfNode "b") 2
  checkEq "root" (ownerOfNode "root") 0
  checkEq "edge inside a" (ownerOfEdge "ea") 1
  checkEq "edge to own port" (ownerOfEdge "eap") 1
  checkEq "inside self loop of b (contained in root)" (ownerOfEdge "ebb") 2
  checkEq "edge between sibling ports" (ownerOfEdge "eab") 0
  checkEq "hierarchy-crossing edge" (ownerOfEdge "ec") 0
  checkEq "cuts 2" (toString (balancedCuts #[10, 10, 10, 10] 2).toList) "[0, 2]"
  checkEq "cuts heavy head" (toString (balancedCuts #[100, 1, 1, 1] 3).toList) "[0, 1, 2]"
  checkEq "cuts heavy tail" (toString (balancedCuts #[1, 1, 1, 100] 2).toList) "[0, 3]"
  checkEq "cuts more parts than units" (toString (balancedCuts #[5, 5] 4).toList) "[0, 1]"
  checkEq "cuts one part" (toString (balancedCuts #[5, 5, 5] 1).toList) "[0]"

/-- Two units `x`, `y` (one edge each, no sections) under the root. -/
private def mergeGraph : String := "{\"id\":\"root\",\"children\":[
  {\"id\":\"x\",\"children\":[{\"id\":\"x1\"},{\"id\":\"x2\"}],\"edges\":[{\"id\":\"ex\",\"sources\":[\"x1\"],\"targets\":[\"x2\"]}]},
  {\"id\":\"y\",\"children\":[{\"id\":\"y1\"},{\"id\":\"y2\"}],\"edges\":[{\"id\":\"ey\",\"sources\":[\"y1\"],\"targets\":[\"y2\"]}]}]}"

def merge : Suite := suite "parallel.merge" do
  let (root, orig) ← importJson mergeGraph
  let units := (orig.node root).children
  let own := computeOwnership orig units
  let ex := edgeByIdentifier orig "ex"
  let ey := edgeByIdentifier orig "ey"
  -- chunk 0 lays out `x` (one new section, a moved node), chunk 1 `y` (one new section)
  let (r0, _) := ElkGraphUtil.firstEdgeSection (orig.modifyNode (nodeByIdentifier orig "x1") fun n => { n with x := 5 }) ex true true
  let (r1, _) := ElkGraphUtil.firstEdgeSection orig ey true true
  -- the sequential run
  let (s1, _) := ElkGraphUtil.firstEdgeSection (orig.modifyNode (nodeByIdentifier orig "x1") fun n => { n with x := 5 }) ex true true
  let (seq, _) := ElkGraphUtil.firstEdgeSection s1 ey true true
  check "chunk 0 stays in its domain" (checkChunk orig r0 own (· == 0))
  match mergeChunk orig r1 r0 own (· == 1) with
  | none => check "merge" false
  | some (m, r) =>
    check "created section moved by one" (!r.isId && r.off.sections == 1)
    checkEq "sections" m.sections.size seq.sections.size
    checkEq "ey sections" (toString ((m.edge ey).sections.map (·.idx)).toList) (toString ((seq.edge ey).sections.map (·.idx)).toList)
    checkEq "section parent" (toString ((m.sections[1]!).parent.map (·.idx))) (toString ((seq.sections[1]!).parent.map (·.idx)))
    checkEq "x1 moved" (m.node (nodeByIdentifier orig "x1")).x 5.0
  -- an element rebuilt with equal content is unchanged; a write outside the domains is rejected
  let rebuilt := r1.modifyNode root fun n => { n with x := n.x }
  check "equal rebuild accepted" (checkChunk orig rebuilt own (· == 1))
  let foreign := r1.modifyNode root fun n => { n with x := n.x + 1 }
  check "write to the parent rejected" (!checkChunk orig foreign own (· == 1))
  check "write to the parent rejected (merge)" (mergeChunk orig foreign r0 own (· == 1)).isNone
  let other := r1.modifyNode (nodeByIdentifier orig "x2") fun n => { n with y := 7 }
  check "write to a sibling's domain rejected" (mergeChunk orig other r0 own (· == 1)).isNone

/-! ## Random graphs -/

private def nextR (s : UInt64) : UInt64 := s * 6364136223846793005 + 1442695040888963407
private def pick (s : UInt64) (n : Nat) : Nat := ((s >>> 33).toNat) % (max n 1)

private def algorithms : Array String :=
  #["layered", "layered", "mrtree", "force", "stress", "rectpacking", "box", "fixed", "radial"]

/-- A compound node `id` laid out with `alg`: `m` leaves, tree edges (radial/mrtree need trees), a port
with an edge from a leaf for layered (and sometimes force), optionally a nested compound. -/
private partial def compound (s : UInt64) (id : String) (depth : Nat) : UInt64 × String × Array String := Id.run do
  let mut s := nextR s
  let alg := algorithms[pick s algorithms.size]!
  s := nextR s
  let m := 2 + pick s 5
  let mut children : Array String := #[]
  let mut edges : Array String := #[]
  let mut ports : Array String := #[]
  for i in [0:m] do
    s := nextR s
    let w := 10 + pick s 30
    s := nextR s
    let h := 10 + pick s 20
    children := children.push s!"\{\"id\":\"{id}_n{i}\",\"width\":{w},\"height\":{h}}"
    if i > 0 then
      s := nextR s
      let p := pick s i
      edges := edges.push s!"\{\"id\":\"{id}_e{i}\",\"sources\":[\"{id}_n{p}\"],\"targets\":[\"{id}_n{i}\"]}"
  s := nextR s
  -- (radial follows an edge to the compound's own port out of the compound and may then recurse
  -- forever, in the sequential run as well; `parallel.ownership` covers that barrier)
  let rootLink := alg == "layered" || (alg == "force" && pick s 3 == 0)
  if rootLink then
    ports := ports.push s!"\{\"id\":\"{id}_p\",\"width\":5,\"height\":5}"
    edges := edges.push s!"\{\"id\":\"{id}_ep\",\"sources\":[\"{id}_n{m - 1}\"],\"targets\":[\"{id}_p\"]}"
  s := nextR s
  if depth == 0 && alg != "radial" && alg != "mrtree" && pick s 2 == 0 then
    let (s', inner, _) := compound s s!"{id}_c" (depth + 1)
    s := s'
    children := children.push inner
  let portsJson := if ports.isEmpty then "" else s!",\"ports\":[{",".intercalate ports.toList}]"
  let node := s!"\{\"id\":\"{id}\",\"layoutOptions\":\{\"elk.algorithm\":\"{alg}\"}{portsJson},\"children\":[{",".intercalate children.toList}],\"edges\":[{",".intercalate edges.toList}]}"
  return (s, node, ports)

/-- A root with 2-5 compound children, a few leaves, edges between them and between ports. -/
private def randomHierarchy (seed : Nat) : String := Id.run do
  let mut s := nextR (UInt64.ofNat (seed * 7919 + 13))
  let k := 2 + pick s 4
  let mut children : Array String := #[]
  let mut ports : Array String := #[]
  let mut ids : Array String := #[]
  for i in [0:k] do
    let (s', node, ps) := compound s s!"c{i}" 0
    s := s'
    children := children.push node
    ports := ports ++ ps
    ids := ids.push s!"c{i}"
  children := children.push "{\"id\":\"leaf\",\"width\":20,\"height\":20}"
  ids := ids.push "leaf"
  let mut edges : Array String := #[]
  for i in [0:k] do
    s := nextR s
    edges := edges.push s!"\{\"id\":\"r{i}\",\"sources\":[\"{ids[i]!}\"],\"targets\":[\"{ids[pick s ids.size]!}\"]}"
  for i in [1:ports.size] do
    edges := edges.push s!"\{\"id\":\"rp{i}\",\"sources\":[\"{ports[i - 1]!}\"],\"targets\":[\"{ports[i]!}\"]}"
  return s!"\{\"id\":\"root\",\"layoutOptions\":\{\"elk.algorithm\":\"layered\"},\"children\":[{",".intercalate children.toList}],\"edges\":[{",".intercalate edges.toList}]}"

/-- A flat layered graph with `k` components (chains). -/
private def multiComponent (k : Nat) : String := Id.run do
  let mut children : Array String := #[]
  let mut edges : Array String := #[]
  for c in [0:k] do
    for i in [0:4] do
      children := children.push s!"\{\"id\":\"k{c}_{i}\",\"width\":20,\"height\":20}"
      if i > 0 then edges := edges.push s!"\{\"id\":\"ke{c}_{i}\",\"sources\":[\"k{c}_{i - 1}\"],\"targets\":[\"k{c}_{i}\"]}"
  return s!"\{\"id\":\"root\",\"children\":[{",".intercalate children.toList}],\"edges\":[{",".intercalate edges.toList}]}"

private def showResult : Except String String → String
  | .ok s => s
  | .error e => s!"error: {e}"

def differential : Suite := suite "parallel.differential" do
  let before ← stats
  let mut same := 0
  for seed in [1:61] do
    let json := randomHierarchy seed
    let sq ← layoutWith 1 0 json
    let par ← layoutWith 4 0 json
    if showResult sq == showResult par then same := same + 1
    else report s!"seed {seed}" false s!"{(showResult sq).take 200} vs {(showResult par).take 200}"
  checkEq "random hierarchies identical" same 60
  for k in [1, 2, 7, 30] do
    let json := multiComponent k
    checkEq s!"{k} components" (showResult (← layoutWith 4 0 json)) (showResult (← layoutWith 1 0 json))
  let after ← stats
  let tm ← taskManagerAvailable
  -- the parallel path ran (when the test runner has a task manager, which `lake test` has)
  check "parallel segments" (!tm || after.parallelSegments > before.parallelSegments)
  check "no fallbacks" (after.fallbacks == before.fallbacks)

/-- A layered child whose layer constraints throw (Java's `UnsupportedConfigurationException` naming
the child's node), or a normal one. -/
private def child (i : Nat) (throws : Bool) : String :=
  if throws then
    s!"\{\"id\":\"c{i}\",\"children\":[\{\"id\":\"c{i}a\",\"width\":10,\"height\":10,\"layoutOptions\":\{\"elk.layered.layering.layerConstraint\":\"FIRST_SEPARATE\"}},\{\"id\":\"c{i}b\",\"width\":10,\"height\":10,\"layoutOptions\":\{\"elk.layered.layering.layerConstraint\":\"FIRST_SEPARATE\"}}],\"edges\":[\{\"id\":\"c{i}e\",\"sources\":[\"c{i}b\"],\"targets\":[\"c{i}a\"]}]}"
  else
    s!"\{\"id\":\"c{i}\",\"children\":[\{\"id\":\"c{i}a\",\"width\":10,\"height\":10},\{\"id\":\"c{i}b\",\"width\":10,\"height\":10},\{\"id\":\"c{i}c\",\"width\":10,\"height\":10}],\"edges\":[\{\"id\":\"c{i}e\",\"sources\":[\"c{i}a\"],\"targets\":[\"c{i}b\"]},\{\"id\":\"c{i}f\",\"sources\":[\"c{i}b\"],\"targets\":[\"c{i}c\"]}]}"

private def failingGraph (n : Nat) (throwing : List Nat) : String :=
  let cs := (List.range n).map fun i => child i (throwing.contains i)
  s!"\{\"id\":\"root\",\"children\":[{",".intercalate cs}]}"

/-- The arena state an engine run leaves behind when it throws: the error and every node's geometry,
every edge's sections (start, end, bend points), as text. -/
private def engineState (threads minW : Nat) (json : String) : IO String := do
  let (root, g) ← importJson json
  let previous ← minWorkRef.get
  minWorkRef.set minW
  let (err, g) ← (try withThreads threads (((do
        try
          Elk.Core.RecursiveGraphLayoutEngine.layout root Elk.Core.Util.ProgressMonitor.null
          pure "no error"
        catch e => pure (toString e)) : ElkM String).run g)
    finally minWorkRef.set previous)
  let nodes := g.nodes.map fun n => s!"{n.identifier}:{n.x},{n.y},{n.width},{n.height}"
  let edges := g.edges.map fun e => s!"{e.identifier}:{(e.sections.map fun sid =>
    let sec := g.edgeSection sid
    s!"{sec.startX},{sec.startY},{sec.endX},{sec.endY},{sec.bendPoints.size}").toList}"
  return s!"{err}\n{nodes.toList}\n{edges.toList}\n{g.sections.size}"

def failures : Suite := suite "parallel.failures" do
  let n := 6
  let before ← stats
  let mut patterns : Array (List Nat) := #[]
  for i in [0:n] do patterns := patterns.push [i]
  for i in [0:n] do
    for j in [i + 1:n] do patterns := patterns.push [i, j]
  patterns := patterns.push (List.range n)
  for p in patterns do
    let json := failingGraph n p
    let sq ← layoutWith 1 0 json
    let par ← layoutWith 4 0 json
    let first := p.head!
    checkEq s!"throwing {p}" (showResult par) (showResult sq)
    check s!"throwing {p}: first in order" (((showResult sq).splitOn s!"'root.c{first}.c{first}a'").length == 2)
    -- the arena left behind by the exception is the sequential one (earlier siblings laid out, the
    -- throwing one as far as it got, later ones untouched)
    checkEq s!"throwing {p}: arena" (← engineState 4 0 json) (← engineState 1 0 json)
  let after ← stats
  let tm ← taskManagerAvailable
  check "failures went through the parallel path" (!tm || after.failures > before.failures)

def suites : Array Suite := #[ownership, merge, differential, failures]

end Tests.Api.ParallelLayout
