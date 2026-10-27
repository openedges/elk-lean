import Tests.Framework
import Elk.Alg.Common.NetworkSimplex
/-! Tests of `org.eclipse.elk.alg.common` (NetworkSimplex). Owned by the NetworkSimplex porting task.

Ports of the elk-rs tests:

* `n_edge.rs`: `graph_and_edges_release_nodes_and_origins`;
* `network_simplex.rs` (inline): `indexed_fractional_cuts_match_reference_bits_at_every_pivot`,
  `integral_pivot_cuts_equal_full_leaf_elimination`, `incomplete_postorder_keeps_full_cut_computation`,
  `fractional_or_large_weights_keep_original_cut_arithmetic`,
  `subtree_compaction_preserves_survivor_and_reattachment_order`;
* `tests/all/network_simplex_test.rs`: `network_simplex_deltas`.

Plus a few Lean-only checks of the graph API (`makeConnected`, `isAcyclic`, builder errors). -/
namespace Tests.AlgCommon.NetworkSimplex

open Tests Elk.Core.Util Elk.Alg.Common.NetworkSimplex

/-- Graph type used by the tests (no origin payload). -/
private abbrev G := NGraph Unit

/-- Creates `n` plain nodes (`NNode.of().create(graph)`). -/
private def addNodes (g : G) (n : Nat) : G := Id.run do
  let mut g := g
  for _ in [0:n] do
    g := ((NNode.of : NNodeBuilder Unit).create g).1
  return g

/-- Creates the edge `b` (throws on invalid builders). -/
private def addEdge (g : G) (b : NEdgeBuilder Unit) : IO G := do
  return (← b.create g).1

/-- Graph with `n` nodes and the given `(source, target)` edges built with `mk`. -/
private def mkGraph (n : Nat) (edges : Array (Nat × Nat)) (mk : NEdgeBuilder Unit → NEdgeBuilder Unit) : IO G := do
  let mut g := addNodes {} n
  for (s, t) in edges do
    g ← addEdge g (mk (NEdge.of |>.source ⟨s⟩ |>.target ⟨t⟩))
  return g

/-- Runs a network simplex action on a fresh instance for `g`. -/
private def runOn {α : Type} (g : G) (x : NetworkSimplexM Unit α) : IO (α × NetworkSimplex Unit) :=
  x.run (NetworkSimplex.forGraph g)

/-- Rust test helper `dag(count, seed, fraction)`: node 0 is connected to all
other nodes, the remaining forward edges are drawn by an LCG. -/
private def dag (count : Nat) (seed0 : UInt64) (fraction : Float) : IO G := do
  let mut g := addNodes {} count
  let mut seed := seed0
  for source in [0:count] do
    for target in [source + 1:count] do
      seed := seed * 6364136223846793005 + 1
      if source == 0 || seed >>> 60 < 2 then
        g ← addEdge g (NEdge.of
          |>.source ⟨source⟩ |>.target ⟨target⟩
          |>.delta (1 + (((seed >>> 32) % 5).toNat : Int))
          |>.weight (1.0 + (seed % 17).toFloat + fraction))
  return g

-- ============================================================================
-- n_edge.rs
-- ============================================================================

/-- `graph_and_edges_release_nodes_and_origins`: `NEdge::reverse` swaps the end
points. The memory-release assertions (dropped `Arc`s/`Weak` upgrades) do not
apply to the arena representation, which has no reference cycles. -/
def graphAndEdgesReleaseNodesAndOrigins : Suite :=
  suite "alg.common.networksimplex.NEdge.graph_and_edges_release_nodes_and_origins" do
    let g : NGraph Nat := {}
    let (g, source) := (NNode.of |>.origin 42).create g
    let (g, target) := (NNode.of : NNodeBuilder Nat).create g
    let (g, edge) ← (NEdge.of |>.source source |>.target target).create g
    let g := NEdge.reverse g edge
    checkEq "source is old target" (g.edge edge).source target
    checkEq "target is old source" (g.edge edge).target source
    check "old source: incoming only" ((g.node source).incomingEdges == #[edge] && (g.node source).outgoingEdges.isEmpty)
    check "old target: outgoing only" ((g.node target).outgoingEdges == #[edge] && (g.node target).incomingEdges.isEmpty)
    checkEq "origin kept" ((g.node source).origin.getD 0) 42

-- ============================================================================
-- network_simplex.rs (inline tests)
-- ============================================================================

/-- `indexed_fractional_cuts_match_reference_bits_at_every_pivot`: with fractional
weights the indexed leaf elimination (`cutvalues`) reproduces the object-based
reference (`cutvaluesReference`) bit for bit at every pivot. -/
def indexedFractionalCuts : Suite :=
  suite "alg.common.networksimplex.NetworkSimplex.indexed_fractional_cuts_match_reference_bits_at_every_pivot" do
    let mut pivots := 0
    let mut integralSeen := false
    let mut failure : Option String := none
    for count in #[8, 24, 48, 80] do
      for seed in [0:24] do
        for fraction in #[0.01, 0.5] do
          let g ← dag count seed.toUInt64 fraction
          let ((integral, piv, fail), _) ← runOn g (do
            NetworkSimplex.initState
            let integral := (← get).integralCutvalues
            NetworkSimplex.feasibleTree
            let mut piv := 0
            let mut fail : Option String := none
            for _ in [0:512] do
              let actual := (← get).cutvalue.data.map Float.toBits
              NetworkSimplex.cutvaluesReference
              let expected := (← get).cutvalue.data.map Float.toBits
              if actual != expected && fail.isNone then
                fail := some s!"cut bits differ: count={count} seed={seed} fraction={fraction}"
              let some leave := NetworkSimplex.leaveEdge (← get) | break
              let some enter := NetworkSimplex.enterEdge (← get) leave
                | fail := fail <|> some s!"no feasible pivot: count={count} seed={seed}"; break
              NetworkSimplex.exchange leave enter
              piv := piv + 1
            return (integral, piv, fail))
          integralSeen := integralSeen || integral
          pivots := pivots + piv
          if failure.isNone then failure := fail
    check "fractional weights are not integral" !integralSeen
    report "cut values match the reference" failure.isNone (failure.getD "")
    report "exercise fractional tree exchanges" (pivots > 100) s!"pivots={pivots}"

/-- `integral_pivot_cuts_equal_full_leaf_elimination`: with integral weights the
incremental pivot update (`updateCutvalues`) equals a full `cutvalues`, and the
tree adjacency keeps the `nodeEdges` order. -/
def integralPivotCuts : Suite :=
  suite "alg.common.networksimplex.NetworkSimplex.integral_pivot_cuts_equal_full_leaf_elimination" do
    let mut pivots := 0
    let mut allIntegral := true
    let mut failure : Option String := none
    for count in #[8, 24, 48, 80] do
      for seed in [0:24] do
        let g ← dag count seed.toUInt64 0.0
        let ((integral, piv, fail), _) ← runOn g (do
          NetworkSimplex.initState
          let integral := (← get).integralCutvalues
          NetworkSimplex.feasibleTree
          let mut piv := 0
          let mut fail : Option String := none
          for _ in [0:512] do
            let some leave := NetworkSimplex.leaveEdge (← get) | break
            let some enter := NetworkSimplex.enterEdge (← get) leave
              | fail := fail <|> some s!"no feasible pivot: count={count} seed={seed}"; break
            NetworkSimplex.exchange leave enter
            let s ← get
            for nid in [0:s.nodeEdges.size] do
              let expected := s.nodeEdges[nid]!.filter fun eid => s.eTree[eid]!
              if s.treeEdges[nid]! != expected && fail.isNone then
                fail := some s!"tree DFS order differs: count={count} seed={seed} node={nid}"
            let incremental := s.cutvalue
            let treeEdgeIds := s.treeEdgeIds
            NetworkSimplex.cutvalues
            let full := (← get).cutvalue
            for eid in treeEdgeIds do
              if incremental[eid]! != full[eid]! && fail.isNone then
                fail := some s!"cut differs: count={count} seed={seed} pivot={piv} edge={eid}"
            piv := piv + 1
          return (integral, piv, fail))
        allIntegral := allIntegral && integral
        pivots := pivots + piv
        if failure.isNone then failure := fail
    check "integral weights are integral" allIntegral
    report "incremental cuts equal leaf elimination" failure.isNone (failure.getD "")
    report "exercise tree exchanges, including tied cuts" (pivots > 100) s!"pivots={pivots}"

/-- `incomplete_postorder_keeps_full_cut_computation`: disconnected or
source-free cyclic inputs leave nodes outside the post-order traversal, which
disables the incremental cut values. -/
def incompletePostorder : Suite :=
  suite "alg.common.networksimplex.NetworkSimplex.incomplete_postorder_keeps_full_cut_computation" do
    for sourceFreeCycle in #[false, true] do
      let edges := if sourceFreeCycle then #[(0, 1), (1, 2), (2, 0), (3, 4), (4, 5), (5, 3)]
        else #[(0, 1), (1, 2), (0, 2), (3, 4), (4, 5), (3, 5)]
      let g ← mkGraph 6 edges fun b => b.delta 1 |>.weight 1.0
      let ((integralBefore, postOrder, nodeCount, integralAfter, cuts, cuts'), _) ← runOn g (do
        NetworkSimplex.initState
        let integralBefore := (← get).integralCutvalues
        NetworkSimplex.feasibleTree
        let s ← get
        let res := (s.postOrder, s.graph.nodeList.size, s.integralCutvalues, s.cutvalue)
        NetworkSimplex.cutvalues
        return (integralBefore, res.1, res.2.1, res.2.2.1, res.2.2.2, (← get).cutvalue))
      let tag := s!"sourceFreeCycle={sourceFreeCycle}"
      check s!"{tag}: integral after initialize" integralBefore
      report s!"{tag}: post order incomplete" (postOrder <= (nodeCount : Int)) s!"postOrder={postOrder}"
      check s!"{tag}: integral cut values disabled" !integralAfter
      check s!"{tag}: full cut values unchanged" (cuts.data == cuts'.data)

/-- `fractional_or_large_weights_keep_original_cut_arithmetic`. -/
def fractionalOrLargeWeights : Suite :=
  suite "alg.common.networksimplex.NetworkSimplex.fractional_or_large_weights_keep_original_cut_arithmetic" do
    for fraction in #[0.01, 9007199254740992.0] do
      let g ← dag 8 17 fraction
      let (integral, _) ← runOn g (do
        NetworkSimplex.initState
        return (← get).integralCutvalues)
      check s!"fraction={Float.toShortest fraction}: not integral" !integral

/-- `subtree_compaction_preserves_survivor_and_reattachment_order`. -/
def subtreeCompaction : Suite :=
  suite "alg.common.networksimplex.NetworkSimplex.subtree_compaction_preserves_survivor_and_reattachment_order" do
    let g ← mkGraph 7 #[(0, 1), (1, 2), (0, 2), (2, 3), (3, 4), (0, 5), (1, 6)] fun b => b.delta 1
    let ((survivors, ordinals, layers), _) ← runOn g (do
      NetworkSimplex.removeSubtrees
      let survivors := (← get).graph.nodeList.map (·.idx)
      NetworkSimplex.modifyNode ⟨1⟩ fun n => { n with layer := 1 }
      NetworkSimplex.modifyNode ⟨2⟩ fun n => { n with layer := 2 }
      NetworkSimplex.reattachSubtrees
      let g := (← get).graph
      return (survivors, g.nodeList.map (·.idx), g.nodes.map (·.layer)))
    checkEq "survivors" survivors #[0, 1, 2]
    checkEq "reattachment order" ordinals #[0, 1, 2, 3, 6, 5, 4]
    checkEq "layers" layers #[0, 1, 2, 3, 4, 1, 2]

-- ============================================================================
-- tests/all/network_simplex_test.rs
-- ============================================================================

/-- Rust `generate_random_graph`: 4000 nodes, 8000 random edges plus a chain,
then every edge is reversed to point from the lower to the higher node id.
With `setIds` the edges get their creation index as `id` (oracle cross-check). -/
private def generateRandomGraph (random : Random) (setIds : Bool := false) : IO (G × Random) := do
  let n := 4000
  let e := 8000
  let mut random := random
  let mut g : G := {}
  for i in [0:n] do
    g := (NNode.of |>.id (i : Int) |>.create g).1
  for k in [0:e] do
    let (src, r) := random.nextInt n
    random := r
    let (tgt0, r) := random.nextInt n
    random := r
    let mut tgt := tgt0
    while src == tgt do
      let (t, r) := random.nextInt n
      random := r
      tgt := t
    let (delta, r) := random.nextInt 50
    random := r
    let (w, r) := random.nextDouble
    random := r
    g ← addEdge g (NEdge.of |>.id (if setIds then (k : Int) else 0)
      |>.delta delta |>.weight (w * 50.0) |>.source ⟨src.toNat⟩ |>.target ⟨tgt.toNat⟩)
  for i in [0:n - 1] do
    let (delta, r) := random.nextInt 50
    random := r
    let (w, r) := random.nextDouble
    random := r
    g ← addEdge g (NEdge.of |>.id (if setIds then ((e + i : Nat) : Int) else 0)
      |>.delta delta |>.weight (w * 50.0) |>.source ⟨i⟩ |>.target ⟨i + 1⟩)
  for node in g.nodeList do
    let outgoing := (g.node node).outgoingEdges
    for edge in outgoing do
      let ed := g.edge edge
      if (g.node ed.source).id > (g.node ed.target).id then
        g := NEdge.reverse g edge
  return (g, random)

/-- `network_simplex_deltas`: the computed layering respects every edge's
minimum length on 25 random acyclic graphs. -/
def networkSimplexDeltas : Suite :=
  suite "alg.common.networksimplex.network_simplex_test.network_simplex_deltas" do
    let mut random := Random.ofInt 1
    let mut acyclic := true
    let mut violation : Option String := none
    for i in [0:5] do
      for j in [0:5] do
        let (g, r) ← generateRandomGraph random
        random := r
        let (isAcyclic, g) := g.isAcyclic
        acyclic := acyclic && isAcyclic
        let monitor ← ProgressMonitor.basic
        let g ← (NetworkSimplex.forGraph g).execute monitor
        for node in g.nodeList do
          for edge in (g.node node).outgoingEdges do
            let ed := g.edge edge
            if (g.node ed.target).layer - (g.node ed.source).layer < ed.delta && violation.isNone then
              violation := some s!"graph {i}/{j}: edge {edge}"
    check "graphs are acyclic" acyclic
    report "Valid delta" violation.isNone (violation.getD "")

-- ============================================================================
-- elk-rs oracle cross-check
-- ============================================================================

/-! The expected hashes below were produced by a scratch Rust program linked
against the elk-rs crates at the pinned oracle commit (`org-eclipse-elk-alg-common`
0.12.1): it builds the same graphs with the same generator, runs
`NetworkSimplex::execute` and hashes the result. The hash (FNV-1a over
little-endian `i64`s) covers, for every node in `NGraph::nodes` order, its id,
its layer and the ids of its incoming and outgoing edges, so it pins the node
order after subtree removal/reattachment, the layering (balancing, previous
layering, iteration limit) and the edge list mutations. -/

/-- 64-bit LCG of the oracle generator (`next`). -/
private def lcgNext (s : UInt64) : UInt64 × UInt64 :=
  let s := s * 6364136223846793005 + 1442695040888963407
  (s >>> 33, s)

/-- FNV-1a step over the little-endian bytes of an `i64`. -/
private def fnv (h : UInt64) (v : Int) : UInt64 := Id.run do
  let u := Int.toUInt64Wrap v
  let mut h := h
  for k in [0:8] do
    h := (h ^^^ ((u >>> (8 * k).toUInt64) &&& 0xff)) * 0x100000001b3
  return h

/-- Hash of the node order, layers and edge lists (oracle `hash`). -/
private def graphHash (g : G) : UInt64 := Id.run do
  let mut h : UInt64 := 0xcbf29ce484222325
  for node in g.nodeList do
    let n := g.node node
    h := fnv h n.id
    h := fnv h n.layer
    h := fnv h n.incomingEdges.size
    for e in n.incomingEdges do
      h := fnv h (g.edge e).id
    h := fnv h n.outgoingEdges.size
    for e in n.outgoingEdges do
      h := fnv h (g.edge e).id
  return h

/-- Oracle case configuration (`case_params`). -/
private structure OracleCase where
  n : Nat
  m : Nat
  integral : Bool
  chain : Bool
  balance : Bool
  prev : Option (Array Int)
  limit : Option Int
  connect : Bool
  twice : Bool

private def oracleCaseParams (c : Nat) : OracleCase :=
  let sizes : Array Nat := #[3, 5, 12, 39, 40, 41, 60, 100, 250, 700]
  let n := sizes[c % 10]!
  { n := n
    m := n * (1 + c / 10 % 3) / 2 + 1
    integral := c % 2 == 0
    chain := c % 3 != 2
    balance := c % 4 < 2
    prev := if c % 5 == 0 then some #[2, 0, 3, 1] else none
    limit := if c % 7 == 3 then some 2 else none
    connect := c % 6 == 1
    twice := c % 8 == 5 }

/-- Oracle `build`: optional chain edges, then `m` random forward edges. -/
private def oracleBuild (c : Nat) (p : OracleCase) : IO G := do
  let mut s : UInt64 := c.toUInt64 + 12345
  let mut g : G := {}
  for i in [0:p.n] do
    g := (NNode.of |>.id (i : Int) |>.create g).1
  let mut eid : Int := 0
  if p.chain then
    for i in [0:p.n - 1] do
      let (r, s') := lcgNext s
      s := s'
      if r % 4 != 0 then
        -- edge attributes are drawn right away, like `add_edge`
        let (d, s') := lcgNext s
        s := s'
        let (w, s') := lcgNext s
        s := s'
        let weight := if p.integral then (1 + w % 5).toFloat else (w % 1000).toFloat / 37.0
        g ← addEdge g (NEdge.of |>.id eid |>.delta (d % 4).toNat |>.weight weight |>.source ⟨i⟩ |>.target ⟨i + 1⟩)
        eid := eid + 1
  for _ in [0:p.m] do
    let (a, s') := lcgNext s
    s := s'
    let (b, s') := lcgNext s
    s := s'
    let a := (a % p.n.toUInt64).toNat
    let b := (b % p.n.toUInt64).toNat
    if a == b then
      continue
    let (src, tgt) := if a < b then (a, b) else (b, a)
    let (d, s') := lcgNext s
    s := s'
    let (w, s') := lcgNext s
    s := s'
    let weight := if p.integral then (1 + w % 5).toFloat else (w % 1000).toFloat / 37.0
    g ← addEdge g (NEdge.of |>.id eid |>.delta (d % 4).toNat |>.weight weight |>.source ⟨src⟩ |>.target ⟨tgt⟩)
    eid := eid + 1
  return g

/-- Oracle `run_case`. -/
private def oracleRunCase (c : Nat) : IO UInt64 := do
  let p := oracleCaseParams c
  let mut g ← oracleBuild c p
  if p.connect then
    g := g.makeConnected.1
  for _ in [0:if p.twice then 2 else 1] do
    let mut ns := NetworkSimplex.forGraph g |>.withBalancing p.balance |>.withPreviousLayering p.prev
    if let some l := p.limit then
      ns := ns.withIterationLimit l
    g ← ns.execute'
  return graphHash g

/-- Expected `run_case` hashes for cases `0 … 239` (elk-rs oracle). -/
private def oracleCaseHashes : Array UInt64 := #[
    0x4fb40bba0f9e2b43, 0x2ae038a43984ffe7, 0xaa7fbe00600fe886, 0x4172b41e82c92e0e, 0x72e90c7217f86506, 0xc0a4e2fb707f38e3,
    0xe9f86d4f241f6fcc, 0x5dffd1e15d595b22, 0x97d3d4e977450181, 0x14211f649828b3b4, 0x11c1eb9d539844e6, 0xf08e0b3b1efd2b46,
    0x82124f0ef47af5cb, 0x31dc90922d53bbb2, 0xa772d488829f87a3, 0xb18f5cff57618fb4, 0x3d274cd0c4de94fb, 0x9d8010e7cbd19a2c,
    0x1df7cc4d79ad5a01, 0x32374cd0891b7476, 0x8142e1a50d312503, 0x7222d52c1210da08, 0xc03ddd9f732366c9, 0x36a8c6a97e0da423,
    0xf3ef9df80add2e1f, 0xfb17681eb7b6d2cc, 0x7ca283e2413a6d28, 0x77dcb6c4d6320214, 0xdc5ed882eae5e458, 0x7795d5ba7ec71f80,
    0x9f1435764ca0cae4, 0x1c1fef416f86a743, 0x2e774926cee3c784, 0xccb5770313aa6f45, 0x7afbae94f9c3f492, 0x4e677ea31ac9094e,
    0x594beb817269061d, 0xe5ff5f41f699d744, 0x876bdc9d1f9cd364, 0x59374dd669048b68, 0x70c0fa4a5ba2cc41, 0xc39311988bb75300,
    0x7ca05334cb4cf603, 0x4bdb3075807eaf4f, 0x4e2d97a3dcc7fb67, 0xf278dd548bf000a3, 0xd75ea5eff4011909, 0xc269237e6c6d2584,
    0xb0cd124d2063055e, 0xc3d55e2aca12d3ba, 0xad81db3bbdcd7886, 0x0747d1f25408cbcb, 0xeaf0396783608e3d, 0xe0d57d603acb5465,
    0xcf43e0e163c98662, 0x7cfeae59bda69c1a, 0xb1f0ad9b4d894348, 0x70f07f00fc6b9bf4, 0x4e6ec84cd81318a0, 0xed54d2e7926eade8,
    0x7a345bf67bcf2d45, 0x204b7f22da1d58c1, 0x3a6f4ccaf20e4685, 0x779dfc207ce78cfd, 0x47a1347a6fdb0184, 0x60697c9e3a382da7,
    0x3bf13d38454b0e19, 0x1ea5ab8f74165159, 0xcd9611e24b4a56a4, 0x225fbf7ad2b32326, 0xc3d658d301f54603, 0x1ebc7b3af6939261,
    0x8585518393eb8445, 0xcd0bf808c3a31398, 0x752c83b1e88102a8, 0x82b82e2afa487f12, 0xbe1fdcea0e921433, 0xd78b8ab85da5e235,
    0xc2f58cb522ecdcea, 0xc4dbb784dd062466, 0x6cfb50c78fabc1c6, 0xc14df2176a4ee4c4, 0x2ef328686d7f44a7, 0x223ce6e2287d374e,
    0x1074b4d3bff8ddd8, 0x0dd132974ef87323, 0x33564c0073268b22, 0xf403446525e33154, 0x87fee331300096cf, 0xbbc293f08ab6d8e5,
    0xd48e976501c36083, 0xe9564056fe8ee3e8, 0x6b4416e1ecdcada2, 0x5e5fa0b8ef6d0e29, 0x50a3a09090dfcd7a, 0x3e4740eefb810f6b,
    0x92896a2691d728f2, 0xbcf071166a2509f9, 0xdf10ed00820fb3c3, 0xb7852b4bfa7b9d99, 0x97573ee927427e22, 0x8a55bb42a9b069a1,
    0x8478a0d5d3defae0, 0xce37c0843fd5ef12, 0x7db22c4d5f76d80d, 0x3e9baf8a31c46bd4, 0x8ba339fd8757dd84, 0x94a5be2c84407f98,
    0x867ef58b7fd47b32, 0xb9a15803a0c7d522, 0xeadd10372b316a65, 0xdacbbad442367aef, 0x93037d7f0ed8ac89, 0x9b1fd1cd12eb4fa0,
    0xcf71861330b9c245, 0xad6b6bac80443fdc, 0xcaf4be4e2dbd110c, 0x2b977543c3bd68c3, 0x3c20bc887d0c0a50, 0x67d841ba2fe52a9f,
    0x3cbdb3767c397284, 0x1f8edaa01ff6e8e5, 0x47550802b0d14403, 0x930a5f3f98942e7d, 0x5aa5427509f36628, 0x9cc476510817858a,
    0x6d38312912ae93a2, 0xa9dd9c8503c93705, 0x707e2fa9a1acf2c8, 0xae9afafd79a7ead4, 0xef1240d05a30e324, 0xd4c4dca5abb76dc5,
    0xc856beb90c03a84a, 0xc40ddb24db2eed14, 0xcae7e1ba4e101986, 0xe54a99232dad1fe7, 0x8a2486ba58f02da5, 0xbe4f937a0af20ca0,
    0x15b6734faef9d565, 0xb2a37c41d409f1b3, 0xc5d0eeadb2e213c1, 0x450ba45ee7cbd266, 0x7a2704167ea9c7ee, 0xb7122ca37cb43b04,
    0xde53edd2265f4f61, 0x86bf62885cd76975, 0xab795c0e4f6bd0e0, 0x1b482c530c5e6af1, 0x8c2a69fb7e3278bb, 0x33fbd5abe72a54f5,
    0x0556bbce01a6ab43, 0x63e1d92d1693ac20, 0x64c94a66cef3b723, 0x80f99d4de40cc707, 0x4a16bfa0dcd3f7cc, 0x602fe17062558629,
    0x4915fda9036389dc, 0x904e19232c4f4b7b, 0xa4a6ed3522cc288d, 0x82884b2862e20161, 0x684290a2d6874802, 0x61606d434b29a183,
    0xd6dbe5cfd6959b2a, 0xd43fe9686ce83bd0, 0x862b0a33b63ffd62, 0x0b26b8e0856e5766, 0xdcec17539b0b4f60, 0xfb4c64e33f14c689,
    0x7b6de28ed4d1aa32, 0x526c57967afc3f1d, 0xbed50c8e331f7786, 0x6cdc8dfc6f16ed20, 0x9927bbe3ef04e1a7, 0x21223694e53912a2,
    0x5750075f4290ead3, 0x9298df2c90d6a08c, 0xcbb92417cbdad308, 0x6dd3abab17cc4c46, 0x55e65b3d0309e750, 0xd5c1d3c6ce430623,
    0x9294f35643583841, 0x79c7cdf766815603, 0xfadad85793034d87, 0xda2c04144543588d, 0xe14fc78fa5c73461, 0x5e0d1fc1e286f20d,
    0x10da94325696f1ab, 0xbb3d5be61325f82c, 0xdc9e4cef644cc58b, 0xccc16b54515e900c, 0xe59ec70ea0637662, 0x0287018c242aff42,
    0xfd4f6ec7dc7b9f28, 0xa26c59a17ced30dc, 0x141528104e43534f, 0xde0b6a629c88461f, 0xbf0679a9ab61236a, 0xaa771e2ca8ff5764,
    0xb3124a0341df3b36, 0x606290886e17d19e, 0x8d40b722ba721923, 0xd2ec2813c9d98381, 0x958be28244eef5ce, 0x23079b919da5f944,
    0xf31f4cf20b8c7938, 0xf27e63aaf900c0a4, 0x2123fde346b389a4, 0xcbb04a0648975b89, 0x76a0abbf568ba8ef, 0x4512172324765854,
    0x336c33c434ebf2a4, 0x3bc7b24b2774d242, 0xa9b24dca446cb460, 0xe17f9184ab08fc18, 0xd83c24d481b2c094, 0x44b26df9918963ee,
    0x71b7b25ba347c79d, 0xf943c1b4603dbf8f, 0x0d54964a02416706, 0x9c8fce91d04fa5e4, 0x38f0333579952fe7, 0x8ffe43078f69e044,
    0x5cc192744f72b322, 0x6d6eca2e572515b6, 0xb22be221ed3b6aed, 0x3ca4b1ffd878c7a4, 0x3fcb99c1b5a2165a, 0x19cb6ddc3e9a5e40,
    0x42500b05b1837b06, 0x11bf0c7be881cc31, 0x2889962294a84cc4, 0x1beecf05402a6a61, 0xb14eda03772de9c8, 0x9dcea4c4ef20822a,
    0x51b0b3734aff4e7c, 0xa6a75d75ae406fe4, 0x6a964a606f6cfe63, 0xd28aa091281fc75a, 0x72d73583b97737fa, 0x8cc23f9ba2aabc9e]

/-- Expected hashes of the 25 `network_simplex_deltas` graphs (with edge ids). -/
private def oracleRandomHashes : Array UInt64 := #[
    0x51a4fab43a649785, 0x22ad7724f96b6452, 0xd771bbbb6ccae325, 0xc689644bcd1b23bf, 0x1adae26f7d355237, 0x6e138547614ff77d,
    0xf59e6971c85a7d82, 0x0a65afdb29e23bfd, 0xbdc18d4124b06c89, 0x26e89251bb2a2c54, 0x9c1f658a48d53616, 0xca9c64749d9f439b,
    0xea4230e0e324879f, 0xced95f79a1a264a9, 0x27d960444ed43d59, 0x0b6d57b2bdf07b2c, 0x02aa6663186d302e, 0x7a741a9933a2f6dd,
    0xe2594a559b59de7e, 0x5063baaec917d322, 0xb40ac4539c28f731, 0xa02701825a77ad35, 0xdb3444f25e02b118, 0x818591cea8008732,
    0x69929eeea8e5afb2]

/-- Exact parity with elk-rs on generated graphs (see the comment above). -/
def oracleCrossCheck : Suite :=
  suite "alg.common.networksimplex.NetworkSimplex.elk_rs_oracle_cross_check" do
    let mut mismatches : Array Nat := #[]
    for c in [0:oracleCaseHashes.size] do
      if (← oracleRunCase c) != oracleCaseHashes[c]! then
        mismatches := mismatches.push c
    report "generated cases" mismatches.isEmpty s!"mismatching cases {mismatches}"
    let mut random := Random.ofInt 1
    let mut randomMismatches : Array Nat := #[]
    for k in [0:oracleRandomHashes.size] do
      let (g, r) ← generateRandomGraph random (setIds := true)
      random := r
      let g ← (NetworkSimplex.forGraph g).execute (← ProgressMonitor.basic)
      if graphHash g != oracleRandomHashes[k]! then
        randomMismatches := randomMismatches.push k
    report "random 4000-node graphs" randomMismatches.isEmpty s!"mismatching graphs {randomMismatches}"

-- ============================================================================
-- Lean-only API checks
-- ============================================================================

/-- `NGraph.makeConnected`, `NGraph.isAcyclic`, builder failures and `execute`
on small graphs (Java semantics, no Rust counterpart). -/
def graphApi : Suite :=
  suite "alg.common.networksimplex.NGraph.api" do
    -- two components {0,1} and {2}: a root connected with zero-delta, zero-weight edges
    let g ← mkGraph 3 #[(0, 1)] id
    let (g, root) := g.makeConnected
    checkEq "artificial root" (root.map (·.idx)) (some 3)
    checkEq "root edges" ((g.node ⟨3⟩).outgoingEdges.map fun e => ((g.edge e).target.idx, (g.edge e).delta)) #[(0, 0), (2, 0)]
    let (g', root') := g.makeConnected
    checkEq "connected graph: no root" (root'.map (·.idx)) none
    checkEq "connected graph unchanged" g'.nodeList.size 4
    checkEq "acyclic" g.isAcyclic.1 true
    let cyclic ← mkGraph 3 #[(0, 1), (1, 2), (2, 0)] id
    checkEq "cycle detected" cyclic.isAcyclic.1 false
    let back ← mkGraph 3 #[(0, 1), (1, 2), (0, 2), (2, 1)] id
    checkEq "back edge detected" back.isAcyclic.1 false
    checkThrows "self-loop rejected" (do let _ ← (NEdge.of |>.source ⟨0⟩ |>.target ⟨0⟩).create g; pure ())
    checkThrows "missing target rejected" (do let _ ← (NEdge.of |>.source ⟨0⟩).create g; pure ())
    checkThrows "node not part of edge" (do let _ ← (g.edge ⟨0⟩).other ⟨2⟩; pure ())
    -- a diamond with a long edge: 0→1→2→3 and 0→3 (delta 1, weight 1)
    let d ← mkGraph 4 #[(0, 1), (1, 2), (2, 3), (0, 3)] fun b => b.weight 1.0
    let d ← (NetworkSimplex.forGraph d).execute'
    checkEq "diamond layers" (d.nodes.map (·.layer)) #[0, 1, 2, 3]
    let empty ← (NetworkSimplex.forGraph ({} : G)).execute'
    checkEq "empty graph" empty.nodeList.size 0

def suites : Array Tests.Suite := #[
  graphAndEdgesReleaseNodesAndOrigins,
  indexedFractionalCuts,
  integralPivotCuts,
  incompletePostorder,
  fractionalOrLargeWeights,
  subtreeCompaction,
  networkSimplexDeltas,
  oracleCrossCheck,
  graphApi
]

end Tests.AlgCommon.NetworkSimplex
