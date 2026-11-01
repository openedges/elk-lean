import Tests.Framework
import Elk.Alg.Layered
import Tests.Layered.IntermediatePreserveOrder
/-!
Differential tests of the per-layout fast paths of round 13 SMF against their kept references:
`LGraphArena.findPortIndices` (tail loop) against `findPortIndicesRef` (the `for` loop) on random
port side sequences, `LayeredM.randomHolder` (pure loop) against the monadic `for` loop on random
owner chains (including cycles and chains longer than 64 hops), and `Random.nextLongBits` /
`Random.setSeedBits` against `nextLong` / `setSeed`.
-/
namespace Tests.Layered.SmallFastPaths

open Tests Elk.Graph Elk.Core.Util Elk.Core.Options Elk.Alg.Layered Elk.Alg.Layered.Graph
open Tests.Layered.IntermediatePreserveOrder (lcgNext rnd randomGraph)

/-- `findPortIndices` = `findPortIndicesRef` on the nodes of random graphs (ports on random, unsorted
sides; nodes without ports). -/
def findPortIndicesTests : Suite := suite "layered.graph.findPortIndices.fastPath" do
  let mut bad := 0
  let mut nodes := 0
  let mut multiRun := 0
  for k in [0:500] do
    let seed : UInt64 := (k.toUInt64 + 3) * 0x9e3779b97f4a7c15
    let (rg, a) ← LayeredM.run (randomGraph seed)
    for n in rg.nodes do
      nodes := nodes + 1
      let fast := a.findPortIndices n
      let ref := a.findPortIndicesRef n
      if fast != ref then bad := bad + 1
      if (fast.filter (·.isSome)).size > 1 then multiRun := multiRun + 1
  checkEq s!"findPortIndices = findPortIndicesRef ({nodes} nodes)" bad 0
  check "nodes with ports on several sides are exercised" (multiRun > 100)

/-- The original monadic `randomHolder` loop (reference). -/
def randomHolderRef (g : LGraphId) : LayeredM LGraphId := do
  let mut cur := g
  for _ in [0:64] do
    match (← LayeredM.getGraph cur).internal.randomOwner with
    | some o =>
      if o == cur then return cur
      cur := o
    | none => return cur
  return cur

/-- `randomHolder` = `randomHolderRef` on random owner links (self links, cycles, long chains). -/
def randomHolderTests : Suite := suite "layered.graph.randomHolder.pureLoop" do
  let mut bad := 0
  let mut runs := 0
  for k in [0:200] do
    let mut s : UInt64 := (k.toUInt64 + 1) * 0xbf58476d1ce4e5b9
    let (count, s1) := rnd s 90
    s := s1
    let mut owners : Array (Option Nat) := #[]
    for i in [0:count + 1] do
      let (v, s1) := rnd s 6
      let (o, s2) := rnd s1 (count + 1)
      s := s2
      -- mostly a chain to the previous graph (long chains), sometimes a random owner or none
      owners := owners.push (if v == 0 then none else if v == 1 then some o else if i == 0 then none else some (i - 1))
    let ((), a) ← LayeredM.run (do
      let mut ids : Array LGraphId := #[]
      for _ in owners do ids := ids.push (← LayeredM.createGraph)
      for h : i in [0:owners.size] do
        let owner := owners[i].bind (ids[·]?)
        LayeredM.modifyGraph ids[i]! fun x => { x with internal := { x.internal with randomOwner := owner } })
    for i in [0:owners.size] do
      let g : LGraphId := ⟨i⟩
      let (fast, _) ← LayeredM.run (LayeredM.randomHolder g) a
      let (ref, _) ← LayeredM.run (randomHolderRef g) a
      runs := runs + 1
      if fast != ref then bad := bad + 1
  checkEq s!"randomHolder = reference loop ({runs} graphs)" bad 0

/-- `nextLongBits`/`setSeedBits` = `nextLong`/`setSeed` (values, generator states, reseeding). -/
def randomBitsTests : Suite := suite "core.util.random.nextLongBits" do
  let mut bad := 0
  for k in [0:2000] do
    let seed : Int := ((lcgNext (k.toUInt64 + 11)).toNat : Int) - (2 ^ 63 : Nat)
    let r := Random.ofInt (if k % 7 == 0 then (k : Int) - 1000 else seed)
    let (v, r1) := r.nextLong
    let (b, r2) := r.nextLongBits
    if b.toInt64.toInt != v || r1.seed != r2.seed then bad := bad + 1
    if (r.setSeedBits b).seed != (r.setSeed v).seed then bad := bad + 1
  checkEq "nextLongBits/setSeedBits = nextLong/setSeed (2000 generators)" bad 0

def suites : Array Suite := #[findPortIndicesTests, randomHolderTests, randomBitsTests]

end Tests.Layered.SmallFastPaths
