import Tests.Framework
import Elk.Alg.Layered
import Tests.Layered.IntermediatePreserveOrder
/-!
Differential tests of the round 14 M16 in-place update rewrites (PLAN 7.1 items 16, 59) against the
original formulations kept here as references: `KVectorChain.offset`/`offsetValues`/`scale`
(out-of-line updaters) against the inline-lambda `Array.map`s, `NodePromotion.LayerNodeMap.putBoxed`
(fields taken apart, `modifyIn`) against the original record update on random put sequences,
`RectangleStripOverlapRemover.computeOverlaps` (right border read before the updates) against the
original scanline on random rectangles, and `RoutingSlotAssigner.ShiftState.setSlot` against the
original record update.
-/
namespace Tests.Layered.InPlaceUpdates

open Tests Elk.Graph Elk.Core.Math Elk.Core.Util Elk.Alg.Layered Elk.Alg.Layered.Graph
open Elk.Alg.Layered.Intermediate Elk.Alg.Common.Overlaps
open Tests.Layered.IntermediatePreserveOrder (lcgNext rnd)

/-- A random double from a small set that includes signed zeros, NaN and infinities. -/
def rndFloat (s : UInt64) : Float × UInt64 :=
  let (k, s) := rnd s 12
  let (v, s) := rnd s 100000
  let x : Float := match k with
    | 0 => 0.0
    | 1 => -0.0
    | 2 => 0.0 / 0.0
    | 3 => 1.0 / 0.0
    | 4 => -1.0 / 0.0
    | _ => (v.toFloat - 50000.0) / 7.0
  (x, s)

/-- Bitwise equality of two chains. -/
def sameChain (a b : KVectorChain) : Bool :=
  a.size == b.size && (List.range a.size).all fun i =>
    a[i]!.x.toBits == b[i]!.x.toBits && a[i]!.y.toBits == b[i]!.y.toBits

/-- `offset`/`offsetValues`/`scale` = the inline-lambda `map`s (bitwise, on random chains). -/
def kvectorChainTests : Suite := suite "m16.kvectorChain.inPlace" do
  let mut bad := 0
  let mut s : UInt64 := 0x51ab
  for _ in [0:400] do
    let (n, s1) := rnd s 12
    s := s1
    let mut c : KVectorChain := #[]
    for _ in [0:n] do
      let (x, s2) := rndFloat s
      let (y, s3) := rndFloat s2
      s := s3
      c := c.push ⟨x, y⟩
    let (ox, s4) := rndFloat s
    let (oy, s5) := rndFloat s4
    let (f, s6) := rndFloat s5
    s := s6
    let o : KVector := ⟨ox, oy⟩
    -- the inputs are shared with the references, so both copy paths of `map` are exercised too
    if !sameChain (KVectorChain.offset c o) (c.map (· + o)) then bad := bad + 1
    if !sameChain (KVectorChain.offsetValues c ox oy) (c.map (·.addValues ox oy)) then bad := bad + 1
    if !sameChain (KVectorChain.scale c f) (c.map (·.scale f)) then bad := bad + 1
    -- unshared inputs (the in-place path)
    let c1 := c.map id
    if !sameChain (KVectorChain.offset (c1.push ⟨1, 2⟩) o) ((c.push ⟨1, 2⟩).map (· + o)) then bad := bad + 1
  checkEq "offset/offsetValues/scale = map references" bad 0

/-- The original `LayerNodeMap.putBoxed` (reference). -/
def putBoxedRef (m : NodePromotion.LayerNodeMap) (key : Int) (box : Nat) (node : LNodeId) :
    NodePromotion.LayerNodeMap := Id.run do
  let mut layers := m.layers
  if let some (oldKey, _) := m.reverse.get? node then
    if let some i := layers.findIdx? (·.1 == oldKey) then
      layers := layers.modify i fun (k, ns) => (k, ns.filter (· != node))
  match layers.findIdx? (·.1 == key) with
  | some i => layers := layers.modify i fun (k, ns) => (k, ns.push node)
  | none =>
    let pos := (layers.findIdx? (·.1 > key)).getD layers.size
    layers := layers.insertIdx! pos (key, #[node])
  return { m with layers := layers, reverse := m.reverse.insert node (key, box) }

/-- Same layers, boxes and reverse entries. -/
def sameMap (a b : NodePromotion.LayerNodeMap) (nodes : Nat) : Bool :=
  a.layers == b.layers && a.nextBox == b.nextBox &&
    (List.range nodes).all fun i => a.reverse.get? ⟨i⟩ == b.reverse.get? ⟨i⟩

/-- `putBoxed` = `putBoxedRef` on random put sequences (moves between keys, repeated puts). -/
def layerNodeMapTests : Suite := suite "m16.nodePromotion.layerNodeMap" do
  let mut bad := 0
  let mut s : UInt64 := 0x77e1
  for _ in [0:300] do
    let (nodes, s1) := rnd s 20
    let nodes := nodes + 1
    let (ops, s2) := rnd s1 60
    s := s2
    let mut a : NodePromotion.LayerNodeMap := {}
    let mut b : NodePromotion.LayerNodeMap := {}
    for _ in [0:ops] do
      let (k, s3) := rnd s 9
      let (n, s4) := rnd s3 nodes
      let (bx, s5) := rnd s4 5
      s := s5
      let key : Int := (k : Int) - 4
      a := a.putBoxed key bx ⟨n⟩
      b := putBoxedRef b key bx ⟨n⟩
      if !sameMap a b nodes then bad := bad + 1
  checkEq "putBoxed = putBoxedRef after every put" bad 0

/-- The original `computeOverlaps` (reference). -/
def computeOverlapsRef (nodes : Array RectangleNode) : Array RectangleNode := Id.run do
  let mut nodes := nodes.map fun n => { n with overlappingNodes := #[] }
  let mut intersecting : Array (Float × Nat) := #[]
  for currentIndex in [0:nodes.size] do
    let some current := nodes[currentIndex]? | continue
    let scanlinePos := current.rectangle.x
    while true do
      match intersecting[0]? with
      | some first =>
        if first.1 < scanlinePos then
          intersecting := intersecting.eraseIdxIfInBounds 0
        else break
      | none => break
    for (_, otherIndex) in intersecting do
      nodes := nodes.modify currentIndex fun n =>
        { n with overlappingNodes := n.overlappingNodes.push otherIndex }
      nodes := nodes.modify otherIndex fun n =>
        { n with overlappingNodes := n.overlappingNodes.push currentIndex }
    let key := (current.rectangle.x + current.rectangle.width, currentIndex)
    let pos := (intersecting.findIdx? fun k =>
      (match Float.compareTotal key.1 k.1 with | .eq => compare key.2 k.2 | o => o) == .lt).getD intersecting.size
    intersecting := intersecting.insertIdxIfInBounds pos key
  return nodes

/-- `computeOverlaps` = `computeOverlapsRef` on random rectangles sorted by x. -/
def overlapTests : Suite := suite "m16.overlaps.computeOverlaps" do
  let mut bad := 0
  let mut pairs := 0
  let mut s : UInt64 := 0x3c0f
  for _ in [0:300] do
    let (n, s1) := rnd s 40
    s := s1
    let mut xs : Array (Float × Float) := #[]
    for _ in [0:n] do
      let (x, s2) := rnd s 200
      let (w, s3) := rnd s2 60
      s := s3
      xs := xs.push (x.toFloat / 2.0, w.toFloat / 3.0)
    let sorted := stableSort xs fun a b => Float.compareTotal a.1 b.1
    let nodes : Array RectangleNode := (List.range sorted.size).toArray.map fun i =>
      { originalIndex := i, rectangle := { x := sorted[i]!.1, y := 0, width := sorted[i]!.2, height := 1 },
        overlappingNodes := #[i] }
    let fast := RectangleStripOverlapRemover.computeOverlaps nodes
    let ref := computeOverlapsRef nodes
    pairs := pairs + fast.foldl (fun acc nd => acc + nd.overlappingNodes.size) 0
    let same := fast.size == ref.size && (List.range fast.size).all fun i =>
      fast[i]!.overlappingNodes == ref[i]!.overlappingNodes && fast[i]!.rectangle == ref[i]!.rectangle &&
        fast[i]!.originalIndex == ref[i]!.originalIndex
    if !same then bad := bad + 1
  checkEq "computeOverlaps = computeOverlapsRef" bad 0
  check "overlaps are exercised" (pairs > 1000)

open Elk.Alg.Layered.Intermediate.Loops Elk.Alg.Layered.Intermediate.Loops.Routing in
/-- `ShiftState.setSlot` = the original record update on random slot assignments. -/
def setSlotTests : Suite := suite "m16.routingSlotAssigner.setSlot" do
  let mut bad := 0
  let mut s : UInt64 := 0x9d21
  let sides : Array Elk.Core.Options.PortSide := #[.undefined, .north, .east, .south, .west]
  let n := 6
  let mut a : RoutingSlotAssigner.ShiftState :=
    { loops := Array.replicate n default, states := Array.replicate n {}, nextFreeRoutingSlotAtPort := #[1, 2] }
  let mut b := a
  for _ in [0:500] do
    let (i, s1) := rnd s (n + 1)
    let (k, s2) := rnd s1 sides.size
    let (v, s3) := rnd s2 7
    s := s3
    let side := sides[k]!
    let slot : Int := (v : Int) - 2
    a := a.setSlot i side slot
    let sideIdx := Elk.ElkEnum.ordinal side
    b := { b with
      states := b.states.modify i fun st => { st with routingSlots := st.routingSlots.set! sideIdx slot }
      loops := b.loops.modify i (·.setRoutingSlot side slot) }
    let same := a.nextFreeRoutingSlotAtPort == b.nextFreeRoutingSlotAtPort &&
      (List.range n).all fun j =>
        a.states[j]!.routingSlots == b.states[j]!.routingSlots &&
          a.states[j]!.occupiedSides == b.states[j]!.occupiedSides &&
          a.loops[j]!.routingSlot == b.loops[j]!.routingSlot
    if !same then bad := bad + 1
  checkEq "setSlot = record update reference" bad 0

def suites : Array Suite := #[kvectorChainTests, layerNodeMapTests, overlapTests, setSlotTests]

end Tests.Layered.InPlaceUpdates
