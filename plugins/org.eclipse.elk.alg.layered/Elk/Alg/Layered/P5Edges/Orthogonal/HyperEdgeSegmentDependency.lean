import Elk.Alg.Layered.P5Edges.Orthogonal.HyperEdgeSegment
import Elk.Graph.ArrayModify
/-!
# `org.eclipse.elk.alg.layered.p5edges.orthogonal.HyperEdgeSegmentDependency`

Port of elk-rs `p5edges/orthogonal/hyper_edge_segment_dependency.rs`: a weighted, regular or
critical dependency `source → target` between two hyperedge segments (the source must be routed
left of the target).

`SegmentGraph` is the local arena replacing Rust's `Rc<RefCell<…>>` object graph: the segments of
one routing run (`edge_segments`, in list order) plus every dependency ever created (a removed
dependency keeps its index with `source`/`target` cleared, exactly like the detached Rust object).
Segments list their dependencies by index. Like Rust (`swap_remove`, not Java's order-preserving
`List.remove`), removing a dependency from a segment's list moves the list's last element into the
freed position.

Representation (ORM): the dependencies live in a `DependencyTable`, three scalar words per
dependency in three columns, so creating one allocates nothing and a dependency costs 24
bytes plus its two list entries (the six one-field columns before cost 48): the *ends* word packs the
`CRITICAL` flag and the encoded source and target (segment index `+ 1`, `0` = none), the *positions*
word the dependency's positions in its source's outgoing and its target's incoming list (which turn
the Rust `position` scan of `swap_remove` into a constant-time lookup; the list contents and order
are those of the scan: a dependency occurs at most once in a list), and the *weight* word the weight
(zigzag-coded `Int`). Every packed word stays below `2^63`, i.e. an unboxed scalar `Nat`: segment
codes and list positions have 31 bits, which no graph reaches (`2^31` segments or dependencies would
need far more memory than the arrays allow). The table is chunked, so it holds no doubling slack and
is never copied while it grows (the dependency count is quadratic in the segments of one routing run:
a node with 5,000 ports gives about 12.5 million). `dependency d` assembles the `HyperEdgeSegmentDependency` value
on demand. The previous six-column representation is kept as the oracle of a differential test
(`Tests.Layered.SegmentGraphRef`).

`SegmentGraph.splitAt` is Java/Rust `HyperEdgeSegment.splitAt`; it is defined here because it removes
dependencies.
-/
namespace Elk.Alg.Layered.P5Edges.Orthogonal

open Elk.Graph Elk.Core.Util Elk.Alg.Layered.P5Edges.Orthogonal.Direction

/-- `HyperEdgeSegmentDependency.DependencyType`. -/
elk_enum DependencyType := regular critical

/-- `CRITICAL_DEPENDENCY_WEIGHT`. -/
def CRITICAL_DEPENDENCY_WEIGHT : Int := 1

/-- `HyperEdgeSegmentDependency`: `source`/`target` are segment indices (`none` once removed). -/
structure HyperEdgeSegmentDependency where
  /-- `dependency_type`. -/
  dependencyType : DependencyType := .regular
  /-- `source` (segment index). -/
  source : Option Nat := none
  /-- `target` (segment index). -/
  target : Option Nat := none
  /-- `weight`. -/
  weight : Int := 0
  deriving Inhabited

/-- Dependencies per chunk of a `DependencyTable` (`2^TABLE_CHUNK_BITS`). -/
private def TABLE_CHUNK : Nat := 65536
/-- `log2 TABLE_CHUNK`. -/
private def TABLE_CHUNK_BITS : Nat := 16
/-- `TABLE_CHUNK - 1`. -/
private def TABLE_CHUNK_MASK : Nat := 65535

/-- The dependency records of a `SegmentGraph` (ORM; no Java/Rust counterpart): three columns of
scalar words (ends, positions, weight; see the module doc), each in chunks of `TABLE_CHUNK` words.
Unlike one `Array`, whose doubling leaves up to half of the capacity unused and holds the old and the
new buffer while it grows, a full chunk is never copied; only the first chunk grows by doubling
(small routing runs allocate little). The columns stay separate because most loops read one word of
consecutive dependencies. Reads past the end give `0` and writes past the end do nothing, like
`Array.get!`/`set!`. -/
structure DependencyTable where
  /-- Ends words, in chunks (all but the last hold exactly `TABLE_CHUNK` words). -/
  ends : Array (Array Nat) := #[]
  /-- Positions words, chunked like `ends`. -/
  positions : Array (Array Nat) := #[]
  /-- Weight words, chunked like `ends`. -/
  weights : Array (Array Nat) := #[]
  /-- Number of dependencies. -/
  count : Nat := 0
  deriving Inhabited

namespace DependencyTable

/-- Word `d` of a chunked column (`0` past the end). -/
@[inline] def columnWord (column : Array (Array Nat)) (d : Nat) : Nat :=
  let ci := d >>> TABLE_CHUNK_BITS
  if h : ci < column.size then column[ci][d &&& TABLE_CHUNK_MASK]! else 0

/-- Ends word of dependency `d`. -/
@[inline] def endsWord (t : DependencyTable) (d : Nat) : Nat := columnWord t.ends d

/-- Positions word of dependency `d`. -/
@[inline] def positionsWord (t : DependencyTable) (d : Nat) : Nat := columnWord t.positions d

/-- Weight word of dependency `d`. -/
@[inline] def weightWord (t : DependencyTable) (d : Nat) : Nat := columnWord t.weights d

/-! The chunk updates are `@[noinline]` and applied with `Array.modify`, which clears the slot with a
scalar dummy: `Array.modifyIn` clears it with `default`, which for an `Array` allocates a fresh empty
array on every update. -/

/-- `chunk.set! off v` (see above). -/
@[noinline] private def chunkSet (off v : Nat) (chunk : Array Nat) : Array Nat := chunk.set! off v

/-- `chunk.push v` (see above). -/
@[noinline] private def chunkPush (v : Nat) (chunk : Array Nat) : Array Nat := chunk.push v

/-- Replaces word `d` of a chunked column (no-op past the end). -/
@[inline] def setColumnWord (column : Array (Array Nat)) (d v : Nat) : Array (Array Nat) :=
  column.modify (d >>> TABLE_CHUNK_BITS) (chunkSet (d &&& TABLE_CHUNK_MASK) v)

/-- Appends a word to a chunked column holding `count` words. -/
@[inline] private def pushColumnWord (column : Array (Array Nat)) (count v : Nat) : Array (Array Nat) :=
  if count &&& TABLE_CHUNK_MASK == 0 then
    column.push (chunkPush v (Array.emptyWithCapacity (if count == 0 then 0 else TABLE_CHUNK)))
  else column.modify (column.size - 1) (chunkPush v)

/-- Replaces the ends word of dependency `d`. -/
@[inline] def setEnds (t : DependencyTable) (d v : Nat) : DependencyTable :=
  match t with
  | ⟨ends, positions, weights, count⟩ => ⟨setColumnWord ends d v, positions, weights, count⟩

/-- Replaces the positions word of dependency `d`. -/
@[inline] def setPositions (t : DependencyTable) (d v : Nat) : DependencyTable :=
  match t with
  | ⟨ends, positions, weights, count⟩ => ⟨ends, setColumnWord positions d v, weights, count⟩

/-- Appends a dependency (a new chunk per column when the last one is full: of capacity `TABLE_CHUNK`,
or growing from empty for the first one). -/
def push (t : DependencyTable) (endsWord positionsWord weightWord : Nat) : DependencyTable :=
  match t with
  | ⟨ends, positions, weights, count⟩ =>
    ⟨pushColumnWord ends count endsWord, pushColumnWord positions count positionsWord,
      pushColumnWord weights count weightWord, count + 1⟩

end DependencyTable

/-- Zigzag code of a weight (`2w` for `w ≥ 0`, `-2w - 1` below). -/
@[inline] private def encodeWeight (w : Int) : Nat :=
  match w with
  | .ofNat n => 2 * n
  | .negSucc n => 2 * n + 1

/-- Inverse of `encodeWeight`. -/
@[inline] private def decodeWeight (code : Nat) : Int :=
  if code &&& 1 == 0 then .ofNat (code >>> 1) else .negSucc (code >>> 1)

/-- Width of a packed segment code or list position (see the module doc). -/
private def FIELD_BITS : UInt64 := 31
/-- Mask of a packed segment code or list position. -/
private def FIELD_MASK : UInt64 := 0x7FFFFFFF
/-- The `CRITICAL` flag of an ends word (bit 62). -/
private def CRITICAL_FLAG : UInt64 := 0x4000000000000000

/-- Ends word of a dependency: the critical flag, the encoded source in bits `31…61` and the
encoded target in bits `0…30`. -/
@[inline] private def packEnds (critical : Bool) (sourceCode targetCode : Nat) : Nat :=
  ((if critical then CRITICAL_FLAG else 0) ||| (sourceCode.toUInt64 <<< FIELD_BITS) ||| targetCode.toUInt64).toNat

/-- Positions word: the position in the source's outgoing list in bits `31…61`, the position in
the target's incoming list in bits `0…30`. -/
@[inline] private def packPositions (sourcePos targetPos : Nat) : Nat :=
  ((sourcePos.toUInt64 <<< FIELD_BITS) ||| targetPos.toUInt64).toNat

/-- The upper field (source code / source position) of a packed word. -/
@[inline] private def upperField (word : Nat) : Nat := ((word.toUInt64 >>> FIELD_BITS) &&& FIELD_MASK).toNat

/-- The lower field (target code / target position) of a packed word. -/
@[inline] private def lowerField (word : Nat) : Nat := (word.toUInt64 &&& FIELD_MASK).toNat

/-- `word` with its upper field replaced by `value`. -/
@[inline] private def withUpperField (word value : Nat) : Nat :=
  ((word.toUInt64 &&& ~~~(FIELD_MASK <<< FIELD_BITS)) ||| (value.toUInt64 <<< FIELD_BITS)).toNat

/-- `word` with its lower field replaced by `value`. -/
@[inline] private def withLowerField (word value : Nat) : Nat :=
  ((word.toUInt64 &&& ~~~FIELD_MASK) ||| value.toUInt64).toNat

/-- The hyperedge segments of one routing run and their dependencies (see the module doc). -/
structure SegmentGraph where
  /-- Rust `edge_segments` (index = position in the list). -/
  segments : Array HyperEdgeSegment := #[]
  /-- The dependencies (index = creation order): ends (`packEnds`), positions in the source's
  outgoing and the target's incoming list (`packPositions`; each meaningful while the dependency has
  that end) and weight (`encodeWeight`). -/
  deps : DependencyTable := {}
  deriving Inhabited

namespace SegmentGraph

/-- The segment with index `i`. -/
@[inline] def segment (g : SegmentGraph) (i : Nat) : HyperEdgeSegment := g.segments[i]!

/-- Number of dependencies created so far. -/
@[inline] def dependencyCount (g : SegmentGraph) : Nat := g.deps.count

/-- Encoded source of dependency `d` (segment index `+ 1`, `0` = none). -/
@[inline] def depSourceCode (g : SegmentGraph) (d : Nat) : Nat := upperField (g.deps.endsWord d)

/-- Encoded target of dependency `d` (segment index `+ 1`, `0` = none). -/
@[inline] def depTargetCode (g : SegmentGraph) (d : Nat) : Nat := lowerField (g.deps.endsWord d)

/-- Weight of dependency `d`. -/
@[inline] def depWeight (g : SegmentGraph) (d : Nat) : Int := decodeWeight (g.deps.weightWord d)

/-- Whether dependency `d` is critical. -/
@[inline] def depIsCritical (g : SegmentGraph) (d : Nat) : Bool := (g.deps.endsWord d).toUInt64 &&& CRITICAL_FLAG != 0

/-- Recorded position of dependency `d` in its source's outgoing list. -/
@[inline] private def depSourcePos (g : SegmentGraph) (d : Nat) : Nat := upperField (g.deps.positionsWord d)

/-- Recorded position of dependency `d` in its target's incoming list. -/
@[inline] private def depTargetPos (g : SegmentGraph) (d : Nat) : Nat := lowerField (g.deps.positionsWord d)

/-- Decodes an encoded segment (`depSourceCode`/`depTargetCode`). -/
@[inline] def decodeSegment (code : Nat) : Option Nat :=
  match code with
  | 0 => none
  | i + 1 => some i

/-- The dependency with index `d`. -/
def dependency (g : SegmentGraph) (d : Nat) : HyperEdgeSegmentDependency :=
  { dependencyType := if g.depIsCritical d then .critical else .regular
    source := decodeSegment (g.depSourceCode d)
    target := decodeSegment (g.depTargetCode d)
    weight := g.depWeight d }

/-- All dependencies created so far (index = creation order). -/
def dependencies (g : SegmentGraph) : Array HyperEdgeSegmentDependency :=
  (Array.range g.dependencyCount).map g.dependency

/-- Updates segment `i` in place (a no-op for an invalid index). The update is only performed in
place when `f` is not inlined (see `HyperEdgeSegment.pushOutgoingDependency`). -/
@[inline] def modifySegment (g : SegmentGraph) (i : Nat) (f : HyperEdgeSegment → HyperEdgeSegment) : SegmentGraph :=
  { g with segments := g.segments.modifyIn i f }

/-- Appends a segment (Rust `edge_segments.push(segment)`); its index is the previous number of
segments. -/
def pushSegment (g : SegmentGraph) (s : HyperEdgeSegment) : SegmentGraph :=
  match g with
  | ⟨segments, deps⟩ => ⟨segments.push s, deps⟩

/-- Appends a segment (Rust `edge_segments.push(segment)`), returning its index. -/
def addSegment (g : SegmentGraph) (s : HyperEdgeSegment) : SegmentGraph × Nat :=
  (g.pushSegment s, g.segments.size)

/-- Size of the outgoing dependency list of segment `i` (`0` for an invalid index). -/
@[inline] private def outgoingSize (g : SegmentGraph) (i : Nat) : Nat :=
  if h : i < g.segments.size then g.segments[i].outgoingSegmentDependencies.size else 0

/-- Size of the incoming dependency list of segment `i` (`0` for an invalid index). -/
@[inline] private def incomingSize (g : SegmentGraph) (i : Nat) : Nat :=
  if h : i < g.segments.size then g.segments[i].incomingSegmentDependencies.size else 0

/-- Position of `d` in `list`, Rust `iter().position(…)`: `hint` when it holds `d` (the recorded
position), else the first occurrence; `list.size` when absent. -/
@[inline] private def positionOf (list : Array Nat) (d hint : Nat) : Nat :=
  if h : hint < list.size then
    if list[hint] == d then hint else (list.findIdx? (· == d)).getD list.size
  else (list.findIdx? (· == d)).getD list.size

/-- Position of dependency `d` in the outgoing list of segment `i` (its size when absent). -/
@[inline] private def outgoingPosition (g : SegmentGraph) (i d : Nat) : Nat :=
  if h : i < g.segments.size then positionOf g.segments[i].outgoingSegmentDependencies d (g.depSourcePos d)
  else 0

/-- Position of dependency `d` in the incoming list of segment `i` (its size when absent). -/
@[inline] private def incomingPosition (g : SegmentGraph) (i d : Nat) : Nat :=
  if h : i < g.segments.size then positionOf g.segments[i].incomingSegmentDependencies d (g.depTargetPos d)
  else 0

/-- The dependency at position `pos` of segment `i`'s outgoing list (`0` past the end). -/
@[inline] private def outgoingAt (g : SegmentGraph) (i pos : Nat) : Nat :=
  if h : i < g.segments.size then g.segments[i].outgoingSegmentDependencies.getD pos 0 else 0

/-- The dependency at position `pos` of segment `i`'s incoming list (`0` past the end). -/
@[inline] private def incomingAt (g : SegmentGraph) (i pos : Nat) : Nat :=
  if h : i < g.segments.size then g.segments[i].incomingSegmentDependencies.getD pos 0 else 0

/-- Replaces the upper field (source code) of the ends word of dependency `d`. -/
@[inline] private def setSourceField (t : DependencyTable) (d value : Nat) : DependencyTable :=
  t.setEnds d (withUpperField (t.endsWord d) value)

/-- Replaces the lower field (target code) of the ends word of dependency `d`. -/
@[inline] private def setTargetField (t : DependencyTable) (d value : Nat) : DependencyTable :=
  t.setEnds d (withLowerField (t.endsWord d) value)

/-- Replaces the upper field (source position) of the positions word of dependency `d`. -/
@[inline] private def setSourcePosField (t : DependencyTable) (d value : Nat) : DependencyTable :=
  t.setPositions d (withUpperField (t.positionsWord d) value)

/-- Replaces the lower field (target position) of the positions word of dependency `d`. -/
@[inline] private def setTargetPosField (t : DependencyTable) (d value : Nat) : DependencyTable :=
  t.setPositions d (withLowerField (t.positionsWord d) value)

/-! The mutators below destructure the graph (`match g with ⟨…⟩ => ⟨…⟩`), rebuild it once and update
the segment array through the non-inlined helpers `pushOutgoingIn` …: after reads of the graph, an
inlined (branching) `Array.modify` makes the compiler copy the fields out and allocate a new graph
cell instead of reusing the unshared one. -/

/-- `segments[i].add_outgoing_dependency(d)` (in place). -/
@[noinline] private def pushOutgoingIn (segments : Array HyperEdgeSegment) (i d : Nat) : Array HyperEdgeSegment :=
  segments.modify i (HyperEdgeSegment.pushOutgoingDependency d)

/-- `segments[i].add_incoming_dependency(d)` (in place). -/
@[noinline] private def pushIncomingIn (segments : Array HyperEdgeSegment) (i d : Nat) : Array HyperEdgeSegment :=
  segments.modify i (HyperEdgeSegment.pushIncomingDependency d)

/-- `swap_remove(pos)` on the outgoing list of `segments[i]` (in place). -/
@[noinline] private def swapRemoveOutgoingIn (segments : Array HyperEdgeSegment) (i pos : Nat) : Array HyperEdgeSegment :=
  segments.modify i (HyperEdgeSegment.swapRemoveOutgoingAt pos)

/-- `swap_remove(pos)` on the incoming list of `segments[i]` (in place). -/
@[noinline] private def swapRemoveIncomingIn (segments : Array HyperEdgeSegment) (i pos : Nat) : Array HyperEdgeSegment :=
  segments.modify i (HyperEdgeSegment.swapRemoveIncomingAt pos)

/-- Swap-removes position `pos` of segment `i`'s outgoing list; `moved` (the last element) takes
position `pos`. -/
private def swapRemoveOutgoing (g : SegmentGraph) (i pos moved : Nat) : SegmentGraph :=
  match g with
  | ⟨segments, deps⟩ => ⟨swapRemoveOutgoingIn segments i pos, setSourcePosField deps moved pos⟩

/-- Swap-removes position `pos` of segment `i`'s incoming list; `moved` (the last element) takes
position `pos`. -/
private def swapRemoveIncoming (g : SegmentGraph) (i pos moved : Nat) : SegmentGraph :=
  match g with
  | ⟨segments, deps⟩ => ⟨swapRemoveIncomingIn segments i pos, setTargetPosField deps moved pos⟩

/-- `remove_outgoing_dependency(dep)` on segment `i`: Rust `swap_remove` of the first occurrence of `d`
(no-op when absent); the dependency moved into the hole (the former last one) gets its new position.
When `d` itself was last, its own recorded position is rewritten, which is harmless: the callers detach
or re-attach `d`. -/
def removeOutgoingDependency (g : SegmentGraph) (i d : Nat) : SegmentGraph :=
  let size := g.outgoingSize i
  let pos := g.outgoingPosition i d
  if pos < size then g.swapRemoveOutgoing i pos (g.outgoingAt i (size - 1)) else g

/-- `remove_incoming_dependency(dep)` on segment `i` (see `removeOutgoingDependency`). -/
def removeIncomingDependency (g : SegmentGraph) (i d : Nat) : SegmentGraph :=
  let size := g.incomingSize i
  let pos := g.incomingPosition i d
  if pos < size then g.swapRemoveIncoming i pos (g.incomingAt i (size - 1)) else g

/-- Sets the encoded source of `d` (no lists touched). -/
private def setSourceCode (g : SegmentGraph) (d code : Nat) : SegmentGraph :=
  match g with
  | ⟨segments, deps⟩ => ⟨segments, setSourceField deps d code⟩

/-- Sets the encoded target of `d` (no lists touched). -/
private def setTargetCode (g : SegmentGraph) (d code : Nat) : SegmentGraph :=
  match g with
  | ⟨segments, deps⟩ => ⟨segments, setTargetField deps d code⟩

/-- Appends `d` to the outgoing list of segment `s` and makes `s` its source. -/
private def attachSource (g : SegmentGraph) (d s : Nat) : SegmentGraph :=
  let pos := g.outgoingSize s
  match g with
  | ⟨segments, deps⟩ => ⟨pushOutgoingIn segments s d, setSourcePosField (setSourceField deps d (s + 1)) d pos⟩

/-- Appends `d` to the incoming list of segment `t` and makes `t` its target. -/
private def attachTarget (g : SegmentGraph) (d t : Nat) : SegmentGraph :=
  let pos := g.incomingSize t
  match g with
  | ⟨segments, deps⟩ => ⟨pushIncomingIn segments t d, setTargetPosField (setTargetField deps d (t + 1)) d pos⟩

/-- `HyperEdgeSegmentDependency::new(type, weight)` followed by `set_source(source)` and
`set_target(target)`: appends the dependency to the outgoing list of `source`, then to the incoming
list of `target`. Its index is the previous `dependencyCount`. -/
def addDependency (g : SegmentGraph) (critical : Bool) (source target : Nat) (weight : Int) : SegmentGraph :=
  let d := g.dependencyCount
  -- (both sizes can be read up front: even a self dependency goes to two different lists)
  let sourcePos := g.outgoingSize source
  let targetPos := g.incomingSize target
  match g with
  | ⟨segments, deps⟩ =>
    let segments := pushOutgoingIn segments source d
    let segments := pushIncomingIn segments target d
    ⟨segments, deps.push (packEnds critical (source + 1) (target + 1)) (packPositions sourcePos targetPos)
      (encodeWeight weight)⟩

/-- `createAndAddRegular(source, target, weight)`: a regular dependency (index returned). -/
def createAndAddRegular (g : SegmentGraph) (source target : Nat) (weight : Int) : SegmentGraph × Nat :=
  (g.addDependency false source target weight, g.dependencyCount)

/-- `createAndAddCritical(source, target)`: a critical dependency of weight `CRITICAL_DEPENDENCY_WEIGHT`
(index returned). -/
def createAndAddCritical (g : SegmentGraph) (source target : Nat) : SegmentGraph × Nat :=
  (g.addDependency true source target CRITICAL_DEPENDENCY_WEIGHT, g.dependencyCount)

/-- `HyperEdgeSegmentDependency.remove()`: detaches the dependency from both segments. -/
def removeDependency (g : SegmentGraph) (d : Nat) : SegmentGraph :=
  let sourceCode := g.depSourceCode d
  let targetCode := g.depTargetCode d
  let g := if sourceCode != 0 then g.removeOutgoingDependency (sourceCode - 1) d else g
  let g := if targetCode != 0 then g.removeIncomingDependency (targetCode - 1) d else g
  (g.setSourceCode d 0).setTargetCode d 0

/-- `HyperEdgeSegmentDependency.reverse()`: swaps source and target (removed from the old lists,
appended to the new ones: first the old target's outgoing, then the old source's incoming list). -/
def reverseDependency (g : SegmentGraph) (d : Nat) : SegmentGraph :=
  let sourceCode := g.depSourceCode d
  let targetCode := g.depTargetCode d
  let g := if sourceCode != 0 then g.removeOutgoingDependency (sourceCode - 1) d else g
  let g := if targetCode != 0 then g.removeIncomingDependency (targetCode - 1) d else g
  let g := (g.setSourceCode d targetCode).setTargetCode d sourceCode
  let g := if targetCode != 0 then g.attachSource d (targetCode - 1) else g
  if sourceCode != 0 then g.attachTarget d (sourceCode - 1) else g

/-- `HyperEdgeSegment.splitAt(splitPosition)` (Rust `HyperEdgeSegment::split_at`): segment `i` keeps its
incoming coordinates and gets the single outgoing coordinate `splitPosition`; the new split partner
(appended to the arena, index returned) gets `splitPosition` as incoming and the old outgoing
coordinates. All dependencies of segment `i` are removed (incoming first, then outgoing, in list
order of the copies taken before the removal). -/
def splitAt (g : SegmentGraph) (i : Nat) (splitPosition : Float) : SegmentGraph × Nat :=
  let seg := g.segment i
  let partnerIdx := g.segments.size
  let partner : HyperEdgeSegment :=
    { routingDirection := seg.routingDirection
      splitPartner := some i
      outgoingConnectionCoordinates := seg.outgoingConnectionCoordinates
      incomingConnectionCoordinates := #[splitPosition] }
  let incomingDeps := seg.incomingSegmentDependencies
  let outgoingDeps := seg.outgoingSegmentDependencies
  let g := { g with segments := g.segments.push partner.recomputeExtent }
  let g := g.modifySegment i fun s =>
    ({ s with splitPartner := some partnerIdx, outgoingConnectionCoordinates := #[splitPosition] } : HyperEdgeSegment).recomputeExtent
  let g := incomingDeps.foldl (fun g d => g.removeDependency d) g
  let g := outgoingDeps.foldl (fun g d => g.removeDependency d) g
  (g, partnerIdx)

end SegmentGraph

end Elk.Alg.Layered.P5Edges.Orthogonal
