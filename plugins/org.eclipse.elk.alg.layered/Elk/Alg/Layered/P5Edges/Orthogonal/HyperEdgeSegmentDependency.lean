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
dependency in three columns, so creating one allocates nothing and a dependency costs 24 bytes plus
its two list entries (the six one-field columns before cost 48): the *ends* word packs the encoded
source and target (segment index `+ 1`, `0` = none), the *positions* word the dependency's
positions in its source's outgoing and its target's incoming list (which turn the Rust `position`
scan of `swap_remove` into a constant-time lookup; the list contents and order are those of the
scan: a dependency occurs at most once in a list), and the *weight* word the weight (zigzag-coded
`Int`) with the `CRITICAL` flag. Every packed word stays below `2^63`, i.e. an unboxed scalar `Nat`:
segment codes and list positions have 31 bits, which no graph reaches (`2^31` segments or
dependencies would need far more memory than the arrays allow). Beyond its first `2^20 - 2` entries
the table is chunked, so it holds no doubling slack and is never copied while it grows (the
dependency count is quadratic in the segments of one routing run: a node with 5,000 ports gives about
12.5 million). `dependency d` assembles the `HyperEdgeSegmentDependency` value on demand. The previous
six-column representation is kept as the oracle of a differential test (`Tests.Layered.SegmentGraphRef`).

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

/-- Words in the head array of a column: `2^20 - 2`, a capacity that the doubling growth of
`Array.push` (`(capacity + 1) * 2` from `0`) reaches exactly, so a full head has no unused slack.
Reading a chunk costs more than reading the flat head (measured: a 2,000-port node about 1.15x in a
warm process); below a million dependencies per routing run (ports of about 1,400 segments) nothing
is chunked. -/
private def COLUMN_HEAD : Nat := 1048574
/-- Words per chunk after the head (`2^COLUMN_CHUNK_BITS`). -/
private def COLUMN_CHUNK : Nat := 65536
/-- `log2 COLUMN_CHUNK`. -/
private def COLUMN_CHUNK_BITS : Nat := 16
/-- `COLUMN_CHUNK - 1`. -/
private def COLUMN_CHUNK_MASK : Nat := 65535

/-! A column of the `DependencyTable` (one of its three words per dependency) is a pair `head`/`rest`:
the first `COLUMN_HEAD` words in one flat array (read with one bounds check like a plain `Array`),
the rest in chunks of `COLUMN_CHUNK` words. Unlike one `Array`, whose doubling leaves up to half of
the capacity unused and holds the old and the new buffer while it grows, a full chunk is never
copied; the head grows by doubling, so small routing runs allocate little. Reads past the end give
`0` and writes past the end do nothing, like `Array.get!`/`set!`. The pairs are fields of the table
itself (not a nested structure): every read then has one indirection less and every update rebuilds
one object. -/

/-- Word `d` of the column `head`/`rest` (`0` past the end). -/
@[inline] private def columnGet (head : Array Nat) (rest : Array (Array Nat)) (d : Nat) : Nat :=
  if d < COLUMN_HEAD then head[d]!
  else
    let e := d - COLUMN_HEAD
    let ci := e >>> COLUMN_CHUNK_BITS
    if h : ci < rest.size then rest[ci][e &&& COLUMN_CHUNK_MASK]! else 0

/-! The chunk updates are `@[noinline]` and applied with `Array.modify`, which clears the slot with a
scalar dummy: `Array.modifyIn` clears it with `default`, which for an `Array` allocates a fresh empty
array on every update. -/

/-- `chunk.set! off v` (see above). -/
@[noinline] private def chunkSet (off v : Nat) (chunk : Array Nat) : Array Nat := chunk.set! off v

/-- `chunk.push v` (see above). -/
@[noinline] private def chunkPush (v : Nat) (chunk : Array Nat) : Array Nat := chunk.push v

/-- `rest` with word `d` (`≥ COLUMN_HEAD`) replaced (no-op past the end). -/
@[inline] private def restSet (rest : Array (Array Nat)) (d v : Nat) : Array (Array Nat) :=
  let e := d - COLUMN_HEAD
  rest.modify (e >>> COLUMN_CHUNK_BITS) (chunkSet (e &&& COLUMN_CHUNK_MASK) v)

/-- `rest` with word number `count` (`≥ COLUMN_HEAD`) appended. -/
@[inline] private def restPush (rest : Array (Array Nat)) (count v : Nat) : Array (Array Nat) :=
  if (count - COLUMN_HEAD) &&& COLUMN_CHUNK_MASK == 0 then rest.push ((Array.emptyWithCapacity COLUMN_CHUNK).push v)
  else rest.modify (rest.size - 1) (chunkPush v)

/-- The dependency records of a `SegmentGraph` (ORM; no Java/Rust counterpart): three columns of
scalar words (ends, positions, weight; see the module doc), each a `head`/`rest` pair (see above).
The columns stay separate because most loops read one word of consecutive dependencies. -/
structure DependencyTable where
  /-- Ends words `0 … COLUMN_HEAD - 1`. -/
  endsHead : Array Nat := #[]
  /-- Further ends words, in chunks (all but the last hold exactly `COLUMN_CHUNK` words). -/
  endsRest : Array (Array Nat) := #[]
  /-- Positions words, like `endsHead`. -/
  positionsHead : Array Nat := #[]
  /-- Further positions words, like `endsRest`. -/
  positionsRest : Array (Array Nat) := #[]
  /-- Weight words, like `endsHead`. -/
  weightsHead : Array Nat := #[]
  /-- Further weight words, like `endsRest`. -/
  weightsRest : Array (Array Nat) := #[]
  /-- Number of dependencies. -/
  count : Nat := 0
  deriving Inhabited

namespace DependencyTable

/-- Ends word of dependency `d`. -/
@[inline] def endsWord (t : DependencyTable) (d : Nat) : Nat := columnGet t.endsHead t.endsRest d

/-- Positions word of dependency `d`. -/
@[inline] def positionsWord (t : DependencyTable) (d : Nat) : Nat := columnGet t.positionsHead t.positionsRest d

/-- Weight word of dependency `d`. -/
@[inline] def weightWord (t : DependencyTable) (d : Nat) : Nat := columnGet t.weightsHead t.weightsRest d

/-! The updates branch on head versus rest *outside* the constructor matches: a branch between the
match and the new constructor makes the compiler free the table and allocate a new one on every
update instead of reusing it (PLAN §7.1 item 13). -/

/-- `setEnds` for `d < COLUMN_HEAD`. -/
@[noinline] private def setEndsHead (t : DependencyTable) (d v : Nat) : DependencyTable :=
  match t with
  | ⟨eh, er, ph, pr, wh, wr, count⟩ => ⟨eh.set! d v, er, ph, pr, wh, wr, count⟩

/-- `setEnds` for `d ≥ COLUMN_HEAD`. -/
@[noinline] private def setEndsRest (t : DependencyTable) (d v : Nat) : DependencyTable :=
  match t with
  | ⟨eh, er, ph, pr, wh, wr, count⟩ => ⟨eh, restSet er d v, ph, pr, wh, wr, count⟩

/-- Replaces the ends word of dependency `d`. -/
@[inline] def setEnds (t : DependencyTable) (d v : Nat) : DependencyTable :=
  if d < COLUMN_HEAD then setEndsHead t d v else setEndsRest t d v

/-- `setPositions` for `d < COLUMN_HEAD`. -/
@[noinline] private def setPositionsHead (t : DependencyTable) (d v : Nat) : DependencyTable :=
  match t with
  | ⟨eh, er, ph, pr, wh, wr, count⟩ => ⟨eh, er, ph.set! d v, pr, wh, wr, count⟩

/-- `setPositions` for `d ≥ COLUMN_HEAD`. -/
@[noinline] private def setPositionsRest (t : DependencyTable) (d v : Nat) : DependencyTable :=
  match t with
  | ⟨eh, er, ph, pr, wh, wr, count⟩ => ⟨eh, er, ph, restSet pr d v, wh, wr, count⟩

/-- Replaces the positions word of dependency `d`. -/
@[inline] def setPositions (t : DependencyTable) (d v : Nat) : DependencyTable :=
  if d < COLUMN_HEAD then setPositionsHead t d v else setPositionsRest t d v

/-- `push` while the heads are not full. -/
@[noinline] private def pushHead (t : DependencyTable) (endsWord positionsWord weightWord : Nat) : DependencyTable :=
  match t with
  | ⟨eh, er, ph, pr, wh, wr, count⟩ =>
    ⟨eh.push endsWord, er, ph.push positionsWord, pr, wh.push weightWord, wr, count + 1⟩

/-- `push` once the heads are full. -/
@[noinline] private def pushRest (t : DependencyTable) (endsWord positionsWord weightWord : Nat) : DependencyTable :=
  match t with
  | ⟨eh, er, ph, pr, wh, wr, count⟩ =>
    ⟨eh, restPush er count endsWord, ph, restPush pr count positionsWord, wh, restPush wr count weightWord, count + 1⟩

/-- Appends a dependency. -/
@[inline] def push (t : DependencyTable) (endsWord positionsWord weightWord : Nat) : DependencyTable :=
  if t.count < COLUMN_HEAD then pushHead t endsWord positionsWord weightWord
  else pushRest t endsWord positionsWord weightWord

end DependencyTable

/-- Weight word of a dependency: the `CRITICAL` flag in bit 0 and above it the zigzag code of the
weight (`2w` for `w ≥ 0`, `-2w - 1` below). The flag lives here, not in the ends word, because the
cycle detector's weight sums read flag and weight together. -/
@[inline] private def packWeight (critical : Bool) (w : Int) : Nat :=
  let zigzag := match w with
    | .ofNat n => 2 * n
    | .negSucc n => 2 * n + 1
  2 * zigzag + (if critical then 1 else 0)

/-- The weight of a weight word. -/
@[inline] private def weightOfWord (word : Nat) : Int :=
  let zigzag := word >>> 1
  if zigzag &&& 1 == 0 then .ofNat (zigzag >>> 1) else .negSucc (zigzag >>> 1)

/-- Width of a packed segment code or list position (see the module doc). -/
private def FIELD_BITS : UInt64 := 31
/-- Mask of a packed segment code or list position. -/
private def FIELD_MASK : UInt64 := 0x7FFFFFFF
/-- Ends word of a dependency: the encoded source in bits `31…61` and the encoded target in bits
`0…30`. -/
@[inline] private def packEnds (sourceCode targetCode : Nat) : Nat :=
  ((sourceCode.toUInt64 <<< FIELD_BITS) ||| targetCode.toUInt64).toNat

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
  that end) and weight with the critical flag (`packWeight`). -/
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
@[inline] def depWeight (g : SegmentGraph) (d : Nat) : Int := weightOfWord (g.deps.weightWord d)

/-- Whether dependency `d` is critical. -/
@[inline] def depIsCritical (g : SegmentGraph) (d : Nat) : Bool := g.deps.weightWord d &&& 1 != 0

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

/-! The table updates below are `@[noinline]`: the graph mutators destructure the `SegmentGraph` and
pass the table on; inlined, the compiler takes its own reference to the table before it checks the
graph for reuse, so the table, the column and the chunk all look shared and are copied (PLAN §7.1
items 13, 26). -/

/-- Replaces the upper field (source code) of the ends word of dependency `d`. -/
@[noinline] private def setSourceField (t : DependencyTable) (d value : Nat) : DependencyTable :=
  t.setEnds d (withUpperField (t.endsWord d) value)

/-- Replaces the lower field (target code) of the ends word of dependency `d`. -/
@[noinline] private def setTargetField (t : DependencyTable) (d value : Nat) : DependencyTable :=
  t.setEnds d (withLowerField (t.endsWord d) value)

/-- Replaces the upper field (source position) of the positions word of dependency `d`. -/
@[noinline] private def setSourcePosField (t : DependencyTable) (d value : Nat) : DependencyTable :=
  t.setPositions d (withUpperField (t.positionsWord d) value)

/-- Replaces the lower field (target position) of the positions word of dependency `d`. -/
@[noinline] private def setTargetPosField (t : DependencyTable) (d value : Nat) : DependencyTable :=
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
    ⟨segments, deps.push (packEnds (source + 1) (target + 1)) (packPositions sourcePos targetPos)
      (packWeight critical weight)⟩

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
