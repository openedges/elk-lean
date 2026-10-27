import Elk.Alg.Layered.Graph
/-!
# `org.eclipse.elk.alg.layered.p3order.counting.CrossMinUtil`

elk-rs `cross_min_util.rs`, plus allocation-free helpers of the crossing minimisation hot loops
(no Java/Rust counterpart): a branch-free `PortSide` comparison (the derived `BEq` is an
out-of-line call) and `getPortSideView(side)` as an index range of the port list instead of a copy.
-/
namespace Elk.Alg.Layered.P3Order.Counting

open Elk.Core.Options Elk.Alg.Layered.Graph

/-- The constructor index of a `PortSide` (`ElkEnum.ordinal` as `UInt8`). -/
@[inline] def sideCode : PortSide → UInt8
  | .undefined => 0
  | .north => 1
  | .east => 2
  | .south => 3
  | .west => 4

/-- `a == b` on `PortSide`s without the out-of-line derived `BEq`. -/
@[inline] def sideIs (a b : PortSide) : Bool := sideCode a == sideCode b

/-- `getPortSideView(side)` of a node as a view of its port list: with `cached` the ports
`ports[lo:hi]`, otherwise the ports whose side is `side` (`LGraphArena.nodePortSideView`'s filter
fallback). -/
structure SideView where
  lo : Nat
  hi : Nat
  cached : Bool

/-- Whether all ports `ports[i:hi]` lie on `side`. -/
partial def allOnSide (a : LGraphArena) (ports : Array LPortId) (i hi : Nat) (side : PortSide) : Bool :=
  if h : i < hi ∧ i < ports.size then
    if sideIs (a.port ports[i]).side side then allOnSide a ports (i + 1) hi side else false
  else true

/-- The `SideView` of `getPortSideView(side)` of `nd` (exactly `LGraphArena.nodePortSideView`: the cached
`[first, last)` range clamped like `Array.extract` when all its ports lie on `side`, else the filter). -/
@[inline] def sideView (a : LGraphArena) (n : LNodeId) (nd : LNode) (side : PortSide) : SideView :=
  if !nd.portSidesCached then ⟨0, 0, false⟩
  else
    let indices := match nd.portSideIndices with
      | some idx => idx
      | none => a.findPortIndices n
    match indices[ElkEnum.ordinal side]? with
    | some (some (first, last)) =>
      let hi := Nat.min last nd.ports.size
      if first >= hi then ⟨0, 0, true⟩
      else if allOnSide a nd.ports first hi side then ⟨first, hi, true⟩
      else ⟨0, 0, false⟩
    | _ => ⟨0, 0, false⟩

/-- Pushes `ports[i:hi]` (ascending) onto `out`. -/
partial def pushRange (ports : Array LPortId) (i hi : Nat) (out : Array LPortId) : Array LPortId :=
  if h : i < hi ∧ i < ports.size then pushRange ports (i + 1) hi (out.push ports[i]) else out

/-- Pushes `ports[lo:i]` (descending from `i - 1`) onto `out`. -/
partial def pushRangeRev (ports : Array LPortId) (lo i : Nat) (out : Array LPortId) : Array LPortId :=
  if lo < i then
    match ports[i - 1]? with
    | some p => pushRangeRev ports lo (i - 1) (out.push p)
    | none => pushRangeRev ports lo (i - 1) out
  else out

/-- Pushes the ports of `ports` on `side` (ascending) onto `out`. -/
partial def pushOnSide (a : LGraphArena) (ports : Array LPortId) (side : PortSide) (i : Nat) (out : Array LPortId) :
    Array LPortId :=
  if h : i < ports.size then
    let p := ports[i]
    pushOnSide a ports side (i + 1) (if sideIs (a.port p).side side then out.push p else out)
  else out

/-- Pushes the ports of `ports[0:i]` on `side` (descending) onto `out`. -/
partial def pushOnSideRev (a : LGraphArena) (ports : Array LPortId) (side : PortSide) (i : Nat) (out : Array LPortId) :
    Array LPortId :=
  if i > 0 then
    match ports[i - 1]? with
    | some p => pushOnSideRev a ports side (i - 1) (if sideIs (a.port p).side side then out.push p else out)
    | none => pushOnSideRev a ports side (i - 1) out
  else out

/-- Appends `getPortSideView(side)` of `node` (reversed with `rev`) to `out` without copying the view. -/
def appendSideView (a : LGraphArena) (node : LNodeId) (side : PortSide) (rev : Bool) (out : Array LPortId) :
    Array LPortId :=
  let nd := a.node node
  let v := sideView a node nd side
  if v.cached then
    if rev then pushRangeRev nd.ports v.lo v.hi out else pushRange nd.ports v.lo v.hi out
  else
    if rev then pushOnSideRev a nd.ports side nd.ports.size out else pushOnSide a nd.ports side 0 out

namespace CrossMinUtil

/-- `inNorthSouthEastWestOrder(node, side)`: the node's ports on `side` (`getPortSideView`)
ordered north→south on the east/west sides and west→east on the north/south sides, i.e.
`EAST`/`NORTH` as stored, `SOUTH`/`WEST` reversed; `UNDEFINED` yields no ports. -/
def inNorthSouthEastWestOrder (a : LGraphArena) (node : LNodeId) (side : PortSide) : Array LPortId :=
  match side with
  | .east | .north => a.nodePortSideView node side
  | .south | .west => (a.nodePortSideView node side).reverse
  | .undefined => #[]

end CrossMinUtil

end Elk.Alg.Layered.P3Order.Counting
