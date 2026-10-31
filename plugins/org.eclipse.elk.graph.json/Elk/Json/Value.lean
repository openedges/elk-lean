import Elk.Core.Util.Java
import Elk.Graph.ArrayModify
/-!
# JSON value model (`Elk.Json.Value`)

elk-lean's own JSON type. Objects keep insertion order (like JavaScript
objects and elkjs), numbers remember whether they were written as integers or
decimals (like `serde_json::Number` in elk-rs), so a graph can be read, laid
out and written back with the exact structure the reference implementations
produce.
-/
namespace Elk.Json

open Elk.Core.Util

/-! Appending number renderings to the output string (C shim `elk_core_ffi.c`; declared here so that
only the JSON modules depend on them). -/

/-- `""` with room for `cap` bytes, so that a printer appending to it does not reallocate (and copy)
the growing output. -/
@[extern "elk_string_with_capacity"]
opaque stringWithCapacity (cap : USize) : String

/-- `out ++ (if x.isFinite then Float.toJsonNumber x else "null")`, appended in place when `out` is
unshared and has the capacity (no temporary string; JSON printer). -/
@[extern "elk_string_append_json_float"]
opaque appendJsonFloat (out : String) (x : Float) : String

/-- `out ++` the JSON rendering of the layout number `x` (`Number.ofFloatElk x |>.render`): exactly
integral finite values other than `-0.0` below `2^63` in magnitude as integers, other finite values
as `Float.toJsonNumber`, non-finite ones as `null`; appended like `appendJsonFloat`. -/
@[extern "elk_string_append_elk_number"]
opaque appendElkNumber (out : String) (x : Float) : String

/-- `out ++ pre ++` the JSON rendering of the layout number `x` (`appendElkNumber`), in one call. -/
@[extern "elk_string_append_pre_elk_number"]
opaque appendPreElkNumber (out : String) (pre : @& String) (x : Float) : String

/-- `out ++ pre ++ "{\"x\":" ++ X ++ ",\"y\":" ++ Y ++ "}"` with the layout numbers `X`, `Y` of `x`, `y`
(`appendElkNumber`): a point object of the layout transfer, in one call. -/
@[extern "elk_string_append_point"]
opaque appendPoint (out : String) (pre : @& String) (x y : Float) : String

/-- `out ++ a ++ b ++ c` in one call (the capacity is ensured once). -/
@[extern "elk_string_append3"]
opaque append3 (out : String) (a b c : @& String) : String

/-- JSON number: integer lexemes stay `Int`, everything else is a double. -/
inductive Number where
  | int (i : Int)
  | float (f : Float)
  deriving Inhabited, BEq

namespace Number

/-- Numeric value as a double. -/
def toFloat : Number → Float
  | .int i => Float.ofInt i
  | .float f => f

/-- Integer value if the number is integral (elk-rs `as_i64`, with a
finite-and-whole check for doubles). -/
def toInt? : Number → Option Int
  | .int i => some i
  | .float f => if f.isFinite && f == f.floor then some f.toIntTrunc else none

/-- `2^63` as an exact bit pattern (a literal such as `9223372036854775808.0` has a mantissa above
`2^53` and would take the slow `Float.ofScientific` path whenever the compiler does not hoist it,
see `Elk.Core.Util.FastFloat`). -/
private def TWO_POW_63 : Float := Float.ofBits 0x43E0000000000000

/-- A layout result as a JSON number, value-preserving like ELK Java (whose Gson output prints the
double itself): exactly integral values within the `i64` range become integers (rendered without
`.0`); `-0.0` and every other value stay floats. Non-finite values stay floats and render as `null`
(elkjs' `JSON.stringify`; Java's lenient Gson would print `NaN`/`Infinity`). elk-rs instead snaps
values within `1e-6` of an integer and writes non-finite values as `0` — not followed, because
the result reference is ELK Java. -/
def ofFloatElk (x : Float) : Number :=
  if x.isFinite && x == x.round && x.toBits != 0x8000000000000000 && x.abs < TWO_POW_63 then
    .int x.toInt64.toInt
  else .float x

/-- Rust `Display` of the underlying value (elk-rs `number_to_string`). -/
def toRustString : Number → String
  | .int i => toString i
  | .float f => Float.toRustDisplay f

/-- serde_json 1.0.149 rendering (the oracle's): integers as decimals, doubles via the zmij
shortest round-trip form (`12.0`, `0.1`, `1e+21`, `3e-6`); non-finite values render as `null`
(serde_json refuses them; elk-rs converts them to `0` beforehand). -/
def render : Number → String
  | .int i => toString i
  | .float f => if f.isFinite then Float.toJsonNumber f else "null"

end Number

/-- JSON value with insertion-ordered objects. -/
inductive Value where
  | null
  | bool (b : Bool)
  | num (n : Number)
  | str (s : String)
  | arr (xs : Array Value)
  | obj (kvs : Array (String × Value))
  deriving Inhabited

/-! Member names of ELK JSON graphs as shared constants. The parser returns these very objects
for equal keys (`Parser.internSlice`), and the importer looks members up with them, so most key
comparisons succeed on pointer equality (`lean_string_eq` tests it first). -/
namespace Key

/-- `"id"`. -/
@[noinline] def id : String := "id"
/-- `"x"`. -/
@[noinline] def x : String := "x"
/-- `"y"`. -/
@[noinline] def y : String := "y"
/-- `"width"`. -/
@[noinline] def width : String := "width"
/-- `"height"`. -/
@[noinline] def height : String := "height"
/-- `"labels"`. -/
@[noinline] def labels : String := "labels"
/-- `"text"`. -/
@[noinline] def text : String := "text"
/-- `"ports"`. -/
@[noinline] def ports : String := "ports"
/-- `"layoutOptions"`. -/
@[noinline] def layoutOptions : String := "layoutOptions"
/-- `"properties"`. -/
@[noinline] def properties : String := "properties"
/-- `"children"`. -/
@[noinline] def children : String := "children"
/-- `"edges"`. -/
@[noinline] def edges : String := "edges"
/-- `"sources"`. -/
@[noinline] def sources : String := "sources"
/-- `"targets"`. -/
@[noinline] def targets : String := "targets"
/-- `"source"`. -/
@[noinline] def source : String := "source"
/-- `"target"`. -/
@[noinline] def target : String := "target"
/-- `"sourcePort"`. -/
@[noinline] def sourcePort : String := "sourcePort"
/-- `"targetPort"`. -/
@[noinline] def targetPort : String := "targetPort"
/-- `"sections"`. -/
@[noinline] def sections : String := "sections"
/-- `"startPoint"`. -/
@[noinline] def startPoint : String := "startPoint"
/-- `"endPoint"`. -/
@[noinline] def endPoint : String := "endPoint"
/-- `"bendPoints"`. -/
@[noinline] def bendPoints : String := "bendPoints"
/-- `"incomingShape"`. -/
@[noinline] def incomingShape : String := "incomingShape"
/-- `"outgoingShape"`. -/
@[noinline] def outgoingShape : String := "outgoingShape"
/-- `"incomingSections"`. -/
@[noinline] def incomingSections : String := "incomingSections"
/-- `"outgoingSections"`. -/
@[noinline] def outgoingSections : String := "outgoingSections"
/-- `"junctionPoints"`. -/
@[noinline] def junctionPoints : String := "junctionPoints"
/-- `"container"`. -/
@[noinline] def container : String := "container"
/-- `"individualSpacings"`. -/
@[noinline] def individualSpacings : String := "individualSpacings"

/-- The member names above (the very same string objects), indexed by `candidateIndex`. -/
def all : Array String :=
  #[id, x, y, width, height, labels, text, ports, layoutOptions, properties, children, edges, sources,
    targets, source, target, sourcePort, targetPort, sections, startPoint, endPoint, bendPoints,
    incomingShape, outgoingShape, incomingSections, outgoingSections, junctionPoints, container,
    individualSpacings]

/-- Byte `i` of `s` (`0` past the end). -/
@[inline] private def byteAt (s : String) (i : Nat) : UInt8 :=
  if h : i < s.utf8ByteSize then s.getUTF8Byte ⟨i⟩ h else 0

/-- Index in `all` of the only member name that the `n` bytes of `s` from `b` can be, chosen by the
length and the first (or second) byte; `all.size` when there is none. The bytes still have to be
compared. -/
def candidateIndex (s : String) (b n : Nat) : Nat :=
  let c := byteAt s b
  match n with
  | 1 => if c == 120 then 1 else if c == 121 then 2 else 29
  | 2 => 0
  | 4 => 6
  | 5 => if c == 119 then 3 else if c == 112 then 7 else if c == 101 then 11 else 29
  | 6 => if c == 104 then 4 else if c == 108 then 5 else if c == 115 then 14 else if c == 116 then 15 else 29
  | 7 => if c == 115 then 12 else if c == 116 then 13 else 29
  | 8 => if c == 99 then 10 else if c == 115 then 18 else if c == 101 then 20 else 29
  | 9 => 27
  | 10 =>
    if c == 112 then 9 else if c == 116 then 17 else if c == 98 then 21
    else if c == 115 then (if byteAt s (b + 1) == 111 then 16 else 19)
    else 29
  | 13 => if c == 108 then 8 else if c == 105 then 22 else if c == 111 then 23 else 29
  | 14 => 26
  | 16 => if c == 105 then 24 else if c == 111 then 25 else 29
  | 18 => 28
  | _ => 29

end Key

/-! Unchecked byte reads with `USize` indices for the byte loops of the parser and printer (no
`Nat` arithmetic per byte, see `PLAN.md` 7.1 item 15). -/
namespace Utf8

/-- The `USize` byte size of `s` (truncated modulo the word size, which no string reaches). -/
@[inline] def usize (s : String) : USize := s.utf8ByteSize.toUSize

theorem lt_size_of_lt_usize (s : String) (i : USize) (h : i < usize s) : i.toNat < s.utf8ByteSize := by
  have h1 : i.toNat < (usize s).toNat := h
  have h2 : (usize s).toNat ≤ s.utf8ByteSize := by
    simp [usize, Nat.toUSize]
    exact Nat.mod_le _ _
  omega

/-- Byte `i` of `s` (`lean_string_uget_byte_fast`). -/
@[inline] def uget (s : String) (i : USize) (h : i < usize s) : UInt8 :=
  String.Internal.ugetUTF8Byte s i (lt_size_of_lt_usize s i h)

end Utf8

/-- Path segment for `Value.getAt`/`modifyAt`. -/
inductive Seg where
  | key (k : String)
  | idx (i : Nat)
  deriving Inhabited, BEq, Repr

namespace Value

@[inline] def ofInt (i : Int) : Value := .num (.int i)
@[inline] def ofNat (n : Nat) : Value := .num (.int n)
@[inline] def ofFloat (f : Float) : Value := .num (.float f)
/-- Layout coordinate: integral-looking doubles become integers (elk-rs behaviour). -/
@[inline] def ofFloatElk (f : Float) : Value := .num (Number.ofFloatElk f)
@[inline] def ofString (s : String) : Value := .str s
@[inline] def emptyObj : Value := .obj #[]
@[inline] def emptyArr : Value := .arr #[]

def isNull : Value → Bool
  | .null => true
  | _ => false

def isObj : Value → Bool
  | .obj _ => true
  | _ => false

def isArr : Value → Bool
  | .arr _ => true
  | _ => false

def getObj? : Value → Option (Array (String × Value))
  | .obj kvs => some kvs
  | _ => none

def getArr? : Value → Option (Array Value)
  | .arr xs => some xs
  | _ => none

def getStr? : Value → Option String
  | .str s => some s
  | _ => none

def getBool? : Value → Option Bool
  | .bool b => some b
  | _ => none

def getNum? : Value → Option Number
  | .num n => some n
  | _ => none

/-- Numeric value as a double. -/
def getFloat? : Value → Option Float
  | .num n => some n.toFloat
  | _ => none

def getInt? : Value → Option Int
  | .num n => n.toInt?
  | _ => none

/-- Index of the first member named `key` from `i` on (`kvs.size` if absent). A plain loop:
`Array.find?`/`findIdx?` go through `forIn` and allocate their loop state on a hit. -/
def keyIndex (kvs : Array (String × Value)) (key : String) (i : Nat := 0) : Nat :=
  if h : i < kvs.size then
    if kvs[i].1 == key then i else keyIndex kvs key (i + 1)
  else kvs.size
termination_by kvs.size - i

/-- Member lookup on an object's entry array (first matching key). -/
def lookup (kvs : Array (String × Value)) (key : String) : Option Value :=
  let i := keyIndex kvs key
  if h : i < kvs.size then some kvs[i].2 else none

/-- Object member lookup (first matching key). -/
def get? (v : Value) (key : String) : Option Value :=
  match v with
  | .obj kvs => lookup kvs key
  | _ => none

def hasKey (v : Value) (key : String) : Bool :=
  match v with
  | .obj kvs => keyIndex kvs key < kvs.size
  | _ => false

/-- `obj[key] = x` on an entry array: replaces the first member named `key` in place or appends. -/
@[inline] def setEntry (kvs : Array (String × Value)) (key : String) (x : Value) : Array (String × Value) :=
  let i := keyIndex kvs key
  if i < kvs.size then kvs.modifyIn i (fun kv => (kv.1, x)) else kvs.push (key, x)

/-- `obj[key] = x`: replaces an existing member in place or appends. Non-objects are unchanged. -/
def set (v : Value) (key : String) (x : Value) : Value :=
  match v with
  | .obj kvs => .obj (setEntry kvs key x)
  | other => other

/-- Removes a member (no-op if absent). -/
def remove (v : Value) (key : String) : Value :=
  match v with
  | .obj kvs =>
    let i := keyIndex kvs key
    if i < kvs.size then .obj (kvs.eraseIdx! i) else v
  | other => other

/-- Applies `f` to a member, inserting `f default` when the member is absent. -/
def modifyKey (v : Value) (key : String) (default : Value) (f : Value → Value) : Value :=
  match v with
  | .obj kvs =>
    let i := keyIndex kvs key
    if i < kvs.size then .obj (kvs.modifyIn i fun kv => (kv.1, f kv.2))
    else .obj (kvs.push (key, f default))
  | other => other

/-- Value at a path, if present. -/
def getAt (v : Value) : List Seg → Option Value
  | [] => some v
  | .key k :: rest => (v.get? k).bind (·.getAt rest)
  | .idx i :: rest => match v with
    | .arr xs => (xs[i]?).bind (·.getAt rest)
    | _ => none

/-- Modifies the value at a path (no-op if the path does not exist). -/
partial def modifyAt (v : Value) (path : List Seg) (f : Value → Value) : Value :=
  match path with
  | [] => f v
  | .key k :: rest =>
    match v with
    | .obj kvs =>
      let i := keyIndex kvs k
      if i < kvs.size then .obj (kvs.modifyIn i fun kv => (kv.1, kv.2.modifyAt rest f)) else v
    | other => other
  | .idx i :: rest =>
    match v with
    | .arr xs => if i < xs.size then .arr (xs.modifyIn i (·.modifyAt rest f)) else v
    | other => other

/-- `getAt` on the segments `path[i:]` (no list conversion). -/
partial def getAtFrom (v : Value) (path : Array Seg) (i : Nat) : Option Value :=
  if h : i < path.size then
    match path[i] with
    | .key k =>
      match v with
      | .obj kvs =>
        let j := keyIndex kvs k
        if hj : j < kvs.size then kvs[j].2.getAtFrom path (i + 1) else none
      | _ => none
    | .idx j =>
      match v with
      | .arr xs => if hj : j < xs.size then xs[j].getAtFrom path (i + 1) else none
      | _ => none
  else some v

/-- `modifyAt` on the segments `path[i:]` (no list conversion). -/
partial def modifyAtFrom (v : Value) (path : Array Seg) (i : Nat) (f : Value → Value) : Value :=
  if h : i < path.size then
    match path[i] with
    | .key k =>
      match v with
      | .obj kvs =>
        let j := keyIndex kvs k
        if j < kvs.size then .obj (kvs.modifyIn j fun kv => (kv.1, kv.2.modifyAtFrom path (i + 1) f)) else v
      | other => other
    | .idx j =>
      match v with
      | .arr xs => if j < xs.size then .arr (xs.modifyIn j (·.modifyAtFrom path (i + 1) f)) else v
      | other => other
  else f v

/-- `x`, `y`, `width`, `height` of the object at the path `path[i:]` set to the given values (in this
order, like four `set` calls: existing members are replaced in place, missing ones appended). The
dedicated traversal of `transferXywh` (no update closure). -/
partial def setXywhAtFrom (v : Value) (path : Array Seg) (i : Nat) (x y w h : Value) : Value :=
  if hp : i < path.size then
    match path[i] with
    | .key k =>
      match v with
      | .obj kvs =>
        let j := keyIndex kvs k
        if j < kvs.size then .obj (kvs.modifyIn j fun kv => (kv.1, kv.2.setXywhAtFrom path (i + 1) x y w h)) else v
      | other => other
    | .idx j =>
      match v with
      | .arr xs => if j < xs.size then .arr (xs.modifyIn j (·.setXywhAtFrom path (i + 1) x y w h)) else v
      | other => other
  else
    match v with
    | .obj kvs =>
      .obj (setEntry (setEntry (setEntry (setEntry kvs Key.x x) Key.y y) Key.width w) Key.height h)
    | other => other

/-- Structural equality (objects compare in order). -/
partial def beq : Value → Value → Bool
  | .null, .null => true
  | .bool a, .bool b => a == b
  | .num a, .num b => a == b
  | .str a, .str b => a == b
  | .arr a, .arr b => a.size == b.size && (a.zip b).all fun (x, y) => beq x y
  | .obj a, .obj b => a.size == b.size && (a.zip b).all fun (x, y) => x.1 == y.1 && beq x.2 y.2
  | _, _ => false

instance : BEq Value := ⟨beq⟩

end Value

end Elk.Json
