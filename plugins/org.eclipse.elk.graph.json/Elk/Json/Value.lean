import Elk.Core.Util.Java
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
for equal keys (`Parser.knownKeys`), and the importer looks members up with them, so most key
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

end Key

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
  if i < kvs.size then kvs.set! i (key, x) else kvs.push (key, x)

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
    if i < kvs.size then .obj (kvs.modify i fun kv => (kv.1, f kv.2))
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
      if i < kvs.size then .obj (kvs.modify i fun kv => (kv.1, kv.2.modifyAt rest f)) else v
    | other => other
  | .idx i :: rest =>
    match v with
    | .arr xs => if i < xs.size then .arr (xs.modify i (·.modifyAt rest f)) else v
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
        if j < kvs.size then .obj (kvs.modify j fun kv => (kv.1, kv.2.modifyAtFrom path (i + 1) f)) else v
      | other => other
    | .idx j =>
      match v with
      | .arr xs => if j < xs.size then .arr (xs.modify j (·.modifyAtFrom path (i + 1) f)) else v
      | other => other
  else f v

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
