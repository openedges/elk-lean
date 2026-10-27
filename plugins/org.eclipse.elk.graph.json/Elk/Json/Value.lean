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

/-- `2^64` (`u64::MAX as f64`) as an exact bit pattern: a literal such as `18446744073709551616.0`
has a mantissa above `2^53` and would take the slow `Float.ofScientific` path at run time whenever
the compiler does not hoist it (see `Elk.Core.Util.FastFloat`). -/
private def TWO_POW_64 : Float := Float.ofBits 0x43F0000000000000

/-- `2^63` (`i64::MAX as f64`, `-(i64::MIN as f64)`) as an exact bit pattern. -/
private def TWO_POW_63 : Float := Float.ofBits 0x43E0000000000000

/-- elk-rs `f64_to_number`: finite values within `1e-6` of an integer become
integers, non-finite values become `0`. Used for all layout results. -/
def ofFloatElk (x : Float) : Number :=
  if x.isFinite then
    let r := x.round
    if (x - r).abs <= 1e-6 then
      -- `rounded as u64` for `0 <= rounded <= u64::MAX as f64` (= 2^64, saturating), else
      -- `rounded as i64` within `[i64::MIN as f64, i64::MAX as f64]`, else the float itself
      if r >= 0.0 && r <= TWO_POW_64 then
        .int (if r >= TWO_POW_64 then 18446744073709551615 else (r.toUInt64.toNat : Int))
      else if r >= -TWO_POW_63 && r <= TWO_POW_63 then .int r.toIntTrunc
      else .float x
    else .float x
  else .int 0

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

/-- Object member lookup (first matching key). -/
def get? (v : Value) (key : String) : Option Value :=
  match v with
  | .obj kvs => (kvs.find? (fun kv => kv.1 == key)).map (·.2)
  | _ => none

def hasKey (v : Value) (key : String) : Bool := (v.get? key).isSome

/-- Member lookup on an object's entry array. -/
def lookup (kvs : Array (String × Value)) (key : String) : Option Value :=
  (kvs.find? (fun kv => kv.1 == key)).map (·.2)

/-- `obj[key] = x`: replaces an existing member in place or appends. Non-objects are unchanged. -/
def set (v : Value) (key : String) (x : Value) : Value :=
  match v with
  | .obj kvs =>
    match kvs.findIdx? (fun kv => kv.1 == key) with
    | some i => .obj (kvs.set! i (key, x))
    | none => .obj (kvs.push (key, x))
  | other => other

/-- Removes a member (no-op if absent). -/
def remove (v : Value) (key : String) : Value :=
  match v with
  | .obj kvs =>
    match kvs.findIdx? (fun kv => kv.1 == key) with
    | some i => .obj (kvs.eraseIdx! i)
    | none => v
  | other => other

/-- Applies `f` to a member, inserting `f default` when the member is absent. -/
def modifyKey (v : Value) (key : String) (default : Value) (f : Value → Value) : Value :=
  match v with
  | .obj kvs =>
    match kvs.findIdx? (fun kv => kv.1 == key) with
    | some i => .obj (kvs.modify i fun kv => (kv.1, f kv.2))
    | none => .obj (kvs.push (key, f default))
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
      match kvs.findIdx? (fun kv => kv.1 == k) with
      | some i => .obj (kvs.modify i fun kv => (kv.1, kv.2.modifyAt rest f))
      | none => v
    | other => other
  | .idx i :: rest =>
    match v with
    | .arr xs => if i < xs.size then .arr (xs.modify i (·.modifyAt rest f)) else v
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
