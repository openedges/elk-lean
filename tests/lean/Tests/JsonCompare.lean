import Tests.Framework
import Elk.Json.Parser
/-!
# Structural comparison of layout JSON (fixture suites)

The result reference is ELK Java 0.12.0, whose Gson output differs from elk-lean's in formatting
only (`12.0` vs `12`, key order of added fields, `NaN`/`Infinity` tokens). Layout outputs are
therefore compared as values: objects as key → value maps, arrays by position, numbers by value
(an integer equals the float of the same value) within an absolute tolerance, and a non-finite
expected number equals `null` (elk-lean renders non-finite values as `null`, like elkjs).
-/
namespace Tests

open Elk.Json

private def numValue : Number → Float
  | .int i => Float.ofInt i
  | .float f => f

/-- Tolerance for fixture expectations that still come from the elk-rs oracle: elk-rs snaps values
within `1e-6` of an integer, elk-lean (like ELK Java) does not. Fixtures regenerated from ELK Java
compare with tolerance `0`. -/
def ELK_RS_FIXTURE_TOL : Float := 1e-6

/-- The first difference between `actual` and `expected` (`none` when equivalent). -/
partial def jsonDiff (path : String) (actual expected : Value) (tol : Float) : Option String :=
  match actual, expected with
  | .null, .null => none
  | .null, .num n =>
    if (numValue n).isFinite then some s!"{path}: null vs {(numValue n)}" else none
  | .bool a, .bool b => if a == b then none else some s!"{path}: {a} vs {b}"
  | .str a, .str b => if a == b then none else some s!"{path}: {repr a} vs {repr b}"
  | .num a, .num b =>
    let x := numValue a
    let y := numValue b
    let same := if x.isNaN || y.isNaN then x.isNaN && y.isNaN
      else if x.isFinite && y.isFinite then (x - y).abs <= tol else x == y
    if same then none else some s!"{path}: {x} vs {y}"
  | .arr xs, .arr ys =>
    if xs.size != ys.size then some s!"{path}: array size {xs.size} vs {ys.size}"
    else Id.run do
      for i in [0:xs.size] do
        if let some d := jsonDiff s!"{path}[{i}]" xs[i]! ys[i]! tol then return some d
      return none
  | .obj kvs, .obj ekvs =>
    if kvs.size != ekvs.size then
      some s!"{path}: keys {kvs.map (·.1)} vs {ekvs.map (·.1)}"
    else Id.run do
      for (k, v) in ekvs do
        match kvs.find? (·.1 == k) with
        | some (_, av) => if let some d := jsonDiff s!"{path}/{k}" av v tol then return some d
        | none => return some s!"{path}: missing key {k}"
      return none
  | _, _ => some s!"{path}: different kinds"

/-- Checks that the layout JSON `actual` (elk-lean output) is equivalent to `expected` (reference
output; parsed leniently to accept Gson's `NaN`/`Infinity`) within `tol`. -/
def checkJson (name : String) (actual expected : String) (tol : Float := 0.0) : TestM Unit :=
  match Elk.Json.parse actual, Elk.Json.parse expected (lenient := true) with
  | .ok a, .ok e => report name (jsonDiff "" a e tol).isNone ((jsonDiff "" a e tol).getD "")
  | .error err, _ => report name false s!"actual is not JSON: {err}"
  | _, .error err => report name false s!"expected is not JSON: {err}"

/-- `checkJson` as a Boolean (for suites that accept one of several references). -/
def jsonEquivalent (actual expected : String) (tol : Float := 0.0) : Bool :=
  match Elk.Json.parse actual, Elk.Json.parse expected (lenient := true) with
  | .ok a, .ok e => (jsonDiff "" a e tol).isNone
  | _, _ => false

end Tests
