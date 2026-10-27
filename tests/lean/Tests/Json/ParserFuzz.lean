import Tests.Framework
import Elk.Json.Parser
import Elk.Core.Util.Random
import Tests.Json.ParserReference
/-!
Differential test of `Elk.Json.parse` (position-threading parser) against the previous `StateT`
parser kept in `Tests.Json.ParserReference`: on seed documents and on random byte mutations of them,
both modes (strict, lenient) must give the same value (floats compared by bits) or the same error
message at the same byte position. With `ELK_PARSER_CORPUS=<dir>` every `*.json` below `<dir>` is
compared as well.
-/
namespace Tests.Json.ParserFuzz

open Tests Elk.Json Elk.Core.Util

partial def valueEq : Value → Value → Bool
  | .null, .null => true
  | .bool a, .bool b => a == b
  | .num (.int a), .num (.int b) => a == b
  | .num (.float a), .num (.float b) => a.toBits == b.toBits
  | .str a, .str b => a == b
  | .arr xs, .arr ys => xs.size == ys.size && (xs.zip ys).all fun (x, y) => valueEq x y
  | .obj xs, .obj ys =>
    xs.size == ys.size && (xs.zip ys).all fun ((k1, v1), (k2, v2)) => k1 == k2 && valueEq v1 v2
  | _, _ => false

def sameResult (text : String) (lenient : Bool) : Bool :=
  match Elk.Json.parse text lenient, Tests.Json.ParserReference.parse text lenient with
  | .ok a, .ok b => valueEq a b
  | .error e1, .error e2 => e1.pos == e2.pos && e1.message == e2.message
  | _, _ => false

def seeds : Array String := #[
  "{\"id\":\"root\",\"children\":[{\"id\":\"n1\",\"width\":40,\"height\":30.5,\"x\":-1.25e3}],\"edges\":[]}",
  "[1, -0, 0.5, 1e10, -2.5E-7, 123456789012345678, 1234567890123456789, 99999999999999999999, -9223372036854775809, 18446744073709551615]",
  "{\"s\":\"a\\\"b\\\\c\\/d\\b\\f\\n\\r\\t\\u00e9\\ud83d\\ude00\\udc00\\ud800x\",\"t\":true,\"f\":false,\"z\":null}",
  "{ // comment\n  key: 'single', \"k2\": [1, 2, 3,], /* block */ 'q': +5, n: .5, m: 5., i: Infinity, j: -Infinity, k: NaN; }",
  "  \t\n {\"empty\": {}, \"arr\": [], \"nested\": [[[]], {\"a\": [{}]}]}  ",
  "{\"a\":1,}", "[1,2,]", "{\"a\" 1}", "{\"a\":}", "[01]", "[1.]", "[.5]", "[1e]", "[1e+]", "\"abc", "{\"a\":\"\\x\"}",
  "{\"a\":\"\\u12\"}", "{\"a\":\"\\u12G4\"}", "truex", "nul", "[true, false, null]", "{\"c\":\"tab\there\"}", "", "   ",
  "{\"a\":1} x", "[1 2]", "{\"a\":1 \"b\":2}", "'str'", "{'a':'b\\'c'}", "{\"line\":\"a\\\nb\"}", "-", "+1", "-Infinity", "NaNx"]

/-- Bytes the mutations insert or substitute. -/
def alphabet : Array UInt8 := Id.run do
  let mut a : Array UInt8 := #[]
  for c in "{}[]:,;\"'\\/*\n\t ae.E+-0123456789uINtfnrx_$".toList do a := a.push c.toNat.toUInt8
  return a ++ #[0x01, 0x1F, 0x7F]

/-- A random mutation (insert, delete or replace one to three bytes) of `s`, if still UTF-8. -/
def mutate (s : String) (r : Random) : Option String × Random := Id.run do
  let mut bs := s.toUTF8
  let mut r := r
  let (k, r1) := r.nextInt 3
  r := r1
  for _ in [0:(k.toNat + 1)] do
    let (op, r2) := r.nextInt 3
    let (pos, r3) := r2.nextInt ((bs.size : Int) + 1)
    let (ci, r4) := r3.nextInt (alphabet.size : Int)
    r := r4
    let p := pos.toNat
    let c := alphabet[ci.toNat]!
    if op == 0 then
      bs := (bs.extract 0 p).push c ++ bs.extract p bs.size
    else if op == 1 && p < bs.size then
      bs := bs.extract 0 p ++ bs.extract (p + 1) bs.size
    else if p < bs.size then
      bs := bs.set! p c
  return (String.fromUTF8? bs, r)

def suite : Suite := Tests.suite "json.parser.differential" do
  let mut bad : Array String := #[]
  for s in seeds do
    for lenient in [false, true] do
      if !sameResult s lenient then bad := bad.push s!"seed {repr s} lenient={lenient}"
  let mut r := Random.ofInt 7
  let mut count := 0
  for _ in [0:4000] do
    for s in seeds do
      let (m, r') := mutate s r
      r := r'
      if let some t := m then
        count := count + 1
        for lenient in [false, true] do
          if !sameResult t lenient && bad.size < 20 then bad := bad.push s!"mutation {repr t} lenient={lenient}"
  checkEq s!"parsers agree on seeds and {count} mutations" bad #[]
  if let some dir ← IO.getEnv "ELK_PARSER_CORPUS" then
    let files ← (System.FilePath.mk dir).walkDir
    let mut n := 0
    let mut diff : Array String := #[]
    for f in files do
      if f.extension == some "json" then
        let text ← IO.FS.readFile f
        n := n + 1
        if !sameResult text false then diff := diff.push f.toString
    checkEq s!"parsers agree on {n} corpus files" diff #[]

def suites : Array Suite := #[suite]

end Tests.Json.ParserFuzz
