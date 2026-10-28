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

/-- A random decimal lexeme: optional `-`, 1–20 integer digits (no leading zero unless `0`),
optionally a fraction of 0–20 digits and an exponent with 1–3 digits. -/
def randomDecimal (r : Random) : String × Random := Id.run do
  let mut r := r
  let mut s := ""
  let (sign, r1) := r.nextInt 3
  r := r1
  if sign == 0 then s := s.push '-'
  let (intLen, r2) := r.nextInt 21
  r := r2
  if intLen == 0 then s := s.push '0'
  else
    for k in [0:intLen.toNat] do
      let (d, r3) := r.nextInt 10
      r := r3
      let d := if k == 0 && d == 0 then 1 else d
      s := s.push (Char.ofNat (48 + d.toNat))
  let (fracKind, r4) := r.nextInt 4
  r := r4
  if fracKind != 0 then
    let (fracLen, r5) := r.nextInt 21
    r := r5
    s := s.push '.'
    for _ in [0:(max fracLen.toNat 1)] do
      let (d, r6) := r.nextInt 10
      r := r6
      s := s.push (Char.ofNat (48 + d.toNat))
  let (expKind, r7) := r.nextInt 3
  r := r7
  if expKind == 0 || fracKind == 0 then
    let (e, r8) := r.nextInt 40
    let (es, r9) := r8.nextInt 3
    r := r9
    s := s.push (if es == 0 then 'E' else 'e')
    if es == 1 then s := s.push '-' else if es == 2 then s := s.push '+'
    s := s ++ toString e.toNat
  return (s, r)

/-- `strictNumber?` (with the Clinger fast path) against `strtod` on random decimal lexemes and on
boundary cases of the fast path (`2^53`, `10^22`, 18/19 digits). -/
def numberSuite : Suite := Tests.suite "json.parser.number_fast_path" do
  let fixed := #["0.0", "-0.0", "-0e5", "9007199254740991.0", "9007199254740992.0", "9007199254740993.0",
    "1e22", "1e23", "1.5e-22", "1.5e-23", "123456789012345678.5", "12345678901234567.8", "0.000001",
    "4.9e-324", "1.7976931348623157e308", "2.2250738585072014e-308", "8.0", "101.0", "15.5", "-12.25",
    "0.1", "0.3", "1e0", "1E+0", "1e-0", "100000000000000000000000.0", "999999999999999999e-22"]
  let mut bad : Array String := #[]
  let check (t : String) : Option String :=
    match Elk.Json.Parser.strictNumber? t with
    | some (.float f) => if f.toBits == (strtodUnchecked t).toBits then none else some t
    | some (.int _) => none
    | none => some s!"{t} (rejected)"
  for t in fixed do
    if let some e := check t then bad := bad.push e
  let mut r := Random.ofInt 11
  for _ in [0:20000] do
    let (t, r') := randomDecimal r
    r := r'
    if let some e := check t then
      if bad.size < 20 then bad := bad.push e
  checkEq "fast path agrees with strtod" bad #[]
  -- lenient spellings
  for t in #["5.", ".5", "+1.25", "+.5e1", "-5.e2"] do
    match Elk.Json.parse t true with
    | .ok (.num (.float f)) =>
      let lex := if t.startsWith "+" then (t.drop 1).toString else t
      checkEq s!"lenient {t}" f.toBits (strtodUnchecked lex).toBits
    | _ => checkEq s!"lenient {t} parses" false true

def suites : Array Suite := #[suite, numberSuite]

end Tests.Json.ParserFuzz
