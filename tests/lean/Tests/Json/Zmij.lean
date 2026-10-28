import Tests.Framework
import Elk.Json
/-!
# JSON double rendering against zmij 1.0.19

* `json.zmij` — every `(bits, string)` pair of `tests/fixtures/json/zmij_cases.tsv` (written by a Rust
  harness around `zmij::Buffer::format_finite`, the formatter of the oracle's serde_json 1.0.149):
  `(Value.num (.float (Float.ofBits bits))).render` must equal the string byte for byte.
* `core.float.shortest` — `Float.toShortest` (ryu-style exponents) keeps the output of the earlier
  `%.*e` search, including the longer digits for some powers of two, which `Float.toJsonNumber`
  prints like zmij.
-/
namespace Tests.Json.Zmij

open Tests Elk.Json Elk.Core.Util

private def fixturePath : System.FilePath := "tests/fixtures/json/zmij_cases.tsv"

/-- Value of a lower-case or upper-case hex digit. -/
private def hexDigit? (c : Char) : Option UInt64 :=
  if '0' ≤ c && c ≤ '9' then some (c.toNat - '0'.toNat).toUInt64
  else if 'a' ≤ c && c ≤ 'f' then some (c.toNat - 'a'.toNat + 10).toUInt64
  else if 'A' ≤ c && c ≤ 'F' then some (c.toNat - 'A'.toNat + 10).toUInt64
  else none

/-- 16-digit hex bit pattern. -/
private def parseBits? (s : String) : Option UInt64 :=
  if s.length != 16 then none
  else s.foldl (fun acc c => acc.bind fun a => (hexDigit? c).map fun d => (a <<< 4) ||| d) (some 0)

def zmijCases : Suite := suite "json.zmij" do
  let text ← IO.FS.readFile fixturePath
  let mut count := 0
  let mut bad := 0
  for line in text.splitOn "\n" do
    if line.isEmpty || line.startsWith "#" then continue
    match line.splitOn "\t" with
    | [hex, expected] =>
      match parseBits? hex with
      | some bits =>
        let actual := (Value.num (.float (Float.ofBits bits))).render
        count := count + 1
        if actual != expected then
          bad := bad + 1
          report s!"render {hex}" false s!"expected {expected}, got {actual}"
      | none => report s!"bad bit pattern '{hex}'" false
    | _ => report s!"bad fixture line '{line}'" false
  check s!"{count} zmij cases ({bad} mismatches)" (bad == 0 && count ≥ 4000)

def shortest : Suite := suite "core.float.shortest" do
  -- powers of two: JSON as zmij (shortest in the asymmetric interval), toShortest as before
  let p777 := Float.ofBits 0x0f50000000000000
  checkEq "2^-777 json" (Float.toJsonNumber p777) "6.290184345309701e-235"
  checkEq "2^-777 shortest" (Float.toShortest p777) "6.2901843453097005e-235"
  let p122 := Float.ofBits 0xc790000000000000
  checkEq "-2^122 json" (Float.toJsonNumber p122) "-5.316911983139664e+36"
  checkEq "-2^122 shortest" (Float.toShortest p122) "-5.3169119831396635e36"
  checkEq "2^-1022 shortest" (Float.toShortest (Float.ofBits 0x0010000000000000)) "2.2250738585072014e-308"
  checkEq "2^-1022 json" (Float.toJsonNumber (Float.ofBits 0x0010000000000000)) "2.2250738585072014e-308"
  checkEq "0.5 shortest" (Float.toShortest 0.5) "0.5"
  checkEq "1024 shortest" (Float.toShortest 1024.0) "1024.0"
  checkEq "2^60 shortest" (Float.toShortest 1152921504606846976.0) "1.152921504606847e18"
  checkEq "2^60 json" (Float.toJsonNumber 1152921504606846976.0) "1.152921504606847e+18"
  -- layout switch points and extremes
  checkEq "1e15" (Float.toShortest 1e15) "1000000000000000.0"
  checkEq "1e16" (Float.toShortest 1e16) "1e16"
  checkEq "1e16 json" (Float.toJsonNumber 1e16) "1e+16"
  checkEq "1e-5" (Float.toShortest 1e-5) "0.00001"
  checkEq "1e-6" (Float.toShortest 1e-6) "1e-6"
  checkEq "5e-324" (Float.toShortest (Float.ofBits 1)) "5e-324"
  checkEq "-5e-324 json" (Float.toJsonNumber (Float.ofBits 0x8000000000000001)) "-5e-324"
  checkEq "f64::MAX" (Float.toShortest 1.7976931348623157e308) "1.7976931348623157e308"
  checkEq "0.1 + 0.2" (Float.toShortest (0.1 + 0.2)) "0.30000000000000004"
  checkEq "-0.0" (Float.toShortest (-0.0)) "-0.0"
  checkEq "-0.0 json" (Float.toJsonNumber (-0.0)) "-0.0"
  -- non-finite values
  checkEq "NaN" (Float.toShortest (0.0 / 0.0)) "NaN"
  checkEq "inf" (Float.toShortest (1.0 / 0.0)) "inf"
  checkEq "-inf" (Float.toShortest (-1.0 / 0.0)) "-inf"
  checkEq "inf json" (Float.toJsonNumber (1.0 / 0.0)) "inf"
  checkEq "NaN value renders null" (Value.num (.float (0.0 / 0.0))).render "null"

/-- String escaping of the printer's append-in-place path (`Printer.escapeInto`). -/
def escapes : Suite := suite "json.printer.escape" do
  checkEq "plain" (Value.str "abc").render "\"abc\""
  checkEq "empty" (Value.str "").render "\"\""
  checkEq "all short escapes" (Value.str "\"\\\n\r\t\x08\x0c").render "\"\\\"\\\\\\n\\r\\t\\b\\f\""
  checkEq "control chars" (Value.str "\x00\x1f\x7f").render "\"\\u0000\\u001f\x7f\""
  checkEq "unicode with escape" (Value.str "é\"→😀").render "\"é\\\"→😀\""
  checkEq "escaped key" (Value.obj #[("a\"b", .num (.int 1))]).render "{\"a\\\"b\":1}"
  checkEq "pretty escaped key" (Value.obj #[("k\n", .str "v\t")]).renderPretty "{\n  \"k\\n\": \"v\\t\"\n}"
  -- ELK member names come from pre-rendered literals (also when the key is not the shared object),
  -- other keys of the same length and first byte are quoted normally
  let v := Value.obj #[("x", .num (.int 1)), (Key.width, .num (.int 2)), ("widtH", .num (.int 3)),
    ("sourcePort", .str "p"), ("startPoint", .obj #[("y", .null)]), ("yy", .bool true)]
  checkEq "member name literals (compact)" v.render
    "{\"x\":1,\"width\":2,\"widtH\":3,\"sourcePort\":\"p\",\"startPoint\":{\"y\":null},\"yy\":true}"
  -- integers are written two digits per step (inner pairs keep their zeros)
  let ints : Array Int := #[0, 7, 10, 99, 100, 101, 109, 1000, 1009, 10005, 123456789, -1, -100, -2147483648,
    9223372036854775807, -9223372036854775808, 18446744073709551615]
  checkEq "integers" (Value.arr (ints.map Value.ofInt)).render ("[" ++ ",".intercalate (ints.map toString).toList ++ "]")
  -- nesting below the pre-rendered indentation levels
  let deep := (List.range 40).foldl (fun acc _ => Value.arr #[acc, .num (.int 1)]) (Value.obj #[("k", .num (.int 2))])
  let expected := Id.run do
    -- reference rendering of `deep` (the former one-piece-at-a-time printer)
    let rec go (v : Value) (level : Nat) (out : String) (fuel : Nat) : String :=
      match fuel, v with
      | 0, _ => out
      | fuel + 1, .arr xs =>
        let out := xs.size.fold (init := out ++ "[\n") fun i _ acc =>
          go xs[i]! (level + 1) ((if i != 0 then acc ++ ",\n" else acc).pushn ' ' (2 * (level + 1))) fuel
        (out ++ "\n").pushn ' ' (2 * level) ++ "]"
      | _ + 1, .obj _ => (((out ++ "{\n").pushn ' ' (2 * (level + 1)) ++ "\"k\": 2\n").pushn ' ' (2 * level)) ++ "}"
      | _ + 1, other => out ++ other.render
    return go deep 0 "" 100
  checkEq "pretty nesting deeper than the indentation tables" deep.renderPretty expected
  checkEq "member name literals (pretty)" v.renderPretty
    "{\n  \"x\": 1,\n  \"width\": 2,\n  \"widtH\": 3,\n  \"sourcePort\": \"p\",\n  \"startPoint\": {\n    \"y\": null\n  },\n  \"yy\": true\n}"

def suites : Array Suite := #[zmijCases, shortest, escapes]

end Tests.Json.Zmij
