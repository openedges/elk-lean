import Tests.Framework
import Elk.Json
/-! Tests for the JSON value model, parser and printer. -/
namespace Tests.Json

open Tests Elk.Json

def roundTrip (text : String) (name : String) : TestM Unit := do
  match parse text with
  | .ok v => checkEq name v.render text
  | .error e => check s!"{name}: parse error {e}" false

def printer : Suite := suite "json.printer" do
  let v : Value := .obj #[("b", .num (.int 1)), ("a", .arr #[.num (.float 2.5), .str "x\"y\n", .null, .bool true]), ("e", .obj #[]), ("f", .arr #[])]
  checkEq "compact" v.render "{\"b\":1,\"a\":[2.5,\"x\\\"y\\n\",null,true],\"e\":{},\"f\":[]}"
  checkEq "sorted" (v.render (sortKeys := true)) "{\"a\":[2.5,\"x\\\"y\\n\",null,true],\"b\":1,\"e\":{},\"f\":[]}"
  checkEq "pretty" v.renderPretty "{\n  \"b\": 1,\n  \"a\": [\n    2.5,\n    \"x\\\"y\\n\",\n    null,\n    true\n  ],\n  \"e\": {},\n  \"f\": []\n}"
  checkEq "float 12.0" (Value.ofFloat 12.0).render "12.0"
  -- oracle (serde_json 1.0.149 / zmij): signed exponent
  checkEq "float 1e21" (Value.ofFloat 1e21).render "1e+21"
  checkEq "float 3e-6" (Value.ofFloat 3e-6).render "3e-6"
  checkEq "float f64::MAX" (Value.ofFloat 1.7976931348623157e308).render "1.7976931348623157e+308"
  -- value-preserving like ELK Java: integers only for exactly integral values inside i64
  checkEq "elk number: 2^64 stays a float" (Value.ofFloatElk 18446744073709551616.0).render "1.8446744073709552e+19"
  checkEq "elk number: 2^63 stays a float" (Value.ofFloatElk 9223372036854775808.0).render "9.223372036854776e+18"
  checkEq "elk number: 2^62 integer" (Value.ofFloatElk 4611686018427387904.0).render "4611686018427387904"
  checkEq "elk number: -0.0 stays a float" (Value.ofFloatElk (-0.0)).render "-0.0"
  checkEq "elk number: -1e19 stays a float" (Value.ofFloatElk (-1e19)).render "-1e+19"
  checkEq "elk number: f64::MAX stays a float" (Value.ofFloatElk 1.7976931348623157e308).render "1.7976931348623157e+308"
  checkEq "elk number 12.0000001 is not snapped" (Value.ofFloatElk 12.0000001).render "12.0000001"
  checkEq "elk number 99.99999999999999 is not snapped" (Value.ofFloatElk 99.99999999999999).render "99.99999999999999"
  checkEq "elk number 12" (Value.ofFloatElk 12.0).render "12"
  checkEq "elk number 27.5" (Value.ofFloatElk 27.5).render "27.5"
  checkEq "elk number nan renders null" (Value.ofFloatElk (0.0 / 0.0)).render "null"
  checkEq "control escape" (Value.str "a\x01b").render "\"a\\u0001b\""
  checkEq "unicode kept" (Value.str "é→").render "\"é→\""

def parserStrict : Suite := suite "json.parser" do
  roundTrip "{\"id\":\"root\",\"children\":[{\"id\":\"n1\",\"width\":30,\"height\":30.5}],\"x\":-0.0015}" "roundtrip"
  match parse "-1.5e-3" with
  | .ok v => checkEq "exponent lexeme renders like serde" v.render "-0.0015"
  | .error e => check s!"exp parse error {e}" false
  match parse "[1, 2.0, 1e2, -0, 18446744073709551615, 9223372036854775808, \"\\u00e9\\ud83d\\ude00\", \"\\/\"]" with
  | .ok (.arr xs) =>
    check "int" (xs[0]! == .num (.int 1))
    check "float kept" (xs[1]! == .num (.float 2.0))
    checkEq "1e2 render" xs[2]!.render "100.0"
    -- `-0` is read as `-0.0` like ELK Java (`Double.parseDouble`)
    checkEq "-0 render" xs[3]!.render "-0.0"
    checkEq "u64" xs[4]!.render "18446744073709551615"
    checkEq "big" xs[5]!.render "9223372036854775808"
    check "unicode escape" (xs[6]! == .str "é😀")
    check "slash escape" (xs[7]! == .str "/")
  | .ok _ => check "array expected" false
  | .error e => check s!"parse error {e}" false
  check "trailing comma rejected" (parse "[1,]" matches .error _)
  check "comment rejected" (parse "[1] // x" matches .error _)
  check "single quote rejected" (parse "{'a':1}" matches .error _)
  check "leading zero" ((parse "01") matches .error _ )
  check "lone minus" ((parse "-") matches .error _ )
  check "whitespace" ((parse " \n\t{ } \r\n") matches .ok (.obj #[]))
  match parse "{\"a\":1,\"a\":2}" with
  | .ok v => checkEq "duplicate keys kept in order" v.render "{\"a\":1,\"a\":2}"
  | .error e => check s!"dup error {e}" false

def parserLenient : Suite := suite "json.lenient" do
  let text := "// comment\n{ id: 'root', /* block */ layoutOptions: { 'elk.algorithm': \"layered\"; }, children: [ {id: \"n1\", width: +30, height: .5,}, ], n: Infinity, m: -Infinity }"
  match parse text (lenient := true) with
  | .ok v =>
    check "id" (v.get? "id" == some (.str "root"))
    check "nested" ((v.get? "layoutOptions").bind (·.get? "elk.algorithm") == some (.str "layered"))
    let child0 := v.getAt [.key "children", .idx 0]
    check "plus" (child0.bind (·.get? "width") == some (.num (.int 30)))
    check "leading dot" (child0.bind (·.get? "height") == some (.num (.float 0.5)))
    let n := (v.get? "n").bind (·.getFloat?)
    check "infinity" (n.map (·.isInf) == some true)
  | .error e => check s!"lenient parse error {e}" false
  check "strict rejects" (parse text matches .error _)

def accessors : Suite := suite "json.value" do
  let v : Value := .obj #[("a", .num (.int 1)), ("b", .arr #[.obj #[("c", .str "x")]])]
  check "getAt" (v.getAt [.key "b", .idx 0, .key "c"] == some (.str "x"))
  let v2 := v.modifyAt [.key "b", .idx 0] (·.set "d" (.bool true))
  checkEq "modifyAt" v2.render "{\"a\":1,\"b\":[{\"c\":\"x\",\"d\":true}]}"
  checkEq "set replaces" (v.set "a" (.num (.int 2))).render "{\"a\":2,\"b\":[{\"c\":\"x\"}]}"
  checkEq "remove" (v.remove "a").render "{\"b\":[{\"c\":\"x\"}]}"
  let a := (v.getAt [.key "a"]).bind (·.getInt?)
  check "getInt" (a == some 1)
  check "toInt? float" ((Number.float 3.0).toInt? == some 3 && (Number.float 3.5).toInt? == none)

def suites : Array Suite := #[printer, parserStrict, parserLenient, accessors]

end Tests.Json
