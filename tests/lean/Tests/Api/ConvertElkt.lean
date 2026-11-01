import Tests.Framework
import Elk.Api
/-!
`Elk.Api.convertElkt` (ELK Text → ELK JSON, the `elk convert` path shared with the C API, NAPI,
WASM and npm `convertElkt`): output of each flag combination, the flag bit decoding of the C API
and the error message (`ELK Text parse error: <line>:<col>: …`).
-/
namespace Tests.Api.ConvertElkt

open Tests Elk.Api

private def sample : String := "algorithm: layered\nnode a { label \"A\" }\nnode b { port p }\nedge a -> b.p\n"

def convert : Suite := suite "api.convertElkt" do
  match ← convertElkt sample with
  | .error e => report "plain conversion" false e
  | .ok out =>
    checkEq "plain: exporter key order, no sizes"
      out "{\"id\":\"n0\",\"children\":[{\"id\":\"a\",\"labels\":[{\"text\":\"A\"}]},{\"id\":\"b\",\"ports\":[{\"id\":\"p\"}]}],\"layoutOptions\":{\"elk.algorithm\":\"layered\"},\"edges\":[{\"id\":\"e0\",\"sources\":[\"a\"],\"targets\":[\"p\"]}]}"
  match ← convertElkt sample (defaults := true) (sortKeys := true) with
  | .error e => report "defaults + sortKeys" false e
  | .ok out =>
    check "defaults: node size 30" ((out.splitOn "\"width\":30").length > 1)
    check "defaults: port size 5" ((out.splitOn "\"width\":5").length > 1)
    check "sortKeys: children before id" (out.startsWith "{\"children\":")
  match ← convertElkt sample (pretty := true) with
  | .error e => report "pretty" false e
  | .ok out => check "pretty: indented" ((out.splitOn "\n  ").length > 1)
  -- flag bits of elk_lean_convert_elkt_flags
  let f := ConvertFlags.ofBits 5
  check "bits 5 = defaults + sortKeys" (f.defaults && !f.pretty && f.sortKeys)
  let f := ConvertFlags.ofBits 2
  check "bits 2 = pretty" (!f.defaults && f.pretty && !f.sortKeys)
  match ← convertElktWith sample (ConvertFlags.ofBits 0), ← convertElkt sample with
  | .ok a, .ok b => checkEq "convertElktWith 0 = convertElkt" a b
  | _, _ => report "convertElktWith 0" false "error"
  match ← convertElkt "node a\nedge a -> \n" with
  | .ok _ => report "syntax error" false "expected an error"
  | .error e => check s!"syntax error message with line:col ({e})" (e.startsWith "ELK Text parse error: 3:1: ")

def suites : Array Suite := #[convert]

end Tests.Api.ConvertElkt
