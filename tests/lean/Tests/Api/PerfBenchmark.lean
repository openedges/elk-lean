import Tests.Framework
import Elk.Api
/-!
Test suites for `Elk.Api.PerfBenchmark` (elk-rs `perf_benchmark.rs`, `rust_api` engine).

* `api.perf.generators`: the synthetic scenario JSON equals `tests/fixtures/perf/*.input.json`
  (independent transcription of the Rust generators), scenario names and order follow
  `synthetic_scenarios_json`.
* `api.perf.layout`: laying out those inputs reproduces the oracle output byte for byte.
* `api.perf.format`: `lcg` and the `{:.N}` formatter.
-/
namespace Tests.Api.PerfBenchmark

open Tests Elk.Api Elk.Api.PerfBenchmark

private def fixtureDir : System.FilePath := "tests/fixtures/perf"

private def fixtureNames : Array String := #["layered_small", "hierarchy_nested", "rectpacking_medium"]

def generators : Suite := suite "api.perf.generators" do
  let names := syntheticScenarios.map (·.1)
  checkEq "scenario count" names.size 26
  checkEq "first scenario" names[0]! "layered_small"
  checkEq "last scenario" names[25]! "hierarchy_nested"
  for n in fixtureNames do
    let expected ← IO.FS.readFile (fixtureDir / s!"{n}.input.json")
    match syntheticScenarios.find? (·.1 == n) with
    | some (_, json) => check s!"{n} input identical to the elk-rs generator" (json == expected)
    | none => check s!"{n} present" false

def layout : Suite := suite "api.perf.layout" do
  for n in fixtureNames do
    let input ← IO.FS.readFile (fixtureDir / s!"{n}.input.json")
    let expected ← IO.FS.readFile (fixtureDir / s!"{n}.oracle.json")
    match ← layoutJson input "{}" (pretty := true) (sortKeys := true) with
    | .ok out => check s!"{n} layout byte-identical to the oracle" (out == expected)
    | .error e => check s!"{n} layout: {e}" false

def format : Suite := suite "api.perf.format" do
  checkEq "lcg 42" (lcg 42).toNat 1250496027
  checkEq "lcg wraps" (lcg 0x7fffffff).toNat ((0x7fffffff * 1103515245 + 12345) % 2 ^ 32 % 2 ^ 31)
  checkEq "fixed 6" (fmtFixed 2.8762091 6) "2.876209"
  checkEq "fixed 2" (fmtFixed 347.68 2) "347.68"
  checkEq "fixed pads" (fmtFixed 0.5 4) "0.5000"
  checkEq "fixed 0" (fmtFixed 347.68 0) "348"

def suites : Array Suite := #[generators, layout, format]

end Tests.Api.PerfBenchmark
