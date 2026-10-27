import Tests.Framework
import Elk.Json.Parser
/-!
Strict-mode JSON numbers must parse exactly like the oracle's serde_json 1.0.149 (default
features: `u64` significand, `f64_from_parts`, no `float_roundtrip`). `tests/fixtures/json/serde_numbers.tsv`
holds lexemes with serde's result (`u <u64>`, `i <i64>`, `f <f64 bits>`, `e` = error), produced by
a Rust harness against serde_json itself. `ELK_SERDE_NUMBERS=<tsv>` checks an additional file.
-/
namespace Tests.Json.SerdeNumbers

open Tests Elk.Json

/-- Whether the strict parse of `lexeme` agrees with serde's result `expected`. -/
def agrees (lexeme expected : String) : Bool :=
  match (Elk.Json.parse lexeme), expected.splitOn " " with
  | .error _, ["e"] => true
  | .ok (.num (.int i)), ["u", v] => v.toNat?.map (fun n => (n : Int)) == some i
  | .ok (.num (.int i)), ["i", v] => v.toInt? == some i
  | .ok (.num (.float f)), ["f", bits] =>
    match bits.toList.foldl (fun (acc : Option Nat) c =>
        acc.bind fun a => (if c.isDigit then some (c.toNat - 48) else if c >= 'a' && c <= 'f' then
          some (c.toNat - 87) else none).map (a * 16 + ·)) (some 0) with
    | some b => f.toBits.toNat == b
    | none => false
  | _, _ => false

def checkFile (path : System.FilePath) : TestM Unit := do
  let text ← IO.FS.readFile path
  let mut n := 0
  let mut bad : Array String := #[]
  for line in text.splitOn "\n" do
    match line.splitOn "\t" with
    | [lexeme, expected] =>
      n := n + 1
      if !agrees lexeme expected && bad.size < 10 then bad := bad.push s!"{lexeme} (serde: {expected})"
    | _ => pure ()
  checkEq s!"{n} lexemes of {path} parse like serde_json" bad #[]

def suite : Suite := Tests.suite "json.parser.serde_numbers" do
  checkFile "tests/fixtures/json/serde_numbers.tsv"
  if let some extra ← IO.getEnv "ELK_SERDE_NUMBERS" then checkFile extra

def suites : Array Suite := #[suite]

end Tests.Json.SerdeNumbers
