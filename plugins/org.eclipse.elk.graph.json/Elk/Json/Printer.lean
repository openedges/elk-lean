import Elk.Json.Value
import Elk.Core.Util.Sort
/-!
# JSON printer

Byte-compatible with `serde_json::to_string` / `to_string_pretty` (two-space
indentation) for the values elk-lean produces, so outputs can be diffed
against elk-rs directly. Keys are rendered in insertion order; pass
`sortKeys := true` to emulate elk-rs's alphabetically ordered maps.
-/
namespace Elk.Json

namespace Printer

private def hexDigit (n : Nat) : Char :=
  if n < 10 then Char.ofNat ('0'.toNat + n) else Char.ofNat ('a'.toNat + n - 10)

/-- serde_json string escaping. -/
def escapeString (s : String) : String := Id.run do
  let mut out := "\""
  for c in s.toList do
    match c with
    | '"' => out := out ++ "\\\""
    | '\\' => out := out ++ "\\\\"
    | '\n' => out := out ++ "\\n"
    | '\r' => out := out ++ "\\r"
    | '\t' => out := out ++ "\\t"
    | '\x08' => out := out ++ "\\b"
    | '\x0c' => out := out ++ "\\f"
    | c =>
      if c.toNat < 0x20 then
        out := out ++ "\\u00" ++ String.singleton (hexDigit (c.toNat / 16)) ++ String.singleton (hexDigit (c.toNat % 16))
      else
        out := out.push c
  return out.push '"'

private def sortEntries (kvs : Array (String × Value)) : Array (String × Value) :=
  Elk.Core.Util.stableSort kvs (fun a b => compare a.1 b.1)

/-- Compact rendering (`serde_json::to_string`). -/
partial def compact (sortKeys : Bool) (v : Value) (out : String) : String :=
  match v with
  | .null => out ++ "null"
  | .bool b => out ++ (if b then "true" else "false")
  | .num n => out ++ n.render
  | .str s => out ++ escapeString s
  | .arr xs => Id.run do
    let mut out := out.push '['
    let mut first := true
    for x in xs do
      if !first then out := out.push ','
      first := false
      out := compact sortKeys x out
    return out.push ']'
  | .obj kvs => Id.run do
    let kvs := if sortKeys then sortEntries kvs else kvs
    let mut out := out.push '{'
    let mut first := true
    for (k, x) in kvs do
      if !first then out := out.push ','
      first := false
      out := out ++ escapeString k
      out := out.push ':'
      out := compact sortKeys x out
    return out.push '}'

private def indent (out : String) (level : Nat) : String :=
  out ++ String.ofList (List.replicate (2 * level) ' ')

/-- Pretty rendering (`serde_json::to_string_pretty`, two-space indentation). -/
partial def pretty (sortKeys : Bool) (v : Value) (level : Nat) (out : String) : String :=
  match v with
  | .arr xs =>
    if xs.isEmpty then out ++ "[]"
    else Id.run do
      let mut out := out ++ "[\n"
      let mut first := true
      for x in xs do
        if !first then out := out ++ ",\n"
        first := false
        out := indent out (level + 1)
        out := pretty sortKeys x (level + 1) out
      out := out.push '\n'
      out := indent out level
      return out.push ']'
  | .obj kvs =>
    if kvs.isEmpty then out ++ "{}"
    else Id.run do
      let kvs := if sortKeys then sortEntries kvs else kvs
      let mut out := out ++ "{\n"
      let mut first := true
      for (k, x) in kvs do
        if !first then out := out ++ ",\n"
        first := false
        out := indent out (level + 1)
        out := out ++ escapeString k ++ ": "
        out := pretty sortKeys x (level + 1) out
      out := out.push '\n'
      out := indent out level
      return out.push '}'
  | other => compact sortKeys other out

end Printer

namespace Value

/-- `serde_json::to_string`. -/
def render (v : Value) (sortKeys : Bool := false) : String := Printer.compact sortKeys v ""

/-- `serde_json::to_string_pretty`. -/
def renderPretty (v : Value) (sortKeys : Bool := false) : String := Printer.pretty sortKeys v 0 ""

instance : ToString Value := ⟨fun v => v.render⟩

end Value

end Elk.Json
