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

/-- Appends `c` with serde_json string escaping. -/
private def pushEscaped (out : String) (c : Char) : String :=
  match c with
  | '"' => out ++ "\\\""
  | '\\' => out ++ "\\\\"
  | '\n' => out ++ "\\n"
  | '\r' => out ++ "\\r"
  | '\t' => out ++ "\\t"
  | '\x08' => out ++ "\\b"
  | '\x0c' => out ++ "\\f"
  | c =>
    if c.toNat < 0x20 then
      ((out ++ "\\u00").push (hexDigit (c.toNat / 16))).push (hexDigit (c.toNat % 16))
    else
      out.push c

/-- Whether `s` has a character that serde_json escapes (`"`, `\`, control characters), checked on
the UTF-8 bytes from byte `i` (bytes of multi-byte characters are `≥ 0x80`). -/
private def hasEscapes (s : String) (n : Nat) (hn : n = s.utf8ByteSize) (i : Nat) : Bool :=
  if h : i < n then
    let b := s.getUTF8Byte ⟨i⟩ (show i < s.utf8ByteSize from hn ▸ h)
    b < 0x20 || b == 0x22 || b == 0x5c || hasEscapes s n hn (i + 1)
  else
    false
termination_by n - i

/-- Appends `s` as a JSON string literal (serde_json escaping) to `out`. -/
def escapeInto (out s : String) : String :=
  let out := out.push '"'
  let out := if hasEscapes s s.utf8ByteSize rfl 0 then s.foldl pushEscaped out else out ++ s
  out.push '"'

/-- serde_json string escaping. -/
def escapeString (s : String) : String := escapeInto "" s

private def sortEntries (kvs : Array (String × Value)) : Array (String × Value) :=
  Elk.Core.Util.stableSort kvs (fun a b => compare a.1 b.1)

/-- Appends the decimal representation of `n` (`Nat.repr` without the intermediate string). -/
private def pushNat (out : String) (n : Nat) : String :=
  if n < 10 then out.push (Char.ofNat (48 + n))
  else (pushNat out (n / 10)).push (Char.ofNat (48 + n % 10))
termination_by n
decreasing_by omega

/-- Appends `n.render`; integers are written in place. -/
@[inline] private def pushNumber (out : String) (n : Number) : String :=
  match n with
  | .int (.ofNat k) => pushNat out k
  | .int (.negSucc k) => pushNat (out.push '-') (k + 1)
  | n => out ++ n.render

/-- Compact rendering (`serde_json::to_string`). -/
partial def compact (sortKeys : Bool) (v : Value) (out : String) : String :=
  match v with
  | .null => out ++ "null"
  | .bool b => out ++ (if b then "true" else "false")
  | .num n => pushNumber out n
  | .str s => escapeInto out s
  | .arr xs => Id.run do
    let mut out := out.push '['
    for h : i in [0:xs.size] do
      if i != 0 then out := out.push ','
      out := compact sortKeys xs[i] out
    return out.push ']'
  | .obj kvs => Id.run do
    let kvs := if sortKeys then sortEntries kvs else kvs
    let mut out := out.push '{'
    for h : i in [0:kvs.size] do
      if i != 0 then out := out.push ','
      let (k, x) := kvs[i]
      out := (escapeInto out k).push ':'
      out := compact sortKeys x out
    return out.push '}'

@[inline] private def indent (out : String) (level : Nat) : String :=
  out.pushn ' ' (2 * level)

/-- Pretty rendering (`serde_json::to_string_pretty`, two-space indentation). -/
partial def pretty (sortKeys : Bool) (v : Value) (level : Nat) (out : String) : String :=
  match v with
  | .arr xs =>
    if xs.isEmpty then out ++ "[]"
    else Id.run do
      let mut out := out ++ "[\n"
      for h : i in [0:xs.size] do
        if i != 0 then out := out ++ ",\n"
        out := indent out (level + 1)
        out := pretty sortKeys xs[i] (level + 1) out
      out := out.push '\n'
      out := indent out level
      return out.push ']'
  | .obj kvs =>
    if kvs.isEmpty then out ++ "{}"
    else Id.run do
      let kvs := if sortKeys then sortEntries kvs else kvs
      let mut out := out ++ "{\n"
      for h : i in [0:kvs.size] do
        if i != 0 then out := out ++ ",\n"
        let (k, x) := kvs[i]
        out := indent out (level + 1)
        out := escapeInto out k ++ ": "
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
