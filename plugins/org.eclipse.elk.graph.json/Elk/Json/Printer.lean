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
private partial def hasEscapes (s : String) (n : USize) (hn : n = Utf8.usize s) (i : USize) : Bool :=
  if h : i < n then
    let b := Utf8.uget s i (hn ▸ h)
    if b < 0x20 || b == 0x22 || b == 0x5c then true else hasEscapes s n hn (i + 1)
  else
    false

/-- Appends `pre`, `s` with serde_json escaping and `post` to `out`: `pre`/`post` carry the quotes
and the punctuation around the literal, so a plain string costs three appends. -/
@[inline] private def appendQuoted (out pre s post : String) : String :=
  if hasEscapes s (Utf8.usize s) rfl 0 then s.foldl pushEscaped (out ++ pre) ++ post
  else out ++ pre ++ s ++ post

/-- Appends `s` as a JSON string literal (serde_json escaping) to `out`. -/
def escapeInto (out s : String) : String := appendQuoted out "\"" s "\""

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

mutual

/-- Compact rendering (`serde_json::to_string`). The element loops are plain tail recursions (a
`for` over `[0:n]` allocates its range object). -/
partial def compact (sortKeys : Bool) (v : Value) (out : String) : String :=
  match v with
  | .null => out ++ "null"
  | .bool b => out ++ (if b then "true" else "false")
  | .num n => pushNumber out n
  | .str s => escapeInto out s
  | .arr xs => compactItems sortKeys xs 0 (out ++ "[") ++ "]"
  | .obj kvs =>
    let kvs := if sortKeys then sortEntries kvs else kvs
    compactMembers sortKeys kvs 0 (out ++ "{") ++ "}"

/-- `compact` of the elements `xs[i:]`, comma separated. -/
partial def compactItems (sortKeys : Bool) (xs : Array Value) (i : Nat) (out : String) : String :=
  if h : i < xs.size then
    let out := if i != 0 then out ++ "," else out
    compactItems sortKeys xs (i + 1) (compact sortKeys xs[i] out)
  else out

/-- `compact` of the members `kvs[i:]`, comma separated. -/
partial def compactMembers (sortKeys : Bool) (kvs : Array (String × Value)) (i : Nat) (out : String) : String :=
  if h : i < kvs.size then
    let kv := kvs[i]
    let out := appendQuoted out (if i == 0 then "\"" else ",\"") kv.1 "\":"
    compactMembers sortKeys kvs (i + 1) (compact sortKeys kv.2 out)
  else out

end

/-- `"\n"` followed by the indentation of levels `0 … 31` (two spaces per level). -/
private def nlIndents : Array String := (Array.range 32).map fun l => "\n".pushn ' ' (2 * l)

/-- A line break and the indentation of `level`. -/
@[inline] private def nlIndent (level : Nat) : String :=
  if h : level < nlIndents.size then nlIndents[level] else "\n".pushn ' ' (2 * level)

mutual

/-- Pretty rendering (`serde_json::to_string_pretty`, two-space indentation). -/
partial def pretty (sortKeys : Bool) (v : Value) (level : Nat) (out : String) : String :=
  match v with
  | .arr xs =>
    if xs.isEmpty then out ++ "[]"
    else prettyItems sortKeys xs (level + 1) (nlIndent (level + 1)) 0 (out ++ "[") ++ nlIndent level ++ "]"
  | .obj kvs =>
    if kvs.isEmpty then out ++ "{}"
    else
      let kvs := if sortKeys then sortEntries kvs else kvs
      prettyMembers sortKeys kvs (level + 1) (nlIndent (level + 1)) 0 (out ++ "{") ++ nlIndent level ++ "}"
  | other => compact sortKeys other out

/-- `pretty` of the elements `xs[i:]` at `level`, each on its own line (`inner` is `nlIndent level`). -/
partial def prettyItems (sortKeys : Bool) (xs : Array Value) (level : Nat) (inner : String) (i : Nat)
    (out : String) : String :=
  if h : i < xs.size then
    let out := (if i != 0 then out ++ "," else out) ++ inner
    prettyItems sortKeys xs level inner (i + 1) (pretty sortKeys xs[i] level out)
  else out

/-- `pretty` of the members `kvs[i:]` at `level`, each on its own line. -/
partial def prettyMembers (sortKeys : Bool) (kvs : Array (String × Value)) (level : Nat) (inner : String)
    (i : Nat) (out : String) : String :=
  if h : i < kvs.size then
    let kv := kvs[i]
    let out := (if i != 0 then out ++ "," else out) ++ inner
    let out := appendQuoted out "\"" kv.1 "\": "
    prettyMembers sortKeys kvs level inner (i + 1) (pretty sortKeys kv.2 level out)
  else out

end

end Printer

namespace Value

/-- `serde_json::to_string`. -/
def render (v : Value) (sortKeys : Bool := false) : String := Printer.compact sortKeys v ""

/-- `serde_json::to_string_pretty`. -/
def renderPretty (v : Value) (sortKeys : Bool := false) : String := Printer.pretty sortKeys v 0 ""

instance : ToString Value := ⟨fun v => v.render⟩

end Value

end Elk.Json
