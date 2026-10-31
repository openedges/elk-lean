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

/-! The ELK member names (`Key.all`) rendered with their quotes and punctuation, so writing such a
key is one append (no escape scan). -/

/-- `"key":` (first member, compact). -/
private def compactKeysFirst : Array String := Key.all.map fun k => "\"" ++ k ++ "\":"
/-- `,"key":` (later members, compact). -/
private def compactKeysNext : Array String := Key.all.map fun k => ",\"" ++ k ++ "\":"
/-- `"key": ` (pretty). -/
private def prettyKeys : Array String := Key.all.map fun k => "\"" ++ k ++ "\": "

/-- Appends the key `k` between `pre` and `post` (`appendQuoted`), from `lits` (`pre ++ k ++ post`
for each `Key.all` entry) when `k` is one of the ELK member names (the parser shares their objects,
so the equality test is usually a pointer comparison). -/
@[inline] private def appendKey (out : String) (lits : Array String) (pre k post : String) : String :=
  let j := Key.candidateIndex k 0 k.utf8ByteSize
  if h : j < lits.size then
    if k == Key.all.getD j "" then out ++ lits[j] else appendQuoted out pre k post
  else appendQuoted out pre k post

/-- serde_json string escaping. -/
def escapeString (s : String) : String := escapeInto "" s

private def sortEntries (kvs : Array (String × Value)) : Array (String × Value) :=
  Elk.Core.Util.stableSort kvs (fun a b => compare a.1 b.1)

/-- `"0"` … `"99"`. -/
private def smallNats : Array String := (Array.range 100).map toString

/-- `"00"` … `"99"`. -/
private def digitPairs : Array String := (Array.range 100).map fun n => if n < 10 then "0" ++ toString n else toString n

/-- Appends the decimal representation of `n` (`Nat.repr` without the intermediate string), two
digits per append. -/
private def pushNat (out : String) (n : Nat) : String :=
  if n < 100 then out ++ smallNats.getD n ""
  else pushNat out (n / 100) ++ digitPairs.getD (n % 100) ""
termination_by n
decreasing_by omega

/-- Appends `n.render`; integers and doubles are written in place (no temporary string). -/
@[inline] private def pushNumber (out : String) (n : Number) : String :=
  match n with
  | .int (.ofNat k) => pushNat out k
  | .int (.negSucc k) => pushNat (out ++ "-") (k + 1)
  | .float f => appendJsonFloat out f

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
    let out := if i == 0 then appendKey out compactKeysFirst "\"" kv.1 "\":"
      else appendKey out compactKeysNext ",\"" kv.1 "\":"
    compactMembers sortKeys kvs (i + 1) (compact sortKeys kv.2 out)
  else out

end

/-- `pre ++ "\n"`, the indentation of a level (two spaces each) and `post`. -/
private def indentLit (pre post : String) (level : Nat) : String := (pre ++ "\n").pushn ' ' (2 * level) ++ post

/-- `indentLit pre post` for the levels `0 … 31`. -/
private def indentTable (pre post : String) : Array String := (Array.range 32).map (indentLit pre post)

/-! Line breaks with their indentation and punctuation, one append each. -/
private def openObjs : Array String := indentTable "{" ""
private def openArrs : Array String := indentTable "[" ""
private def closeObjs : Array String := indentTable "" "}"
private def closeArrs : Array String := indentTable "" "]"
private def commaLines : Array String := indentTable "," ""

/-- Entry `level` of a table built by `indentTable pre post`. -/
@[inline] private def indentOf (t : Array String) (pre post : String) (level : Nat) : String :=
  if h : level < t.size then t[level] else indentLit pre post level

mutual

/-- Pretty rendering (`serde_json::to_string_pretty`, two-space indentation). -/
partial def pretty (sortKeys : Bool) (v : Value) (level : Nat) (out : String) : String :=
  match v with
  | .arr xs =>
    if xs.isEmpty then out ++ "[]"
    else
      let out := prettyItems sortKeys xs (level + 1) (indentOf commaLines "," "" (level + 1)) 0
        (out ++ indentOf openArrs "[" "" (level + 1))
      out ++ indentOf closeArrs "" "]" level
  | .obj kvs =>
    if kvs.isEmpty then out ++ "{}"
    else
      let kvs := if sortKeys then sortEntries kvs else kvs
      let out := prettyMembers sortKeys kvs (level + 1) (indentOf commaLines "," "" (level + 1)) 0
        (out ++ indentOf openObjs "{" "" (level + 1))
      out ++ indentOf closeObjs "" "}" level
  | other => compact sortKeys other out

/-- `pretty` of the elements `xs[i:]` at `level`, each on its own line (`sep` is `,` and the line
break with the indentation of `level`; the caller wrote the first line break). -/
partial def prettyItems (sortKeys : Bool) (xs : Array Value) (level : Nat) (sep : String) (i : Nat)
    (out : String) : String :=
  if h : i < xs.size then
    let out := if i != 0 then out ++ sep else out
    prettyItems sortKeys xs level sep (i + 1) (pretty sortKeys xs[i] level out)
  else out

/-- `pretty` of the members `kvs[i:]` at `level`, each on its own line. -/
partial def prettyMembers (sortKeys : Bool) (kvs : Array (String × Value)) (level : Nat) (sep : String)
    (i : Nat) (out : String) : String :=
  if h : i < kvs.size then
    let kv := kvs[i]
    let out := if i != 0 then out ++ sep else out
    let out := appendKey out prettyKeys "\"" kv.1 "\": "
    prettyMembers sortKeys kvs level sep (i + 1) (pretty sortKeys kv.2 level out)
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
