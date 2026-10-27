import Elk.Json.Value
/-!
# JSON parser

Strict RFC 8259 parser over the UTF-8 bytes of the input, plus a lenient mode
matching what elk-rs accepts (`preprocess_lenient_json` + the `json5` crate):
`//` and `/* */` comments, single-quoted strings, unquoted identifier keys,
trailing commas, `;` as a separator, leading `+`, `Infinity`/`NaN`, `.5`/`5.`.

Implementation: recursive descent over the byte array with the position threaded explicitly.
Byte scanning (whitespace, comments, string bodies, digits) runs in tail-recursive functions on
`(bytes, position)`, so it allocates nothing; every parsed value costs one `PR` result object.
Strings without escapes are sliced out of the input in one step. Error messages and the byte
positions they report are those of the previous `StateT` parser (kept as a test reference in
`tests/lean/Tests/Json/ParserReference.lean`, compared by `Tests.Json.ParserFuzz`).
-/
namespace Elk.Json

open Elk.Core.Util

structure ParseError where
  pos : Nat
  message : String

instance : ToString ParseError := ⟨fun e => s!"{e.message} at byte {e.pos}"⟩

namespace Parser

/-- A parse result: the value and the position after it, or an error. One allocation. -/
inductive PR (α : Type) where
  | ok (v : α) (pos : Nat)
  | err (e : ParseError)

instance {α : Type} : Inhabited (PR α) := ⟨.err { pos := 0, message := "" }⟩

@[inline] private def fail {α : Type} (pos : Nat) (msg : String) : PR α := .err { pos, message := msg }

/-! Byte classes (ASCII codes as `UInt8` literals: `' '` 32, `'\t'` 9, `'\n'` 10, `'\r'` 13, …). -/

@[inline] private def isWs (x : UInt8) : Bool := x == 32 || x == 9 || x == 10 || x == 13

@[inline] private def isDigit (x : UInt8) : Bool := x >= 48 && x <= 57

@[inline] private def isIdentStart (x : UInt8) : Bool :=
  (x >= 97 && x <= 122) || (x >= 65 && x <= 90) || x == 95 || x == 36

@[inline] private def isIdentChar (x : UInt8) : Bool := isIdentStart x || isDigit x

/-- The byte at `i`, or `0` past the end (callers test `i < bs.size` where `0` would be ambiguous). -/
@[inline] private def byteAt (bs : ByteArray) (i : Nat) : UInt8 :=
  if h : i < bs.size then bs[i] else 0

/-- Whether position `i` holds byte `c`. -/
@[inline] private def isAt (bs : ByteArray) (i : Nat) (c : UInt8) : Bool :=
  i < bs.size && byteAt bs i == c

/-! ## Whitespace and comments -/

/-- `//` comment body: up to (not including) the next `\n`. -/
private partial def skipLineComment (bs : ByteArray) (i : Nat) : Nat :=
  if i < bs.size then
    if byteAt bs i == 10 then i else skipLineComment bs (i + 1)
  else i

/-- `/* */` comment body: past the next `*/` (or to the end). -/
private partial def skipBlockComment (bs : ByteArray) (i : Nat) : Nat :=
  if i < bs.size then
    if byteAt bs i == 42 && isAt bs (i + 1) 47 then i + 2 else skipBlockComment bs (i + 1)
  else i

/-- Skips whitespace, and comments in lenient mode. -/
private partial def skipWs (bs : ByteArray) (lenient : Bool) (i : Nat) : Nat :=
  if i < bs.size then
    let x := byteAt bs i
    if isWs x then skipWs bs lenient (i + 1)
    else if x == 47 && lenient && i + 1 < bs.size then
      let y := byteAt bs (i + 1)
      if y == 47 then skipWs bs lenient (skipLineComment bs (i + 2))
      else if y == 42 then skipWs bs lenient (skipBlockComment bs (i + 2))
      else i
    else i
  else i

/-- `expected 'c'` at `i`. -/
@[inline] private def expectByte (bs : ByteArray) (i : Nat) (c : UInt8) (ch : Char) : PR Unit :=
  if i < bs.size then
    if byteAt bs i == c then .ok () (i + 1) else fail i s!"expected '{ch}'"
  else fail i s!"expected '{ch}' but reached end of input"

/-! ## Strings -/

private def hexVal (x : UInt8) : Option Nat :=
  if isDigit x then some (x.toNat - 48)
  else if x >= 97 && x <= 102 then some (x.toNat - 87)
  else if x >= 65 && x <= 70 then some (x.toNat - 55)
  else none

/-- Four hex digits from `i`. -/
private def parseHex4 (bs : ByteArray) (i : Nat) : PR Nat := Id.run do
  let mut v := 0
  let mut p := i
  for _ in [0:4] do
    if p < bs.size then
      match hexVal (byteAt bs p) with
      | some h =>
        v := v * 16 + h
        p := p + 1
      | none => return fail p "invalid \\u escape"
    else return fail p "unterminated \\u escape"
  return .ok v p

private def pushChar (buf : ByteArray) (code : Nat) : ByteArray :=
  buf ++ (String.singleton (Char.ofNat code)).toUTF8

/-- Fast scan of a string body from `i`: the index of the closing quote `q` when the body has no
escape and (in strict mode) no control character; `none` when the general loop must decide. -/
private partial def scanPlainString (bs : ByteArray) (q : UInt8) (lenient : Bool) (i : Nat) : Option Nat :=
  if i < bs.size then
    let x := byteAt bs i
    if x == q then some i
    else if x == 92 then none
    else if x < 32 && !lenient then none
    else scanPlainString bs q lenient (i + 1)
  else none

/-- The general string loop (escapes, errors) from position `i` with the decoded bytes `buf`. -/
private partial def parseStringBody (bs : ByteArray) (q : UInt8) (lenient : Bool) (i : Nat)
    (buf : ByteArray) : PR ByteArray :=
  if i >= bs.size then fail i "unterminated string"
  else
    let x := byteAt bs i
    if x == q then .ok buf (i + 1)
    else if x == 92 then
      let i := i + 1
      if i >= bs.size then fail i "unterminated escape"
      else
        let e := byteAt bs i
        let i := i + 1
        if e == 34 then parseStringBody bs q lenient i (buf.push 34)
        else if e == 92 then parseStringBody bs q lenient i (buf.push 92)
        else if e == 47 then parseStringBody bs q lenient i (buf.push 47)
        else if e == 98 then parseStringBody bs q lenient i (buf.push 8)
        else if e == 102 then parseStringBody bs q lenient i (buf.push 12)
        else if e == 110 then parseStringBody bs q lenient i (buf.push 10)
        else if e == 114 then parseStringBody bs q lenient i (buf.push 13)
        else if e == 116 then parseStringBody bs q lenient i (buf.push 9)
        else if e == 117 then
          match parseHex4 bs i with
          | .err err => .err err
          | .ok hi i =>
            if hi >= 0xD800 && hi <= 0xDBFF then
              -- surrogate pair
              if isAt bs i 92 && isAt bs (i + 1) 117 then
                match parseHex4 bs (i + 2) with
                | .err err => .err err
                | .ok lo i =>
                  if lo >= 0xDC00 && lo <= 0xDFFF then
                    parseStringBody bs q lenient i (pushChar buf (0x10000 + ((hi - 0xD800) <<< 10) + (lo - 0xDC00)))
                  else
                    parseStringBody bs q lenient i (pushChar (pushChar buf 0xFFFD) lo)
              else parseStringBody bs q lenient i (pushChar buf 0xFFFD)
            else if hi >= 0xDC00 && hi <= 0xDFFF then parseStringBody bs q lenient i (pushChar buf 0xFFFD)
            else parseStringBody bs q lenient i (pushChar buf hi)
        else if lenient && e == 39 then parseStringBody bs q lenient i (buf.push 39)
        else if lenient && e == 10 then parseStringBody bs q lenient i buf   -- line continuation
        else fail i "invalid escape sequence"
    else if x < 32 && !lenient then fail i "control character in string"
    else parseStringBody bs q lenient (i + 1) (buf.push x)

/-- Parses a string literal starting at the opening quote (`"` or, lenient, `'`). -/
private def parseStringLit (bs : ByteArray) (lenient : Bool) (i : Nat) : PR String :=
  if i >= bs.size then fail i "expected string"
  else
    let q := byteAt bs i
    if q != 34 && !(q == 39 && lenient) then fail i "expected string"
    else
      let body := i + 1
      match scanPlainString bs q lenient body with
      | some close =>
        match String.fromUTF8? (bs.extract body close) with
        | some s => .ok s (close + 1)
        | none => fail (close + 1) "invalid UTF-8 in string"
      | none =>
        match parseStringBody bs q lenient body ByteArray.empty with
        | .err e => .err e
        | .ok buf i =>
          match String.fromUTF8? buf with
          | some s => .ok s i
          | none => fail i "invalid UTF-8 in string"

/-! ## Numbers -/

/-- Index of the first non-digit from `i`. -/
private partial def skipDigits (bs : ByteArray) (i : Nat) : Nat :=
  if i < bs.size && isDigit (byteAt bs i) then skipDigits bs (i + 1) else i

/-- Value of the decimal digits `bs[i:j]` (at most 18 digits, so it fits an `i64`). -/
private partial def digitsValue (bs : ByteArray) (i j : Nat) (acc : Nat) : Nat :=
  if i < j then digitsValue bs (i + 1) j (acc * 10 + (byteAt bs i - 48).toNat) else acc

/-- Whether `bs[i:]` starts with the bytes of `lit`. -/
private partial def startsWithAt (bs : ByteArray) (i : Nat) (lit : ByteArray) (k : Nat) : Bool :=
  if k < lit.size then
    i + k < bs.size && byteAt bs (i + k) == byteAt lit k && startsWithAt bs i lit (k + 1)
  else true

/-- Parses a number lexeme starting at `start`. Values follow ELK Java's JSON input (Gson numbers read
with `Double.parseDouble`): floats are correctly rounded (`strtod`), integers stay exact, and `-0` is
`-0.0` (what Java computes with). elk-rs' serde_json, which reads long mantissas with two roundings,
is not followed: the result reference is ELK Java. -/
private def parseNumber (bs : ByteArray) (lenient : Bool) (start : Nat) : PR Number := Id.run do
  let mut pos := start
  -- sign
  if pos < bs.size then
    let x := byteAt bs pos
    if x == 45 then pos := pos + 1
    else if x == 43 && lenient then pos := pos + 1
  -- lenient Infinity / NaN
  if lenient then
    if pos + 8 <= bs.size && startsWithAt bs pos "Infinity".toUTF8 0 then
      let neg := byteAt bs start == 45
      return .ok (.float (if neg then Float.negInf else Float.posInf)) (pos + 8)
    if pos + 3 <= bs.size && startsWithAt bs pos "NaN".toUTF8 0 then
      return .ok (.float Float.nan) (pos + 3)
  -- integer part (a leading zero may not be followed by more digits)
  if isAt bs pos 48 && pos + 1 < bs.size && isDigit (byteAt bs (pos + 1)) then
    return fail pos "invalid number: leading zero"
  let intStart := pos
  pos := skipDigits bs pos
  let intDigits := pos - intStart
  let mut isFloat := false
  -- fraction
  if isAt bs pos 46 then
    let nextIsDigit := pos + 1 < bs.size && isDigit (byteAt bs (pos + 1))
    if nextIsDigit || (lenient && intDigits > 0) then
      isFloat := true
      pos := skipDigits bs (pos + 1)
    else return fail pos "invalid number"
  if intDigits == 0 && !isFloat then return fail pos "invalid number"
  -- exponent
  if pos < bs.size then
    let x := byteAt bs pos
    if x == 101 || x == 69 then
      isFloat := true
      pos := pos + 1
      if pos < bs.size then
        let y := byteAt bs pos
        if y == 43 || y == 45 then pos := pos + 1
      let expStart := pos
      pos := skipDigits bs pos
      if pos == expStart then return fail pos "invalid exponent"
  let neg := byteAt bs start == 45
  -- plain integers of at most 18 digits (always within `i64`) without building the lexeme
  if !isFloat && intDigits <= 18 then
    let v := digitsValue bs intStart pos 0
    if neg && v == 0 then return .ok (.float (-0.0)) pos
    return .ok (.int (if neg then -(v : Int) else (v : Int))) pos
  let lexeme := String.fromUTF8! (bs.extract start pos)
  let lexeme := if lexeme.startsWith "+" then (lexeme.drop 1).toString else lexeme
  if isFloat then
    return .ok (.float (strtodUnchecked lexeme)) pos
  else
    match parseInt64? lexeme with
    | some i => return .ok (.int i) pos
    | none =>
      -- out of i64 range: parsed as u64 or f64
      let digits := if lexeme.startsWith "-" then (lexeme.drop 1).toString else lexeme
      match digits.toNat? with
      | some n =>
        if !lexeme.startsWith "-" && n <= 18446744073709551615 then return .ok (.int n) pos
        else return .ok (.float (strtodUnchecked lexeme)) pos
      | none => return fail pos "invalid number"

/-! ## Identifiers and literals -/

/-- Index of the first non-identifier byte from `i`. -/
private partial def skipIdent (bs : ByteArray) (i : Nat) : Nat :=
  if i < bs.size && isIdentChar (byteAt bs i) then skipIdent bs (i + 1) else i

/-- An unquoted (lenient) key. -/
private def parseIdent (bs : ByteArray) (i : Nat) : PR String :=
  let j := skipIdent bs i
  if j == i then fail i "expected identifier"
  else .ok (String.fromUTF8! (bs.extract i j)) j

/-- Position after the keyword `lit` at `i` when it is not followed by an identifier character. -/
private def matchLiteral (bs : ByteArray) (i : Nat) (lit : ByteArray) : Option Nat :=
  let j := i + lit.size
  if j <= bs.size && startsWithAt bs i lit 0 then
    if j < bs.size && isIdentChar (byteAt bs j) then none else some j
  else none

/-! ## Values -/

mutual

/-- A value at `i` (after optional whitespace). -/
partial def parseValue (bs : ByteArray) (lenient : Bool) (i : Nat) : PR Value :=
  let i := skipWs bs lenient i
  if i >= bs.size then fail i "unexpected end of input"
  else
    let x := byteAt bs i
    if x == 123 then parseObject bs lenient i
    else if x == 91 then parseArray bs lenient i
    else if x == 34 || (x == 39 && lenient) then
      match parseStringLit bs lenient i with
      | .ok s j => .ok (.str s) j
      | .err e => .err e
    else if x == 45 || x == 43 || x == 46 || isDigit x then
      match parseNumber bs lenient i with
      | .ok n j => .ok (.num n) j
      | .err e => .err e
    else
      match matchLiteral bs i "true".toUTF8 with
      | some j => .ok (.bool true) j
      | none =>
      match matchLiteral bs i "false".toUTF8 with
      | some j => .ok (.bool false) j
      | none =>
      match matchLiteral bs i "null".toUTF8 with
      | some j => .ok .null j
      | none =>
        if lenient && (x == 73 || x == 78) then
          match parseNumber bs lenient i with
          | .ok n j => .ok (.num n) j
          | .err e => .err e
        else fail i "unexpected character"

/-- An array at `i` (the `[`). -/
partial def parseArray (bs : ByteArray) (lenient : Bool) (i : Nat) : PR Value :=
  -- the caller checked the opening bracket
  let i := skipWs bs lenient (i + 1)
  if isAt bs i 93 then .ok (.arr #[]) (i + 1)
  else parseArrayItems bs lenient i #[]

/-- Array elements from `i` (an element is expected). -/
partial def parseArrayItems (bs : ByteArray) (lenient : Bool) (i : Nat) (xs : Array Value) : PR Value :=
  match parseValue bs lenient i with
  | .err e => .err e
  | .ok v i =>
    let xs := xs.push v
    let i := skipWs bs lenient i
    if i < bs.size then
      let x := byteAt bs i
      if x == 44 || (x == 59 && lenient) then
        let i := skipWs bs lenient (i + 1)
        if lenient && isAt bs i 93 then .ok (.arr xs) (i + 1)
        else parseArrayItems bs lenient i xs
      else if x == 93 then .ok (.arr xs) (i + 1)
      else fail i "expected ',' or ']'"
    else fail i "unterminated array"

/-- An object at `i` (the `{`). -/
partial def parseObject (bs : ByteArray) (lenient : Bool) (i : Nat) : PR Value :=
  -- the caller checked the opening brace
  let i := skipWs bs lenient (i + 1)
  if isAt bs i 125 then .ok (.obj #[]) (i + 1)
  else parseObjectMembers bs lenient i #[]

/-- Object members from `i` (a key is expected after optional whitespace). -/
partial def parseObjectMembers (bs : ByteArray) (lenient : Bool) (i : Nat) (kvs : Array (String × Value)) :
    PR Value :=
  let i := skipWs bs lenient i
  let key : PR String :=
    if i < bs.size then
      let x := byteAt bs i
      if x == 34 then parseStringLit bs lenient i
      else if lenient && x == 39 then parseStringLit bs lenient i
      else if lenient && isIdentStart x then parseIdent bs i
      else fail i "expected object key"
    else fail i "unterminated object"
  match key with
  | .err e => .err e
  | .ok key i =>
    let i := skipWs bs lenient i
    match expectByte bs i 58 ':' with
    | .err e => .err e
    | .ok () i =>
      match parseValue bs lenient i with
      | .err e => .err e
      | .ok v i =>
        let kvs := kvs.push (key, v)
        let i := skipWs bs lenient i
        if i < bs.size then
          let x := byteAt bs i
          if x == 44 || (x == 59 && lenient) then
            let i := skipWs bs lenient (i + 1)
            if lenient && isAt bs i 125 then .ok (.obj kvs) (i + 1)
            else parseObjectMembers bs lenient i kvs
          else if x == 125 then .ok (.obj kvs) (i + 1)
          else fail i "expected ',' or '}'"
        else fail i "unterminated object"

end

/-- The strict-mode value of a complete number lexeme, `none` when the lexeme is not a strict JSON
number. Used by tests. -/
def strictNumber? (lexeme : String) : Option Number :=
  let bs := lexeme.toUTF8
  if bs.size == 0 then none
  else match parseNumber bs false 0 with
    | .ok n i => if i == bs.size then some n else none
    | .err _ => none

/-- Parses a complete document; trailing content (other than whitespace/comments) is an error. -/
def parseDocument (bs : ByteArray) (lenient : Bool) : PR Value :=
  match parseValue bs lenient 0 with
  | .err e => .err e
  | .ok v i =>
    let i := skipWs bs lenient i
    if i < bs.size then fail i "trailing characters" else .ok v i

end Parser

/-- Parses a JSON document. -/
def parse (text : String) (lenient : Bool := false) : Except ParseError Value :=
  match Parser.parseDocument text.toUTF8 lenient with
  | .ok v _ => .ok v
  | .err e => .error e

/-- `parse` with the error rendered as a string. -/
def parseString (text : String) (lenient : Bool := false) : Except String Value :=
  match parse text lenient with
  | .ok v => .ok v
  | .error e => .error (toString e)

end Elk.Json
