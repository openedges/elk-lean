import Elk.Json.Value
/-!
# JSON parser

Strict RFC 8259 parser over the UTF-8 bytes of the input, plus a lenient mode
matching what elk-rs accepts (`preprocess_lenient_json` + the `json5` crate):
`//` and `/* */` comments, single-quoted strings, unquoted identifier keys,
trailing commas, `;` as a separator, leading `+`, `Infinity`/`NaN`, `.5`/`5.`.
-/
namespace Elk.Json

open Elk.Core.Util

structure ParseError where
  pos : Nat
  message : String

instance : ToString ParseError := ⟨fun e => s!"{e.message} at byte {e.pos}"⟩

namespace Parser

structure St where
  bytes : ByteArray
  pos : Nat := 0
  lenient : Bool := false

abbrev M := StateT St (Except ParseError)

@[inline] private def fail {α : Type} (msg : String) : M α := do
  throw { pos := (← get).pos, message := msg }

@[inline] private def peek? : M (Option UInt8) := do
  let s ← get
  return if s.pos < s.bytes.size then some (s.bytes.get! s.pos) else none

@[inline] private def peekAt? (off : Nat) : M (Option UInt8) := do
  let s ← get
  return if s.pos + off < s.bytes.size then some (s.bytes.get! (s.pos + off)) else none

@[inline] private def advance (n : Nat := 1) : M Unit := modify fun s => { s with pos := s.pos + n }

@[inline] private def isLenient : M Bool := do return (← get).lenient

private def b (c : Char) : UInt8 := c.toNat.toUInt8

private def isWs (x : UInt8) : Bool := x == b ' ' || x == b '\t' || x == b '\n' || x == b '\r'

private def isDigit (x : UInt8) : Bool := x >= b '0' && x <= b '9'

private def isIdentStart (x : UInt8) : Bool :=
  (x >= b 'a' && x <= b 'z') || (x >= b 'A' && x <= b 'Z') || x == b '_' || x == b '$'

private def isIdentChar (x : UInt8) : Bool := isIdentStart x || isDigit x

/-- Skips whitespace, and comments in lenient mode. -/
private partial def skipLineComment : M Unit := do
  match ← peek? with
  | some z =>
    if z == b '\n' then pure ()
    else
      advance
      skipLineComment
  | none => pure ()

private partial def skipBlockComment : M Unit := do
  match ← peek? with
  | some z =>
    if z == b '*' && (← peekAt? 1) == some (b '/') then advance 2
    else
      advance
      skipBlockComment
  | none => pure ()

private partial def skipWs : M Unit := do
  match ← peek? with
  | some x =>
    if isWs x then
      advance
      skipWs
    else if x == b '/' && (← isLenient) then
      match ← peekAt? 1 with
      | some y =>
        if y == b '/' then
          advance 2
          skipLineComment
          skipWs
        else if y == b '*' then
          advance 2
          skipBlockComment
          skipWs
        else pure ()
      | none => pure ()
    else pure ()
  | none => pure ()

private def expectByte (c : Char) : M Unit := do
  match ← peek? with
  | some x => if x == b c then advance else fail s!"expected '{c}'"
  | none => fail s!"expected '{c}' but reached end of input"

private def hexVal (x : UInt8) : Option Nat :=
  if isDigit x then some (x.toNat - '0'.toNat)
  else if x >= b 'a' && x <= b 'f' then some (x.toNat - 'a'.toNat + 10)
  else if x >= b 'A' && x <= b 'F' then some (x.toNat - 'A'.toNat + 10)
  else none

private def parseHex4 : M Nat := do
  let mut v := 0
  for _ in [0:4] do
    match ← peek? with
    | some x =>
      match hexVal x with
      | some h =>
        v := v * 16 + h
        advance
      | none => fail "invalid \\u escape"
    | none => fail "unterminated \\u escape"
  return v

private def pushChar (buf : ByteArray) (code : Nat) : ByteArray :=
  buf ++ (String.singleton (Char.ofNat code)).toUTF8

/-- Parses a string literal starting at the opening quote (`"` or, lenient, `'`). -/
private partial def parseStringLit : M String := do
  let some q ← peek? | fail "expected string"
  if q != b '"' && !(q == b '\'' && (← isLenient)) then fail "expected string"
  advance
  let mut buf : ByteArray := ByteArray.empty
  let mut done := false
  while !done do
    match ← peek? with
    | none => fail "unterminated string"
    | some x =>
      if x == q then
        advance
        done := true
      else if x == b '\\' then
        advance
        match ← peek? with
        | none => fail "unterminated escape"
        | some e =>
          advance
          if e == b '"' then buf := buf.push (b '"')
          else if e == b '\\' then buf := buf.push (b '\\')
          else if e == b '/' then buf := buf.push (b '/')
          else if e == b 'b' then buf := buf.push 8
          else if e == b 'f' then buf := buf.push 12
          else if e == b 'n' then buf := buf.push (b '\n')
          else if e == b 'r' then buf := buf.push (b '\r')
          else if e == b 't' then buf := buf.push (b '\t')
          else if e == b 'u' then
            let hi ← parseHex4
            if hi >= 0xD800 && hi <= 0xDBFF then
              -- surrogate pair
              if (← peek?) == some (b '\\') && (← peekAt? 1) == some (b 'u') then
                advance 2
                let lo ← parseHex4
                if lo >= 0xDC00 && lo <= 0xDFFF then
                  buf := pushChar buf (0x10000 + ((hi - 0xD800) <<< 10) + (lo - 0xDC00))
                else
                  buf := pushChar buf 0xFFFD
                  buf := pushChar buf lo
              else buf := pushChar buf 0xFFFD
            else if hi >= 0xDC00 && hi <= 0xDFFF then buf := pushChar buf 0xFFFD
            else buf := pushChar buf hi
          else if (← isLenient) && (e == b '\'' ) then buf := buf.push (b '\'')
          else if (← isLenient) && e == b '\n' then pure ()   -- line continuation
          else fail "invalid escape sequence"
      else if x < 0x20 && !(← isLenient) then fail "control character in string"
      else
        buf := buf.push x
        advance
  match String.fromUTF8? buf with
  | some s => return s
  | none => fail "invalid UTF-8 in string"

/-- Parses a number lexeme. -/
private partial def parseNumber : M Number := do
  let start := (← get).pos
  let lenient ← isLenient
  let mut isFloat := false
  -- sign
  match ← peek? with
  | some x =>
    if x == b '-' then advance
    else if x == b '+' && lenient then advance
  | none => pure ()
  -- lenient Infinity / NaN
  if lenient then
    let s ← get
    let rest := s.bytes.extract s.pos (min s.bytes.size (s.pos + 8))
    if rest.size >= 8 && String.fromUTF8! rest == "Infinity" then
      advance 8
      let neg := s.bytes.get! start == b '-'
      return .float (if neg then Float.negInf else Float.posInf)
    if rest.size >= 3 && String.fromUTF8! (rest.extract 0 3) == "NaN" then
      advance 3
      return .float Float.nan
  -- integer part (a leading zero may not be followed by more digits)
  let mut intDigits := 0
  if (← peek?) == some (b '0') && (← peekAt? 1).any isDigit then fail "invalid number: leading zero"
  while (← peek?).any isDigit do
    advance
    intDigits := intDigits + 1
  -- fraction
  if (← peek?) == some (b '.') then
    let next ← peekAt? 1
    if next.any isDigit || (lenient && intDigits > 0) then
      isFloat := true
      advance
      while (← peek?).any isDigit do advance
    else if intDigits == 0 then fail "invalid number"
    else fail "invalid number"
  if intDigits == 0 && !isFloat then fail "invalid number"
  -- exponent
  match ← peek? with
  | some x =>
    if x == b 'e' || x == b 'E' then
      isFloat := true
      advance
      match ← peek? with
      | some y =>
        if y == b '+' || y == b '-' then advance
      | none => pure ()
      let mut expDigits := 0
      while (← peek?).any isDigit do
        advance
        expDigits := expDigits + 1
      if expDigits == 0 then fail "invalid exponent"
  | none => pure ()
  let s ← get
  let lexeme := String.fromUTF8! (s.bytes.extract start s.pos)
  let lexeme := if lexeme.startsWith "+" then (lexeme.drop 1).toString else lexeme
  if isFloat then
    return .float (strtodUnchecked lexeme)
  else
    match parseInt64? lexeme with
    | some i => return .int i
    | none =>
      -- out of i64 range: serde parses as u64 or f64
      let digits := if lexeme.startsWith "-" then (lexeme.drop 1).toString else lexeme
      match digits.toNat? with
      | some n => if !lexeme.startsWith "-" && n <= 18446744073709551615 then return .int n else return .float (strtodUnchecked lexeme)
      | none => fail "invalid number"

private def parseIdent : M String := do
  let start := (← get).pos
  while (← peek?).any isIdentChar do advance
  let s ← get
  if s.pos == start then fail "expected identifier"
  return String.fromUTF8! (s.bytes.extract start s.pos)

private def matchLiteral (lit : String) : M Bool := do
  let s ← get
  let bs := lit.toUTF8
  if s.pos + bs.size <= s.bytes.size && s.bytes.extract s.pos (s.pos + bs.size) == bs then
    -- must not be followed by an identifier character
    let next := if s.pos + bs.size < s.bytes.size then some (s.bytes.get! (s.pos + bs.size)) else none
    if next.any isIdentChar then return false
    advance bs.size
    return true
  else return false

mutual

partial def parseValue : M Value := do
  skipWs
  match ← peek? with
  | none => fail "unexpected end of input"
  | some x =>
    if x == b '{' then parseObject
    else if x == b '[' then parseArray
    else if x == b '"' then return .str (← parseStringLit)
    else if x == b '\'' && (← isLenient) then return .str (← parseStringLit)
    else if x == b '-' || x == b '+' || x == b '.' || isDigit x then return .num (← parseNumber)
    else if ← matchLiteral "true" then return .bool true
    else if ← matchLiteral "false" then return .bool false
    else if ← matchLiteral "null" then return .null
    else if (← isLenient) && (x == b 'I' || x == b 'N') then return .num (← parseNumber)
    else fail "unexpected character"

partial def parseArray : M Value := do
  expectByte '['
  let mut xs : Array Value := #[]
  skipWs
  if (← peek?) == some (b ']') then
    advance
    return .arr xs
  let mut done := false
  while !done do
    xs := xs.push (← parseValue)
    skipWs
    match ← peek? with
    | some x =>
      if x == b ',' || (x == b ';' && (← isLenient)) then
        advance
        skipWs
        if (← isLenient) && (← peek?) == some (b ']') then
          advance
          done := true
      else if x == b ']' then
        advance
        done := true
      else fail "expected ',' or ']'"
    | none => fail "unterminated array"
  return .arr xs

partial def parseObject : M Value := do
  expectByte '{'
  let mut kvs : Array (String × Value) := #[]
  skipWs
  if (← peek?) == some (b '}') then
    advance
    return .obj kvs
  let mut done := false
  while !done do
    skipWs
    let key ← match ← peek? with
      | some x =>
        if x == b '"' then parseStringLit
        else if (← isLenient) && x == b '\'' then parseStringLit
        else if (← isLenient) && isIdentStart x then parseIdent
        else fail "expected object key"
      | none => fail "unterminated object"
    skipWs
    expectByte ':'
    let v ← parseValue
    kvs := kvs.push (key, v)
    skipWs
    match ← peek? with
    | some x =>
      if x == b ',' || (x == b ';' && (← isLenient)) then
        advance
        skipWs
        if (← isLenient) && (← peek?) == some (b '}') then
          advance
          done := true
      else if x == b '}' then
        advance
        done := true
      else fail "expected ',' or '}'"
    | none => fail "unterminated object"
  return .obj kvs

end

/-- Parses a complete document; trailing content (other than whitespace/comments) is an error. -/
def parseDocument : M Value := do
  let v ← parseValue
  skipWs
  if (← peek?).isSome then fail "trailing characters"
  return v

end Parser

/-- Parses a JSON document. -/
def parse (text : String) (lenient : Bool := false) : Except ParseError Value :=
  match (Parser.parseDocument).run { bytes := text.toUTF8, lenient := lenient } with
  | .ok (v, _) => .ok v
  | .error e => .error e

/-- `parse` with the error rendered as a string. -/
def parseString (text : String) (lenient : Bool := false) : Except String Value :=
  match parse text lenient with
  | .ok v => .ok v
  | .error e => .error (toString e)

end Elk.Json
