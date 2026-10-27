/-!
# `.elkt` lexer (`org.eclipse.elk.graph.text`, `ElkGraph.xtext` terminals)

Tokeniser for the ELK Text format. It reproduces the ANTLR lexer that Xtext
generates for `ElkGraph.xtext` (`InternalElkGraphLexer`):

* keywords `graph node layout position size port label edge incoming outgoing
  start end bends section true false null` and the punctuation
  `[ ] : , { } -> | .`; keywords win over `ID` when both match the same text;
* `ID` is `'^'? [a-zA-Z_] [a-zA-Z_0-9]*` (the `^` escape lets keywords be used
  as identifiers; it is stripped from the token value);
* `SIGNED_INT` is `('+'|'-')? [0-9]+`, `FLOAT` is
  `('+'|'-')? ([0-9]+ '.' [0-9]+ | [0-9]+ ('.' [0-9]+)? [eE] ('+'|'-')? [0-9]+)`
  (longest match wins);
* `STRING` is a single- or double-quoted string with `\` escapes (the token
  keeps the raw text including the quotes);
* `/* ... */` and `// ...` comments and white space are skipped; every other
  character becomes a `Tok.other` token, which makes the parser fail (the
  `ANY_OTHER` terminal of `org.eclipse.xtext.common.Terminals`).

Every token records its line/column (1-based) and its character range so the
parser can check adjacency (`PropertyKey returns IProperty hidden()` forbids
white space inside property keys).
-/
namespace Elk.Text

/-- Token kinds of the ELK Text lexer. -/
inductive Tok where
  /-- A keyword or punctuation token (`node`, `->`, `{`, ...). -/
  | kw (s : String)
  /-- `ID`: `value` has the `^` escape removed, `raw` is the source text. -/
  | id (value : String) (raw : String)
  /-- `STRING`: the raw source text including the quotes. -/
  | str (raw : String)
  /-- `SIGNED_INT` token text. -/
  | int (s : String)
  /-- `FLOAT` token text. -/
  | float (s : String)
  /-- `ANY_OTHER`: a character no rule accepts. -/
  | other (c : Char)
  /-- End of input. -/
  | eof
  deriving BEq, Repr, Inhabited

/-- A lexed token with its source position. -/
structure Token where
  tok : Tok
  /-- Source text of the token (used in error messages). -/
  text : String
  line : Nat
  col : Nat
  /-- Character offset of the first character. -/
  start : Nat
  /-- Character offset after the last character. -/
  stop : Nat
  deriving Repr, Inhabited

/-- Keywords of `ElkGraph.xtext` that are made of letters. -/
def wordKeywords : Array String :=
  #["graph", "node", "layout", "position", "size", "port", "label", "edge", "incoming",
    "outgoing", "start", "end", "bends", "section", "true", "false", "null"]

private structure LexState where
  pos : Nat := 0
  line : Nat := 1
  col : Nat := 1

private def LexState.step (cs : Array Char) (s : LexState) : LexState :=
  if s.pos < cs.size then
    if cs[s.pos]! == '\n' then { pos := s.pos + 1, line := s.line + 1, col := 1 }
    else { s with pos := s.pos + 1, col := s.col + 1 }
  else s

private def LexState.stepTo (cs : Array Char) (s : LexState) (target : Nat) : LexState := Id.run do
  let mut s := s
  while s.pos < target && s.pos < cs.size do
    s := s.step cs
  return s

private def isDigit (c : Char) : Bool := c >= '0' && c <= '9'

private def isIdStart (c : Char) : Bool :=
  (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z') || c == '_'

private def isIdPart (c : Char) : Bool := isIdStart c || isDigit c

private def sliceText (cs : Array Char) (a b : Nat) : String :=
  String.ofList (cs.extract a b).toList

private def charAt (cs : Array Char) (i : Nat) : Char := if h : i < cs.size then cs[i] else '\x00'

/-- Scans a number starting at `i`; returns the end offset and whether the lexeme is a `FLOAT`. -/
private def scanNumber (cs : Array Char) (i : Nat) : Nat × Bool := Id.run do
  let mut j := i
  if charAt cs j == '+' || charAt cs j == '-' then j := j + 1
  while isDigit (charAt cs j) do j := j + 1
  let mut k := j
  let mut isFloat := false
  if charAt cs k == '.' && isDigit (charAt cs (k + 1)) then
    k := k + 1
    while isDigit (charAt cs k) do k := k + 1
    isFloat := true
  if charAt cs k == 'e' || charAt cs k == 'E' then
    let mut m := k + 1
    if charAt cs m == '+' || charAt cs m == '-' then m := m + 1
    if isDigit (charAt cs m) then
      while isDigit (charAt cs m) do m := m + 1
      k := m
      isFloat := true
  return (k, isFloat)

/-- Tokenises `.elkt` source text. The result always ends with an `eof` token.
Errors are reported as `"line:col: message"`. -/
def tokenize (text : String) : Except String (Array Token) := do
  let cs := text.toList.toArray
  let mut st : LexState := {}
  let mut out : Array Token := #[]
  while st.pos < cs.size do
    let c := cs[st.pos]!
    let c1 := charAt cs (st.pos + 1)
    let start := st.pos
    if c == ' ' || c == '\t' || c == '\r' || c == '\n' then
      st := st.step cs
    else if c == '/' && c1 == '/' then
      while st.pos < cs.size && cs[st.pos]! != '\n' do
        st := st.step cs
    else if c == '/' && c1 == '*' then
      let l := st.line
      let k := st.col
      st := (st.step cs).step cs
      let mut closed := false
      while !closed && st.pos < cs.size do
        if cs[st.pos]! == '*' && charAt cs (st.pos + 1) == '/' then
          st := (st.step cs).step cs
          closed := true
        else
          st := st.step cs
      if !closed then throw s!"{l}:{k}: unterminated comment"
    else if c == '"' || c == '\'' then
      let l := st.line
      let k := st.col
      st := st.step cs
      let mut closed := false
      while !closed && st.pos < cs.size do
        let d := cs[st.pos]!
        if d == '\\' then
          st := (st.step cs).step cs
        else if d == c then
          st := st.step cs
          closed := true
        else
          st := st.step cs
      if !closed then throw s!"{l}:{k}: unterminated string"
      let raw := sliceText cs start st.pos
      out := out.push { tok := .str raw, text := raw, line := l, col := k, start, stop := st.pos }
    else if isDigit c || ((c == '+' || c == '-') && isDigit c1) then
      let l := st.line
      let k := st.col
      let (e, isFloat) := scanNumber cs start
      st := st.stepTo cs e
      let s := sliceText cs start e
      out := out.push { tok := if isFloat then .float s else .int s, text := s, line := l, col := k, start, stop := e }
    else if isIdStart c || (c == '^' && isIdStart c1) then
      let l := st.line
      let k := st.col
      let mut e := start + 1
      while isIdPart (charAt cs e) do e := e + 1
      st := st.stepTo cs e
      let s := sliceText cs start e
      let tok :=
        if c == '^' then Tok.id (s.drop 1).toString s
        else if wordKeywords.contains s then Tok.kw s
        else Tok.id s s
      out := out.push { tok, text := s, line := l, col := k, start, stop := e }
    else
      let l := st.line
      let k := st.col
      let isArrow := c == '-' && c1 == '>'
      let single := c == '[' || c == ']' || c == ':' || c == ',' || c == '{' || c == '}' || c == '|' || c == '.'
      let len := if isArrow then 2 else 1
      st := st.stepTo cs (start + len)
      let s := sliceText cs start (start + len)
      let tok := if isArrow || single then Tok.kw s else Tok.other c
      out := out.push { tok, text := s, line := l, col := k, start, stop := start + len }
  out := out.push { tok := .eof, text := "<EOF>", line := st.line, col := st.col, start := st.pos, stop := st.pos }
  return out

end Elk.Text
