import Elk.Core.Util.Java
import Elk.Text.Lexer
/-!
# `.elkt` parser (`org.eclipse.elk.graph.text`, `ElkGraph.xtext`)

Recursive-descent parser producing a syntax tree (`RootAst`) that follows the
rules of `ElkGraph.xtext` one by one:

```
RootNode:   ('graph' ID)? ShapeLayout? Property* (ElkLabel | ElkPort | ElkNode | ElkEdge)*
ElkNode:    'node' ID ('{' ShapeLayout? Property* (ElkLabel | ElkPort | ElkNode | ElkEdge)* '}')?
ElkLabel:   'label' (ID ':')? STRING ('{' ShapeLayout? Property* ElkLabel* '}')?
ElkPort:    'port' ID ('{' ShapeLayout? Property* ElkLabel* '}')?
ShapeLayout:'layout' '[' (('position' ':' Number ',' Number)? & ('size' ':' Number ',' Number)?) ']'
ElkEdge:    'edge' (ID ':')? QualifiedId (',' QualifiedId)* '->' QualifiedId (',' QualifiedId)*
            ('{' EdgeLayout? Property* ElkLabel* '}')?
EdgeLayout: 'layout' '[' (ElkSingleEdgeSection | ElkEdgeSection+) ']'
ElkEdgeSection: 'section' ID ('->' ID (',' ID)*)? '[' SectionBody ']'
SectionBody: (incoming? & outgoing? & start? & end?) ('bends' ':' Number ',' Number ('|' ...)*)? Property*
Property:   PropertyKey ':' (STRING | QualifiedId | Number | 'true' | 'false' | 'null')
```

The tree keeps source positions for the cross reference diagnostics of the
linking phase (`Elk.Text.Loader`). This is a port of the Xtext-generated
`InternalElkGraphParser` (ANTLR); the hand-written Rust loader
`elkt_test_loader.rs` of elk-rs implements an ad-hoc, line based dialect and is
not a parser of this grammar (see `Elk.Text.Loader` for the differences).
-/
namespace Elk.Text

open Elk.Core.Util

/-- Source position (1-based). -/
structure Pos where
  line : Nat := 0
  col : Nat := 0
  deriving Repr, BEq, Inhabited

/-- Right-hand side of a `Property`. -/
inductive ValueAst where
  /-- `STRING`: raw token text including the quotes. -/
  | str (raw : String)
  /-- `QualifiedId` value: the `ID` segments with the `^` escape removed. -/
  | qid (segs : Array String)
  /-- `SIGNED_INT` / `FLOAT` token text. -/
  | num (text : String)
  /-- `true` / `false`. -/
  | bool (b : Bool)
  /-- The keyword `null`. -/
  | null
  deriving Repr, BEq, Inhabited

/-- `Property`: `key: value`. -/
structure PropertyAst where
  pos : Pos
  /-- The key as written (`ID` raw texts joined by `.`, `^` kept). -/
  keyRaw : String
  /-- The key segments with the `^` escape removed. -/
  keySegs : Array String
  value : ValueAst
  deriving Repr, BEq, Inhabited

/-- A cross reference by qualified name (`[ElkConnectableShape|QualifiedId]`). -/
structure RefAst where
  pos : Pos
  segs : Array String
  deriving Repr, BEq, Inhabited

/-- `ShapeLayout`: optional `position` and `size`. -/
structure ShapeLayoutAst where
  position : Option (Float × Float) := none
  size : Option (Float × Float) := none
  deriving Repr, BEq, Inhabited

/-- `ElkLabel`. -/
structure LabelAst where
  pos : Pos := {}
  identifier : Option String := none
  /-- Text with the string escapes already resolved. -/
  text : String := ""
  layout : ShapeLayoutAst := {}
  props : Array PropertyAst := #[]
  labels : Array LabelAst := #[]
  deriving Repr, BEq, Inhabited

/-- `ElkPort`. -/
structure PortAst where
  pos : Pos := {}
  identifier : String := ""
  layout : ShapeLayoutAst := {}
  props : Array PropertyAst := #[]
  labels : Array LabelAst := #[]
  deriving Repr, BEq, Inhabited

/-- `ElkSingleEdgeSection` / `ElkEdgeSection`. -/
structure SectionAst where
  pos : Pos := {}
  identifier : Option String := none
  /-- `-> a, b`: names of the successor sections. -/
  outgoingSections : Array RefAst := #[]
  incomingShape : Option RefAst := none
  outgoingShape : Option RefAst := none
  start : Option (Float × Float) := none
  stop : Option (Float × Float) := none
  bends : Array (Float × Float) := #[]
  props : Array PropertyAst := #[]
  deriving Repr, BEq, Inhabited

/-- `ElkEdge`. -/
structure EdgeAst where
  pos : Pos := {}
  identifier : Option String := none
  sources : Array RefAst := #[]
  targets : Array RefAst := #[]
  sections : Array SectionAst := #[]
  props : Array PropertyAst := #[]
  labels : Array LabelAst := #[]
  deriving Repr, BEq, Inhabited

/-- Members of a node body, in source order. -/
inductive Item where
  | label (l : LabelAst)
  | port (p : PortAst)
  | edge (e : EdgeAst)
  /-- `ElkNode`: position, identifier, layout, properties and nested items. -/
  | node (pos : Pos) (identifier : String) (layout : ShapeLayoutAst) (props : Array PropertyAst)
      (items : Array Item)
  deriving Repr, BEq, Inhabited

/-- `RootNode`. -/
structure RootAst where
  identifier : Option String := none
  layout : ShapeLayoutAst := {}
  props : Array PropertyAst := #[]
  items : Array Item := #[]
  deriving Repr, BEq, Inhabited

/-! ### Parser monad -/

/-- Parser state: the token array (reader) and the current index (state). -/
abbrev PM := ReaderT (Array Token) (StateT Nat (Except String))

instance {α : Type} : Inhabited (PM α) := ⟨throw "unreachable"⟩

private def peekAt (k : Nat) : PM Token := do
  let ts ← read
  let i ← get
  return ts[min (i + k) (ts.size - 1)]!

private def peek : PM Token := peekAt 0

private def advance : PM Token := do
  let t ← peek
  let ts ← read
  let i ← get
  if i + 1 < ts.size then set (i + 1)
  return t

private def posOf (t : Token) : Pos := ⟨t.line, t.col⟩

private def failAt {α : Type} (t : Token) (expecting : String) : PM α :=
  throw s!"{t.line}:{t.col}: mismatched input '{t.text}' expecting {expecting}"

private def isKw (t : Token) (s : String) : Bool :=
  match t.tok with
  | .kw k => k == s
  | _ => false

private def isId (t : Token) : Bool :=
  match t.tok with
  | .id _ _ => true
  | _ => false

private def expectKw (s : String) : PM Token := do
  let t ← peek
  if isKw t s then advance else failAt t s!"'{s}'"

/-- `ID`: returns the token and its value (without `^`). -/
private def expectId : PM (Token × String) := do
  let t ← peek
  match t.tok with
  | .id v _ => let _ ← advance; return (t, v)
  | _ => failAt t "RULE_ID"

private def numberValue (s : String) : Float := (parseFloat? s).getD 0.0

/-- `Number returns ecore::EDouble: SIGNED_INT | FLOAT`. -/
private def expectNumber : PM Float := do
  let t ← peek
  match t.tok with
  | .int s => let _ ← advance; return numberValue s
  | .float s => let _ ← advance; return numberValue s
  | _ => failAt t "RULE_SIGNED_INT or RULE_FLOAT"

/-- `Number ',' Number`. -/
private def expectPair : PM (Float × Float) := do
  let x ← expectNumber
  let _ ← expectKw ","
  let y ← expectNumber
  return (x, y)

/-- Resolves the escapes of a `STRING` token (`STRINGValueConverter`,
`Strings.convertFromJavaString`). Unknown escapes keep the escaped character. -/
def unescapeString (raw : String) : String := Id.run do
  let cs := raw.toList.toArray
  if cs.size < 2 then return raw
  let mut out := ""
  let mut i := 1
  let last := cs.size - 1
  let hex (c : Char) : Option Nat :=
    if c >= '0' && c <= '9' then some (c.toNat - '0'.toNat)
    else if c >= 'a' && c <= 'f' then some (c.toNat - 'a'.toNat + 10)
    else if c >= 'A' && c <= 'F' then some (c.toNat - 'A'.toNat + 10)
    else none
  let hex4 (cs : Array Char) (j : Nat) : Option Nat := do
    let a ← hex (cs[j]!)
    let b ← hex (cs[j + 1]!)
    let c ← hex (cs[j + 2]!)
    let d ← hex (cs[j + 3]!)
    return a * 4096 + b * 256 + c * 16 + d
  while i < last do
    let c := cs[i]!
    if c == '\\' && i + 1 < last then
      let d := cs[i + 1]!
      i := i + 2
      if d == 'b' then out := out.push '\x08'
      else if d == 't' then out := out.push '\t'
      else if d == 'n' then out := out.push '\n'
      else if d == 'f' then out := out.push '\x0c'
      else if d == 'r' then out := out.push '\r'
      else if d == 'u' && i + 3 < last then
        match hex4 cs i with
        | some v =>
          i := i + 4
          if v >= 0xD800 && v < 0xDC00 && i + 5 < last && cs[i]! == '\\' && cs[i + 1]! == 'u' then
            match hex4 cs (i + 2) with
            | some w =>
              if w >= 0xDC00 && w < 0xE000 then
                out := out.push (Char.ofNat (0x10000 + (v - 0xD800) * 0x400 + (w - 0xDC00)))
                i := i + 6
              else out := out.push (Char.ofNat v)
            | none => out := out.push (Char.ofNat v)
          else out := out.push (Char.ofNat v)
        | none => out := out.push 'u'
      else if d >= '0' && d <= '7' then
        let mut v := d.toNat - '0'.toNat
        let maxDigits := if d <= '3' then 2 else 1
        let mut n := 0
        while n < maxDigits && i < last && cs[i]! >= '0' && cs[i]! <= '7' do
          v := v * 8 + (cs[i]!.toNat - '0'.toNat)
          i := i + 1
          n := n + 1
        out := out.push (Char.ofNat v)
      else out := out.push d
    else
      out := out.push c
      i := i + 1
  return out

/-! ### Rules -/

/-- `QualifiedId` (white space allowed around the dots): segments without `^`. -/
private def parseRef : PM RefAst := do
  let (t, v) ← expectId
  let mut segs := #[v]
  while isKw (← peek) "." do
    let _ ← advance
    let (_, w) ← expectId
    segs := segs.push w
  return ⟨posOf t, segs⟩

private def parseRefList : PM (Array RefAst) := do
  let mut refs := #[← parseRef]
  while isKw (← peek) "," do
    let _ ← advance
    refs := refs.push (← parseRef)
  return refs

/-- `Property`. `PropertyKey` is `hidden()`: no white space inside the key. -/
private def parseProperty : PM PropertyAst := do
  let (t0, v0) ← expectId
  let raw0 := match t0.tok with | .id _ r => r | _ => v0
  let mut segs := #[v0]
  let mut raw := raw0
  let mut lastStop := t0.stop
  while true do
    let dot ← peek
    if isKw dot "." && dot.start == lastStop then
      let _ ← advance
      let nxt ← peek
      match nxt.tok with
      | .id v r =>
        if nxt.start != dot.stop then failAt nxt "RULE_ID"
        let _ ← advance
        segs := segs.push v
        raw := raw ++ "." ++ r
        lastStop := nxt.stop
      | _ => failAt nxt "RULE_ID"
    else break
  let _ ← expectKw ":"
  let t ← peek
  let value ← match t.tok with
    | .str rawText => do let _ ← advance; pure (ValueAst.str rawText)
    | .kw "true" => do let _ ← advance; pure (ValueAst.bool true)
    | .kw "false" => do let _ ← advance; pure (ValueAst.bool false)
    | .kw "null" => do let _ ← advance; pure ValueAst.null
    | .int s => do let _ ← advance; pure (ValueAst.num s)
    | .float s => do let _ ← advance; pure (ValueAst.num s)
    | .id _ _ => do
      let r ← parseRef
      pure (ValueAst.qid r.segs)
    | _ => failAt t "RULE_STRING, RULE_ID, RULE_SIGNED_INT, RULE_FLOAT, 'true', 'false' or 'null'"
  return { pos := posOf t0, keyRaw := raw, keySegs := segs, value }

private def parseProperties : PM (Array PropertyAst) := do
  let mut props := #[]
  while isId (← peek) do
    props := props.push (← parseProperty)
  return props

/-- `ShapeLayout`: `layout [ (position: x, y)? & (size: w, h)? ]`. -/
private def parseShapeLayout : PM ShapeLayoutAst := do
  if !isKw (← peek) "layout" then return {}
  let _ ← advance
  let _ ← expectKw "["
  let mut res : ShapeLayoutAst := {}
  while true do
    let t ← peek
    if isKw t "position" && res.position.isNone then
      let _ ← advance
      let _ ← expectKw ":"
      res := { res with position := some (← expectPair) }
    else if isKw t "size" && res.size.isNone then
      let _ ← advance
      let _ ← expectKw ":"
      res := { res with size := some (← expectPair) }
    else break
  let _ ← expectKw "]"
  return res

/-- `ElkLabel` (recursive through nested labels). -/
private partial def parseLabel : PM LabelAst := do
  let t0 ← expectKw "label"
  let mut identifier : Option String := none
  let t1 ← peek
  if isId t1 then
    let (_, v) ← expectId
    let _ ← expectKw ":"
    identifier := some v
  let ts ← peek
  let text ← match ts.tok with
    | .str raw => do let _ ← advance; pure (unescapeString raw)
    | _ => failAt ts "RULE_STRING"
  let mut layout : ShapeLayoutAst := {}
  let mut props : Array PropertyAst := #[]
  let mut labels : Array LabelAst := #[]
  if isKw (← peek) "{" then
    let _ ← advance
    layout ← parseShapeLayout
    props ← parseProperties
    while isKw (← peek) "label" do
      labels := labels.push (← parseLabel)
    let _ ← expectKw "}"
  return { pos := posOf t0, identifier, text, layout, props, labels }

private def parseLabels : PM (Array LabelAst) := do
  let mut labels := #[]
  while isKw (← peek) "label" do
    labels := labels.push (← parseLabel)
  return labels

/-- `ElkPort`. -/
private def parsePort : PM PortAst := do
  let t0 ← expectKw "port"
  let (_, identifier) ← expectId
  let mut layout : ShapeLayoutAst := {}
  let mut props : Array PropertyAst := #[]
  let mut labels : Array LabelAst := #[]
  if isKw (← peek) "{" then
    let _ ← advance
    layout ← parseShapeLayout
    props ← parseProperties
    labels ← parseLabels
    let _ ← expectKw "}"
  return { pos := posOf t0, identifier, layout, props, labels }

/-- Body of an `ElkSingleEdgeSection` / `ElkEdgeSection` up to (excluding) the closing `]`. -/
private def parseSectionBody (sec : SectionAst) : PM SectionAst := do
  let mut sec := sec
  let mut seenIncoming := false
  let mut seenOutgoing := false
  let mut seenStart := false
  let mut seenEnd := false
  while true do
    let t ← peek
    if isKw t "incoming" && !seenIncoming then
      let _ ← advance
      let _ ← expectKw ":"
      sec := { sec with incomingShape := some (← parseRef) }
      seenIncoming := true
    else if isKw t "outgoing" && !seenOutgoing then
      let _ ← advance
      let _ ← expectKw ":"
      sec := { sec with outgoingShape := some (← parseRef) }
      seenOutgoing := true
    else if isKw t "start" && !seenStart then
      let _ ← advance
      let _ ← expectKw ":"
      sec := { sec with start := some (← expectPair) }
      seenStart := true
    else if isKw t "end" && !seenEnd then
      let _ ← advance
      let _ ← expectKw ":"
      sec := { sec with stop := some (← expectPair) }
      seenEnd := true
    else break
  if isKw (← peek) "bends" then
    let _ ← advance
    let _ ← expectKw ":"
    let mut bends := #[← expectPair]
    while isKw (← peek) "|" do
      let _ ← advance
      bends := bends.push (← expectPair)
    sec := { sec with bends }
  let props ← parseProperties
  return { sec with props }

/-- `ElkEdgeSection`: `section ID ('->' ID (',' ID)*)? '[' ... ']'`. -/
private def parseNamedSection : PM SectionAst := do
  let t0 ← expectKw "section"
  let (_, identifier) ← expectId
  let mut outgoing : Array RefAst := #[]
  if isKw (← peek) "->" then
    let _ ← advance
    let (t, v) ← expectId
    outgoing := #[⟨posOf t, #[v]⟩]
    while isKw (← peek) "," do
      let _ ← advance
      let (t, v) ← expectId
      outgoing := outgoing.push ⟨posOf t, #[v]⟩
  let _ ← expectKw "["
  let sec ← parseSectionBody { pos := posOf t0, identifier := some identifier, outgoingSections := outgoing }
  let _ ← expectKw "]"
  return sec

/-- `EdgeLayout`: `layout [ ElkSingleEdgeSection | ElkEdgeSection+ ]`. -/
private def parseEdgeLayout : PM (Array SectionAst) := do
  let t0 ← expectKw "layout"
  let _ ← expectKw "["
  let mut sections : Array SectionAst := #[]
  if isKw (← peek) "section" then
    while isKw (← peek) "section" do
      sections := sections.push (← parseNamedSection)
  else
    sections := #[← parseSectionBody { pos := posOf t0 }]
  let _ ← expectKw "]"
  return sections

/-- `ElkEdge`. -/
private def parseEdge : PM EdgeAst := do
  let t0 ← expectKw "edge"
  let mut identifier : Option String := none
  let t1 ← peek
  let t2 ← peekAt 1
  if isId t1 && isKw t2 ":" then
    let (_, v) ← expectId
    let _ ← advance
    identifier := some v
  let sources ← parseRefList
  let _ ← expectKw "->"
  let targets ← parseRefList
  let mut sections : Array SectionAst := #[]
  let mut props : Array PropertyAst := #[]
  let mut labels : Array LabelAst := #[]
  if isKw (← peek) "{" then
    let _ ← advance
    if isKw (← peek) "layout" then
      sections ← parseEdgeLayout
    props ← parseProperties
    labels ← parseLabels
    let _ ← expectKw "}"
  return { pos := posOf t0, identifier, sources, targets, sections, props, labels }

mutual

/-- Node body members `(labels | ports | children | containedEdges)*`; stops at `}` (or EOF for the root). -/
private partial def parseItems (isRoot : Bool) : PM (Array Item) := do
  let mut items : Array Item := #[]
  while true do
    let t ← peek
    match t.tok with
    | .kw "label" => items := items.push (.label (← parseLabel))
    | .kw "port" => items := items.push (.port (← parsePort))
    | .kw "edge" => items := items.push (.edge (← parseEdge))
    | .kw "node" => items := items.push (← parseNode)
    | .kw "}" => if isRoot then failAt t "EOF" else break
    | .eof => if isRoot then break else failAt t "'}'"
    | _ =>
      if isRoot then failAt t "EOF, 'label', 'port', 'node' or 'edge'"
      else failAt t "'}', 'label', 'port', 'node' or 'edge'"
  return items

/-- `ElkNode`. -/
private partial def parseNode : PM Item := do
  let t0 ← expectKw "node"
  let (_, identifier) ← expectId
  let mut layout : ShapeLayoutAst := {}
  let mut props : Array PropertyAst := #[]
  let mut items : Array Item := #[]
  if isKw (← peek) "{" then
    let _ ← advance
    layout ← parseShapeLayout
    props ← parseProperties
    items ← parseItems false
    let _ ← expectKw "}"
  return .node (posOf t0) identifier layout props items

end

/-- `RootNode`. -/
private def parseRoot : PM RootAst := do
  let mut identifier : Option String := none
  if isKw (← peek) "graph" then
    let _ ← advance
    let (_, v) ← expectId
    identifier := some v
  let layout ← parseShapeLayout
  let props ← parseProperties
  let items ← parseItems true
  return { identifier, layout, props, items }

/-- Parses `.elkt` text into a syntax tree. Errors are `"line:col: message"`. -/
def parseAst (text : String) : Except String RootAst := do
  let tokens ← tokenize text
  let (root, _) ← (parseRoot.run tokens).run 0
  return root

end Elk.Text
