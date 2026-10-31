import Elk.Json.TransferOverlay
/-!
# Printing the document with the transfer overlay

`OverlayPrinter.render c model` is `(Overlay.materialize c model).render` (compact, keys in document
order) without building the rewritten document: the members the transfer writes are printed from
the overlay tables (numbers straight from the doubles, `appendElkNumber`), in the place
`Value.set` would put them (the first member of the key, or appended in the order of the writes),
and everything else is printed from the imported document. Element objects are found like
`Overlay.materialize` finds them (`ElemIndex`). Tested against `materialize` + `Printer.compact` in
`Tests.Json.Overlay`.
-/
namespace Elk.Json

namespace OverlayPrinter

open Printer Overlay

/-- No ELK member name (`Key.candidateIndex` past the end of `Key.all`). -/
private def KEY_NONE : Nat := 29

/-- Index in `Key.all` of the member name `k`, `KEY_NONE` for other names. -/
@[inline] def keyId (k : String) : Nat :=
  let j := Key.candidateIndex k 0 k.utf8ByteSize
  if j < KEY_NONE then (if k == Key.all.getD j "" then j else KEY_NONE) else KEY_NONE

/-! Indices in `Key.all` of the members the transfer writes or descends into. -/
private def K_X : Nat := 1
private def K_Y : Nat := 2
private def K_WIDTH : Nat := 3
private def K_HEIGHT : Nat := 4
private def K_LABELS : Nat := 5
private def K_PORTS : Nat := 7
private def K_CHILDREN : Nat := 10
private def K_EDGES : Nat := 11
private def K_SECTIONS : Nat := 18
private def K_START : Nat := 19
private def K_END : Nat := 20
private def K_BENDS : Nat := 21
private def K_IN_SHAPE : Nat := 22
private def K_OUT_SHAPE : Nat := 23
private def K_IN_SECS : Nat := 24
private def K_OUT_SECS : Nat := 25
private def K_JUNCTION : Nat := 26
private def K_CONTAINER : Nat := 27
/-- A bit of `seen` past the member names: the replacement `sections` member was written. -/
private def BIT_SECTIONS_SET : UInt32 := (1 : UInt32) <<< 29

/-- The `seen` bit of member name index `j` (`0` for `KEY_NONE`). -/
@[inline] private def bitOf (j : Nat) : UInt32 := if j < KEY_NONE then (1 : UInt32) <<< j.toUInt32 else 0

/-- Whether bit `j` is set in `seen`. -/
@[inline] private def has (seen : UInt32) (j : Nat) : Bool := seen &&& bitOf j != 0

/-- `"k":` (`nonEmpty`: preceded by `,`) for the member name `k` with index `j`. -/
@[inline] private def memberKey (out : String) (nonEmpty : Bool) (k : String) (j : Nat) : String :=
  if nonEmpty then
    if h : j < compactKeysNext.size then out ++ compactKeysNext[j] else appendQuoted out ",\"" k "\":"
  else
    if h : j < compactKeysFirst.size then out ++ compactKeysFirst[j] else appendQuoted out "\"" k "\":"

/-- The key of a member appended after the members of the object (`j` is a member name index). -/
@[inline] private def appendedKey (out : String) (nonEmpty : Bool) (j : Nat) : String :=
  out ++ (if nonEmpty then compactKeysNext.getD j "" else compactKeysFirst.getD j "")

/-- `{"x":x,"y":y}` (`pointValue`). -/
@[inline] private def point (out : String) (x y : Float) : String :=
  appendElkNumber (appendElkNumber (out ++ "{\"x\":") x ++ ",\"y\":") y ++ "}"

/-- `pointsValue` from pair `i` on. -/
private partial def pointItems (xs : FloatArray) (i : Nat) (out : String) : String :=
  if i + 1 < xs.size then
    let out := if i != 0 then out ++ "," else out
    pointItems xs (i + 2) (point out (xs.get! i) (xs.get! (i + 1)))
  else out

/-- `pointsValue xs`. -/
@[inline] private def points (out : String) (xs : FloatArray) : String := pointItems xs 0 (out ++ "[") ++ "]"

/-- `JsonId.toValue`. -/
private def jsonId (out : String) : JsonId → String
  | .str s => escapeInto out s
  | .int i => pushNumber out (.int i)

/-- An array of `JsonId.toValue`s from `i` on. -/
private partial def jsonIdItems (ids : Array JsonId) (i : Nat) (out : String) : String :=
  if h : i < ids.size then
    let out := if i != 0 then out ++ "," else out
    jsonIdItems ids (i + 1) (jsonId out ids[i])
  else out

/-! ## Sections -/

/-- The value of section member `j` written by the transfer (`j` is one it writes). -/
private def sectionMember (so : SectionOut) (j : Nat) (out : String) : String :=
  if j == K_START then point out so.sx so.sy
  else if j == K_END then point out so.ex so.ey
  else if j == K_BENDS then points out so.bends
  else if j == K_IN_SHAPE then match so.inShape with
    | some id => jsonId out id
    | none => out
  else if j == K_OUT_SHAPE then match so.outShape with
    | some id => jsonId out id
    | none => out
  else if j == K_IN_SECS then match so.inSecs with
    | some ids => jsonIdItems ids 0 (out ++ "[") ++ "]"
    | none => out
  else match so.outSecs with
    | some ids => jsonIdItems ids 0 (out ++ "[") ++ "]"
    | none => out

/-- Whether the transfer writes member `j` of the section. -/
@[inline] private def sectionWrites (so : SectionOut) (j : Nat) : Bool :=
  if j == K_START || j == K_END then true
  else if j == K_BENDS then so.bends.size != 0
  else if j == K_IN_SHAPE then so.inShape.isSome
  else if j == K_OUT_SHAPE then so.outShape.isSome
  else if j == K_IN_SECS then so.inSecs.isSome
  else if j == K_OUT_SECS then so.outSecs.isSome
  else false

/-- The written section members `j …` not in `seen`, appended in the order of the writes. -/
private partial def sectionAppends (so : SectionOut) (j : Nat) (seen : UInt32) (nonEmpty : Bool) (out : String) : String :=
  if j <= K_OUT_SECS then
    if sectionWrites so j && !has seen j then
      sectionAppends so (j + 1) seen true (sectionMember so j (appendedKey out nonEmpty j))
    else sectionAppends so (j + 1) seen nonEmpty out
  else out

/-- The members of a section's base object from `i` on. -/
private partial def sectionMembers (so : SectionOut) (kvs : Array (String × Value)) (i : Nat) (seen : UInt32)
    (out : String) : String :=
  if h : i < kvs.size then
    let kv := kvs[i]
    let j := keyId kv.1
    let out := memberKey out (i != 0) kv.1 j
    let out := if j >= K_START && j <= K_OUT_SECS && !has seen j && sectionWrites so j then sectionMember so j out
      else compact false kv.2 out
    sectionMembers so kvs (i + 1) (seen ||| bitOf j) out
  else sectionAppends so K_START seen (kvs.size != 0) out

/-- `sectionValue input so`. -/
private def sectionObj (input : Option Value) (so : SectionOut) (out : String) : String :=
  let base : Array (String × Value) := match so.base with
    | some j =>
      match input with
      | some (.arr xs) =>
        match xs[j]? with
        | some (.obj kvs) => kvs
        | _ => #[]
      | _ => #[]
    | none => #[(Key.id, .str so.fallbackId)]
  sectionMembers so base 0 0 (out ++ "{") ++ "}"

/-- The replacement `sections` array from section `i` on. -/
private partial def sectionItems (input : Option Value) (secs : Array SectionOut) (i : Nat) (out : String) : String :=
  if h : i < secs.size then
    let out := if i != 0 then out ++ "," else out
    sectionItems input secs (i + 1) (sectionObj input secs[i] out)
  else out

/-! ## Labels, ports, nodes and edges -/

/-- `x`/`y`/`width`/`height` of transferred shape `d` (dense index) for member index `j`. -/
@[inline] private def xywh (ov : Overlay) (d j : Nat) (out : String) : String :=
  if j == K_X then appendElkNumber out (ov.sx.get! d)
  else if j == K_Y then appendElkNumber out (ov.sy.get! d)
  else if j == K_WIDTH then appendElkNumber out (ov.sw.get! d)
  else appendElkNumber out (ov.sh.get! d)

/-- `x`, `y`, `width`, `height` of shape `d` not in `seen`, appended in this order. -/
private partial def xywhAppends (ov : Overlay) (d j : Nat) (seen : UInt32) (nonEmpty : Bool) (out : String) : String :=
  if j <= K_HEIGHT then
    if !has seen j then xywhAppends ov d (j + 1) seen true (xywh ov d j (appendedKey out nonEmpty j))
    else xywhAppends ov d (j + 1) seen nonEmpty out
  else out

mutual

/-- A label object (label `l`). -/
partial def label (c : Ctx) (l : Nat) (kvs : Array (String × Value)) (out : String) : String :=
  shapeMembers c 2 l (c.labelBase + l) kvs 0 0 (out ++ "{") ++ "}"

/-- A port object (port `p`). -/
partial def port (c : Ctx) (p : Nat) (kvs : Array (String × Value)) (out : String) : String :=
  shapeMembers c 1 p (c.portBase + p) kvs 0 0 (out ++ "{") ++ "}"

/-- A node object (node `n`). -/
partial def node (c : Ctx) (n : Nat) (kvs : Array (String × Value)) (out : String) : String :=
  shapeMembers c 0 n n kvs 0 0 (out ++ "{") ++ "}"

/-- The members of a node (`kind` 0), port (1) or label (2) object from `i` on: element id `id`,
dense index `d`. -/
partial def shapeMembers (c : Ctx) (kind : UInt8) (id d : Nat) (kvs : Array (String × Value)) (i : Nat)
    (seen : UInt32) (out : String) : String :=
  if h : i < kvs.size then
    let kv := kvs[i]
    let j := keyId kv.1
    let first := !has seen j
    let out := memberKey out (i != 0) kv.1 j
    let out :=
      if j <= K_HEIGHT && j >= K_X && first && c.ov.isDone d then xywh c.ov d j out
      else if first && j == K_LABELS && kind != 2 then
        match kv.2 with
        | .arr xs =>
          let firstLabel := if kind == 0 then c.ix.nodeFirstLabel.getD id 0 else c.ix.portFirstLabel.getD id 0
          labelItems c xs 0 firstLabel (out ++ "[") ++ "]"
        | v => compact false v out
      else if first && kind == 0 && (j == K_PORTS || j == K_CHILDREN || j == K_EDGES) then
        match kv.2 with
        | .arr xs =>
          let out := out ++ "["
          let out :=
            if j == K_PORTS then portItems c xs 0 (c.ix.nodeFirstPort.getD id 0) out
            else if j == K_CHILDREN then childItems c xs 0 (id + 1) out
            else edgeItems c xs 0 (c.ix.nodeFirstEdge.getD id 0) out
          out ++ "]"
        | v => compact false v out
      else compact false kv.2 out
    shapeMembers c kind id d kvs (i + 1) (seen ||| bitOf j) out
  else if c.ov.isDone d then xywhAppends c.ov d K_X seen (kvs.size != 0) out
  else out

/-- The objects of a `labels` array from `i` on, the next one being label `l`. -/
partial def labelItems (c : Ctx) (xs : Array Value) (i l : Nat) (out : String) : String :=
  if h : i < xs.size then
    let out := if i != 0 then out ++ "," else out
    match xs[i] with
    | .obj kvs => labelItems c xs (i + 1) (l + 1) (label c l kvs out)
    | v => labelItems c xs (i + 1) l (compact false v out)
  else out

/-- The objects of a `ports` array from `i` on, the next one being port `p`. -/
partial def portItems (c : Ctx) (xs : Array Value) (i p : Nat) (out : String) : String :=
  if h : i < xs.size then
    let out := if i != 0 then out ++ "," else out
    match xs[i] with
    | .obj kvs => portItems c xs (i + 1) (p + 1) (port c p kvs out)
    | v => portItems c xs (i + 1) p (compact false v out)
  else out

/-- The objects of a `children` array from `i` on, the next one being node `n` (preorder ids). -/
partial def childItems (c : Ctx) (xs : Array Value) (i n : Nat) (out : String) : String :=
  if h : i < xs.size then
    let out := if i != 0 then out ++ "," else out
    match xs[i] with
    | .obj kvs => childItems c xs (i + 1) (c.ix.nodeSubtreeEnd.getD n (n + 1)) (node c n kvs out)
    | v => childItems c xs (i + 1) n (compact false v out)
  else out

/-- The objects of an `edges` array from `i` on, the next one being edge `e`. -/
partial def edgeItems (c : Ctx) (xs : Array Value) (i e : Nat) (out : String) : String :=
  if h : i < xs.size then
    let out := if i != 0 then out ++ "," else out
    match xs[i] with
    | .obj kvs => edgeItems c xs (i + 1) (e + 1) (edge c e kvs out)
    | v => edgeItems c xs (i + 1) e (compact false v out)
  else out

/-- An edge object (edge `e`) with the writes of `transfer_layout_edge`. -/
partial def edge (c : Ctx) (e : Nat) (kvs : Array (String × Value)) (out : String) : String :=
  let eo? := c.ov.edges.getD e none
  let input := match eo? with
    | some eo => if eo.sections.isEmpty then none else Value.lookup kvs Key.sections
    | none => none
  edgeMembers c e eo? input kvs 0 0 false (out ++ "{") ++ "}"

/-- The members of an edge object from `i` on (`nonEmpty`: a member was written; the first
`sections` member is dropped when the transfer replaces it). -/
partial def edgeMembers (c : Ctx) (e : Nat) (eo? : Option EdgeOut) (input : Option Value)
    (kvs : Array (String × Value)) (i : Nat) (seen : UInt32) (nonEmpty : Bool) (out : String) : String :=
  if h : i < kvs.size then
    let kv := kvs[i]
    let j := keyId kv.1
    let first := !has seen j
    let seen' := seen ||| bitOf j
    match eo? with
    | some eo =>
      if j == K_SECTIONS && !eo.sections.isEmpty then
        if first then edgeMembers c e eo? input kvs (i + 1) seen' nonEmpty out
        else if seen &&& BIT_SECTIONS_SET == 0 then
          let out := sectionItems input eo.sections 0 (memberKey out nonEmpty kv.1 j ++ "[") ++ "]"
          edgeMembers c e eo? input kvs (i + 1) (seen' ||| BIT_SECTIONS_SET) true out
        else edgeMembers c e eo? input kvs (i + 1) seen' true (compact false kv.2 (memberKey out nonEmpty kv.1 j))
      else
        let out := memberKey out nonEmpty kv.1 j
        let out :=
          if first && j == K_JUNCTION && eo.junction.isSome then points out (eo.junction.getD .empty)
          else if first && j == K_CONTAINER && eo.container.isSome then escapeInto out (eo.container.getD "")
          else edgeValue c e first j kv.2 out
        edgeMembers c e eo? input kvs (i + 1) seen' true out
    | none =>
      let out := edgeValue c e first j kv.2 (memberKey out nonEmpty kv.1 j)
      edgeMembers c e eo? input kvs (i + 1) seen' true out
  else
    match eo? with
    | some eo =>
      let replaced := !eo.sections.isEmpty && seen &&& BIT_SECTIONS_SET == 0
      let out := if replaced then sectionItems input eo.sections 0 (appendedKey out nonEmpty K_SECTIONS ++ "[") ++ "]" else out
      let nonEmpty := nonEmpty || replaced
      let jp := eo.junction.isSome && !has seen K_JUNCTION
      let out := match eo.junction with
        | some xs => if jp then points (appendedKey out nonEmpty K_JUNCTION) xs else out
        | none => out
      let nonEmpty := nonEmpty || jp
      match eo.container with
      | some cid => if !has seen K_CONTAINER then escapeInto (appendedKey out nonEmpty K_CONTAINER) cid else out
      | none => out
    | none => out

/-- An edge member's value other than the transfer's writes: the edge labels, or the value itself. -/
partial def edgeValue (c : Ctx) (e : Nat) (first : Bool) (j : Nat) (v : Value) (out : String) : String :=
  if first && j == K_LABELS then
    match v with
    | .arr xs => labelItems c xs 0 (c.ix.edgeFirstLabel.getD e 0) (out ++ "[") ++ "]"
    | v => compact false v out
  else compact false v out

end

/-- `(Overlay.materialize c model).render` (compact, document key order), printed into a buffer with
room for `cap` bytes. -/
def render (c : Ctx) (model : Value) (cap : Nat := 0) : String :=
  let out := stringWithCapacity cap.toUSize
  match model with
  | .obj kvs => node c 0 kvs out
  | v => compact false v out

end OverlayPrinter

end Elk.Json
