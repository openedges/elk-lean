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

/-- The key literal of an ELK member name index `j` (`"key":` or `,"key":`). -/
@[inline] private def keyLit (nonEmpty : Bool) (j : Nat) : String :=
  if nonEmpty then compactKeysNext.getD j "" else compactKeysFirst.getD j ""

/-- The key of a member appended after the members of the object (`j` is a member name index). -/
@[inline] private def appendedKey (out : String) (nonEmpty : Bool) (j : Nat) : String :=
  out ++ keyLit nonEmpty j

/-- A member of the document as `Printer.compactMembers` prints it: an ELK member name with a string
value without escapes in one append. -/
@[inline] private def plainMember (out : String) (nonEmpty : Bool) (k : String) (j : Nat) (v : Value) : String :=
  match v with
  | .str s =>
    if j < KEY_NONE && !hasEscapes s (Utf8.usize s) rfl 0 then
      append3 out (if nonEmpty then compactKeysNextQ.getD j "" else compactKeysFirstQ.getD j "") s "\""
    else escapeInto (memberKey out nonEmpty k j) s
  | v => compact false v (memberKey out nonEmpty k j)

/-- `pointsValue` from pair `i` on. -/
private partial def pointItems (xs : FloatArray) (i : Nat) (out : String) : String :=
  if i + 1 < xs.size then
    pointItems xs (i + 2) (appendPoint out (if i != 0 then "," else "") (xs.get! i) (xs.get! (i + 1)))
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

/-- Section member `j` written by the transfer (`j` is one it writes) with its key (`nonEmpty`: after
another member). -/
private def sectionMember (so : SectionOut) (j : Nat) (nonEmpty : Bool) (out : String) : String :=
  if j == K_START then appendPoint out (keyLit nonEmpty j) so.sx so.sy
  else if j == K_END then appendPoint out (keyLit nonEmpty j) so.ex so.ey
  else
  let out := out ++ keyLit nonEmpty j
  if j == K_BENDS then points out so.bends
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
      sectionAppends so (j + 1) seen true (sectionMember so j nonEmpty out)
    else sectionAppends so (j + 1) seen nonEmpty out
  else out

/-- The members of a section's base object from `i` on. -/
private partial def sectionMembers (so : SectionOut) (kvs : Array (String × Value)) (i : Nat) (seen : UInt32)
    (out : String) : String :=
  if h : i < kvs.size then
    let kv := kvs[i]
    let j := keyId kv.1
    let out := if j >= K_START && j <= K_OUT_SECS && !has seen j && sectionWrites so j then sectionMember so j (i != 0) out
      else plainMember out (i != 0) kv.1 j kv.2
    sectionMembers so kvs (i + 1) (seen ||| bitOf j) out
  else sectionAppends so K_START seen (kvs.size != 0) out

/-- `sectionValue edgeId input so`. -/
private def sectionObj (edgeId : String) (input : Option Value) (so : SectionOut) (out : String) : String :=
  match so.base with
  | some j =>
    let base : Array (String × Value) := match input with
      | some (.arr xs) =>
        match xs[j]? with
        | some (.obj kvs) => kvs
        | _ => #[]
      | _ => #[]
    sectionMembers so base 0 0 (out ++ "{") ++ "}"
  | none =>
    -- `{"id": fallbackId}`; `<edgeId>_s<index>` is escaped like the edge id (the suffix has nothing
    -- to escape)
    let out := match so.ident with
      | some s => plainMember (out ++ "{") false Key.id 0 (.str s)
      | none =>
        if hasEscapes edgeId (Utf8.usize edgeId) rfl 0 then
          plainMember (out ++ "{") false Key.id 0 (.str (so.fallbackId edgeId))
        else pushNat (append3 out "{\"id\":\"" edgeId "_s") so.index ++ "\""
    sectionAppends so K_START 0 true out ++ "}"

/-- The replacement `sections` array from section `i` on. -/
private partial def sectionItems (edgeId : String) (input : Option Value) (secs : Array SectionOut) (i : Nat)
    (out : String) : String :=
  if h : i < secs.size then
    let out := if i != 0 then out ++ "," else out
    sectionItems edgeId input secs (i + 1) (sectionObj edgeId input secs[i] out)
  else out

/-! ## Labels, ports, nodes and edges -/

/-- Member `x`/`y`/`width`/`height` (index `j`) of transferred shape `d` (dense index) with its key. -/
@[inline] private def xywh (ov : Overlay) (d j : Nat) (nonEmpty : Bool) (out : String) : String :=
  let v := if j == K_X then ov.sx.get! d
    else if j == K_Y then ov.sy.get! d
    else if j == K_WIDTH then ov.sw.get! d
    else ov.sh.get! d
  appendPreElkNumber out (keyLit nonEmpty j) v

/-- `x`, `y`, `width`, `height` of shape `d` not in `seen`, appended in this order. -/
private partial def xywhAppends (ov : Overlay) (d j : Nat) (seen : UInt32) (nonEmpty : Bool) (out : String) : String :=
  if j <= K_HEIGHT then
    if !has seen j then xywhAppends ov d (j + 1) seen true (xywh ov d j nonEmpty out)
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
    let ne := i != 0
    let out :=
      if j <= K_HEIGHT && j >= K_X && first && c.ov.isDone d then xywh c.ov d j ne out
      else if first && j == K_LABELS && kind != 2 then
        match kv.2 with
        | .arr xs =>
          let firstLabel := if kind == 0 then c.ix.nodeFirstLabel.getD id 0 else c.ix.portFirstLabel.getD id 0
          labelItems c xs 0 firstLabel (memberKey out ne kv.1 j ++ "[") ++ "]"
        | v => plainMember out ne kv.1 j v
      else if first && kind == 0 && (j == K_PORTS || j == K_CHILDREN || j == K_EDGES) then
        match kv.2 with
        | .arr xs =>
          let out := memberKey out ne kv.1 j ++ "["
          let out :=
            if j == K_PORTS then portItems c xs 0 (c.ix.nodeFirstPort.getD id 0) out
            else if j == K_CHILDREN then childItems c xs 0 (id + 1) out
            else edgeItems c xs 0 (c.ix.nodeFirstEdge.getD id 0) out
          out ++ "]"
        | v => plainMember out ne kv.1 j v
      else plainMember out ne kv.1 j kv.2
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
          let out := sectionItems eo.edgeId input eo.sections 0 (memberKey out nonEmpty kv.1 j ++ "[") ++ "]"
          edgeMembers c e eo? input kvs (i + 1) (seen' ||| BIT_SECTIONS_SET) true out
        else edgeMembers c e eo? input kvs (i + 1) seen' true (plainMember out nonEmpty kv.1 j kv.2)
      else
        let out :=
          if first && j == K_JUNCTION && eo.junction.isSome then points (memberKey out nonEmpty kv.1 j) (eo.junction.getD .empty)
          else if first && j == K_CONTAINER && eo.container.isSome then
            plainMember out nonEmpty kv.1 j (.str (eo.container.getD ""))
          else edgeValue c e first nonEmpty kv.1 j kv.2 out
        edgeMembers c e eo? input kvs (i + 1) seen' true out
    | none =>
      let out := edgeValue c e first nonEmpty kv.1 j kv.2 out
      edgeMembers c e eo? input kvs (i + 1) seen' true out
  else
    match eo? with
    | some eo =>
      let replaced := !eo.sections.isEmpty && seen &&& BIT_SECTIONS_SET == 0
      let out := if replaced then sectionItems eo.edgeId input eo.sections 0 (appendedKey out nonEmpty K_SECTIONS ++ "[") ++ "]" else out
      let nonEmpty := nonEmpty || replaced
      let jp := eo.junction.isSome && !has seen K_JUNCTION
      let out := match eo.junction with
        | some xs => if jp then points (appendedKey out nonEmpty K_JUNCTION) xs else out
        | none => out
      let nonEmpty := nonEmpty || jp
      match eo.container with
      | some cid => if !has seen K_CONTAINER then plainMember out nonEmpty Key.container K_CONTAINER (.str cid) else out
      | none => out
    | none => out

/-- An edge member other than the transfer's writes, with its key: the edge labels, or the member
itself. -/
partial def edgeValue (c : Ctx) (e : Nat) (first nonEmpty : Bool) (k : String) (j : Nat) (v : Value) (out : String) :
    String :=
  if first && j == K_LABELS then
    match v with
    | .arr xs => labelItems c xs 0 (c.ix.edgeFirstLabel.getD e 0) (memberKey out nonEmpty k j ++ "[") ++ "]"
    | v => plainMember out nonEmpty k j v
  else plainMember out nonEmpty k j v

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
