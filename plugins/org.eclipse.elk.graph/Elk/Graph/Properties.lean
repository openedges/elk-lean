import Elk.Graph.Ids
import Elk.Graph.Enum
import Elk.Core.Util.Java
import Elk.Core.Math.KVector
import Elk.Core.Math.KVectorChain
import Elk.Core.Math.Spacing
/-!
# Property system (`org.eclipse.elk.graph.properties`)

`IProperty<T>` / `MapPropertyHolder` ported with a closed value type:

* `PropValue` is the universe of layout option values (plus a `proxy` for
  option strings whose metadata was unknown at import time, like
  `LayoutOptionProxy`, and `dynamic` as a typed escape hatch).
* `Property α` carries the option id, default value and bounds; `PropCodec α`
  converts between `α` and `PropValue`.
* `PropertyMap` is a small insertion-ordered association array with
  precomputed key hashes. ELK elements rarely carry more than ten options,
  so the linear scan is faster than hashing and the iteration order is
  deterministic.

Algorithm-internal properties (`InternalProperties`) are *not* stored here;
they become typed fields of the algorithm's own graph structures.
-/
namespace Elk.Graph

open Elk Elk.Core.Util Elk.Core.Math

/-- `org.eclipse.elk.graph.properties.GraphFeature`. -/
elk_enum GraphFeature := selfLoops insideSelfLoops multiEdges edgeLabels ports compound clusters disconnected

/-- `GraphFeature.getDescription()`. -/
def GraphFeature.description : GraphFeature → String
  | .selfLoops => "Edges connecting a node with itself."
  | .insideSelfLoops => "Self-loops routed through a node instead of around it."
  | .multiEdges => "Multiple edges with the same source and target node."
  | .edgeLabels => "Labels that are associated with edges."
  | .ports => "Edges are connected to nodes over ports."
  | .compound => "Edges that connect nodes from different hierarchy levels and are incident to compound nodes."
  | .clusters => "Edges that connect nodes from different clusters, but not the cluster parent nodes."
  | .disconnected => "Multiple connected components."

/-- Property identifier with a precomputed hash. -/
structure PropKey where
  id : String
  hash : UInt64
  deriving Repr, Inhabited

namespace PropKey
def ofString (id : String) : PropKey := ⟨id, Hashable.hash id⟩
instance : BEq PropKey := ⟨fun a b => a.hash == b.hash && a.id == b.id⟩
instance : Hashable PropKey := ⟨(·.hash)⟩
instance : ToString PropKey := ⟨(·.id)⟩
end PropKey

/-- Closed universe of property values. -/
inductive PropValue where
  | bool (b : Bool)
  | int (i : Int)
  | double (d : Float)
  | string (s : String)
  /-- Enum constant by ordinal; the enum type is known from the `Property`. -/
  | enum (ordinal : Nat)
  /-- `EnumSet` bit mask over ordinals. -/
  | enumSet (bits : UInt64)
  | vector (v : KVector)
  | vectorChain (c : KVectorChain)
  | padding (p : ElkPadding)
  | margins (m : ElkMargin)
  /-- `IndividualSpacings`: a nested property map. -/
  | individualSpacings (entries : Array (PropKey × PropValue))
  | intList (xs : Array Int)
  | stringList (xs : Array String)
  | doubleList (xs : Array Float)
  /-- Unparsed option string (`LayoutOptionProxy`): decoded lazily by the typed getter. -/
  | proxy (raw : String)
  /-- Escape hatch for object values that have no dedicated constructor. -/
  | dynamic (d : Dynamic)
  deriving Inhabited

/-- Conversion between a Lean type and `PropValue`. -/
class PropCodec (α : Type) where
  enc : α → PropValue
  dec : PropValue → Option α

/-- A layout property (`IProperty<T>`): id, default value and optional bounds. -/
structure Property (α : Type) where
  key : PropKey
  default : Option α := none
  lowerBound : Option α := none
  upperBound : Option α := none

namespace Property

variable {α : Type}

/-- `new Property<>(id)`. -/
def mk' (id : String) : Property α := { key := PropKey.ofString id }

/-- `new Property<>(id, defaultValue)`. -/
def withDefault (id : String) (d : α) : Property α := { key := PropKey.ofString id, default := some d }

/-- `new Property<>(id, defaultValue, lowerBound, upperBound)`. -/
def withBounds (id : String) (d : α) (lower upper : Option α) : Property α :=
  { key := PropKey.ofString id, default := some d, lowerBound := lower, upperBound := upper }

/-- `new Property<>(otherProperty, defaultValue)`. -/
def ofProperty (p : Property α) (d : α) : Property α := { p with default := some d }

@[inline] def id (p : Property α) : String := p.key.id

instance : ToString (Property α) := ⟨fun p => p.key.id⟩
instance : BEq (Property α) := ⟨fun a b => a.key == b.key⟩
instance : Hashable (Property α) := ⟨fun p => p.key.hash⟩

end Property

/-! ## Codecs -/

namespace PropValue

/-- elk-rs `parse_value` for `BOOLEAN`: case-insensitive `true`/`false`. -/
def parseBool? (s : String) : Option Bool :=
  let l := s.toLower
  if l == "true" then some true else if l == "false" then some false else none

end PropValue

instance : PropCodec Bool where
  enc := .bool
  dec
    | .bool b => some b
    | .proxy s => PropValue.parseBool? s
    | _ => none

instance : PropCodec Int where
  enc := .int
  dec
    | .int i => some i
    | .proxy s => parseInt32? s
    | _ => none

instance : PropCodec Float where
  enc := .double
  dec
    | .double d => some d
    | .int i => some (Float.ofInt i)
    | .proxy s => parseFloat? s
    | _ => none

instance : PropCodec String where
  enc := .string
  dec
    | .string s => some s
    | .proxy s => some s
    | _ => none

/-- Enum constants: stored by ordinal, parsed leniently from strings
(trim, upper-case, `-`/space → `_`), like elk-rs `parse_enum_value`. -/
instance {α : Type} [ElkEnum α] : PropCodec α where
  enc x := .enum (ElkEnum.ordinal x)
  dec
    | .enum o => ElkEnum.ofOrdinal? o
    | .proxy s => ElkEnum.ofNameLoose? s
    | _ => none

namespace EnumSetParse

/-- Token separators of `EnumSet.parse?`. -/
@[inline] def isSep (b : UInt8) : Bool := b == 91 || b == 93 || b == 44 || ElkEnum.isWsByte b

/-- End of the token starting at `i`. -/
partial def tokenEnd (s : String) (stop i : Nat) : Nat :=
  if i < stop && !isSep (ElkEnum.utf8ByteAt s i) then tokenEnd s stop (i + 1) else i

/-- Parses the tokens from `i` on into `set`. -/
partial def go {α : Type} [ElkEnum α] (s : String) (stop i : Nat) (set : EnumSet α) : Option (EnumSet α) :=
  if i < stop then
    if isSep (ElkEnum.utf8ByteAt s i) then go s stop (i + 1) set
    else
      let j := tokenEnd s stop i
      match (ElkEnum.ofNameLooseRange? s i j : Option α) with
      | some v => go s stop j (set.insert v)
      | none => none
  else some set

end EnumSetParse

/-- elk-rs `parse_enumset_value`: tokens split on `[`, `]`, `,` and whitespace;
every token must parse, otherwise the whole value is rejected. -/
def EnumSet.parse? {α : Type} [ElkEnum α] (s : String) : Option (EnumSet α) :=
  -- byte-wise: the separators are ASCII, so the tokens are the maximal runs of other bytes
  -- (they hold no whitespace, so `trimAscii` keeps them as they are)
  EnumSetParse.go s s.utf8ByteSize 0 EnumSet.empty

instance {α : Type} [ElkEnum α] : PropCodec (EnumSet α) where
  enc s := .enumSet s.bits
  dec
    | .enumSet bits => some ⟨bits⟩
    | .proxy s => EnumSet.parse? s
    | _ => none

instance : PropCodec KVector where
  enc := .vector
  dec
    | .vector v => some v
    | .proxy s => (KVector.parse s).toOption
    | _ => none

instance : PropCodec KVectorChain where
  enc := .vectorChain
  dec
    | .vectorChain c => some c
    | .proxy s => (KVectorChain.parse s).toOption
    | _ => none

/-- elk-rs `parse_spacing_value`: only `key=value` tokens (`top`, `left`,
`bottom`, `right`); unknown keys are ignored, missing sides are `0`. -/
def parseSpacingValue? (s : String) : Option (Float × Float × Float × Float) := Id.run do
  let chars := s.toList.toArray
  let isDelim (c : Char) (d : String) : Bool := d.any (· == c)
  let mut start := 0
  while start < chars.size && isDelim chars[start]! "([{\"' \t\r\n" do
    start := start + 1
  let mut stop := chars.size
  while stop > 0 && isDelim chars[stop - 1]! ")]}\"' \t\r\n" do
    stop := stop - 1
  if start >= stop then return none
  let slice := String.ofList (chars.extract start stop).toList
  let mut top := 0.0
  let mut left := 0.0
  let mut bottom := 0.0
  let mut right := 0.0
  for tok in (slice.replace ";" ",").splitOn "," do
    let t := tok.trimAscii.toString
    if t.isEmpty then continue
    match t.splitOn "=" with
    | [] => return none
    | [_] => return none
    | k :: rest =>
      let v := ("=".intercalate rest).trimAscii.toString
      match parseFloat? v with
      | none => return none
      | some f =>
        match k.trimAscii.toString with
        | "top" => top := f
        | "left" => left := f
        | "bottom" => bottom := f
        | "right" => right := f
        | _ => pure ()
  return some (top, right, bottom, left)

instance : PropCodec ElkPadding where
  enc := .padding
  dec
    | .padding p => some p
    | .proxy s => (parseSpacingValue? s).map fun (t, r, b, l) => ⟨t, r, b, l⟩
    | _ => none

instance : PropCodec ElkMargin where
  enc := .margins
  dec
    | .margins m => some m
    | .proxy s => (parseSpacingValue? s).map fun (t, r, b, l) => ⟨t, r, b, l⟩
    | _ => none

instance : PropCodec (Array Int) where
  enc := .intList
  dec
    | .intList xs => some xs
    | _ => none

instance : PropCodec (Array String) where
  enc := .stringList
  dec
    | .stringList xs => some xs
    | _ => none

instance : PropCodec (Array Float) where
  enc := .doubleList
  dec
    | .doubleList xs => some xs
    | _ => none

instance : PropCodec Dynamic where
  enc := .dynamic
  dec
    | .dynamic d => some d
    | _ => none

instance : PropCodec PropValue where
  enc := id
  dec := some

/-! ## Property map -/

/-- `MapPropertyHolder`: insertion-ordered association array. -/
structure PropertyMap where
  entries : Array (PropKey × PropValue) := #[]
  deriving Inhabited

namespace PropertyMap

def empty : PropertyMap := {}

@[inline] def size (m : PropertyMap) : Nat := m.entries.size
@[inline] def isEmpty (m : PropertyMap) : Bool := m.entries.isEmpty

/-- An index below `a.usize` is in bounds. -/
private theorem usize_lt_size {α : Type} {a : Array α} {i : USize} (h : i < a.usize) : i.toNat < a.size := by
  have h1 : i.toNat < a.usize.toNat := (USize.lt_iff_toNat_lt).mp h
  have h2 : a.usize.toNat ≤ a.size := by
    simp only [Array.usize, Nat.toUSize]
    exact Nat.mod_le _ _
  omega

/-- Index of the entry with key `id`/`hash` from `i` on (`es.size` if absent). A plain loop:
`Array.find?`/`findIdx?` go through `forIn` and allocate their loop state on a hit. The index is a
`USize` with a proved bound (`uget`), so an iteration is a compare, a load and the hash test without
the `Nat` boxing checks (PLAN 7.1 item 15); the result is the same `Nat`. -/
private partial def indexFrom (es : Array (PropKey × PropValue)) (id : String) (hash : UInt64) (i : USize) : Nat :=
  if h : i < es.usize then
    let k := (es.uget i (usize_lt_size h)).1
    if k.hash == hash && k.id == id then i.toNat else indexFrom es id hash (i + 1)
  else es.size

@[inline] private def indexOf (m : PropertyMap) (k : PropKey) : Nat := indexFrom m.entries k.id k.hash 0

def findIdx? (m : PropertyMap) (k : PropKey) : Option Nat :=
  let i := m.indexOf k
  if i < m.entries.size then some i else none

/-- Raw stored value for a key (no default, no decoding). `@[inline]` so that the `some` of a hit
melts into the caller's decoding match instead of being allocated (PLAN 7.1 item 52); the scan
(`indexFrom`) stays out of line. -/
@[inline] def getRaw? (m : PropertyMap) (k : PropKey) : Option PropValue :=
  let i := m.indexOf k
  if h : i < m.entries.size then some m.entries[i].2 else none

def getRawById? (m : PropertyMap) (id : String) : Option PropValue :=
  m.getRaw? (PropKey.ofString id)

/-- Stores a raw value (replacing an existing entry in place, keeping its position). -/
def setRaw (m : PropertyMap) (k : PropKey) (v : PropValue) : PropertyMap :=
  let i := m.indexOf k
  if i < m.entries.size then { entries := m.entries.set! i (k, v) }
  else { entries := m.entries.push (k, v) }

def setRawById (m : PropertyMap) (id : String) (v : PropValue) : PropertyMap :=
  m.setRaw (PropKey.ofString id) v

def removeRaw (m : PropertyMap) (k : PropKey) : PropertyMap :=
  let i := m.indexOf k
  if i < m.entries.size then { entries := m.entries.eraseIdx! i } else m

@[inline] def hasKey (m : PropertyMap) (k : PropKey) : Bool := m.indexOf k < m.entries.size

@[inline] def hasId (m : PropertyMap) (id : String) : Bool := m.hasKey (PropKey.ofString id)

/-- Stored value decoded to `α`, ignoring the default. -/
@[inline] def get? {α : Type} [PropCodec α] (m : PropertyMap) (p : Property α) : Option α :=
  (m.getRaw? p.key).bind PropCodec.dec

/-- Java `getProperty`: stored value, else the property's default (`none` = Java `null`). -/
@[inline] def get {α : Type} [PropCodec α] (m : PropertyMap) (p : Property α) : Option α :=
  match m.get? p with
  | some v => some v
  | none => p.default

/-- `getProperty` with an explicit fallback. -/
@[inline] def getD {α : Type} [PropCodec α] (m : PropertyMap) (p : Property α) (d : α) : α :=
  (m.get p).getD d

/-- `getProperty` for properties that always have a default; falls back to `Inhabited`. -/
@[inline] def get! {α : Type} [PropCodec α] [Inhabited α] (m : PropertyMap) (p : Property α) : α :=
  (m.get p).getD default

/-- Java `hasProperty`. -/
@[inline] def has {α : Type} (m : PropertyMap) (p : Property α) : Bool := m.hasKey p.key

/-- Java `setProperty(property, value)`. -/
@[inline] def set {α : Type} [PropCodec α] (m : PropertyMap) (p : Property α) (v : α) : PropertyMap :=
  m.setRaw p.key (PropCodec.enc v)

/-- `setProperty(property, null)` removes the entry. -/
@[inline] def setOpt {α : Type} [PropCodec α] (m : PropertyMap) (p : Property α) (v : Option α) : PropertyMap :=
  match v with
  | some v => m.set p v
  | none => m.removeRaw p.key

@[inline] def remove {α : Type} (m : PropertyMap) (p : Property α) : PropertyMap := m.removeRaw p.key

/-- Java `copyProperties(other)`: `putAll`, overwriting existing keys. -/
def copyFrom (m other : PropertyMap) : PropertyMap :=
  if m.isEmpty then other
  else other.entries.foldl (fun acc e => acc.setRaw e.1 e.2) m

def keys (m : PropertyMap) : Array PropKey := m.entries.map (·.1)

def clear (_ : PropertyMap) : PropertyMap := {}

end PropertyMap

end Elk.Graph
