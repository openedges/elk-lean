import Tests.Framework
import Elk.Json
import Elk.Core.Util.Random
/-!
Differential tests of the member-mask lookups (`Value.keyMask`, `lookupK`, `getK` and the
`JsonAdapter.…K` accessors of the importer) against the plain lookups they replace, and of the
parser's shared small-integer values.

The mask is exact only if `Key.candidateIndex` maps the bytes of every member name `Key.all[j]` to
`j` (then `Key.idOf k = j` exactly when `k == Key.all[j]`), and if the bit constants `Key.b…` are
`1 <<< j`: both are checked first. Then random objects (member names from `Key.all` as the shared
constants and as fresh copies, near misses, other names, duplicates, non-object values) must give the
same answer for every member name through both paths, including the importer's error texts.
-/
namespace Tests.Json.KeyMask

open Tests Elk.Json Elk.Core.Util

/-- The bit constants with the member names they stand for. -/
def bits : Array (String × UInt64) := #[
  (Key.id, Key.bId), (Key.x, Key.bX), (Key.y, Key.bY), (Key.width, Key.bWidth), (Key.height, Key.bHeight),
  (Key.labels, Key.bLabels), (Key.text, Key.bText), (Key.ports, Key.bPorts),
  (Key.layoutOptions, Key.bLayoutOptions), (Key.properties, Key.bProperties), (Key.children, Key.bChildren),
  (Key.edges, Key.bEdges), (Key.sources, Key.bSources), (Key.targets, Key.bTargets), (Key.source, Key.bSource),
  (Key.target, Key.bTarget), (Key.sourcePort, Key.bSourcePort), (Key.targetPort, Key.bTargetPort),
  (Key.sections, Key.bSections), (Key.startPoint, Key.bStartPoint), (Key.endPoint, Key.bEndPoint),
  (Key.bendPoints, Key.bBendPoints), (Key.incomingShape, Key.bIncomingShape),
  (Key.outgoingShape, Key.bOutgoingShape), (Key.incomingSections, Key.bIncomingSections),
  (Key.outgoingSections, Key.bOutgoingSections), (Key.individualSpacings, Key.bIndividualSpacings)]

/-- A copy of `s` in a fresh string object (not pointer-equal to `s`). -/
def fresh (s : String) : String := String.ofList s.toList

/-- Member names of the random objects: the ELK names (shared and fresh), near misses and others. -/
def names : Array String :=
  Key.all ++ Key.all.map fresh ++
  #["", "X", "Y", "ID", "idx", "i", "xx", "widtH", "height ", "label", "port", "sourcePorts", "targetPoint",
    "sourcePoint", "junctionPoint", "child", "edge", "section", "layoutoptions", "propertie", "texts",
    "incomingShapes", "outgoingSection", "individualSpacing", "é", "x\u0000", "sourcE", "targetS", "contain"]

/-- A random JSON value of depth at most `d`. -/
def randomValue (r : Random) (d : Nat) : Value × Random :=
  let (k, r) := r.nextInt (if d == 0 then 7 else 9)
  match k.toNat with
  | 0 => (.null, r)
  | 1 => (.bool true, r)
  | 2 => let (i, r) := r.nextInt 2000; (.num (.int (i - 1000)), r)
  | 3 => let (i, r) := r.nextInt 1000; (.num (.float (Float.ofInt i / 8.0)), r)
  | 4 => (.str "n1", r)
  | 5 => let (i, r) := r.nextInt 50; (.str s!"{i}.5", r)
  | 6 => (.str "abc", r)
  | 7 => (.arr #[.str "n1", .num (.int 3)], r)
  | _ => (.obj #[(Key.x, .num (.int 1)), (Key.y, .num (.int 2))], r)

/-- A random object of up to 10 members (names may repeat). -/
def randomObject (r : Random) : Array (String × Value) × Random := Id.run do
  let (n, r1) := r.nextInt 11
  let mut r := r1
  let mut kvs : Array (String × Value) := #[]
  for _ in [0:n.toNat] do
    let (ki, r2) := r.nextInt names.size
    let (v, r3) := randomValue r2 1
    r := r3
    kvs := kvs.push (names[ki.toNat]!, v)
  return (kvs, r)

/-- The plain reference of `keyMask`: bit `j` for every `Key.all[j]` some member is equal to. -/
def maskReference (kvs : Array (String × Value)) : UInt64 := Id.run do
  let mut m : UInt64 := 0
  for h : j in [0:Key.all.size] do
    if kvs.any (·.1 == Key.all[j]) then m := m ||| ((1 : UInt64) <<< j.toUInt64)
  return m

/-- An optional value compared structurally. -/
def optEq (a b : Option Value) : Bool :=
  match a, b with
  | some x, some y => x == y
  | none, none => true
  | _, _ => false

/-- Result of an importer accessor: value or error text. -/
def runI {α : Type} (x : ImportM α) : IO (Except String α) := do
  try
    let ((a, _), _) ← (ImportM.run x).run {}
    return .ok a
  catch e => return .error (toString e)

/-- Two accessor results agree (values by `eq`, errors by text). -/
def sameI {α : Type} (eq : α → α → Bool) (a b : Except String α) : Bool :=
  match a, b with
  | .ok x, .ok y => eq x y
  | .error x, .error y => x == y
  | _, _ => false

def suite : Suite := Tests.suite "json.key_mask" do
  -- the index of every member name and the bit constants
  let mut badIdx : Array String := #[]
  for h : j in [0:Key.all.size] do
    let k := Key.all[j]
    if Key.candidateIndex k 0 k.utf8ByteSize != j then badIdx := badIdx.push s!"candidateIndex {k}"
    if Key.idOf k != j then badIdx := badIdx.push s!"idOf {k}"
    if Key.idOf (fresh k) != j then badIdx := badIdx.push s!"idOf fresh {k}"
  checkEq "candidateIndex and idOf of every member name" badIdx #[]
  let badBits := bits.filter fun (k, b) => b != (1 : UInt64) <<< (Key.idOf k).toUInt64 || Key.idOf k == Key.all.size
  checkEq "bit constants are 1 <<< index" (badBits.map (·.1)) #[]
  checkEq "names outside Key.all have no index"
    ((names.filter fun k => !Key.all.contains k && Key.idOf k != Key.all.size)) #[]
  -- random objects
  let mut r := Random.ofInt 11
  let mut bad : Array String := #[]
  let mut n := 0
  for _ in [0:3000] do
    let (kvs, r') := randomObject r
    r := r'
    let obj : Value := .obj kvs
    let m := Value.keyMask kvs
    if m != maskReference kvs || obj.keyMaskOf != m then bad := bad.push s!"mask {obj.render}"
    for (k, b) in bits do
      n := n + 1
      if !optEq (Value.lookupK kvs m b k) (Value.lookup kvs k) then bad := bad.push s!"lookupK {k} {obj.render}"
      if !optEq (obj.getK m b k) (obj.get? k) then bad := bad.push s!"getK {k} {obj.render}"
      if JsonAdapter.hasKeyK m b != JsonAdapter.hasKey obj k then bad := bad.push s!"hasKeyK {k} {obj.render}"
      if (JsonAdapter.optArrayK obj m b k).map Value.arr != (JsonAdapter.optArray obj k).map Value.arr then
        bad := bad.push s!"optArrayK {k} {obj.render}"
      if !optEq (JsonAdapter.optObjectK obj m b k) (JsonAdapter.optObject obj k) then
        bad := bad.push s!"optObjectK {k} {obj.render}"
      let s1 ← runI (JsonAdapter.optStringK obj m b k)
      let s2 ← runI (JsonAdapter.optString obj k)
      if !sameI (· == ·) s1 s2 then bad := bad.push s!"optStringK {k} {obj.render}"
      let d1 ← runI (JsonAdapter.optDoubleK obj m b k)
      let d2 ← runI (JsonAdapter.optDouble obj k)
      if !sameI (fun a b => a.map Float.toBits == b.map Float.toBits) d1 d2 then bad := bad.push s!"optDoubleK {k} {obj.render}"
    let i1 ← runI (JsonAdapter.getIdK obj m)
    let i2 ← runI (JsonAdapter.getId obj)
    if !sameI (fun a b => a.asString == b.asString) i1 i2 then bad := bad.push s!"getIdK {obj.render}"
    let v1 ← runI (JsonAdapter.idSaveK obj m)
    let v2 ← runI (JsonAdapter.idSave obj)
    if !sameI (· == ·) v1 v2 then bad := bad.push s!"idSaveK {obj.render}"
    if bad.size > 20 then break
  checkEq s!"masked lookups agree with the plain ones ({n} lookups)" (bad.extract 0 20) #[]
  -- parsed documents (member names shared by the parser) and non-objects
  match Elk.Json.parse "{\"id\":\"a\",\"x\":1,\"x\":2,\"labels\":[],\"layoutOptions\":{\"x\":3},\"foo\":null,\"id\":\"b\"}" with
  | .ok v@(.obj kvs) =>
    checkEq "parsed mask" (Value.keyMask kvs) (Key.bId ||| Key.bX ||| Key.bLabels ||| Key.bLayoutOptions)
    check "first duplicate wins" (optEq (v.getK v.keyMaskOf Key.bX Key.x) (some (.num (.int 1))))
    check "absent member" (optEq (v.getK v.keyMaskOf Key.bY Key.y) none)
  | _ => check "parsed object expected" false
  checkEq "mask of a non-object" (Value.arr #[.str "id"]).keyMaskOf 0

def smallInts : Suite := Tests.suite "json.parser.small_ints" do
  let bad := (List.range Elk.Json.Parser.smallIntValues.size).filter fun i =>
    !(Elk.Json.Parser.smallIntValues[i]! == .num (.int i))
  checkEq "smallIntValues[i] = .num (.int i)" bad []
  match Elk.Json.parse "[0, 1, 1023, 1024, -1, -0, 007]" with
  | .ok _ => check "leading zeros rejected" false
  | .error _ => pure ()
  match Elk.Json.parse "[0, 1, 1023, 1024, -1, -0, 1023.0]" with
  | .ok v => checkEq "numbers around the table" v.render "[0,1,1023,1024,-1,-0.0,1023.0]"
  | .error e => check s!"parse error {e}" false

def suites : Array Suite := #[suite, smallInts]

end Tests.Json.KeyMask
