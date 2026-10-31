import Tests.Framework
import Elk.Api
import Tests.Json.PrinterReference
import Tests.Json.ParserFuzz
/-!
# Overlay transfer and printers (JSN)

* `json.overlay.cases` / `json.overlay.corpus`: after import and layout, the reference transfer
  (`JsonImporter.transferLayout`, which rewrites the document) and the overlay transfer
  (`transferLayoutOverlay`) must fail with the same error or both succeed; when the overlay applies
  (`Overlay.ok`), `OverlayPrinter.render` and `Overlay.materialize` (compact, pretty, sorted) must
  give the bytes of the rewritten document. The cases cover duplicate members, non-object array
  entries, escaped and numeric ids, input sections, primitive edges, coordinate modes, inside self
  loops (compaction), hierarchies and duplicate node ids (no overlay). The corpus suite runs every
  `*.json` below `$ELK_MODELS_DIR` (default `external/elk-models`).
* `json.printer.differential`: `Value.render`/`renderPretty` against the previous printer
  (`Tests.Json.PrinterReference`) on the parser seeds, the cases and the corpus documents.
* `json.printer.append`: the C appenders (`appendJsonFloat`, `appendElkNumber`,
  `appendPreElkNumber`, `appendPoint`, `append3`, `stringWithCapacity`) against the Lean renderings,
  including non-ASCII strings (the character count of the result).
-/
namespace Tests.Json.Overlay

open Tests Elk Elk.Graph Elk.Core Elk.Core.Util Elk.Json

/-- The imported and laid-out state of a document (as `Elk.Api.layoutTransfer` prepares it), or
`none` when parsing, importing or the layout fails. -/
def prepare (text : String) : IO (Option (ImporterState × ElkGraph)) := do
  Elk.Api.ensureInitialized
  match Elk.Json.parse text with
  | .error _ => return none
  | .ok input =>
    try
      let ((root, st), g) ← (ImportM.run (JsonImporter.transform input) { defaults := some {} }).run {}
      let ((), g) ← (RecursiveGraphLayoutEngine.layout root (ProgressMonitor.null)).run g
      return some (st, g)
    catch _ => return none

/-- Outcome of the comparison of one document. -/
inductive Outcome where
  | skipped
  | sameError
  | fallback
  | same
  | differs (msg : String)

/-- Compares the reference transfer with the overlay on one document. -/
def compareDoc (text : String) : IO Outcome := do
  let some (st, g) ← prepare text | return .skipped
  let ref ← try
      let (((), st1), _) ← (ImportM.run JsonImporter.transferLayout st).run g
      pure (Except.ok st1.model)
    catch e => pure (Except.error (toString e))
  let ovr ← try
      let ((ov, st2), _) ← (ImportM.run JsonImporter.transferLayoutOverlay st).run g
      pure (Except.ok (ov, st2))
    catch e => pure (Except.error (toString e))
  match ref, ovr with
  | .error a, .error b => return if a == b then .sameError else .differs s!"errors {a} / {b}"
  | .error a, .ok _ => return .differs s!"reference error {a}, overlay none"
  | .ok _, .error b => return .differs s!"overlay error {b}, reference none"
  | .ok model, .ok (ov, st2) =>
    if !ov.ok then return .fallback
    let c := Overlay.Ctx.ofState st2 ov
    let expected := PrinterReference.render model
    let printed := OverlayPrinter.render c st2.model
    if printed != expected then return .differs "OverlayPrinter.render"
    let mat := Overlay.materialize c st2.model
    if mat.render != expected then return .differs "materialize compact"
    if mat.render true != PrinterReference.render model true then return .differs "materialize sorted"
    if mat.renderPretty true != PrinterReference.renderPretty model true then return .differs "materialize pretty sorted"
    if mat.renderPretty != PrinterReference.renderPretty model then return .differs "materialize pretty"
    return .same

/-- Hand-written documents exercising the placement rules of the overlay. -/
def cases : Array String := #[
  -- layered with ports, port/node/edge labels and orthogonal hyperedges (junction points)
  "{\"id\":\"root\",\"layoutOptions\":{\"elk.algorithm\":\"layered\",\"elk.edgeRouting\":\"ORTHOGONAL\"},\"children\":[{\"id\":\"a\",\"width\":30,\"height\":30,\"labels\":[{\"text\":\"A\",\"width\":10,\"height\":10}],\"ports\":[{\"id\":\"a.p\",\"width\":4,\"height\":4,\"labels\":[{\"id\":\"pl\",\"text\":\"p\",\"width\":5,\"height\":5}]}]},{\"id\":\"b\",\"width\":20,\"height\":20},{\"id\":\"c\",\"width\":20,\"height\":20}],\"edges\":[{\"id\":\"e1\",\"sources\":[\"a.p\"],\"targets\":[\"b\"],\"labels\":[{\"text\":\"l1\",\"width\":12,\"height\":8}]},{\"id\":\"e2\",\"sources\":[\"a.p\"],\"targets\":[\"c\"]}]}",
  -- duplicate members (the first one is the element's), non-object array entries, the root's x
  "{\"id\":\"root\",\"x\":1,\"x\":2,\"children\":[1,{\"id\":\"n1\",\"width\":10,\"width\":11,\"height\":5,\"ports\":[null,{\"id\":\"p1\"},\"z\"],\"labels\":[\"t\",{\"text\":\"L\"}]},\"s\",{\"id\":\"n2\",\"children\":[{\"id\":\"n3\",\"width\":3,\"height\":3}]}],\"edges\":[7,{\"id\":\"e\",\"sources\":[\"n1\"],\"targets\":[\"n3\"],\"sections\":3,\"sections\":[]}],\"children\":5}",
  -- a first `children` member that is not an array (no children), a second `edges` member
  "{\"id\":\"root\",\"children\":5,\"children\":[{\"id\":\"n\"}],\"width\":3,\"edges\":[],\"edges\":[1]}",
  -- escaped and numeric ids, section ids built from them
  "{\"id\":\"r\\\"oot\",\"children\":[{\"id\":1,\"width\":10,\"height\":10},{\"id\":\"n\\u00e9\\n\",\"width\":10,\"height\":10}],\"edges\":[{\"id\":\"e\\\"1\",\"sources\":[1],\"targets\":[\"n\\u00e9\\n\"]},{\"id\":2,\"sources\":[\"n\\u00e9\\n\"],\"targets\":[1]}]}",
  -- input sections (ids, shapes, linked sections, extra members) and a second `sections` member
  "{\"id\":\"root\",\"layoutOptions\":{\"algorithm\":\"fixed\"},\"children\":[{\"id\":\"a\",\"x\":0,\"y\":0,\"width\":10,\"height\":10},{\"id\":\"b\",\"x\":50,\"y\":0,\"width\":10,\"height\":10}],\"edges\":[{\"id\":\"e\",\"sources\":[\"a\"],\"targets\":[\"b\"],\"sections\":[{\"id\":\"s1\",\"extra\":true,\"startPoint\":{\"x\":10,\"y\":5},\"endPoint\":{\"x\":30,\"y\":5},\"outgoingSections\":[\"s2\"],\"incomingShape\":\"a\"},{\"id\":\"s2\",\"startPoint\":{\"x\":30,\"y\":5},\"endPoint\":{\"x\":50,\"y\":5},\"bendPoints\":[{\"x\":40,\"y\":9}],\"incomingSections\":[\"s1\"],\"outgoingShape\":\"b\"}],\"junctionPoints\":0,\"container\":\"x\",\"sections\":\"again\"}]}",
  -- primitive edges (`source`/`target`, `sourcePoint`, `bendPoints`) and a hyperedge
  "{\"id\":\"root\",\"layoutOptions\":{\"algorithm\":\"fixed\"},\"children\":[{\"id\":\"a\",\"x\":0,\"y\":0,\"width\":10,\"height\":10,\"ports\":[{\"id\":\"ap\",\"x\":10,\"y\":5}]},{\"id\":\"b\",\"x\":40,\"y\":0,\"width\":10,\"height\":10},{\"id\":\"c\",\"x\":40,\"y\":30,\"width\":10,\"height\":10}],\"edges\":[{\"id\":\"p\",\"source\":\"a\",\"sourcePort\":\"ap\",\"target\":\"b\",\"sourcePoint\":{\"x\":10,\"y\":5},\"targetPoint\":{\"x\":40,\"y\":5},\"bendPoints\":[{\"x\":25,\"y\":5}]},{\"id\":\"h\",\"sources\":[\"a\"],\"targets\":[\"c\"]}]}",
  -- coordinate modes on a hierarchy laid out with INCLUDE_CHILDREN
  "{\"id\":\"root\",\"layoutOptions\":{\"algorithm\":\"layered\",\"hierarchyHandling\":\"INCLUDE_CHILDREN\",\"org.eclipse.elk.json.edgeCoords\":\"ROOT\",\"org.eclipse.elk.json.shapeCoords\":\"ROOT\"},\"children\":[{\"id\":\"p\",\"children\":[{\"id\":\"c1\",\"width\":10,\"height\":10,\"labels\":[{\"text\":\"x\",\"width\":4,\"height\":4}]},{\"id\":\"c2\",\"width\":10,\"height\":10}],\"edges\":[{\"id\":\"ce\",\"sources\":[\"c1\"],\"targets\":[\"c2\"],\"labels\":[{\"text\":\"y\",\"width\":4,\"height\":4}]}],\"layoutOptions\":{\"org.eclipse.elk.json.edgeCoords\":\"PARENT\"}},{\"id\":\"q\",\"width\":10,\"height\":10}],\"edges\":[{\"id\":\"x\",\"sources\":[\"c1\"],\"targets\":[\"q\"]}]}",
  -- edge coordinates relative to the container, nested edges
  "{\"id\":\"root\",\"layoutOptions\":{\"algorithm\":\"layered\"},\"children\":[{\"id\":\"p\",\"layoutOptions\":{\"org.eclipse.elk.json.edgeCoords\":\"CONTAINER\"},\"children\":[{\"id\":\"c1\",\"width\":10,\"height\":10},{\"id\":\"c2\",\"width\":10,\"height\":10}],\"edges\":[{\"id\":\"ce\",\"sources\":[\"c1\"],\"targets\":[\"c2\"]}]}]}",
  -- inside self loops (compaction of zero-sized port nodes, port shifts)
  "{\"id\":\"root\",\"layoutOptions\":{\"algorithm\":\"layered\"},\"children\":[{\"id\":\"n\",\"width\":40,\"height\":40,\"layoutOptions\":{\"org.eclipse.elk.insideSelfLoops.activate\":true},\"ports\":[{\"id\":\"w\",\"layoutOptions\":{\"org.eclipse.elk.port.side\":\"WEST\"}},{\"id\":\"e\",\"layoutOptions\":{\"org.eclipse.elk.port.side\":\"EAST\"}}],\"edges\":[{\"id\":\"s\",\"sources\":[\"e\"],\"targets\":[\"w\"],\"layoutOptions\":{\"org.eclipse.elk.insideSelfLoops.yo\":true}}]},{\"id\":\"m\",\"width\":10,\"height\":10}],\"edges\":[{\"id\":\"o\",\"sources\":[\"e\"],\"targets\":[\"m\"]}]}",
  -- self loops on a node, labels on every element kind
  "{\"id\":\"root\",\"layoutOptions\":{\"algorithm\":\"layered\",\"edgeRouting\":\"SPLINES\"},\"children\":[{\"id\":\"a\",\"width\":20,\"height\":20,\"labels\":[{\"text\":\"a\",\"width\":5,\"height\":5},{\"text\":\"b\",\"width\":5,\"height\":5}]},{\"id\":\"b\",\"width\":20,\"height\":20}],\"edges\":[{\"id\":\"l\",\"sources\":[\"a\"],\"targets\":[\"a\"]},{\"id\":\"ab\",\"sources\":[\"a\"],\"targets\":[\"b\"],\"labels\":[{\"text\":\"m\",\"width\":6,\"height\":6,\"layoutOptions\":{\"edgeLabels.placement\":\"HEAD\"}},{\"text\":\"n\",\"width\":6,\"height\":6}]}]}",
  -- duplicate node ids (no overlay)
  "{\"id\":\"root\",\"children\":[{\"id\":\"a\",\"width\":10,\"height\":10,\"edges\":[{\"id\":\"e1\",\"sources\":[\"a\"],\"targets\":[\"b\"]}]},{\"id\":\"a\",\"width\":10,\"height\":10},{\"id\":\"b\",\"width\":10,\"height\":10}],\"edges\":[{\"id\":\"e2\",\"sources\":[\"b\"],\"targets\":[\"a\"]}]}",
  -- other algorithms: mrtree, radial, force, rectpacking, empty graph
  "{\"id\":\"root\",\"layoutOptions\":{\"algorithm\":\"mrtree\"},\"children\":[{\"id\":\"a\",\"width\":10,\"height\":10},{\"id\":\"b\",\"width\":10,\"height\":10},{\"id\":\"c\",\"width\":10,\"height\":10}],\"edges\":[{\"id\":\"e1\",\"sources\":[\"a\"],\"targets\":[\"b\"]},{\"id\":\"e2\",\"sources\":[\"a\"],\"targets\":[\"c\"]}]}",
  "{\"id\":\"root\",\"layoutOptions\":{\"algorithm\":\"radial\"},\"children\":[{\"id\":\"a\",\"width\":10,\"height\":10},{\"id\":\"b\",\"width\":10.5,\"height\":10},{\"id\":\"c\",\"width\":10,\"height\":-0.0}],\"edges\":[{\"id\":\"e1\",\"sources\":[\"a\"],\"targets\":[\"b\"]},{\"id\":\"e2\",\"sources\":[\"a\"],\"targets\":[\"c\"]}]}",
  "{\"id\":\"root\",\"layoutOptions\":{\"algorithm\":\"force\"},\"children\":[{\"id\":\"a\",\"width\":10,\"height\":10},{\"id\":\"b\",\"width\":10,\"height\":10}],\"edges\":[{\"id\":\"e1\",\"sources\":[\"a\"],\"targets\":[\"b\"]}]}",
  "{\"id\":\"root\",\"layoutOptions\":{\"algorithm\":\"rectpacking\"},\"children\":[{\"id\":\"a\",\"width\":10,\"height\":10},{\"id\":\"b\",\"width\":13,\"height\":7}]}",
  "{\"id\":\"root\"}",
  -- a self loop with an input section
  "{\"id\":\"root\",\"layoutOptions\":{\"algorithm\":\"fixed\"},\"children\":[{\"id\":\"a\"}],\"edges\":[{\"id\":\"e\",\"sources\":[\"a\"],\"targets\":[\"a\"],\"sections\":[{\"id\":\"s\",\"startPoint\":{\"x\":0,\"y\":0},\"endPoint\":{\"x\":0,\"y\":0}}]}]}"
]

/-- Runs `compareDoc` on documents and reports mismatches; returns the outcome counts
`(same, fallback, sameError, skipped)`. -/
def runDocs (label : String) (docs : Array (String × String)) : TestM (Nat × Nat × Nat × Nat) := do
  let mut same := 0
  let mut fallback := 0
  let mut sameError := 0
  let mut skipped := 0
  for (name, text) in docs do
    match ← compareDoc text with
    | .same => same := same + 1
    | .fallback => fallback := fallback + 1
    | .sameError => sameError := sameError + 1
    | .skipped =>
      skipped := skipped + 1
      if label == "case" then report s!"{label} {name} laid out" false "parse, import or layout failed"
    | .differs msg => report s!"{label} {name}" false msg
  return (same, fallback, sameError, skipped)

def casesSuite : Suite := suite "json.overlay.cases" do
  let docs := (cases.mapIdx fun i t => (s!"case {i}", t))
  let (same, fallback, sameError, skipped) ← runDocs "case" docs
  checkEq "cases laid out" (same + fallback + sameError + skipped) cases.size
  check "overlay used" (same >= 12)
  check "duplicate node ids fall back" (fallback >= 1)

/-- Directory of the model corpus. -/
def corpusDir : IO System.FilePath := do
  match ← IO.getEnv "ELK_MODELS_DIR" with
  | some d => return d
  | none => return "external/elk-models"

/-- The `*.json` documents below the corpus directory, sorted by path. -/
def corpusDocs : IO (Array (String × String)) := do
  let dir ← corpusDir
  if !(← dir.isDir) then return #[]
  let files := (← dir.walkDir).filter fun f => f.extension == some "json"
  let names : Array String := files.map (·.toString)
  let names := Elk.Core.Util.stableSort names fun a b => compare a b
  names.mapM fun (f : String) => do return (f, ← IO.FS.readFile (System.FilePath.mk f))

def corpusSuite : Suite := suite "json.overlay.corpus" do
  let docs ← corpusDocs
  if docs.isEmpty then
    IO.println "json.overlay.corpus: no corpus below $ELK_MODELS_DIR / external/elk-models; skipping"
    return
  let (same, fallback, sameError, skipped) ← runDocs "corpus" docs
  IO.println s!"json.overlay.corpus: {docs.size} documents, overlay {same}, fallback {fallback}, same error {sameError}, skipped {skipped}"
  check "corpus overlay used" (same > docs.size / 2)

/-- `Value.render`/`renderPretty` (all four modes) against the reference printer. -/
def printerSame (v : Value) : Bool :=
  v.render == PrinterReference.render v && v.render true == PrinterReference.render v true &&
    v.renderPretty == PrinterReference.renderPretty v && v.renderPretty true == PrinterReference.renderPretty v true

def printerSuite : Suite := suite "json.printer.differential" do
  let mut docs : Array String := Tests.Json.ParserFuzz.seeds ++ cases
  docs := docs ++ (← corpusDocs).map (·.2)
  let mut n := 0
  for text in docs do
    for lenient in [false, true] do
      if let .ok v := Elk.Json.parse text lenient then
        n := n + 1
        if !printerSame v then report "printer" false (text.take 80).toString
  check "documents printed" (n > 0)
  -- values the parser does not produce: escapes in member names, control characters, non-finite
  -- doubles, `-0.0`, big integers
  let v : Value := .obj #[("a\"b", .str "\x01\x1fé\n"), ("x", .num (.float (0.0 / 0.0))),
    ("y", .num (.float (-0.0))), ("z", .arr #[.num (.int (-12345678901234567890)), .num (.float 1e300),
      .num (.float (1.0 / 0.0)), .num (.float 5e-324)]), ("id", .str "q\""), ("width", .str "plain")]
  check "special values" (printerSame v)

/-- Doubles for the appender checks. -/
def sampleDoubles : Array Float := Id.run do
  let mut xs : Array Float := #[0.0, -0.0, 1.0, -1.0, 0.5, 12.0, 1e21, 1e22, 1.5e-7, 123456789012345680.0,
    9007199254740993.0, 9223372036854775807.0, -9223372036854775808.0, 1.8446744073709552e19,
    5e-324, 1.7976931348623157e308, 0.0 / 0.0, 1.0 / 0.0, -1.0 / 0.0, 68.67924528301887, 2911.3333333333335]
  let mut r := Random.ofInt 11
  for _ in [0:3000] do
    let (bits, r1) := r.nextLong
    let (k, r2) := r1.nextInt 4
    r := r2
    let x := Float.ofBits (Int.toUInt64Wrap bits)
    -- also integral values and small decimals
    xs := xs.push (if k == 0 then x else if k == 1 then x.round else if k == 2 then (x / 1e300).round else x / 1e290)
  return xs

def appendSuite : Suite := suite "json.printer.append" do
  let mut bad := 0
  for x in sampleDoubles do
    let n := Number.ofFloatElk x
    if appendElkNumber "ab" x != "ab" ++ n.render then bad := bad + 1
    if appendPreElkNumber "ab" ",\"é\":" x != "ab" ++ ",\"é\":" ++ n.render then bad := bad + 1
    if appendJsonFloat "" x != (Number.float x).render then bad := bad + 1
    if appendPoint "[" "," x (-x) != "[" ++ "," ++ (Value.obj #[(Key.x, .ofFloatElk x), (Key.y, .ofFloatElk (-x))]).render then
      bad := bad + 1
  checkEq "number appenders" bad 0
  let s := append3 (stringWithCapacity 4) "é" "ü😀" "x"
  checkEq "append3" s "éü😀x"
  checkEq "append3 length" s.length 4
  let t := appendPoint s "→" 1.5 2.0
  checkEq "appendPoint length" t.length ("éü😀x→{\"x\":1.5,\"y\":2}".length)
  checkEq "appendPoint after unicode" t "éü😀x→{\"x\":1.5,\"y\":2}"
  -- a shared string is not changed in place
  let base := "shared"
  let a := append3 base "1" "" ""
  let b := append3 base "2" "" ""
  checkEq "shared base" (base, a, b) ("shared", "shared1", "shared2")

def suites : Array Suite := #[casesSuite, corpusSuite, printerSuite, appendSuite]

end Tests.Json.Overlay
