import Tests.Framework
/-!
# Tests for the core metadata registration

`CoreOptions`/`BoxLayouterOptions`/`LabelManagementOptions` providers, the core algorithm
entries and the lazy initialisation through `LayoutMetaDataService.getInstance`.

Expected counts are derived from the Rust sources of elk-rs:
* `core_options_meta.rs`: 94 `register_*option` calls (all with distinct ids), 7
  `register_category` calls and 10 `add_dependency` calls;
* `box_layouter_options.rs` re-registers `org.eclipse.elk.box.packingMode` (replaces the entry);
* `label_management_options.rs` adds `org.eclipse.elk.labels.labelManager` (95 options in total);
* `register_core_algorithms`: fixed, random, box and the layered placeholder (4 algorithms);
  fixed/random/box have no category, so the backup category "Other" is created (8 categories).
-/
namespace Tests.Core.Meta

open Tests Elk Elk.Graph Elk.Core.Math Elk.Core.Data Elk.Core.Options Elk.Core.Labels
open Elk.Core.Data.LayoutMetaDataService

/-- Looks up an option by id; reports a failure (and returns a dummy) if missing. -/
def opt (id : String) : TestM LayoutOptionData := do
  match ← LayoutMetaDataService.getOptionData id with
  | some d => return d
  | none =>
    report s!"option {id} registered" false
    return { id }

/-- Looks up an algorithm by id; reports a failure (and returns a dummy) if missing. -/
def alg (id : String) : TestM LayoutAlgorithmData := do
  match ← LayoutMetaDataService.getAlgorithmData id with
  | some d => return d
  | none =>
    report s!"algorithm {id} registered" false
    return { id }

def isDouble (v : Option PropValue) (x : Float) : Bool :=
  match v with | some (.double y) => y == x | _ => false

def isInt (v : Option PropValue) (x : Int) : Bool :=
  match v with | some (.int y) => y == x | _ => false

def isBool (v : Option PropValue) (x : Bool) : Bool :=
  match v with | some (.bool y) => y == x | _ => false

/-- The value decoded as the enum / object type `α` equals `x`. -/
def isVal {α : Type} [PropCodec α] [BEq α] (v : Option PropValue) (x : α) : Bool :=
  (v.bind PropCodec.dec : Option α) == some x

def lowerIs (d : LayoutOptionData) (exclusive : Bool) (x : Float) : Bool :=
  match d.lowerBound with
  | some b => b.isExclusive == exclusive && isDouble (some b.value) x
  | none => false

def depTarget (d : LayoutOptionData) : String := ((d.dependencies[0]?).map (·.optionId)).getD ""

def depValue (d : LayoutOptionData) : Option PropValue := (d.dependencies[0]?).bind (·.requiredValue)

def hasTargets (d : LayoutOptionData) (ts : Array LayoutOptionTarget) : Bool :=
  d.targets == EnumSet.of ts

def countDependencies (ds : Array LayoutOptionData) : Nat :=
  ds.foldl (fun n d => n + d.dependencies.size) 0

def counts : Suite := suite "core.meta.counts" do
  let s ← LayoutMetaDataService.getInstance
  checkEq "option count (core 95 + layered 89 + disco 4 + force 5 + spore 10 + stress 5 + topdownpacking 2)" s.optionDataList.size 210
  checkEq "option order size" s.optionOrder.size 210
  checkEq "category count" s.categoryDataList.size 8
  checkEq "algorithm count" s.algorithmDataList.size 10
  checkEq "dependency count" (countDependencies s.optionDataList) 10
  checkEq "legacy options (layered Java ids)" s.legacyOptions.size 89
  -- elk-rs order (`layout_api.rs`): core, layered, disco, force, (mrtree, radial, rectpacking,)
  -- spore, stress, (vertiflex); topdownpacking (not registered by elk-rs) last
  checkEqR "algorithm order" s.algorithmOrder
    #["org.eclipse.elk.fixed", "org.eclipse.elk.random", "org.eclipse.elk.box", "org.eclipse.elk.layered",
      "org.eclipse.elk.disco", "org.eclipse.elk.force", "org.eclipse.elk.sporeOverlap",
      "org.eclipse.elk.sporeCompaction", "org.eclipse.elk.stress", "org.eclipse.elk.topdownpacking"]
  checkEqR "category order" s.categoryOrder
    #["org.eclipse.elk.layered", "org.eclipse.elk.orthogonal", "org.eclipse.elk.force",
      "org.eclipse.elk.circle", "org.eclipse.elk.tree", "org.eclipse.elk.planar",
      "org.eclipse.elk.radial", ""]
  -- the provider itself registers 94 options, 7 categories and 10 dependencies
  let r := CoreOptions.metaDataProvider.apply {}
  checkEq "core provider options" r.options.size 94
  checkEq "core provider categories" r.categories.size 7
  checkEq "core provider dependencies" r.dependencies.size 10
  checkEq "core provider option support" r.optionSupport.size 0
  checkEq "core provider algorithms" r.algorithms.size 0
  -- all option ids are distinct
  let ids := r.options.map (·.id)
  checkEq "distinct core option ids" (ids.foldl (fun (acc : Std.HashSet String) i => acc.insert i) {}).size 94
  checkEq "box provider options" (BoxLayouterOptions.metaDataProvider.apply {}).options.size 1
  checkEq "label provider options" (LabelManagementOptions.metaDataProvider.apply {}).options.size 1

def options : Suite := suite "core.meta.options" do
  let nn ← opt "org.eclipse.elk.spacing.nodeNode"
  checkEq "nodeNode type" nn.type LayoutOptionType.double
  checkEq "nodeNode name" nn.name "Node Spacing"
  checkEq "nodeNode group" nn.group "spacing"
  checkEq "nodeNode visibility" nn.visibility LayoutOptionVisibility.visible
  check "nodeNode default 20.0" (isDouble nn.defaultValue 20.0)
  check "nodeNode targets parents" (hasTargets nn #[.parents])
  check "nodeNode lower bound inclusive 0" (lowerIs nn false 0.0)
  check "nodeNode no upper bound" nn.upperBound.isNone
  let ar ← opt "org.eclipse.elk.aspectRatio"
  checkEq "aspectRatio type" ar.type LayoutOptionType.double
  checkEq "aspectRatio visibility" ar.visibility LayoutOptionVisibility.advanced
  check "aspectRatio exclusive lower bound 0" (lowerIs ar true 0.0)
  let sc ← opt "org.eclipse.elk.topdown.sizeCategories"
  check "sizeCategories int lower bound 1" (match sc.lowerBound with
    | some b => !b.isExclusive && isInt (some b.value) 1 | none => false)
  check "sizeCategories default 3" (isInt sc.defaultValue 3)
  checkEq "sizeCategories group" sc.group "topdown"
  let fs ← opt "org.eclipse.elk.font.size"
  checkEq "font.size visibility" fs.visibility LayoutOptionVisibility.hidden
  checkEq "font.size targets" fs.targets (EnumSet.of #[.labels])
  let alg' ← opt "org.eclipse.elk.algorithm"
  checkEq "algorithm type" alg'.type LayoutOptionType.string
  checkEq "algorithm name" alg'.name "Layout Algorithm"
  check "algorithm targets" (hasTargets alg' #[.parents])
  let ra ← opt "org.eclipse.elk.resolvedAlgorithm"
  checkEq "resolvedAlgorithm type" ra.type LayoutOptionType.object
  checkEq "resolvedAlgorithm visibility" ra.visibility LayoutOptionVisibility.hidden
  let pad ← opt "org.eclipse.elk.padding"
  checkEq "padding type" pad.type LayoutOptionType.object
  check "padding default 12" (isVal pad.defaultValue (ElkPadding.ofAny 12.0))
  check "padding targets parents+nodes" (hasTargets pad #[.parents, .nodes])
  checkEq "padding visibility" pad.visibility LayoutOptionVisibility.advanced
  let si ← opt "org.eclipse.elk.spacing.individual"
  check "individual spacing targets" (hasTargets si #[.nodes, .edges, .ports, .labels])
  checkEq "individual spacing group" si.group "spacing"
  let dbg ← opt "org.eclipse.elk.debugMode"
  checkEq "debugMode type" dbg.type LayoutOptionType.boolean
  check "debugMode default false" (isBool dbg.defaultValue false)
  let part ← opt "org.eclipse.elk.partitioning.partition"
  checkEq "partition type" part.type LayoutOptionType.int
  check "partition no default" part.defaultValue.isNone
  let nl ← opt "org.eclipse.elk.noLayout"
  check "noLayout default false" (isBool nl.defaultValue false)
  checkEq "noLayout visibility" nl.visibility LayoutOptionVisibility.visible
  let atf ← opt "org.eclipse.elk.animTimeFactor"
  check "animTimeFactor default 100" (isInt atf.defaultValue 100)
  let ps ← opt "org.eclipse.elk.port.side"
  checkEq "port.side type" ps.type LayoutOptionType.enum
  check "port.side default UNDEFINED" (isVal ps.defaultValue PortSide.undefined)
  let lm ← opt "org.eclipse.elk.labelManager"
  checkEq "labelManager type" lm.type LayoutOptionType.object
  check "labelManager targets" (hasTargets lm #[.parents, .labels])
  check "labelManager has no parser" lm.parser.isNone
  -- the label management provider
  let lm2 ← opt "org.eclipse.elk.labels.labelManager"
  checkEq "labels.labelManager name" lm2.name "Label Manager"
  checkEq "labels.labelManager visibility" lm2.visibility LayoutOptionVisibility.hidden
  check "labels.labelManager targets" (hasTargets lm2 #[.parents, .labels])
  checkEq "LABEL_MANAGER id" LabelManagementOptions.LABEL_MANAGER.id "org.eclipse.elk.labels.labelManager"
  -- the box provider replaces the CoreOptions entry of the packing mode
  let bpm ← opt "org.eclipse.elk.box.packingMode"
  checkEq "box packing mode type" bpm.type LayoutOptionType.enum
  checkEq "box packing mode name (replaced)" bpm.name ""
  checkEq "box packing mode group (replaced)" bpm.group ""
  check "box packing mode targets" (hasTargets bpm #[.parents])
  check "box packing mode default SIMPLE" (isVal bpm.defaultValue PackingMode.simple)
  checkEqR "box packing mode choices" bpm.choices #["SIMPLE", "GROUP_DEC", "GROUP_MIXED", "GROUP_INC"]

def enums : Suite := suite "core.meta.enums" do
  let choices (id : String) : TestM (Array String) := do return (← opt id).choices
  checkEqR "direction choices" (← choices "org.eclipse.elk.direction")
    #["UNDEFINED", "RIGHT", "LEFT", "DOWN", "UP"]
  checkEqR "alignment choices" (← choices "org.eclipse.elk.alignment")
    #["AUTOMATIC", "LEFT", "RIGHT", "TOP", "BOTTOM", "CENTER"]
  checkEqR "edgeRouting choices" (← choices "org.eclipse.elk.edgeRouting")
    #["UNDEFINED", "POLYLINE", "ORTHOGONAL", "SPLINES"]
  checkEqR "hierarchyHandling choices" (← choices "org.eclipse.elk.hierarchyHandling")
    #["INHERIT", "INCLUDE_CHILDREN", "SEPARATE_CHILDREN"]
  checkEqR "shapeCoords choices" (← choices "org.eclipse.elk.json.shapeCoords")
    #["INHERIT", "PARENT", "ROOT"]
  checkEqR "edgeCoords choices" (← choices "org.eclipse.elk.json.edgeCoords")
    #["INHERIT", "CONTAINER", "PARENT", "ROOT"]
  checkEqR "portAlignment choices" (← choices "org.eclipse.elk.portAlignment.default")
    #["DISTRIBUTED", "JUSTIFIED", "BEGIN", "CENTER", "END"]
  checkEqR "portConstraints choices" (← choices "org.eclipse.elk.portConstraints")
    #["UNDEFINED", "FREE", "FIXED_SIDE", "FIXED_ORDER", "FIXED_RATIO", "FIXED_POS"]
  checkEqR "edge.type choices" (← choices "org.eclipse.elk.edge.type")
    #["NONE", "DIRECTED", "UNDIRECTED", "ASSOCIATION", "GENERALIZATION", "DEPENDENCY"]
  checkEqR "topdown.nodeType choices" (← choices "org.eclipse.elk.topdown.nodeType")
    #["PARALLEL_NODE", "HIERARCHICAL_NODE", "ROOT_NODE"]
  checkEqR "edgeLabels.placement choices" (← choices "org.eclipse.elk.edgeLabels.placement")
    #["CENTER", "HEAD", "TAIL"]
  checkEqR "nodeSize.constraints choices" (← choices "org.eclipse.elk.nodeSize.constraints")
    #["PORTS", "PORT_LABELS", "NODE_LABELS", "MINIMUM_SIZE"]
  checkEqR "nodeLabels.placement choices" (← choices "org.eclipse.elk.nodeLabels.placement")
    #["H_LEFT", "H_CENTER", "H_RIGHT", "V_TOP", "V_CENTER", "V_BOTTOM", "INSIDE", "OUTSIDE",
      "H_PRIORITY"]
  let dir ← opt "org.eclipse.elk.direction"
  checkEq "direction type" dir.type LayoutOptionType.enum
  check "direction default UNDEFINED" (isVal dir.defaultValue Direction.undefined)
  checkEq "direction getChoices" dir.getChoices.size 5
  let ca ← opt "org.eclipse.elk.contentAlignment"
  checkEq "contentAlignment type" ca.type LayoutOptionType.enumSet
  checkEq "contentAlignment choices" ca.choices.size 6
  let nsc ← opt "org.eclipse.elk.nodeSize.constraints"
  checkEq "nodeSize.constraints type" nsc.type LayoutOptionType.enumSet
  check "nodeSize.constraints default empty" (isVal nsc.defaultValue (EnumSet.empty : EnumSet SizeConstraint))

def parsing : Suite := suite "core.meta.parsing" do
  let dir ← opt "org.eclipse.elk.direction"
  check "parse RIGHT" (isVal (dir.parseValue "RIGHT") Direction.right)
  check "parse lower-case down" (isVal (dir.parseValue "down") Direction.down)
  check "parse ordinal 2" (isVal (dir.parseValue "2") Direction.left)
  checkNone "parse bogus enum" (dir.parseValue "BOGUS")
  checkNone "parse null" (dir.parseValue "null")
  let nsc ← opt "org.eclipse.elk.nodeSize.constraints"
  check "parse enum set" (isVal (nsc.parseValue "[NODE_LABELS, PORTS]")
    (EnumSet.of #[SizeConstraint.nodeLabels, SizeConstraint.ports]))
  check "parse empty enum set" (isVal (nsc.parseValue "[]") (EnumSet.empty : EnumSet SizeConstraint))
  checkNone "parse bogus enum set" (nsc.parseValue "[NOPE]")
  let pad ← opt "org.eclipse.elk.padding"
  check "parse padding" (isVal (pad.parseValue "[top=1,left=2,bottom=3,right=4]")
    (⟨1.0, 4.0, 3.0, 2.0⟩ : ElkPadding))
  checkNone "parse padding junk" (pad.parseValue "[top=x]")
  let nn ← opt "org.eclipse.elk.spacing.nodeNode"
  check "parse double" (isDouble (nn.parseValue "25.5") 25.5)
  checkNone "parse double junk" (nn.parseValue "abc")
  let dbg ← opt "org.eclipse.elk.debugMode"
  check "parse bool" (isBool (dbg.parseValue "TRUE") true)
  let sc ← opt "org.eclipse.elk.topdown.sizeCategories"
  check "parse int" (isInt (sc.parseValue "42") 42)
  checkNone "parse int float" (sc.parseValue "1.5")
  let pos ← opt "org.eclipse.elk.position"
  check "parse kvector" (isVal (pos.parseValue "1.5,2.5") (KVector.mk 1.5 2.5))
  let bp ← opt "org.eclipse.elk.bendPoints"
  check "parse kvector chain" (match bp.parseValue "1,2,3,4" with
    | some (.vectorChain c) => c.size == 2
    | _ => false)
  let isp ← opt "org.eclipse.elk.spacing.individual"
  check "individual spacings has a parser" isp.canParseValue
  checkNone "individual spacings parser TODO" (isp.parseValue "org.eclipse.elk.spacing.nodeNode:5")
  let ra ← opt "org.eclipse.elk.resolvedAlgorithm"
  check "resolvedAlgorithm cannot be parsed" (!ra.canParseValue)
  let bpm ← opt "org.eclipse.elk.box.packingMode"
  check "parse box packing mode" (isVal (bpm.parseValue "GROUP_MIXED") PackingMode.groupMixed)
  check "parse box packing mode loose" (isVal (bpm.parseValue "groupdec") PackingMode.groupDec)
  check "parse box packing mode ordinal" (isVal (bpm.parseValue "3") PackingMode.groupInc)
  checkNone "parse box packing mode out of range" (bpm.parseValue "4")

def dependencies : Suite := suite "core.meta.dependencies" do
  let part ← opt "org.eclipse.elk.partitioning.partition"
  checkEq "partition dependency count" part.dependencies.size 1
  checkEq "partition depends on activate" (depTarget part) "org.eclipse.elk.partitioning.activate"
  check "partition dependency value true" (isBool (depValue part) true)
  let tl ← opt "org.eclipse.elk.topdownLayout"
  checkEq "topdownLayout dependency target" (depTarget tl) "org.eclipse.elk.topdown.nodeType"
  check "topdownLayout dependency any value" (depValue tl).isNone
  let cats ← opt "org.eclipse.elk.topdown.sizeCategories"
  check "sizeCategories dependency value" (isVal (depValue cats)
    TopdownSizeApproximator.fixedIntegerRatioBoxes)
  let sf ← opt "org.eclipse.elk.topdown.scaleFactor"
  check "scaleFactor dependency value" (isVal (depValue sf)
    TopdownNodeTypes.hierarchicalNode)
  let nt ← opt "org.eclipse.elk.topdown.nodeType"
  checkEq "nodeType dependency" (depTarget nt) "org.eclipse.elk.nodeSize.fixedGraphSize"
  let sp ← opt "org.eclipse.elk.spacing.nodeNode"
  checkEq "nodeNode has no dependencies" sp.dependencies.size 0

def algorithms : Suite := suite "core.meta.algorithms" do
  let fixed ← alg "org.eclipse.elk.fixed"
  checkEq "fixed name" fixed.name "ELK Fixed"
  checkEq "fixed bundle" fixed.bundleName (some "ELK")
  checkEq "fixed defining bundle" fixed.definingBundleId (some "org.eclipse.elk.core")
  check "fixed no preview image" fixed.previewImagePath.isNone
  checkEqR "fixed known options" fixed.knownOptionIds
    #["org.eclipse.elk.padding", "org.eclipse.elk.position", "org.eclipse.elk.bendPoints",
      "org.eclipse.elk.nodeSize.constraints", "org.eclipse.elk.nodeSize.minimum",
      "org.eclipse.elk.nodeSize.fixedGraphSize"]
  check "fixed padding default 15" (isVal (fixed.defaultValueRaw "org.eclipse.elk.padding") (ElkPadding.ofAny 15.0))
  let random ← alg "org.eclipse.elk.random"
  checkEq "random name" random.name "ELK Randomizer"
  checkEq "random preview image" random.previewImagePath (some "images/random_layout.png")
  checkEq "random known option count" random.knownOptions.size 4
  check "random seed default 0" (isInt (random.defaultValueRaw "org.eclipse.elk.randomSeed") 0)
  check "random aspect ratio 1.6" (isDouble (random.defaultValueRaw "org.eclipse.elk.aspectRatio") 1.6)
  check "random node spacing 15" (isDouble (random.defaultValueRaw "org.eclipse.elk.spacing.nodeNode") 15.0)
  let box ← alg "org.eclipse.elk.box"
  checkEq "box name" box.name "ELK Box"
  checkEq "box description" box.description "Algorithm for packing of unconnected boxes, i.e. graphs without edges."
  checkEq "box preview image" box.previewImagePath (some "images/box_layout.png")
  checkEq "box known option count" box.knownOptions.size 11
  check "box aspect ratio 1.3" (isDouble (box.defaultValueRaw "org.eclipse.elk.aspectRatio") 1.3)
  check "box priority 0" (isInt (box.defaultValueRaw "org.eclipse.elk.priority") 0)
  check "box knows packing mode" (box.knowsOption "org.eclipse.elk.box.packingMode")
  check "box knows contentAlignment" (box.knowsOption "org.eclipse.elk.contentAlignment")
  check "box packing mode has no algorithm default" (box.defaultValueRaw "org.eclipse.elk.box.packingMode").isNone
  check "box does not know direction" (!box.knowsOption "org.eclipse.elk.direction")
  let layered ← alg "org.eclipse.elk.layered"
  checkEq "layered name" layered.name "ELK Layered"
  checkEq "layered category" layered.categoryId (some "org.eclipse.elk.layered")
  checkEq "layered defining bundle" layered.definingBundleId (some "org.eclipse.elk.alg.layered")
  checkEq "layered bundle name" layered.bundleName none
  checkEq "layered known option count (28 core + 125 supports)" layered.knownOptions.size 153
  check "layered supports self loops" (layered.supportsFeature .selfLoops)
  check "layered supports clusters" (layered.supportsFeature .clusters)
  check "layered does not support disconnected" (!layered.supportsFeature .disconnected)
  checkEq "layered feature count" layered.supportedFeatures.size 7
  check "layered edge routing default" (isVal (layered.defaultValueRaw "org.eclipse.elk.edgeRouting") EdgeRouting.orthogonal)
  check "layered padding default 12" (isVal (layered.defaultValueRaw "org.eclipse.elk.padding") (ElkPadding.ofAny 12.0))
  check "layered separate components default" (isBool (layered.defaultValueRaw "org.eclipse.elk.separateConnectedComponents") true)
  check "layered port alignment default" (isVal (layered.defaultValueRaw "org.eclipse.elk.portAlignment.default") PortAlignment.justified)
  check "layered random seed 1" (isInt (layered.defaultValueRaw "org.eclipse.elk.randomSeed") 1)
  check "layered node type default" (isVal (layered.defaultValueRaw "org.eclipse.elk.topdown.nodeType") TopdownNodeTypes.hierarchicalNode)
  check "layered knows noLayout" (layered.knowsOption "org.eclipse.elk.noLayout")
  check "layered nodeNode default 20 (option support)" (match layered.defaultValueRaw "org.eclipse.elk.spacing.nodeNode" with | some (.double d) => d == 20.0 | _ => false)
  check "layered knows nodeNode" (layered.knowsOption "org.eclipse.elk.spacing.nodeNode")
  -- typed default access
  check "layered typed edge routing default"
    (layered.defaultValue CoreOptions.EDGE_ROUTING == some EdgeRouting.orthogonal)

def lookup : Suite := suite "core.meta.lookup" do
  let nn ← LayoutMetaDataService.getOptionDataBySuffix "nodeNode"
  checkEq "suffix nodeNode" (nn.map (·.id)) (some "org.eclipse.elk.spacing.nodeNode")
  let dir ← LayoutMetaDataService.getOptionDataBySuffix "direction"
  checkEq "suffix direction is ambiguous once layered (priority.direction) is registered" (dir.map (·.id)) none
  checkNone "suffix unknown option" (← LayoutMetaDataService.getOptionDataBySuffix "doesNotExist")
  checkNone "suffix empty option" (← LayoutMetaDataService.getOptionDataBySuffix "  ")
  let layered ← LayoutMetaDataService.getAlgorithmDataBySuffix "layered"
  checkEq "suffix layered" (layered.map (·.id)) (some "org.eclipse.elk.layered")
  let box ← LayoutMetaDataService.getAlgorithmDataBySuffix "box"
  checkEq "suffix box" (box.map (·.id)) (some "org.eclipse.elk.box")
  checkNone "suffix unknown algorithm" (← LayoutMetaDataService.getAlgorithmDataBySuffix "mrtree")
  let dflt ← LayoutMetaDataService.getAlgorithmDataBySuffixOrDefault (some "nope") (some "fixed")
  checkEq "suffix or default" (dflt.map (·.id)) (some "org.eclipse.elk.fixed")
  let resolved ← LayoutMetaDataService.resolveOption "org.eclipse.elk.spacing.portPort"
  checkEq "resolve full id" (resolved.map (·.id)) (some "org.eclipse.elk.spacing.portPort")
  -- options usable with the box algorithm for nodes (padding and priority apply to nodes)
  let box? ← LayoutMetaDataService.getAlgorithmData "org.eclipse.elk.box"
  match box? with
  | some b =>
    let forNodes ← LayoutMetaDataService.getOptionDataForAlgorithm b .nodes
    check "box node options contain priority" (forNodes.any (·.id == "org.eclipse.elk.priority"))
    check "box node options contain padding" (forNodes.any (·.id == "org.eclipse.elk.padding"))
    check "box node options contain algorithm" (!forNodes.any (·.id == "org.eclipse.elk.algorithm"))
    let forParents ← LayoutMetaDataService.getOptionDataForAlgorithm b .parents
    check "box parent options contain algorithm" (forParents.any (·.id == "org.eclipse.elk.algorithm"))
  | none => report "box algorithm available" false

def categories : Suite := suite "core.meta.categories" do
  let layeredCat ← LayoutMetaDataService.getCategoryData "org.eclipse.elk.layered"
  checkEq "layered category name" (layeredCat.map (·.name)) (some "Layered")
  checkEqR "layered category members" ((layeredCat.map (·.layouters)).getD #[]) #["org.eclipse.elk.layered"]
  let other ← LayoutMetaDataService.getCategoryData ""
  checkEq "backup category name" (other.map (·.name)) (some "Other")
  checkEqR "backup category members" ((other.map (·.layouters)).getD #[])
    #["org.eclipse.elk.fixed", "org.eclipse.elk.random", "org.eclipse.elk.box", "org.eclipse.elk.disco",
      "org.eclipse.elk.sporeOverlap", "org.eclipse.elk.sporeCompaction", "org.eclipse.elk.topdownpacking"]
  let radial ← LayoutMetaDataService.getCategoryData "org.eclipse.elk.radial"
  checkEq "radial description"
    (radial.map (·.description))
    (some "Radial layout algorithms usually position the nodes of the graph on concentric circles.")
  let force ← LayoutMetaDataService.getCategoryData "org.eclipse.elk.force"
  checkEq "force name" (force.map (·.name)) (some "Force")
  checkEqR "force members" ((force.map (·.layouters)).getD #[]) #["org.eclipse.elk.force", "org.eclipse.elk.stress"]

/-- Provider machinery on a private (non-global) service: legacy ids, dependencies and option
support with unknown ids being ignored. -/
def machinery : Suite := suite "core.meta.machinery" do
  let provider : LayoutMetaDataProvider := ⟨fun r =>
    r.registerAlgorithm { id := "org.test.alg", name := "Test" }
      |>.registerOption { id := "org.test.a", legacyIds := #["old.a", "older.a"] }
      |>.registerOption { id := "org.test.b" }
      |>.addDependency "org.test.a" "org.test.b" (some (.int 3))
      |>.addDependency "org.test.a" "org.test.missing" none
      |>.addOptionSupport "org.test.alg" "org.test.a" (some (.double 2.5))
      |>.addOptionSupport "org.test.alg" "org.test.missing" none
      |>.addOptionSupport "org.test.unknown" "org.test.a" none⟩
  let s := LayoutMetaDataService.applyProvider {} provider
  checkEq "legacy lookup" ((s.optionData? "old.a").map (·.id)) (some "org.test.a")
  checkEq "second legacy lookup" ((s.optionData? "older.a").map (·.id)) (some "org.test.a")
  checkEq "legacy map size" s.legacyOptions.size 2
  let (bySuffix, _) := s.optionDataBySuffix "older.a"
  checkEq "legacy suffix lookup" (bySuffix.map (·.id)) (some "org.test.a")
  let a := (s.optionData? "org.test.a").getD { id := "" }
  checkEq "dependency recorded" a.dependencies.size 1
  check "dependency value" (isInt (depValue a) 3)
  let algorithm := (s.algorithmData? "org.test.alg").getD { id := "" }
  checkEqR "option support recorded" algorithm.knownOptionIds #["org.test.a"]
  check "option support default" (isDouble (algorithm.defaultValueRaw "org.test.a") 2.5)
  checkEq "backup category created" (s.categoryData? "").isSome true
  -- the global instance is unaffected
  let g ← LayoutMetaDataService.getInstance
  check "global instance unaffected" (g.optionData? "org.test.a").isNone

def suites : Array Tests.Suite :=
  #[counts, options, enums, parsing, dependencies, algorithms, lookup, categories, machinery]

end Tests.Core.Meta
