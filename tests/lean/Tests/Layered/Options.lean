import Tests.Framework
import Elk.Alg.Layered.Options
import Elk.Alg.Layered.Components
/-!
# Tests for `org.eclipse.elk.alg.layered.options`

`LayeredOptions` constants, the option enums, `LayeredMetaDataProvider` and `LayeredSpacings`.

Expected counts are derived from the Rust sources of elk-rs:
* `layered_options.rs`: 89 `*_PROPERTY` statics, 40 re-exported core options (`CoreOptions::*`
  aliases) and `ALGORITHM_ID`;
* `layered_meta_data_provider.rs`: 89 `register_option` calls (14 sections), 153
  `add_option_support` calls (89 layered + 64 core options), no dependencies, no categories;
* the algorithm entry of `register_core_algorithms` has 28 known options; together with the
  option supports the layered algorithm knows 153 options once the core options are registered
  (every placeholder option is also an option support), and 28 + 89 = 117 on a fresh registry
  (supports of unregistered core options are dropped).

The metadata checks work on a snapshot of the service (`applyProvider` on the value returned by
`getInstance`), so the global registry is not modified.
-/
namespace Tests.Layered.Options

open Tests Elk Elk.Graph Elk.Core.Math Elk.Core.Data Elk.Core.Options Elk.Core.Util
open Elk.Alg.Layered.Options Elk.Alg.Layered.Components

def isDouble (v : Option PropValue) (x : Float) : Bool :=
  match v with | some (.double y) => y == x | _ => false

def isInt (v : Option PropValue) (x : Int) : Bool :=
  match v with | some (.int y) => y == x | _ => false

def isBool (v : Option PropValue) (x : Bool) : Bool :=
  match v with | some (.bool y) => y == x | _ => false

/-- The value decoded as `α` equals `x`. -/
def isVal {α : Type} [PropCodec α] [BEq α] (v : Option PropValue) (x : α) : Bool :=
  (v.bind PropCodec.dec : Option α) == some x

def lowerInt (d : LayoutOptionData) (x : Int) : Bool :=
  match d.lowerBound with
  | some b => !b.isExclusive && isInt (some b.value) x
  | none => false

def lowerDouble (d : LayoutOptionData) (x : Float) : Bool :=
  match d.lowerBound with
  | some b => !b.isExclusive && isDouble (some b.value) x
  | none => false

/-- The service with the core metadata and the layered provider applied (pure snapshot). -/
def service : IO LayoutMetaDataService := do
  return (← LayoutMetaDataService.getInstance).applyProvider LayeredMetaDataProvider.metaDataProvider

def optIn (s : LayoutMetaDataService) (id : String) : TestM LayoutOptionData := do
  match s.optionData? id with
  | some d => return d
  | none =>
    report s!"option {id} registered" false
    return { id }

def pfx : String := "org.eclipse.elk.alg.layered."

def constants : Suite := suite "layered.options.constants" do
  checkEq "ALGORITHM_ID" LayeredOptions.ALGORITHM_ID "org.eclipse.elk.layered"
  checkEq "SPACING_BASE_VALUE id" LayeredOptions.SPACING_BASE_VALUE.id (pfx ++ "spacing.baseValue")
  check "SPACING_BASE_VALUE no default" LayeredOptions.SPACING_BASE_VALUE.default.isNone
  checkEq "SPACING_NODE_NODE_BETWEEN_LAYERS default"
    LayeredOptions.SPACING_NODE_NODE_BETWEEN_LAYERS.default (some 20.0)
  checkEq "THOROUGHNESS id/default" (LayeredOptions.THOROUGHNESS.id, LayeredOptions.THOROUGHNESS.default)
    (pfx ++ "thoroughness", some 7)
  checkEq "LAYERING_COFFMAN_GRAHAM_LAYER_BOUND default"
    LayeredOptions.LAYERING_COFFMAN_GRAHAM_LAYER_BOUND.default (some 2147483647)
  checkEq "LAYERING_LAYER_ID default" LayeredOptions.LAYERING_LAYER_ID.default (some (-1))
  checkEq "CROSSING_MINIMIZATION_GREEDY_SWITCH_TYPE default"
    LayeredOptions.CROSSING_MINIMIZATION_GREEDY_SWITCH_TYPE.default (some GreedySwitchType.twoSided)
  checkEq "NODE_PLACEMENT_STRATEGY default"
    LayeredOptions.NODE_PLACEMENT_STRATEGY.default (some NodePlacementStrategy.brandesKoepf)
  checkEq "EDGE_LABELS_SIDE_SELECTION default"
    LayeredOptions.EDGE_LABELS_SIDE_SELECTION.default (some EdgeLabelSideSelection.smartDown)
  checkEq "WRAPPING_CUTTING_STRATEGY default"
    LayeredOptions.WRAPPING_CUTTING_STRATEGY.default (some CuttingStrategy.msd)
  checkEqR "GROUP_MODEL_ORDER_CM_ENFORCED_GROUP_ORDERS default"
    LayeredOptions.GROUP_MODEL_ORDER_CM_ENFORCED_GROUP_ORDERS.default (some #[1, 2, 6, 7, 10, 11])
  checkEq "CONSIDER_MODEL_ORDER_COMPONENTS id"
    LayeredOptions.CONSIDER_MODEL_ORDER_COMPONENTS.id (pfx ++ "considerModelOrder.components")
  check "RECOMPUTE_NODE_PLACEMENT no default"
    LayeredOptions.NODE_PLACEMENT_NETWORK_SIMPLEX_NODE_FLEXIBILITY_RECOMPUTE_NODE_PLACEMENT.default.isNone
  -- core aliases keep id and default
  checkEq "SPACING_NODE_NODE alias" LayeredOptions.SPACING_NODE_NODE.id CoreOptions.SPACING_NODE_NODE.id
  checkEq "SPACING_NODE_NODE alias default" LayeredOptions.SPACING_NODE_NODE.default (some 20.0)
  checkEq "PORT_CONSTRAINTS alias" LayeredOptions.PORT_CONSTRAINTS.id "org.eclipse.elk.portConstraints"
  checkEq "EDGE_ROUTING alias default" LayeredOptions.EDGE_ROUTING.default (some EdgeRouting.undefined)

def enumHelpers : Suite := suite "layered.options.enums" do
  checkEqR "FixedAlignment java names" ((ElkEnum.values : Array FixedAlignment).map ElkEnum.javaName)
    #["NONE", "LEFTUP", "RIGHTUP", "LEFTDOWN", "RIGHTDOWN", "BALANCED"]
  checkEqR "NodePromotionStrategy java names"
    ((ElkEnum.values : Array NodePromotionStrategy).map ElkEnum.javaName)
    #["NONE", "NIKOLOV", "NIKOLOV_PIXEL", "NIKOLOV_IMPROVED", "NIKOLOV_IMPROVED_PIXEL",
      "DUMMYNODE_PERCENTAGE", "NODECOUNT_PERCENTAGE", "NO_BOUNDARY", "MODEL_ORDER_LEFT_TO_RIGHT",
      "MODEL_ORDER_RIGHT_TO_LEFT"]
  checkEq "CycleBreakingStrategy count" (ElkEnum.count (α := CycleBreakingStrategy)) 9
  checkEq "LayeringStrategy BF_MODEL_ORDER ordinal" (ElkEnum.ordinal LayeringStrategy.bfModelOrder) 7
  checkEq "ComponentOrderingStrategy names"
    ((ElkEnum.values : Array ComponentOrderingStrategy).map ElkEnum.javaName)
    #["NONE", "INSIDE_PORT_SIDE_GROUPS", "GROUP_MODEL_ORDER", "MODEL_ORDER"]
  check "parse leftUp loosely" ((ElkEnum.ofNameLoose? "LEFT_UP" : Option FixedAlignment) == some .leftUp)
  check "nodeSize flexible size" (NodeFlexibility.nodeSize.isFlexibleSize && !NodeFlexibility.portPosition.isFlexibleSize)
  check "where space permits" NodeFlexibility.nodeSizeWhereSpacePermits.isFlexibleSizeWhereSpacePermits
  check "flexible ports" (NodeFlexibility.portPosition.isFlexiblePorts && !NodeFlexibility.none.isFlexiblePorts)
  check "isAtLeast fall-through" (NodeFlexibility.nodeSizeWhereSpacePermits.isAtLeast .portPosition)
  check "label size info" (CenterEdgeLabelPlacementStrategy.widestLayer.usesLabelSizeInformation &&
    !CenterEdgeLabelPlacementStrategy.medianLayer.usesLabelSizeInformation)
  checkEq "transpose" EdgeLabelSideSelection.smartDown.transpose EdgeLabelSideSelection.smartUp
  checkEq "returnValue over" LongEdgeOrderingStrategy.dummyNodeOver.returnValue 2147483647
  checkEq "returnValue under" LongEdgeOrderingStrategy.dummyNodeUnder.returnValue (-2147483648)
  check "GraphProperties enum set" ((EnumSet.of #[GraphProperties.selfLoops, .partitions]).contains .partitions)

def provider : Suite := suite "layered.options.provider" do
  let r := LayeredMetaDataProvider.metaDataProvider.apply {}
  checkEq "registered options (89 register_option calls)" r.options.size 89
  checkEq "option supports (153 add_option_support calls)" r.optionSupport.size 153
  checkEq "optionSupports array" LayeredMetaDataProvider.optionSupports.size 153
  checkEq "dependencies" r.dependencies.size 0
  checkEq "categories" r.categories.size 0
  checkEq "algorithms" r.algorithms.size 1
  let ids := r.options.map (·.id)
  checkEq "distinct option ids" (ids.foldl (fun (acc : Std.HashSet String) i => acc.insert i) {}).size 89
  check "all ids alg.layered" (ids.all (·.startsWith pfx))
  checkEq "first option" (ids[0]?) (some (pfx ++ "spacing.baseValue"))
  checkEq "last option" (ids.back?) (some (pfx ++ "considerModelOrder.groupModelOrder.cmEnforcedGroupOrders"))
  -- fresh registry: only the layered option supports apply
  let fresh := ({} : LayoutMetaDataService).applyProvider LayeredMetaDataProvider.metaDataProvider
  checkEq "fresh option count" fresh.optionDataList.size 89
  checkEq "fresh known options (28 + 89)"
    (((fresh.algorithmData? "org.eclipse.elk.layered").map (·.knownOptions.size)).getD 0) 117

def options : Suite := suite "layered.options.meta" do
  let s ← service
  let base ← optIn s (pfx ++ "spacing.baseValue")
  checkEq "baseValue type" base.type LayoutOptionType.double
  checkEq "baseValue name" base.name "Spacing Base Value"
  checkEq "baseValue group" base.group "spacing"
  check "baseValue no default" base.defaultValue.isNone
  check "baseValue lower bound 0.0" (lowerDouble base 0.0)
  check "baseValue no upper bound" base.upperBound.isNone
  checkEq "baseValue targets" base.targets (EnumSet.of #[.parents])
  checkEqR "baseValue legacy ids" base.legacyIds #["org.eclipse.elk.layered.spacing.baseValue"]
  checkEq "legacy id lookup" ((s.optionData? "org.eclipse.elk.layered.thoroughness").map (·.id))
    (some (pfx ++ "thoroughness"))
  let pd ← optIn s (pfx ++ "priority.direction")
  checkEq "priority.direction visibility" pd.visibility LayoutOptionVisibility.advanced
  check "priority.direction default 0" (isInt pd.defaultValue 0)
  check "priority.direction lower bound 0" (lowerInt pd 0)
  checkEq "priority.direction targets" pd.targets (EnumSet.of #[.edges])
  let split ← optIn s (pfx ++ "layerUnzipping.layerSplit")
  check "layerSplit default 2" (isInt split.defaultValue 2)
  check "layerSplit lower bound 1" (lowerInt split 1)
  let ws ← optIn s (pfx ++ "wrapping.strategy")
  checkEq "wrapping.strategy type" ws.type LayoutOptionType.enum
  check "wrapping.strategy default OFF" (isVal ws.defaultValue WrappingStrategy.off)
  checkEqR "wrapping.strategy choices" ws.choices #["OFF", "SINGLE_EDGE", "MULTI_EDGE"]
  check "wrapping.strategy parser" ((ws.parseValue "multiEdge").bind PropCodec.dec == some WrappingStrategy.multiEdge)
  let fa ← optIn s (pfx ++ "nodePlacement.bk.fixedAlignment")
  checkEqR "fixedAlignment choices (elk-rs names)" fa.choices
    #["NONE", "LEFT_UP", "RIGHT_UP", "LEFT_DOWN", "RIGHT_DOWN", "BALANCED"]
  check "fixedAlignment parses LEFTUP" ((fa.parseValue "LEFTUP").bind PropCodec.dec == some FixedAlignment.leftUp)
  let cb ← optIn s (pfx ++ "cycleBreaking.strategy")
  checkEq "cycleBreaking choices" cb.choices.size 9
  checkEq "cycleBreaking visibility" cb.visibility LayoutOptionVisibility.visible
  let rec' ← optIn s (pfx ++ "nodePlacement.networkSimplex.nodeFlexibility.recomputeNodePlacement")
  check "recompute no default" rec'.defaultValue.isNone
  checkEq "recompute choices" rec'.choices.size 5
  checkEq "recompute group" rec'.group "nodePlacement.networkSimplex.nodeFlexibility"
  let cuts ← optIn s (pfx ++ "wrapping.cutting.cuts")
  checkEq "cuts type" cuts.type LayoutOptionType.object
  check "cuts no parser" cuts.parser.isNone
  let enf ← optIn s (pfx ++ "considerModelOrder.groupModelOrder.cmEnforcedGroupOrders")
  check "enforced group orders default" (isVal enf.defaultValue (#[1, 2, 6, 7, 10, 11] : Array Int))
  let cmid ← optIn s (pfx ++ "considerModelOrder.groupModelOrder.crossingMinimizationId")
  checkEq "crossingMinimizationId targets" cmid.targets (EnumSet.of #[.nodes, .edges, .ports])
  let cl ← optIn s (pfx ++ "edgeLabels.centerLabelPlacementStrategy")
  checkEq "centerLabelPlacement targets" cl.targets (EnumSet.of #[.parents, .labels])
  let dp ← optIn s (pfx ++ "wrapping.multiEdge.distancePenalty")
  checkEq "distancePenalty name (trailing space)" dp.name "Distance Penalty When Improving Cuts "
  checkEq "distancePenalty description" dp.description ""
  let dc ← optIn s (pfx ++ "directionCongruency")
  checkEq "directionCongruency group" dc.group ""
  let anf ← optIn s (pfx ++ "allowNonFlowPortsToSwitchSides")
  checkEq "allowNonFlow targets" anf.targets (EnumSet.of #[.ports])
  let ilp ← optIn s (pfx ++ "crossingMinimization.inLayerPredOf")
  checkEq "inLayerPredOf type" ilp.type LayoutOptionType.string

def algorithm : Suite := suite "layered.options.algorithm" do
  let s ← service
  let a := (s.algorithmData? "org.eclipse.elk.layered").getD { id := "" }
  checkEq "id" a.id "org.eclipse.elk.layered"
  checkEq "name" a.name "ELK Layered"
  checkEq "category" a.categoryId (some "org.eclipse.elk.layered")
  checkEq "defining bundle" a.definingBundleId (some "org.eclipse.elk.alg.layered")
  checkEq "preview image" a.previewImagePath (some "images/layered_layout.png")
  checkEq "features" a.supportedFeatures
    (EnumSet.of #[.selfLoops, .insideSelfLoops, .multiEdges, .edgeLabels, .ports, .compound, .clusters])
  check "no disconnected feature" (!a.supportsFeature .disconnected)
  checkEq "known options" a.knownOptions.size 153
  check "edgeRouting = ORTHOGONAL" (isVal (a.defaultValueRaw "org.eclipse.elk.edgeRouting") EdgeRouting.orthogonal)
  check "spacing.nodeNode = 20" (isDouble (a.defaultValueRaw "org.eclipse.elk.spacing.nodeNode") 20.0)
  check "priority = 0" (isInt (a.defaultValueRaw "org.eclipse.elk.priority") 0)
  check "randomSeed = 1" (isInt (a.defaultValueRaw "org.eclipse.elk.randomSeed") 1)
  check "aspectRatio = 1.6" (isDouble (a.defaultValueRaw "org.eclipse.elk.aspectRatio") 1.6)
  check "separateConnectedComponents = true"
    (isBool (a.defaultValueRaw "org.eclipse.elk.separateConnectedComponents") true)
  check "portAlignment.default = JUSTIFIED"
    (isVal (a.defaultValueRaw "org.eclipse.elk.portAlignment.default") PortAlignment.justified)
  check "topdown.nodeType = HIERARCHICAL_NODE"
    (isVal (a.defaultValueRaw "org.eclipse.elk.topdown.nodeType") TopdownNodeTypes.hierarchicalNode)
  check "padding = 12" (isVal (a.defaultValueRaw "org.eclipse.elk.padding") (ElkPadding.ofAny 12.0))
  check "thoroughness = 7" (isInt (a.defaultValueRaw (pfx ++ "thoroughness")) 7)
  check "baseValue known without default"
    (a.knowsOption (pfx ++ "spacing.baseValue") && (a.defaultValueRaw (pfx ++ "spacing.baseValue")).isNone)
  check "port.borderOffset = 0.0" (isDouble (a.defaultValueRaw "org.eclipse.elk.port.borderOffset") 0.0)
  checkEq "first known option (placeholder order)" (a.knownOptionIds[0]?) (some "org.eclipse.elk.spacing.commentComment")
  check "category lists layered" (((s.categoryData? "org.eclipse.elk.layered").map (·.layouters.contains "org.eclipse.elk.layered")).getD false)

def spacings : Suite := suite "layered.options.spacings" do
  let b := LayeredSpacings.withBaseValue 33.0
  checkEq "factor count (base + 13)" b.factors.size 14
  -- layered_spacing_factors_match_defaults
  for o in LayeredSpacingsBuilder.dependentSpacingOptions do
    checkFloat s!"factor {o.id}" ((b.factorOf? o).getD 0.0) (o.default.getD 0.0 / 20.0) 1e-4
  checkFloat "between layers factor 0.5"
    ((b.factorOf? LayeredOptions.SPACING_EDGE_NODE_BETWEEN_LAYERS).getD 0.0) 0.5
  -- layered_spacing_applies_between_layers (configuration part)
  match b.withFactor LayeredOptions.SPACING_NODE_NODE_BETWEEN_LAYERS 2.0 with
  | .ok b2 =>
    let props := b2.applyToProperties {}
    checkFloat "nodeNodeBetweenLayers = 66" (props.getD LayeredOptions.SPACING_NODE_NODE_BETWEEN_LAYERS 0.0) 66.0
    checkFloat "nodeNode = 33" (props.getD LayeredOptions.SPACING_NODE_NODE 0.0) 33.0
  | .error e => report "withFactor ok" false e
  -- spacing_defaults_after_configuration
  let props := (LayeredSpacings.withBaseValue 35.0).applyToProperties {}
  check "edgeNode set" (props.has LayeredOptions.SPACING_EDGE_NODE)
  checkFloat "edgeNode = 35 * 0.5" (props.getD LayeredOptions.SPACING_EDGE_NODE 0.0) 17.5
  -- existing values are kept unless overwrite is set
  let preset := PropertyMap.empty.set LayeredOptions.SPACING_EDGE_EDGE 1.0
  checkFloat "no overwrite" ((LayeredSpacings.withBaseValue 40.0).applyToProperties preset |>.getD
    LayeredOptions.SPACING_EDGE_EDGE 0.0) 1.0
  checkFloat "overwrite" (((LayeredSpacings.withBaseValue 40.0).withOverwrite true).applyToProperties preset |>.getD
    LayeredOptions.SPACING_EDGE_EDGE 0.0) 20.0
  checkEq "default base is a no-op" ((LayeredSpacings.withBaseValue 20.0).applyToProperties {}).size 0
  -- withValue: factor = value / base
  match b.withValue LayeredOptions.SPACING_PORT_PORT 66.0 with
  | .ok b3 => checkFloat "withValue factor" ((b3.factorOf? LayeredOptions.SPACING_PORT_PORT).getD 0.0) 2.0
  | .error e => report "withValue ok" false e
  -- errors
  check "base option rejected" (b.withFactor LayeredOptions.SPACING_NODE_NODE 2.0 |>.toOption).isNone
  check "negative factor rejected" (b.withFactor LayeredOptions.SPACING_EDGE_EDGE (-1.0) |>.toOption).isNone
  check "unknown option rejected" (b.withFactor LayeredOptions.SPACING_BASE_VALUE 1.0 |>.toOption).isNone
  check "zero base rejected by withValue"
    ((LayeredSpacings.withBaseValue 0.0).withValue LayeredOptions.SPACING_EDGE_EDGE 1.0 |>.toOption).isNone
  let expected := "java.lang.IllegalArgumentException: " ++
    "'org.eclipse.elk.alg.layered.spacing.baseValue' is not a configurable spacing option."
  match b.withFactor LayeredOptions.SPACING_BASE_VALUE 1.0 with
  | .error e => checkEq "error message" e expected
  | .ok _ => report "error message" false

def suites : Array Tests.Suite := #[constants, enumHelpers, provider, options, algorithm, spacings]

end Tests.Layered.Options
