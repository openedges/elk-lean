import Elk.Core.Data
import Elk.Core.Options
import Elk.Alg.Layered.Options.LayeredOptions
/-!
# `org.eclipse.elk.alg.layered.options.LayeredMetaDataProvider`

Port of `layered_meta_data_provider.rs` (elk-rs), the counterpart of the Java
`LayeredMetaDataProvider` generated from `Layered.melk`.

`metaDataProvider.apply` registers, in the order of the Rust `apply`:
1. the algorithm entry `org.eclipse.elk.layered` (`algorithmData`, see below);
2. the layered options, one `register*Options` function per Rust section (spacing, priority,
   wrapping, layer unzipping, cycle breaking, layering, crossing minimization, node placement,
   edge routing, compaction, high degree nodes, misc, edge labels, consider model order);
3. the option supports of the algorithm (`optionSupports`, Rust `register_option_supports`)
   with their algorithm-specific defaults.

Rust semantics kept on purpose (they differ from the generated Java provider):
* Only the 89 options declared by `layered_options.rs` are registered. Option supports that
  name an option nobody registered are dropped by `LayoutMetaDataService.applyRegistry`, like
  `Registry::apply_dependencies` does.
* No option dependencies are registered (the Rust provider registers none).
* Only a lower bound is ever set (inclusive); upper bounds are not registered.
* Every option gets the legacy id `org.eclipse.elk.layered.<suffix>` (`layered_legacy_ids`).
* Enum choices are the Java constant names (elk-rs `enum_choices` equals them except for
  `FixedAlignment`, where `FixedAlignment.javaChoiceNames` keeps the Java spelling). OBJECT options (`Vec<i32>`) have no
  parser.
* `property_default_any` yields the property default for every option type used here (all of
  them are registered with `ElkReflect` in elk-rs), so `propertyDefault` is simply
  `property.default`.

Algorithm entry: elk-rs registers the layered algorithm in core (`register_core_algorithms`) and
the provider only adds option supports. `algorithmData` reproduces that entry exactly (name,
description, category, bundle, preview image, supported features and the 28 known options with
their defaults, in Rust order) and is registered by `apply`, so that the provider also works on a
fresh registry. Applied after the core initialisation it replaces the identical placeholder entry
of `Elk.Core.Init`, i.e. the resulting metadata equals elk-rs. (The Java provider builds the
entry without the 28 core-registered known options; elk-rs is the parity oracle.)
-/
namespace Elk.Alg.Layered.Options

open Elk Elk.Graph Elk.Core.Data Elk.Core.Math Elk.Core.Util Elk.Core.Options
open Elk.Alg.Layered.Components

namespace LayeredMetaDataProvider

/-! ### Targets (`TARGET_*` constants) -/

/-- `TARGET_PARENTS`. -/
def targetParents : Array LayoutOptionTarget := #[.parents]
/-- `TARGET_EDGES`. -/
def targetEdges : Array LayoutOptionTarget := #[.edges]
/-- `TARGET_NODES`. -/
def targetNodes : Array LayoutOptionTarget := #[.nodes]
/-- `TARGET_PORTS`. -/
def targetPorts : Array LayoutOptionTarget := #[.ports]
/-- `TARGET_PARENTS_LABELS`. -/
def targetParentsLabels : Array LayoutOptionTarget := #[.parents, .labels]
/-- `TARGET_NODES_EDGES_PORTS`. -/
def targetNodesEdgesPorts : Array LayoutOptionTarget := #[.nodes, .edges, .ports]

/-! ### Registration helpers -/

/-- `layered_legacy_ids`: `org.eclipse.elk.alg.layered.<suffix>` has the legacy id
`org.eclipse.elk.layered.<suffix>` (the Java id); other ids have none. The one explicit legacy id
of ELK Java's `.melk` files is kept too: `allowNonFlowPortsToSwitchSides` was
`org.eclipse.elk.layered.northOrSouthPort` (`getOptionDataBySuffix` resolves `northOrSouthPort`
through it, as in Java). -/
def layeredLegacyIds (id : String) : Array String :=
  let pfx := "org.eclipse.elk.alg.layered."
  if id.startsWith pfx then
    let javaId := "org.eclipse.elk.layered." ++ (id.drop pfx.length).toString
    if javaId == "org.eclipse.elk.layered.allowNonFlowPortsToSwitchSides" then
      #[javaId, "org.eclipse.elk.layered.northOrSouthPort"]
    else #[javaId]
  else #[]

/-- `property_default_any`: the default value of a property as a `PropValue`. -/
def propertyDefault {α : Type} [PropCodec α] (property : Property α) : Option PropValue :=
  property.default.map PropCodec.enc

/-- `register_option` for non-enum options (BOOLEAN, INT, DOUBLE, STRING, OBJECT): id, type,
default value (`property_default_any`), name, description, targets, visibility, legacy ids,
group and lower bound. No parser is attached (the Rust helper only adds one for enums). -/
def registerOption {α : Type} [PropCodec α] (r : Registry) (property : Property α)
    (optionType : LayoutOptionType) (name description : String)
    (targets : Array LayoutOptionTarget) (visibility : LayoutOptionVisibility)
    (group : Option String) (lowerBound : Option OptionBound) : Registry :=
  r.registerOption
    { id := property.id, type := optionType, defaultValue := propertyDefault property, name,
      description, targets := EnumSet.of targets, visibility,
      legacyIds := layeredLegacyIds property.id, group := group.getD "", lowerBound }

/-- `register_option` for ENUM options: as `registerOption`, plus the enum choices and the
lenient enum parser (`layered_enum_support` / `enum_support`). -/
def registerEnumOption {α : Type} [ElkEnum α] (r : Registry) (property : Property α)
    (name description : String) (targets : Array LayoutOptionTarget)
    (visibility : LayoutOptionVisibility) (group : Option String) (lowerBound : Option OptionBound)
    (choices : Array String := LayoutOptionData.enumChoices α) : Registry :=
  r.registerOption
    { id := property.id, type := .enum, defaultValue := propertyDefault property, name,
      description, targets := EnumSet.of targets, visibility,
      legacyIds := layeredLegacyIds property.id, group := group.getD "", lowerBound, choices,
      parser := some (LayoutOptionData.enumParser α) }

/-! ### Option sections -/

/-- `register_spacing_options`. -/
def registerSpacingOptions (r : Registry) : Registry :=
  let r := registerOption r LayeredOptions.SPACING_BASE_VALUE .double
    "Spacing Base Value"
    "An optional base value for all other layout options of the 'spacing' group. It can be used to conveniently alter the overall 'spaciousness' of the drawing. Whenever an explicit value is set for the other layout options, this base value will have no effect. The base value is not inherited, i.e. it must be set for each hierarchical node."
    targetParents .visible (some "spacing") (some (OptionBound.atLeast 0.0))
  let r := registerOption r LayeredOptions.SPACING_EDGE_NODE_BETWEEN_LAYERS .double
    "Edge Node Between Layers Spacing"
    "The spacing to be preserved between nodes and edges that are routed next to the node's layer. For the spacing between nodes and edges that cross the node's layer 'spacing.edgeNode' is used."
    targetParents .visible (some "spacing") (some (OptionBound.atLeast 0.0))
  let r := registerOption r LayeredOptions.SPACING_EDGE_EDGE_BETWEEN_LAYERS .double
    "Edge Edge Between Layer Spacing"
    "Spacing to be preserved between pairs of edges that are routed between the same pair of layers. Note that 'spacing.edgeEdge' is used for the spacing between pairs of edges crossing the same layer."
    targetParents .visible (some "spacing") (some (OptionBound.atLeast 0.0))
  let r := registerOption r LayeredOptions.SPACING_NODE_NODE_BETWEEN_LAYERS .double
    "Node Node Between Layers Spacing"
    "The spacing to be preserved between any pair of nodes of two adjacent layers. Note that 'spacing.nodeNode' is used for the spacing between nodes within the layer itself."
    targetParents .visible (some "spacing") (some (OptionBound.atLeast 0.0))
  r

/-- `register_priority_options`. -/
def registerPriorityOptions (r : Registry) : Registry :=
  let r := registerOption r LayeredOptions.PRIORITY_DIRECTION .int
    "Direction Priority"
    "Defines how important it is to have a certain edge point into the direction of the overall layout. This option is evaluated during the cycle breaking phase."
    targetEdges .advanced (some "priority") (some (OptionBound.atLeastInt 0))
  let r := registerOption r LayeredOptions.PRIORITY_SHORTNESS .int
    "Shortness Priority"
    "Defines how important it is to keep an edge as short as possible. This option is evaluated during the layering phase."
    targetEdges .advanced (some "priority") (some (OptionBound.atLeastInt 0))
  let r := registerOption r LayeredOptions.PRIORITY_STRAIGHTNESS .int
    "Straightness Priority"
    "Defines how important it is to keep an edge straight, i.e. aligned with one of the two axes. This option is evaluated during node placement."
    targetEdges .advanced (some "priority") (some (OptionBound.atLeastInt 0))
  r

/-- `register_wrapping_options`. -/
def registerWrappingOptions (r : Registry) : Registry :=
  let r := registerEnumOption r LayeredOptions.WRAPPING_STRATEGY
    "Graph Wrapping Strategy"
    "For certain graphs and certain prescribed drawing areas it may be desirable to split the laid out graph into chunks that are placed side by side. The edges that connect different chunks are 'wrapped' around from the end of one chunk to the start of the other chunk. The points between the chunks are referred to as 'cuts'."
    targetParents .advanced (some "wrapping") none
  let r := registerOption r LayeredOptions.WRAPPING_ADDITIONAL_EDGE_SPACING .double
    "Additional Wrapped Edges Spacing"
    "To visually separate edges that are wrapped from regularly routed edges an additional spacing value can be specified in form of this layout option. The spacing is added to the regular edgeNode spacing."
    targetParents .advanced (some "wrapping") none
  let r := registerOption r LayeredOptions.WRAPPING_CORRECTION_FACTOR .double
    "Correction Factor for Wrapping"
    "At times and for certain types of graphs the executed wrapping may produce results that are consistently biased in the same fashion: either wrapping to often or to rarely. This factor can be used to correct the bias. Internally, it is simply multiplied with the 'aspect ratio' layout option."
    targetParents .advanced (some "wrapping") none
  let r := registerEnumOption r LayeredOptions.WRAPPING_CUTTING_STRATEGY
    "Cutting Strategy"
    "The strategy by which the layer indexes are determined at which the layering crumbles into chunks."
    targetParents .advanced (some "wrapping.cutting") none
  let r := registerOption r LayeredOptions.WRAPPING_CUTTING_CUTS .object
    "Manually Specified Cuts"
    "Allows the user to specify her own cuts for a certain graph."
    targetParents .advanced (some "wrapping.cutting") none
  let r := registerOption r LayeredOptions.WRAPPING_CUTTING_MSD_FREEDOM .int
    "MSD Freedom"
    "The MSD cutting strategy starts with an initial guess on the number of chunks the graph should be split into. The freedom specifies how much the strategy may deviate from this guess. E.g. if an initial number of 3 is computed, a freedom of 1 allows 2, 3, and 4 cuts."
    targetParents .advanced (some "wrapping.cutting.msd") (some (OptionBound.atLeastInt 0))
  let r := registerEnumOption r LayeredOptions.WRAPPING_VALIDIFY_STRATEGY
    "Validification Strategy"
    "When wrapping graphs, one can specify indices that are not allowed as split points. The validification strategy makes sure every computed split point is allowed."
    targetParents .advanced (some "wrapping.validify") none
  let r := registerOption r LayeredOptions.WRAPPING_VALIDIFY_FORBIDDEN_INDICES .object
    "Valid Indices for Wrapping"
    ""
    targetParents .advanced (some "wrapping.validify") none
  let r := registerOption r LayeredOptions.WRAPPING_MULTI_EDGE_IMPROVE_CUTS .boolean
    "Improve Cuts"
    "For general graphs it is important that not too many edges wrap backwards. Thus a compromise between evenly-distributed cuts and the total number of cut edges is sought."
    targetParents .advanced (some "wrapping.multiEdge") none
  let r := registerOption r LayeredOptions.WRAPPING_MULTI_EDGE_DISTANCE_PENALTY .double
    "Distance Penalty When Improving Cuts "
    ""
    targetParents .advanced (some "wrapping.multiEdge") none
  let r := registerOption r LayeredOptions.WRAPPING_MULTI_EDGE_IMPROVE_WRAPPED_EDGES .boolean
    "Improve Wrapped Edges"
    "The initial wrapping is performed in a very simple way. As a consequence, edges that wrap from one chunk to another may be unnecessarily long. Activating this option tries to shorten such edges."
    targetParents .advanced (some "wrapping.multiEdge") none
  r

/-- `register_layer_unzipping_options`. -/
def registerLayerUnzippingOptions (r : Registry) : Registry :=
  let r := registerEnumOption r LayeredOptions.LAYER_UNZIPPING_STRATEGY
    "Layer Unzipping Strategy"
    "The strategy to use for unzipping a layer into multiple sublayers while maintaining the existing ordering of nodes and edges after crossing minimization. The default value is 'NONE'."
    targetParents .visible (some "layerUnzipping") none
  let r := registerOption r LayeredOptions.LAYER_UNZIPPING_MINIMIZE_EDGE_LENGTH .boolean
    "Minimize Edge Length Heuristic"
    "Use a heuristic to decide whether or not to actually perform the layer split with the goal of minimizing the total edge length. This option only works when layerSplit is set to 2. The property can be set to the nodes in a layer, which then applies the property for the layer. If any node sets the value to true, then the value is set to true for the entire layer."
    targetNodes .visible (some "layerUnzipping") none
  let r := registerOption r LayeredOptions.LAYER_UNZIPPING_LAYER_SPLIT .int
    "Unzipping Layer Split"
    "Defines the number of sublayers to split a layer into. The property can be set to the nodes in a layer, which then applies the property for the layer. If multiple nodes set the value to different values, then the lowest value is chosen."
    targetNodes .advanced (some "layerUnzipping") (some (OptionBound.atLeastInt 1))
  let r := registerOption r LayeredOptions.LAYER_UNZIPPING_RESET_ON_LONG_EDGES .boolean
    "Reset Alternation on Long Edges"
    "If set to true, nodes will always be placed in the first sublayer after a long edge when using the ALTERNATING strategy. Otherwise long edge dummies are treated the same as regular nodes. The default value is true. The property can be set to the nodes in a layer, which then applies the property for the layer. If any node sets the value to false, then the value is set to false for the entire layer."
    targetNodes .visible (some "layerUnzipping") none
  r

/-- `register_cycle_breaking_options`. -/
def registerCycleBreakingOptions (r : Registry) : Registry :=
  let r := registerEnumOption r LayeredOptions.CYCLE_BREAKING_STRATEGY
    "Cycle Breaking Strategy"
    "Strategy for cycle breaking. Cycle breaking looks for cycles in the graph and determines which edges to reverse to break the cycles."
    targetParents .visible (some "cycleBreaking") none
  r

/-- `register_layering_options`. -/
def registerLayeringOptions (r : Registry) : Registry :=
  let r := registerEnumOption r LayeredOptions.LAYERING_STRATEGY
    "Node Layering Strategy"
    "Strategy for node layering."
    targetParents .visible (some "layering") none
  let r := registerEnumOption r LayeredOptions.LAYERING_LAYER_CONSTRAINT
    "Layer Constraint"
    "Determines a constraint on the placement of the node regarding the layering."
    targetNodes .advanced (some "layering") none
  let r := registerOption r LayeredOptions.LAYERING_LAYER_CHOICE_CONSTRAINT .int
    "Layer Choice Constraint"
    "Allows to set a constraint regarding the layer placement of a node."
    targetNodes .advanced (some "layering") (some (OptionBound.atLeastInt (-1)))
  let r := registerOption r LayeredOptions.LAYERING_LAYER_ID .int
    "Layer ID"
    "Layer identifier that was calculated by ELK Layered for a node."
    targetNodes .advanced (some "layering") (some (OptionBound.atLeastInt (-1)))
  let r := registerOption r LayeredOptions.LAYERING_MIN_WIDTH_UPPER_BOUND_ON_WIDTH .int
    "Upper Bound On Width [MinWidth Layerer]"
    "Defines a loose upper bound on the width of the MinWidth layerer. If set to -1 multiple values are tested and the best result is selected."
    targetParents .advanced (some "layering.minWidth") (some (OptionBound.atLeastInt (-1)))
  let r := registerOption r LayeredOptions.LAYERING_MIN_WIDTH_UPPER_LAYER_ESTIMATION_SCALING_FACTOR .int
    "Upper Layer Estimation Scaling Factor [MinWidth Layerer]"
    "Multiplied with Upper Bound On Width for defining an upper bound on the width of layers which haven't been determined yet."
    targetParents .advanced (some "layering.minWidth") (some (OptionBound.atLeastInt (-1)))
  let r := registerEnumOption r LayeredOptions.LAYERING_NODE_PROMOTION_STRATEGY
    "Node Promotion Strategy"
    "Reduces number of dummy nodes after layering phase (if possible)."
    targetParents .advanced (some "layering.nodePromotion") none
  let r := registerOption r LayeredOptions.LAYERING_NODE_PROMOTION_MAX_ITERATIONS .int
    "Max Node Promotion Iterations"
    "Limits the number of iterations for node promotion."
    targetParents .advanced (some "layering.nodePromotion") (some (OptionBound.atLeastInt 0))
  let r := registerOption r LayeredOptions.LAYERING_COFFMAN_GRAHAM_LAYER_BOUND .int
    "Layer Bound"
    "The maximum number of nodes allowed per layer."
    targetParents .advanced (some "layering.coffmanGraham") none
  r

/-- `register_crossing_minimization_options`. -/
def registerCrossingMinimizationOptions (r : Registry) : Registry :=
  let r := registerEnumOption r LayeredOptions.CROSSING_MINIMIZATION_STRATEGY
    "Crossing Minimization Strategy"
    "Strategy for crossing minimization."
    targetParents .visible (some "crossingMinimization") none
  let r := registerOption r LayeredOptions.CROSSING_MINIMIZATION_FORCE_NODE_MODEL_ORDER .boolean
    "Force Node Model Order"
    "The node order given by the model does not change to produce a better layout. This assumes that the node model order is already respected before crossing minimization."
    targetParents .visible (some "crossingMinimization") none
  let r := registerOption r LayeredOptions.CROSSING_MINIMIZATION_HIERARCHICAL_SWEEPINESS .double
    "Hierarchical Sweepiness"
    "How likely it is to use cross-hierarchy (1) vs bottom-up (-1)."
    targetParents .advanced (some "crossingMinimization") none
  let r := registerOption r LayeredOptions.CROSSING_MINIMIZATION_GREEDY_SWITCH_ACTIVATION_THRESHOLD .int
    "Greedy Switch Activation Threshold"
    "By default it is decided automatically if the greedy switch is activated or not. A value of 0 enforces the activation."
    targetParents .advanced (some "crossingMinimization.greedySwitch") (some (OptionBound.atLeastInt 0))
  let r := registerEnumOption r LayeredOptions.CROSSING_MINIMIZATION_GREEDY_SWITCH_TYPE
    "Greedy Switch Crossing Minimization"
    "Greedy switch strategy executed after regular crossing minimization."
    targetParents .advanced (some "crossingMinimization.greedySwitch") none
  let r := registerEnumOption r LayeredOptions.CROSSING_MINIMIZATION_GREEDY_SWITCH_HIERARCHICAL_TYPE
    "Greedy Switch Crossing Minimization (Hierarchical)"
    "Greedy switch strategy in case hierarchical layout is used."
    targetParents .advanced (some "crossingMinimization.greedySwitchHierarchical") none
  let r := registerOption r LayeredOptions.CROSSING_MINIMIZATION_SEMI_INTERACTIVE .boolean
    "Semi-Interactive Crossing Minimization"
    "Preserves the order of nodes within a layer but still minimizes crossings between edges connecting long edge dummies."
    targetParents .advanced (some "crossingMinimization") none
  let r := registerOption r LayeredOptions.CROSSING_MINIMIZATION_IN_LAYER_PRED_OF .string
    "In Layer Predecessor Of"
    "Specifies of which node the current node is the predecessor in the same layer."
    targetNodes .visible (some "crossingMinimization") none
  let r := registerOption r LayeredOptions.CROSSING_MINIMIZATION_IN_LAYER_SUCC_OF .string
    "In Layer Successor Of"
    "Specifies of which node the current node is the successor in the same layer."
    targetNodes .advanced (some "crossingMinimization") none
  let r := registerOption r LayeredOptions.CROSSING_MINIMIZATION_POSITION_CHOICE_CONSTRAINT .int
    "Position Choice Constraint"
    "Allows to set a constraint regarding the position placement of a node in a layer."
    targetNodes .advanced (some "crossingMinimization") (some (OptionBound.atLeastInt (-1)))
  let r := registerOption r LayeredOptions.CROSSING_MINIMIZATION_POSITION_ID .int
    "Position ID"
    "Position within a layer that was determined by ELK Layered for a node."
    targetNodes .advanced (some "crossingMinimization") (some (OptionBound.atLeastInt (-1)))
  r

/-- `register_node_placement_options`. -/
def registerNodePlacementOptions (r : Registry) : Registry :=
  let r := registerEnumOption r LayeredOptions.NODE_PLACEMENT_STRATEGY
    "Node Placement Strategy"
    "Strategy for node placement."
    targetParents .visible (some "nodePlacement") none
  let r := registerOption r LayeredOptions.NODE_PLACEMENT_FAVOR_STRAIGHT_EDGES .boolean
    "Favor Straight Edges Over Balancing"
    "Favor straight edges over a balanced node placement. The default behavior is determined automatically based on the used edge routing."
    targetParents .visible (some "nodePlacement") none
  let r := registerEnumOption r LayeredOptions.NODE_PLACEMENT_BK_EDGE_STRAIGHTENING
    "BK Edge Straightening"
    "Specifies whether the Brandes-Koepf node placer tries to increase the number of straight edges."
    targetParents .advanced (some "nodePlacement.bk") none
  let r := registerEnumOption r LayeredOptions.NODE_PLACEMENT_BK_FIXED_ALIGNMENT
    "BK Fixed Alignment"
    "Tells the BK node placer to use a certain alignment."
    targetParents .advanced (some "nodePlacement.bk") none (choices := FixedAlignment.javaChoiceNames)
  let r := registerOption r LayeredOptions.NODE_PLACEMENT_LINEAR_SEGMENTS_DEFLECTION_DAMPENING .double
    "Linear Segments Deflection Dampening"
    "Dampens the movement of nodes to keep the diagram from getting too large."
    targetParents .advanced (some "nodePlacement.linearSegments") (some (OptionBound.atLeast 0.0))
  let r := registerEnumOption r LayeredOptions.NODE_PLACEMENT_NETWORK_SIMPLEX_NODE_FLEXIBILITY
    "Node Flexibility"
    "Aims at shorter and straighter edges by allowing ports or node sizes to change during network simplex node placement."
    targetNodes .advanced (some "nodePlacement.networkSimplex") none
  let r := registerEnumOption r LayeredOptions.NODE_PLACEMENT_NETWORK_SIMPLEX_NODE_FLEXIBILITY_DEFAULT
    "Node Flexibility Default"
    "Default value of the node flexibility option for the children of a hierarchical node."
    targetParents .advanced (some "nodePlacement.networkSimplex.nodeFlexibility") none
  let r := registerEnumOption r LayeredOptions.NODE_PLACEMENT_NETWORK_SIMPLEX_NODE_FLEXIBILITY_RECOMPUTE_NODE_PLACEMENT
    "Node Flexibility Recompute Node Placement"
    "Run a second node placement algorithm after the initial network simplex with node flexibility. In the second run, node flexibility is disabled and a different node placer can be used. The node sizes determined by the node flexibility option are used as fixed node sizes in the second run. If set to null (default) no second run is performed."
    targetParents .advanced (some "nodePlacement.networkSimplex.nodeFlexibility") none
  r

/-- `register_edge_routing_options`. -/
def registerEdgeRoutingOptions (r : Registry) : Registry :=
  let r := registerEnumOption r LayeredOptions.EDGE_ROUTING_SPLINES_MODE
    "Spline Routing Mode"
    "Specifies the way control points are assembled for each individual edge."
    targetParents .visible (some "edgeRouting.splines") none
  let r := registerOption r LayeredOptions.EDGE_ROUTING_SPLINES_SLOPPY_LAYER_SPACING_FACTOR .double
    "Sloppy Spline Layer Spacing Factor"
    "Spacing factor for routing area between layers when using sloppy spline routing."
    targetParents .visible (some "edgeRouting.splines.sloppy") none
  let r := registerOption r LayeredOptions.EDGE_ROUTING_POLYLINE_SLOPED_EDGE_ZONE_WIDTH .double
    "Sloped Edge Zone Width"
    "Width of the strip to the left and to the right of each layer where the polyline edge router is allowed to refrain from ensuring that edges are routed horizontally."
    targetParents .advanced (some "edgeRouting.polyline") none
  let r := registerEnumOption r LayeredOptions.EDGE_ROUTING_SELF_LOOP_DISTRIBUTION
    "Self-Loop Distribution"
    "Alter the distribution of the loops around the node."
    targetNodes .visible (some "edgeRouting") none
  let r := registerEnumOption r LayeredOptions.EDGE_ROUTING_SELF_LOOP_ORDERING
    "Self-Loop Ordering"
    "Alter the ordering of the loops."
    targetNodes .visible (some "edgeRouting") none
  r

/-- `register_compaction_options`. -/
def registerCompactionOptions (r : Registry) : Registry :=
  let r := registerEnumOption r LayeredOptions.COMPACTION_POST_COMPACTION_STRATEGY
    "Post Compaction Strategy"
    "Specifies whether and how post-process compaction is applied."
    targetParents .advanced (some "compaction.postCompaction") none
  let r := registerEnumOption r LayeredOptions.COMPACTION_POST_COMPACTION_CONSTRAINTS
    "Post Compaction Constraint Calculation"
    "Specifies how post-process compaction constraints are calculated."
    targetParents .advanced (some "compaction.postCompaction") none
  let r := registerOption r LayeredOptions.COMPACTION_CONNECTED_COMPONENTS .boolean
    "Connected Components Compaction"
    "Tries to further compact components (disconnected sub-graphs)."
    targetParents .advanced (some "compaction") none
  r

/-- `register_high_degree_options`. -/
def registerHighDegreeOptions (r : Registry) : Registry :=
  let r := registerOption r LayeredOptions.HIGH_DEGREE_NODES_TREATMENT .boolean
    "High Degree Node Treatment"
    "Makes room around high degree nodes to place leafs and trees."
    targetParents .advanced (some "highDegreeNodes") none
  let r := registerOption r LayeredOptions.HIGH_DEGREE_NODES_THRESHOLD .int
    "High Degree Node Threshold"
    "Whether a node is considered to have a high degree."
    targetParents .advanced (some "highDegreeNodes") (some (OptionBound.atLeastInt 0))
  let r := registerOption r LayeredOptions.HIGH_DEGREE_NODES_TREE_HEIGHT .int
    "High Degree Node Maximum Tree Height"
    "Maximum height of a subtree connected to a high degree node to be moved to separate layers."
    targetParents .advanced (some "highDegreeNodes") (some (OptionBound.atLeastInt 0))
  r

/-- `register_misc_options`. -/
def registerMiscOptions (r : Registry) : Registry :=
  let r := registerEnumOption r LayeredOptions.DIRECTION_CONGRUENCY
    "Direction Congruency"
    "Specifies how drawings of the same graph with different layout directions compare to each other: either a natural reading direction is preserved or the drawings are rotated versions of each other."
    targetParents .advanced none none
  let r := registerOption r LayeredOptions.FEEDBACK_EDGES .boolean
    "Feedback Edges"
    "Whether feedback edges should be highlighted by routing around the nodes."
    targetParents .advanced none none
  let r := registerEnumOption r LayeredOptions.INTERACTIVE_REFERENCE_POINT
    "Interactive Reference Point"
    "Determines which point of a node is considered by interactive layout phases."
    targetParents .advanced none none
  let r := registerOption r LayeredOptions.MERGE_EDGES .boolean
    "Merge Edges"
    "Edges that have no ports are merged so they touch the connected nodes at the same points."
    targetParents .advanced none none
  let r := registerOption r LayeredOptions.MERGE_HIERARCHY_EDGES .boolean
    "Merge Hierarchy-Crossing Edges"
    "If hierarchical layout is active, hierarchy-crossing edges use as few hierarchical ports as possible."
    targetParents .advanced none none
  let r := registerOption r LayeredOptions.ALLOW_NON_FLOW_PORTS_TO_SWITCH_SIDES .boolean
    "Allow Non-Flow Ports To Switch Sides"
    "Specifies whether non-flow ports may switch sides for FIXED_SIDE or FIXED_ORDER constraints."
    targetPorts .advanced none none
  let r := registerEnumOption r LayeredOptions.PORT_SORTING_STRATEGY
    "Port Sorting Strategy"
    "Determines the way a node's ports are distributed on the sides of a node if their order is not prescribed."
    targetParents .advanced none none
  let r := registerOption r LayeredOptions.THOROUGHNESS .int
    "Thoroughness"
    "How much effort should be spent to produce a nice layout."
    targetParents .advanced none (some (OptionBound.atLeastInt 1))
  let r := registerOption r LayeredOptions.UNNECESSARY_BENDPOINTS .boolean
    "Add Unnecessary Bendpoints"
    "Adds bend points even if an edge does not change direction."
    targetParents .advanced none none
  let r := registerOption r LayeredOptions.GENERATE_POSITION_AND_LAYER_IDS .boolean
    "Generate Position and Layer IDs"
    "If enabled position id and layer id are generated, which are usually only used internally when setting the interactive layout option."
    targetParents .advanced none none
  r

/-- `register_edge_label_options`. -/
def registerEdgeLabelOptions (r : Registry) : Registry :=
  let r := registerEnumOption r LayeredOptions.EDGE_LABELS_SIDE_SELECTION
    "Edge Label Side Selection"
    "Method to decide on edge label sides."
    targetParents .visible (some "edgeLabels") none
  let r := registerEnumOption r LayeredOptions.EDGE_LABELS_CENTER_LABEL_PLACEMENT_STRATEGY
    "Edge Center Label Placement Strategy"
    "Determines in which layer center labels of long edges should be placed."
    targetParentsLabels .advanced (some "edgeLabels") none
  r

/-- `register_consider_model_order_options`. -/
def registerConsiderModelOrderOptions (r : Registry) : Registry :=
  let r := registerEnumOption r LayeredOptions.CONSIDER_MODEL_ORDER_STRATEGY
    "Consider Model Order"
    "Preserves the order of nodes and edges in the model file if this does not lead to additional edge crossings. Depending on the strategy this is not always possible since the node and edge order might be conflicting."
    targetParents .visible (some "considerModelOrder") none
  let r := registerOption r LayeredOptions.CONSIDER_MODEL_ORDER_PORT_MODEL_ORDER .boolean
    "Consider Port Order"
    "If disabled the port order of output ports is derived from the edge order and input ports are ordered by their incoming connections. If enabled all ports are ordered by the port model order."
    targetParents .visible (some "considerModelOrder") none
  let r := registerOption r LayeredOptions.CONSIDER_MODEL_ORDER_NO_MODEL_ORDER .boolean
    "No Model Order"
    "Set on a node to not set a model order for this node even though it is a real node."
    targetNodes .visible (some "considerModelOrder") none
  let r := registerEnumOption r LayeredOptions.CONSIDER_MODEL_ORDER_COMPONENTS
    "Consider Model Order for Components"
    "If set to NONE the usual ordering strategy (by cumulative node priority and size of nodes) is used. INSIDE_PORT_SIDES orders the components with external ports only inside the groups with the same port side. FORCE_MODEL_ORDER enforces the mode order on components. This option might produce bad alignments and sub optimal drawings in terms of used area since the ordering should be respected."
    targetParents .visible (some "considerModelOrder") none
  let r := registerEnumOption r LayeredOptions.CONSIDER_MODEL_ORDER_LONG_EDGE_STRATEGY
    "Long Edge Ordering Strategy"
    "Indicates whether long edges are sorted under, over, or equal to nodes that have no connection to a previous layer in a left-to-right or right-to-left layout. Under and over changes to right and left in a vertical layout."
    targetParents .visible (some "considerModelOrder") none
  let r := registerOption r LayeredOptions.CONSIDER_MODEL_ORDER_CROSSING_COUNTER_NODE_INFLUENCE .double
    "Crossing Counter Node Order Influence"
    "Indicates with what percentage (1 for 100%) violations of the node model order are weighted against the crossings e.g. a value of 0.5 means two model order violations are as important as on edge crossing. This allows some edge crossings in favor of preserving the model order. It is advised to set this value to a very small positive value (e.g. 0.001) to have minimal crossing and a optimal node order. Defaults to no influence (0)."
    targetParents .visible (some "considerModelOrder") none
  let r := registerOption r LayeredOptions.CONSIDER_MODEL_ORDER_CROSSING_COUNTER_PORT_INFLUENCE .double
    "Crossing Counter Port Order Influence"
    "Indicates with what percentage (1 for 100%) violations of the port model order are weighted against the crossings e.g. a value of 0.5 means two model order violations are as important as on edge crossing. This allows some edge crossings in favor of preserving the model order. It is advised to set this value to a very small positive value (e.g. 0.001) to have minimal crossing and a optimal port order. Defaults to no influence (0)."
    targetParents .visible (some "considerModelOrder") none
  let r := registerOption r LayeredOptions.GROUP_MODEL_ORDER_CYCLE_BREAKING_ID .int
    "Group ID of the Node Type"
    "Used to define partial ordering groups during cycle breaking. A lower group id means that the group is sorted before other groups. A group model order of 0 is the default group."
    targetNodes .visible (some "considerModelOrder.groupModelOrder") none
  let r := registerOption r LayeredOptions.GROUP_MODEL_ORDER_CROSSING_MINIMIZATION_ID .int
    "Group ID of the Node Type"
    "Used to define partial ordering groups during crossing minimization. A lower group id means that the group is sorted before other groups. A group model order of 0 is the default group."
    targetNodesEdgesPorts .visible (some "considerModelOrder.groupModelOrder") none
  let r := registerOption r LayeredOptions.GROUP_MODEL_ORDER_COMPONENT_GROUP_ID .int
    "Group ID of the Node Type"
    "Used to define partial ordering groups during component packing. A lower group id means that the group is sorted before other groups. A group model order of 0 is the default group."
    targetNodesEdgesPorts .visible (some "considerModelOrder.groupModelOrder") none
  let r := registerEnumOption r LayeredOptions.GROUP_MODEL_ORDER_CB_GROUP_ORDER_STRATEGY
    "Cycle Breaking Group Ordering Strategy"
    "Determines how to count ordering violations during cycle breaking. NONE: They do not count. ENFORCED: A group with a higher model order is before a node with a smaller. MODEL_ORDER: The model order counts instead of the model order group id ordering."
    targetParents .visible (some "considerModelOrder.groupModelOrder") none
  let r := registerOption r LayeredOptions.GROUP_MODEL_ORDER_CB_PREFERRED_SOURCE_ID .int
    "Cycle Breaking Preferred Source Id"
    "The model order group id for which should be preferred as a source if possible."
    targetParents .visible (some "considerModelOrder.groupModelOrder") none
  let r := registerOption r LayeredOptions.GROUP_MODEL_ORDER_CB_PREFERRED_TARGET_ID .int
    "Cycle Breaking Preferred Target Id"
    "The model order group id for which should be preferred as a target if possible."
    targetParents .visible (some "considerModelOrder.groupModelOrder") none
  let r := registerEnumOption r LayeredOptions.GROUP_MODEL_ORDER_CM_GROUP_ORDER_STRATEGY
    "Crossing Minimization Group Ordering Strategy"
    "Determines how to count ordering violations during crossing minimization. NONE: They do not count. ENFORCED: A group with a lower id is before a group with a higher id. MODEL_ORDER: The model order counts instead of the model order group id ordering."
    targetParents .visible (some "considerModelOrder.groupModelOrder") none
  let r := registerOption r LayeredOptions.GROUP_MODEL_ORDER_CM_ENFORCED_GROUP_ORDERS .object
    "Crossing Minimization Enforced Group Orders"
    "Holds all group ids which are enforcing their order during crossing minimization strategies. E.g. if only groups 2 and -1 (default) enforce their ordering. Other groups e.g. the group of timer nodes can be ordered arbitrarily if it helps and the mentioned groups may not change their order."
    targetParents .visible (some "considerModelOrder.groupModelOrder") none
  r

/-! ### Option supports -/

/-- `register_option_supports`: the options known to `org.eclipse.elk.layered` with their
algorithm-specific defaults, in Rust order (`(option id, default)`). Most defaults are the
property defaults (`property_default_any`); the explicit ones (`explicit_default_any`) are
`PRIORITY = 0`, `TOPDOWN_NODE_TYPE = HIERARCHICAL_NODE`, `EDGE_ROUTING = ORTHOGONAL`,
`PORT_BORDER_OFFSET = 0.0`, `RANDOM_SEED = 1`, `ASPECT_RATIO = 1.6`,
`SEPARATE_CONNECTED_COMPONENTS = true` and `PORT_ALIGNMENT_DEFAULT = JUSTIFIED`. -/
def optionSupports : Array (String × Option PropValue) := #[
  (LayeredOptions.SPACING_COMMENT_COMMENT.id, propertyDefault LayeredOptions.SPACING_COMMENT_COMMENT),
  (LayeredOptions.SPACING_COMMENT_NODE.id, propertyDefault LayeredOptions.SPACING_COMMENT_NODE),
  (LayeredOptions.SPACING_COMPONENT_COMPONENT.id, propertyDefault LayeredOptions.SPACING_COMPONENT_COMPONENT),
  (LayeredOptions.SPACING_EDGE_EDGE.id, propertyDefault LayeredOptions.SPACING_EDGE_EDGE),
  (LayeredOptions.SPACING_EDGE_LABEL.id, propertyDefault LayeredOptions.SPACING_EDGE_LABEL),
  (LayeredOptions.SPACING_EDGE_NODE.id, propertyDefault LayeredOptions.SPACING_EDGE_NODE),
  (LayeredOptions.SPACING_LABEL_LABEL.id, propertyDefault LayeredOptions.SPACING_LABEL_LABEL),
  (LayeredOptions.SPACING_LABEL_PORT_HORIZONTAL.id, propertyDefault LayeredOptions.SPACING_LABEL_PORT_HORIZONTAL),
  (LayeredOptions.SPACING_LABEL_PORT_VERTICAL.id, propertyDefault LayeredOptions.SPACING_LABEL_PORT_VERTICAL),
  (LayeredOptions.SPACING_LABEL_NODE.id, propertyDefault LayeredOptions.SPACING_LABEL_NODE),
  (LayeredOptions.SPACING_NODE_NODE.id, propertyDefault LayeredOptions.SPACING_NODE_NODE),
  (LayeredOptions.SPACING_NODE_SELF_LOOP.id, propertyDefault LayeredOptions.SPACING_NODE_SELF_LOOP),
  (LayeredOptions.SPACING_PORT_PORT.id, propertyDefault LayeredOptions.SPACING_PORT_PORT),
  (LayeredOptions.SPACING_INDIVIDUAL.id, propertyDefault LayeredOptions.SPACING_INDIVIDUAL),
  (LayeredOptions.SPACING_BASE_VALUE.id, propertyDefault LayeredOptions.SPACING_BASE_VALUE),
  (LayeredOptions.SPACING_EDGE_EDGE_BETWEEN_LAYERS.id, propertyDefault LayeredOptions.SPACING_EDGE_EDGE_BETWEEN_LAYERS),
  (LayeredOptions.SPACING_EDGE_NODE_BETWEEN_LAYERS.id, propertyDefault LayeredOptions.SPACING_EDGE_NODE_BETWEEN_LAYERS),
  (LayeredOptions.SPACING_NODE_NODE_BETWEEN_LAYERS.id, propertyDefault LayeredOptions.SPACING_NODE_NODE_BETWEEN_LAYERS),
  (LayeredOptions.PRIORITY.id, some (.int 0)),
  (LayeredOptions.PRIORITY_DIRECTION.id, propertyDefault LayeredOptions.PRIORITY_DIRECTION),
  (LayeredOptions.PRIORITY_SHORTNESS.id, propertyDefault LayeredOptions.PRIORITY_SHORTNESS),
  (LayeredOptions.PRIORITY_STRAIGHTNESS.id, propertyDefault LayeredOptions.PRIORITY_STRAIGHTNESS),
  (LayeredOptions.WRAPPING_STRATEGY.id, propertyDefault LayeredOptions.WRAPPING_STRATEGY),
  (LayeredOptions.WRAPPING_ADDITIONAL_EDGE_SPACING.id, propertyDefault LayeredOptions.WRAPPING_ADDITIONAL_EDGE_SPACING),
  (LayeredOptions.WRAPPING_CORRECTION_FACTOR.id, propertyDefault LayeredOptions.WRAPPING_CORRECTION_FACTOR),
  (LayeredOptions.WRAPPING_CUTTING_STRATEGY.id, propertyDefault LayeredOptions.WRAPPING_CUTTING_STRATEGY),
  (LayeredOptions.WRAPPING_CUTTING_CUTS.id, propertyDefault LayeredOptions.WRAPPING_CUTTING_CUTS),
  (LayeredOptions.WRAPPING_CUTTING_MSD_FREEDOM.id, propertyDefault LayeredOptions.WRAPPING_CUTTING_MSD_FREEDOM),
  (LayeredOptions.WRAPPING_VALIDIFY_STRATEGY.id, propertyDefault LayeredOptions.WRAPPING_VALIDIFY_STRATEGY),
  (LayeredOptions.WRAPPING_VALIDIFY_FORBIDDEN_INDICES.id, propertyDefault LayeredOptions.WRAPPING_VALIDIFY_FORBIDDEN_INDICES),
  (LayeredOptions.WRAPPING_MULTI_EDGE_IMPROVE_CUTS.id, propertyDefault LayeredOptions.WRAPPING_MULTI_EDGE_IMPROVE_CUTS),
  (LayeredOptions.WRAPPING_MULTI_EDGE_DISTANCE_PENALTY.id, propertyDefault LayeredOptions.WRAPPING_MULTI_EDGE_DISTANCE_PENALTY),
  (LayeredOptions.WRAPPING_MULTI_EDGE_IMPROVE_WRAPPED_EDGES.id, propertyDefault LayeredOptions.WRAPPING_MULTI_EDGE_IMPROVE_WRAPPED_EDGES),
  (LayeredOptions.LAYER_UNZIPPING_STRATEGY.id, propertyDefault LayeredOptions.LAYER_UNZIPPING_STRATEGY),
  (LayeredOptions.LAYER_UNZIPPING_MINIMIZE_EDGE_LENGTH.id, propertyDefault LayeredOptions.LAYER_UNZIPPING_MINIMIZE_EDGE_LENGTH),
  (LayeredOptions.LAYER_UNZIPPING_LAYER_SPLIT.id, propertyDefault LayeredOptions.LAYER_UNZIPPING_LAYER_SPLIT),
  (LayeredOptions.LAYER_UNZIPPING_RESET_ON_LONG_EDGES.id, propertyDefault LayeredOptions.LAYER_UNZIPPING_RESET_ON_LONG_EDGES),
  (LayeredOptions.NODE_PLACEMENT_NETWORK_SIMPLEX_NODE_FLEXIBILITY.id, propertyDefault LayeredOptions.NODE_PLACEMENT_NETWORK_SIMPLEX_NODE_FLEXIBILITY),
  (LayeredOptions.NODE_PLACEMENT_NETWORK_SIMPLEX_NODE_FLEXIBILITY_DEFAULT.id, propertyDefault LayeredOptions.NODE_PLACEMENT_NETWORK_SIMPLEX_NODE_FLEXIBILITY_DEFAULT),
  (LayeredOptions.NODE_PLACEMENT_NETWORK_SIMPLEX_NODE_FLEXIBILITY_RECOMPUTE_NODE_PLACEMENT.id, propertyDefault LayeredOptions.NODE_PLACEMENT_NETWORK_SIMPLEX_NODE_FLEXIBILITY_RECOMPUTE_NODE_PLACEMENT),
  (LayeredOptions.EDGE_ROUTING_SPLINES_MODE.id, propertyDefault LayeredOptions.EDGE_ROUTING_SPLINES_MODE),
  (LayeredOptions.EDGE_ROUTING_SPLINES_SLOPPY_LAYER_SPACING_FACTOR.id, propertyDefault LayeredOptions.EDGE_ROUTING_SPLINES_SLOPPY_LAYER_SPACING_FACTOR),
  (CoreOptions.TOPDOWN_LAYOUT.id, propertyDefault CoreOptions.TOPDOWN_LAYOUT),
  (CoreOptions.TOPDOWN_SCALE_FACTOR.id, propertyDefault CoreOptions.TOPDOWN_SCALE_FACTOR),
  (CoreOptions.TOPDOWN_HIERARCHICAL_NODE_WIDTH.id, propertyDefault CoreOptions.TOPDOWN_HIERARCHICAL_NODE_WIDTH),
  (CoreOptions.TOPDOWN_HIERARCHICAL_NODE_ASPECT_RATIO.id, propertyDefault CoreOptions.TOPDOWN_HIERARCHICAL_NODE_ASPECT_RATIO),
  (LayeredOptions.TOPDOWN_NODE_TYPE.id, some (PropCodec.enc TopdownNodeTypes.hierarchicalNode)),
  (CoreOptions.PADDING.id, propertyDefault CoreOptions.PADDING),
  (LayeredOptions.EDGE_ROUTING.id, some (PropCodec.enc EdgeRouting.orthogonal)),
  (LayeredOptions.PORT_BORDER_OFFSET.id, some (.double 0.0)),
  (LayeredOptions.RANDOM_SEED.id, some (.int 1)),
  (LayeredOptions.ASPECT_RATIO.id, some (.double 1.6)),
  (CoreOptions.NO_LAYOUT.id, propertyDefault CoreOptions.NO_LAYOUT),
  (LayeredOptions.PORT_CONSTRAINTS.id, propertyDefault LayeredOptions.PORT_CONSTRAINTS),
  (LayeredOptions.PORT_SIDE.id, propertyDefault LayeredOptions.PORT_SIDE),
  (CoreOptions.DEBUG_MODE.id, propertyDefault CoreOptions.DEBUG_MODE),
  (LayeredOptions.ALIGNMENT.id, propertyDefault LayeredOptions.ALIGNMENT),
  (LayeredOptions.HIERARCHY_HANDLING.id, propertyDefault LayeredOptions.HIERARCHY_HANDLING),
  (LayeredOptions.SEPARATE_CONNECTED_COMPONENTS.id, some (.bool true)),
  (CoreOptions.INSIDE_SELF_LOOPS_ACTIVATE.id, propertyDefault CoreOptions.INSIDE_SELF_LOOPS_ACTIVATE),
  (CoreOptions.INSIDE_SELF_LOOPS_YO.id, propertyDefault CoreOptions.INSIDE_SELF_LOOPS_YO),
  (LayeredOptions.NODE_SIZE_CONSTRAINTS.id, propertyDefault LayeredOptions.NODE_SIZE_CONSTRAINTS),
  (CoreOptions.NODE_SIZE_OPTIONS.id, propertyDefault CoreOptions.NODE_SIZE_OPTIONS),
  (CoreOptions.NODE_SIZE_FIXED_GRAPH_SIZE.id, propertyDefault CoreOptions.NODE_SIZE_FIXED_GRAPH_SIZE),
  (LayeredOptions.DIRECTION.id, propertyDefault LayeredOptions.DIRECTION),
  (LayeredOptions.NODE_LABELS_PLACEMENT.id, propertyDefault LayeredOptions.NODE_LABELS_PLACEMENT),
  (LayeredOptions.NODE_LABELS_PADDING.id, propertyDefault LayeredOptions.NODE_LABELS_PADDING),
  (CoreOptions.PORT_LABELS_PLACEMENT.id, propertyDefault CoreOptions.PORT_LABELS_PLACEMENT),
  (CoreOptions.PORT_LABELS_NEXT_TO_PORT_IF_POSSIBLE.id, propertyDefault CoreOptions.PORT_LABELS_NEXT_TO_PORT_IF_POSSIBLE),
  (CoreOptions.PORT_LABELS_TREAT_AS_GROUP.id, propertyDefault CoreOptions.PORT_LABELS_TREAT_AS_GROUP),
  (CoreOptions.PORT_ALIGNMENT_DEFAULT.id, some (PropCodec.enc PortAlignment.justified)),
  (CoreOptions.PORT_ALIGNMENT_NORTH.id, propertyDefault CoreOptions.PORT_ALIGNMENT_NORTH),
  (CoreOptions.PORT_ALIGNMENT_SOUTH.id, propertyDefault CoreOptions.PORT_ALIGNMENT_SOUTH),
  (CoreOptions.PORT_ALIGNMENT_WEST.id, propertyDefault CoreOptions.PORT_ALIGNMENT_WEST),
  (CoreOptions.PORT_ALIGNMENT_EAST.id, propertyDefault CoreOptions.PORT_ALIGNMENT_EAST),
  (LayeredOptions.UNNECESSARY_BENDPOINTS.id, propertyDefault LayeredOptions.UNNECESSARY_BENDPOINTS),
  (LayeredOptions.LAYERING_STRATEGY.id, propertyDefault LayeredOptions.LAYERING_STRATEGY),
  (LayeredOptions.LAYERING_NODE_PROMOTION_STRATEGY.id, propertyDefault LayeredOptions.LAYERING_NODE_PROMOTION_STRATEGY),
  (LayeredOptions.THOROUGHNESS.id, propertyDefault LayeredOptions.THOROUGHNESS),
  (LayeredOptions.LAYERING_LAYER_CONSTRAINT.id, propertyDefault LayeredOptions.LAYERING_LAYER_CONSTRAINT),
  (LayeredOptions.CYCLE_BREAKING_STRATEGY.id, propertyDefault LayeredOptions.CYCLE_BREAKING_STRATEGY),
  (LayeredOptions.CROSSING_MINIMIZATION_STRATEGY.id, propertyDefault LayeredOptions.CROSSING_MINIMIZATION_STRATEGY),
  (LayeredOptions.CROSSING_MINIMIZATION_FORCE_NODE_MODEL_ORDER.id, propertyDefault LayeredOptions.CROSSING_MINIMIZATION_FORCE_NODE_MODEL_ORDER),
  (LayeredOptions.CROSSING_MINIMIZATION_GREEDY_SWITCH_ACTIVATION_THRESHOLD.id, propertyDefault LayeredOptions.CROSSING_MINIMIZATION_GREEDY_SWITCH_ACTIVATION_THRESHOLD),
  (LayeredOptions.CROSSING_MINIMIZATION_GREEDY_SWITCH_TYPE.id, propertyDefault LayeredOptions.CROSSING_MINIMIZATION_GREEDY_SWITCH_TYPE),
  (LayeredOptions.CROSSING_MINIMIZATION_GREEDY_SWITCH_HIERARCHICAL_TYPE.id, propertyDefault LayeredOptions.CROSSING_MINIMIZATION_GREEDY_SWITCH_HIERARCHICAL_TYPE),
  (LayeredOptions.CROSSING_MINIMIZATION_SEMI_INTERACTIVE.id, propertyDefault LayeredOptions.CROSSING_MINIMIZATION_SEMI_INTERACTIVE),
  (LayeredOptions.MERGE_EDGES.id, propertyDefault LayeredOptions.MERGE_EDGES),
  (LayeredOptions.MERGE_HIERARCHY_EDGES.id, propertyDefault LayeredOptions.MERGE_HIERARCHY_EDGES),
  (LayeredOptions.INTERACTIVE_REFERENCE_POINT.id, propertyDefault LayeredOptions.INTERACTIVE_REFERENCE_POINT),
  (LayeredOptions.NODE_PLACEMENT_STRATEGY.id, propertyDefault LayeredOptions.NODE_PLACEMENT_STRATEGY),
  (LayeredOptions.NODE_PLACEMENT_BK_FIXED_ALIGNMENT.id, propertyDefault LayeredOptions.NODE_PLACEMENT_BK_FIXED_ALIGNMENT),
  (LayeredOptions.FEEDBACK_EDGES.id, propertyDefault LayeredOptions.FEEDBACK_EDGES),
  (LayeredOptions.NODE_PLACEMENT_LINEAR_SEGMENTS_DEFLECTION_DAMPENING.id, propertyDefault LayeredOptions.NODE_PLACEMENT_LINEAR_SEGMENTS_DEFLECTION_DAMPENING),
  (LayeredOptions.EDGE_ROUTING_SELF_LOOP_DISTRIBUTION.id, propertyDefault LayeredOptions.EDGE_ROUTING_SELF_LOOP_DISTRIBUTION),
  (LayeredOptions.EDGE_ROUTING_SELF_LOOP_ORDERING.id, propertyDefault LayeredOptions.EDGE_ROUTING_SELF_LOOP_ORDERING),
  (CoreOptions.CONTENT_ALIGNMENT.id, propertyDefault CoreOptions.CONTENT_ALIGNMENT),
  (LayeredOptions.NODE_PLACEMENT_BK_EDGE_STRAIGHTENING.id, propertyDefault LayeredOptions.NODE_PLACEMENT_BK_EDGE_STRAIGHTENING),
  (LayeredOptions.COMPACTION_POST_COMPACTION_STRATEGY.id, propertyDefault LayeredOptions.COMPACTION_POST_COMPACTION_STRATEGY),
  (LayeredOptions.COMPACTION_POST_COMPACTION_CONSTRAINTS.id, propertyDefault LayeredOptions.COMPACTION_POST_COMPACTION_CONSTRAINTS),
  (LayeredOptions.COMPACTION_CONNECTED_COMPONENTS.id, propertyDefault LayeredOptions.COMPACTION_CONNECTED_COMPONENTS),
  (LayeredOptions.HIGH_DEGREE_NODES_TREATMENT.id, propertyDefault LayeredOptions.HIGH_DEGREE_NODES_TREATMENT),
  (LayeredOptions.HIGH_DEGREE_NODES_THRESHOLD.id, propertyDefault LayeredOptions.HIGH_DEGREE_NODES_THRESHOLD),
  (LayeredOptions.HIGH_DEGREE_NODES_TREE_HEIGHT.id, propertyDefault LayeredOptions.HIGH_DEGREE_NODES_TREE_HEIGHT),
  (LayeredOptions.NODE_SIZE_MINIMUM.id, propertyDefault LayeredOptions.NODE_SIZE_MINIMUM),
  (LayeredOptions.JUNCTION_POINTS.id, propertyDefault LayeredOptions.JUNCTION_POINTS),
  (CoreOptions.EDGE_THICKNESS.id, propertyDefault CoreOptions.EDGE_THICKNESS),
  (LayeredOptions.EDGE_LABELS_PLACEMENT.id, propertyDefault LayeredOptions.EDGE_LABELS_PLACEMENT),
  (LayeredOptions.EDGE_LABELS_INLINE.id, propertyDefault LayeredOptions.EDGE_LABELS_INLINE),
  (LayeredOptions.CROSSING_MINIMIZATION_HIERARCHICAL_SWEEPINESS.id, propertyDefault LayeredOptions.CROSSING_MINIMIZATION_HIERARCHICAL_SWEEPINESS),
  (LayeredOptions.PORT_INDEX.id, propertyDefault LayeredOptions.PORT_INDEX),
  (LayeredOptions.COMMENT_BOX.id, propertyDefault LayeredOptions.COMMENT_BOX),
  (LayeredOptions.HYPERNODE.id, propertyDefault LayeredOptions.HYPERNODE),
  (LayeredOptions.PORT_ANCHOR.id, propertyDefault LayeredOptions.PORT_ANCHOR),
  (CoreOptions.PARTITIONING_ACTIVATE.id, propertyDefault CoreOptions.PARTITIONING_ACTIVATE),
  (CoreOptions.PARTITIONING_PARTITION.id, propertyDefault CoreOptions.PARTITIONING_PARTITION),
  (LayeredOptions.LAYERING_MIN_WIDTH_UPPER_BOUND_ON_WIDTH.id, propertyDefault LayeredOptions.LAYERING_MIN_WIDTH_UPPER_BOUND_ON_WIDTH),
  (LayeredOptions.LAYERING_MIN_WIDTH_UPPER_LAYER_ESTIMATION_SCALING_FACTOR.id, propertyDefault LayeredOptions.LAYERING_MIN_WIDTH_UPPER_LAYER_ESTIMATION_SCALING_FACTOR),
  (LayeredOptions.POSITION.id, propertyDefault LayeredOptions.POSITION),
  (LayeredOptions.ALLOW_NON_FLOW_PORTS_TO_SWITCH_SIDES.id, propertyDefault LayeredOptions.ALLOW_NON_FLOW_PORTS_TO_SWITCH_SIDES),
  (LayeredOptions.LAYERING_NODE_PROMOTION_MAX_ITERATIONS.id, propertyDefault LayeredOptions.LAYERING_NODE_PROMOTION_MAX_ITERATIONS),
  (LayeredOptions.EDGE_LABELS_SIDE_SELECTION.id, propertyDefault LayeredOptions.EDGE_LABELS_SIDE_SELECTION),
  (LayeredOptions.EDGE_LABELS_CENTER_LABEL_PLACEMENT_STRATEGY.id, propertyDefault LayeredOptions.EDGE_LABELS_CENTER_LABEL_PLACEMENT_STRATEGY),
  (CoreOptions.MARGINS.id, propertyDefault CoreOptions.MARGINS),
  (LayeredOptions.LAYERING_COFFMAN_GRAHAM_LAYER_BOUND.id, propertyDefault LayeredOptions.LAYERING_COFFMAN_GRAHAM_LAYER_BOUND),
  (LayeredOptions.NODE_PLACEMENT_FAVOR_STRAIGHT_EDGES.id, propertyDefault LayeredOptions.NODE_PLACEMENT_FAVOR_STRAIGHT_EDGES),
  (LayeredOptions.SPACING_PORTS_SURROUNDING.id, propertyDefault LayeredOptions.SPACING_PORTS_SURROUNDING),
  (LayeredOptions.DIRECTION_CONGRUENCY.id, propertyDefault LayeredOptions.DIRECTION_CONGRUENCY),
  (LayeredOptions.PORT_SORTING_STRATEGY.id, propertyDefault LayeredOptions.PORT_SORTING_STRATEGY),
  (LayeredOptions.EDGE_ROUTING_POLYLINE_SLOPED_EDGE_ZONE_WIDTH.id, propertyDefault LayeredOptions.EDGE_ROUTING_POLYLINE_SLOPED_EDGE_ZONE_WIDTH),
  (LayeredOptions.CROSSING_MINIMIZATION_IN_LAYER_PRED_OF.id, propertyDefault LayeredOptions.CROSSING_MINIMIZATION_IN_LAYER_PRED_OF),
  (LayeredOptions.CROSSING_MINIMIZATION_IN_LAYER_SUCC_OF.id, propertyDefault LayeredOptions.CROSSING_MINIMIZATION_IN_LAYER_SUCC_OF),
  (LayeredOptions.LAYERING_LAYER_CHOICE_CONSTRAINT.id, propertyDefault LayeredOptions.LAYERING_LAYER_CHOICE_CONSTRAINT),
  (LayeredOptions.CROSSING_MINIMIZATION_POSITION_CHOICE_CONSTRAINT.id, propertyDefault LayeredOptions.CROSSING_MINIMIZATION_POSITION_CHOICE_CONSTRAINT),
  (LayeredOptions.INTERACTIVE_LAYOUT.id, propertyDefault LayeredOptions.INTERACTIVE_LAYOUT),
  (LayeredOptions.LAYERING_LAYER_ID.id, propertyDefault LayeredOptions.LAYERING_LAYER_ID),
  (LayeredOptions.CROSSING_MINIMIZATION_POSITION_ID.id, propertyDefault LayeredOptions.CROSSING_MINIMIZATION_POSITION_ID),
  (LayeredOptions.CONSIDER_MODEL_ORDER_STRATEGY.id, propertyDefault LayeredOptions.CONSIDER_MODEL_ORDER_STRATEGY),
  (LayeredOptions.CONSIDER_MODEL_ORDER_LONG_EDGE_STRATEGY.id, propertyDefault LayeredOptions.CONSIDER_MODEL_ORDER_LONG_EDGE_STRATEGY),
  (LayeredOptions.CONSIDER_MODEL_ORDER_CROSSING_COUNTER_NODE_INFLUENCE.id, propertyDefault LayeredOptions.CONSIDER_MODEL_ORDER_CROSSING_COUNTER_NODE_INFLUENCE),
  (LayeredOptions.CONSIDER_MODEL_ORDER_CROSSING_COUNTER_PORT_INFLUENCE.id, propertyDefault LayeredOptions.CONSIDER_MODEL_ORDER_CROSSING_COUNTER_PORT_INFLUENCE),
  (LayeredOptions.CONSIDER_MODEL_ORDER_NO_MODEL_ORDER.id, propertyDefault LayeredOptions.CONSIDER_MODEL_ORDER_NO_MODEL_ORDER),
  (LayeredOptions.CONSIDER_MODEL_ORDER_COMPONENTS.id, propertyDefault LayeredOptions.CONSIDER_MODEL_ORDER_COMPONENTS),
  (LayeredOptions.CONSIDER_MODEL_ORDER_PORT_MODEL_ORDER.id, propertyDefault LayeredOptions.CONSIDER_MODEL_ORDER_PORT_MODEL_ORDER),
  (LayeredOptions.GROUP_MODEL_ORDER_CYCLE_BREAKING_ID.id, propertyDefault LayeredOptions.GROUP_MODEL_ORDER_CYCLE_BREAKING_ID),
  (LayeredOptions.GROUP_MODEL_ORDER_CROSSING_MINIMIZATION_ID.id, propertyDefault LayeredOptions.GROUP_MODEL_ORDER_CROSSING_MINIMIZATION_ID),
  (LayeredOptions.GROUP_MODEL_ORDER_COMPONENT_GROUP_ID.id, propertyDefault LayeredOptions.GROUP_MODEL_ORDER_COMPONENT_GROUP_ID),
  (LayeredOptions.GROUP_MODEL_ORDER_CB_GROUP_ORDER_STRATEGY.id, propertyDefault LayeredOptions.GROUP_MODEL_ORDER_CB_GROUP_ORDER_STRATEGY),
  (LayeredOptions.GROUP_MODEL_ORDER_CM_GROUP_ORDER_STRATEGY.id, propertyDefault LayeredOptions.GROUP_MODEL_ORDER_CM_GROUP_ORDER_STRATEGY),
  (LayeredOptions.GROUP_MODEL_ORDER_CM_ENFORCED_GROUP_ORDERS.id, propertyDefault LayeredOptions.GROUP_MODEL_ORDER_CM_ENFORCED_GROUP_ORDERS),
  (LayeredOptions.GROUP_MODEL_ORDER_CB_PREFERRED_SOURCE_ID.id, propertyDefault LayeredOptions.GROUP_MODEL_ORDER_CB_PREFERRED_SOURCE_ID),
  (LayeredOptions.GROUP_MODEL_ORDER_CB_PREFERRED_TARGET_ID.id, propertyDefault LayeredOptions.GROUP_MODEL_ORDER_CB_PREFERRED_TARGET_ID),
  (LayeredOptions.GENERATE_POSITION_AND_LAYER_IDS.id, propertyDefault LayeredOptions.GENERATE_POSITION_AND_LAYER_IDS)]

/-- `register_option_supports`: adds every entry of `optionSupports` to the layered algorithm. -/
def registerOptionSupports (r : Registry) : Registry :=
  optionSupports.foldl (fun r (optionId, default) =>
    r.addOptionSupport LayeredOptions.ALGORITHM_ID optionId default) r

/-! ### Algorithm entry -/

/-- The `org.eclipse.elk.layered` algorithm entry ("ELK Layered"), exactly as elk-rs
`register_core_algorithms` creates it: category `org.eclipse.elk.layered`, defining bundle
`org.eclipse.elk.alg.layered`, preview image `images/layered_layout.png`, the supported graph
features `SELF_LOOPS, INSIDE_SELF_LOOPS, MULTI_EDGES, EDGE_LABELS, PORTS, COMPOUND, CLUSTERS`
and 28 known options with their defaults (the option supports are added on top by
`registerOptionSupports`). -/
def algorithmData : LayoutAlgorithmData :=
  let d : LayoutAlgorithmData :=
    { id := LayeredOptions.ALGORITHM_ID
      name := "ELK Layered"
      description := "Layer-based algorithm provided by the Eclipse Layout Kernel. Arranges as many edges as possible into one direction by placing nodes into subsequent layers. This implementation supports different routing styles (straight, orthogonal, splines); if orthogonal routing is selected, arbitrary port constraints are respected, thus enabling the layout of block diagrams such as actor-oriented models or circuit schematics. Furthermore, full layout of compound graphs with cross-hierarchy edges is supported when the respective option is activated on the top level."
      categoryId := some "org.eclipse.elk.layered"
      definingBundleId := some "org.eclipse.elk.alg.layered"
      previewImagePath := some "images/layered_layout.png" }
  let d := d.addSupportedFeature .selfLoops
    |>.addSupportedFeature .insideSelfLoops
    |>.addSupportedFeature .multiEdges
    |>.addSupportedFeature .edgeLabels
    |>.addSupportedFeature .ports
    |>.addSupportedFeature .compound
    |>.addSupportedFeature .clusters
  d.addKnownOptionDefault CoreOptions.SPACING_COMMENT_COMMENT.id none
    |>.addKnownOptionDefault CoreOptions.SPACING_COMMENT_NODE.id none
    |>.addKnownOptionDefault CoreOptions.SPACING_COMPONENT_COMPONENT.id none
    |>.addKnownOptionDefault CoreOptions.SPACING_EDGE_EDGE.id none
    |>.addKnownOptionDefault CoreOptions.SPACING_EDGE_LABEL.id none
    |>.addKnownOptionDefault CoreOptions.SPACING_EDGE_NODE.id none
    |>.addKnownOptionDefault CoreOptions.SPACING_LABEL_LABEL.id none
    |>.addKnownOptionDefault CoreOptions.SPACING_LABEL_PORT_HORIZONTAL.id none
    |>.addKnownOptionDefault CoreOptions.SPACING_LABEL_PORT_VERTICAL.id none
    |>.addKnownOptionDefault CoreOptions.SPACING_LABEL_NODE.id none
    |>.addKnownOptionDefault CoreOptions.SPACING_NODE_NODE.id none
    |>.addKnownOptionDefault CoreOptions.SPACING_NODE_SELF_LOOP.id none
    |>.addKnownOptionDefault CoreOptions.SPACING_PORT_PORT.id none
    |>.addKnownOptionDefault CoreOptions.SPACING_INDIVIDUAL.id none
    |>.addKnownOptionDefault CoreOptions.PRIORITY.id (some (.int 0))
    |>.addKnownOptionDefault CoreOptions.SEPARATE_CONNECTED_COMPONENTS.id (some (.bool true))
    |>.addKnownOptionDefault CoreOptions.PORT_ALIGNMENT_DEFAULT.id
      (some (PropCodec.enc PortAlignment.justified))
    |>.addKnownOptionDefault CoreOptions.TOPDOWN_LAYOUT.id none
    |>.addKnownOptionDefault CoreOptions.TOPDOWN_SCALE_FACTOR.id none
    |>.addKnownOptionDefault CoreOptions.TOPDOWN_HIERARCHICAL_NODE_WIDTH.id none
    |>.addKnownOptionDefault CoreOptions.TOPDOWN_HIERARCHICAL_NODE_ASPECT_RATIO.id none
    |>.addKnownOptionDefault CoreOptions.TOPDOWN_NODE_TYPE.id
      (some (PropCodec.enc TopdownNodeTypes.hierarchicalNode))
    |>.addKnownOptionDefault CoreOptions.PADDING.id (some (PropCodec.enc (ElkPadding.ofAny 12.0)))
    |>.addKnownOptionDefault CoreOptions.EDGE_ROUTING.id
      (some (PropCodec.enc EdgeRouting.orthogonal))
    |>.addKnownOptionDefault CoreOptions.PORT_BORDER_OFFSET.id (some (.double 0.0))
    |>.addKnownOptionDefault CoreOptions.RANDOM_SEED.id (some (.int 1))
    |>.addKnownOptionDefault CoreOptions.ASPECT_RATIO.id (some (.double 1.6))
    |>.addKnownOptionDefault CoreOptions.NO_LAYOUT.id none

/-- `registerAlgorithm`: registers `algorithmData`. -/
def registerAlgorithm (r : Registry) : Registry := r.registerAlgorithm algorithmData

end LayeredMetaDataProvider

namespace LayeredMetaDataProvider

/-- `ILayoutMetaDataProvider.apply` of `LayeredMetaDataProvider` (see the module doc for the
order of the contributions). -/
def metaDataProvider : LayoutMetaDataProvider where
  apply r :=
    let r := registerAlgorithm r
    let r := registerSpacingOptions r
    let r := registerPriorityOptions r
    let r := registerWrappingOptions r
    let r := registerLayerUnzippingOptions r
    let r := registerCycleBreakingOptions r
    let r := registerLayeringOptions r
    let r := registerCrossingMinimizationOptions r
    let r := registerNodePlacementOptions r
    let r := registerEdgeRoutingOptions r
    let r := registerCompactionOptions r
    let r := registerHighDegreeOptions r
    let r := registerMiscOptions r
    let r := registerEdgeLabelOptions r
    let r := registerConsiderModelOrderOptions r
    registerOptionSupports r

/-- `LayoutMetaDataService.registerLayoutMetaDataProvider(new LayeredMetaDataProvider())`:
registers the layered metadata with the global service. Not run at module initialisation. -/
def register : IO Unit := LayoutMetaDataService.registerLayoutMetaDataProvider metaDataProvider

end LayeredMetaDataProvider

end Elk.Alg.Layered.Options
