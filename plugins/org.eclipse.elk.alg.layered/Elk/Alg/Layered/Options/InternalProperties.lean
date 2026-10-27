import Elk.Core.Options
import Elk.Core.Util.Random
import Elk.Alg.Layered.Graph.Ids
import Elk.Alg.Layered.Options.PortType
import Elk.Alg.Layered.Options.EdgeConstraint
import Elk.Alg.Layered.Options.InLayerConstraint
import Elk.Alg.Layered.Options.GraphProperties
import Elk.Alg.Layered.Compound.CrossHierarchyEdge
import Elk.Alg.Layered.Options.Spacings
/-!
# `org.eclipse.elk.alg.layered.options.InternalProperties`

Java stores these algorithm-internal values in the elements' property maps; the Lean
port keeps them as **typed fields** of per-element `…Internals` structures (see
`PORTING.md` §15). Every field documents the Java constant it replaces and its Java
default; `Option` fields are properties without a default (Java `null`).

Conversion rules for the processors: `x.getProperty(InternalProperties.FOO)` →
`x.internal.foo`; `x.setProperty(InternalProperties.FOO, v)` → `{ x with internal.foo := v }`.
Object-valued properties reference arena ids. Properties whose value types are defined
with later packages (`SELF_LOOP_HOLDER`, `BREAKING_POINT_INFO`, `END_LABELS`,
`SPLINE_ROUTE_START`, `SPACINGS`) are added to these structures when those packages are
ported. `PROCESSORS` is not stored on the graph: `ElkLayered` keeps the processor lists.
-/
namespace Elk.Alg.Layered.Options

open Elk.Graph Elk.Core.Math Elk.Core.Options Elk.Core.Util Elk.Alg.Layered.Graph Elk.Alg.Layered.Compound

/-- `InternalProperties.ORIGIN`: the object a layered element was created from (ElkGraph
element or, for compound dummies, another layered element). -/
inductive Origin where
  | elkNode (id : Elk.Graph.NodeId)
  | elkPort (id : Elk.Graph.PortId)
  | elkEdge (id : Elk.Graph.EdgeId)
  | elkLabel (id : Elk.Graph.LabelId)
  | lGraph (id : LGraphId)
  | lNode (id : LNodeId)
  | lPort (id : LPortId)
  | lEdge (id : LEdgeId)
  | lLabel (id : LLabelId)
  deriving BEq, Repr, Inhabited

/-- Internal properties set on `LGraph`s. -/
structure LGraphInternals where
  /-- `ORIGIN`: the `ElkNode` the graph was imported from. -/
  origin : Option Origin := none
  /-- `GRAPH_PROPERTIES` (`graphProperties`, default empty set). -/
  graphProperties : EnumSet GraphProperties := EnumSet.empty
  /-- `RANDOM` (`random`). -/
  random : Option Random := none
  /-- `CYCLIC` (`cyclic`, `false`). -/
  cyclic : Bool := false
  /-- `EXT_PORT_REPLACED_DUMMIES` (`externalPortReplacedDummies`; Java `null` = empty). -/
  extPortReplacedDummies : Array LNodeId := #[]
  /-- `EXT_PORT_CONNECTIONS` (`externalPortConnections`, default empty set). -/
  extPortConnections : EnumSet PortSide := EnumSet.empty
  /-- `MAX_MODEL_ORDER_NODES` (`modelOrder.maximum`, `0`). -/
  maxModelOrderNodes : Int := 0
  /-- `CB_NUM_MODEL_ORDER_GROUPS` (`modelOrderGroups.cb.number`, `0`). -/
  cbNumModelOrderGroups : Int := 0
  /-- `FIRST_TRY_WITH_INITIAL_ORDER` (`firstTryWithInitialOrder`, `false`). -/
  firstTryWithInitialOrder : Bool := false
  /-- `SECOND_TRY_WITH_INITIAL_ORDER` (`secondTryWithInitialOrder`, `false`). -/
  secondTryWithInitialOrder : Bool := false
  /-- `HIDDEN_NODES` (`layerConstraints.hiddenNodes`; Java `null` = empty). -/
  hiddenNodes : Array LNodeId := #[]
  /-- `IN_LAYER_SUCCESSOR_CONSTRAINTS_BETWEEN_NON_DUMMIES` (`false`). -/
  inLayerSuccessorConstraintsBetweenNonDummies : Bool := false
  /-- `CROSS_HIERARCHY_MAP` (`crossHierarchyMap`): original edge → dummy edges, insertion order. -/
  crossHierarchyMap : Array (LEdgeId × Array CrossHierarchyEdge) := #[]
  /-- `SPACINGS` (`spacings`). -/
  spacings : Option Spacings := none
  deriving Inhabited

/-- Internal properties set on `LNode`s. -/
structure LNodeInternals where
  /-- `ORIGIN`. -/
  origin : Option Origin := none
  /-- `COMPOUND_NODE` (`compoundNode`, `false`). -/
  compoundNode : Bool := false
  /-- `ORIGINAL_DUMMY_NODE_POSITION` (`originalDummyNodePosition`). -/
  originalDummyNodePosition : Option Float := none
  /-- `REPRESENTED_LABELS` (`representedLabels`; Java `null` = empty). -/
  representedLabels : Array LLabelId := #[]
  /-- `EDGE_CONSTRAINT` (`edgeConstraint`, `NONE`). -/
  edgeConstraint : EdgeConstraint := .none
  /-- `IN_LAYER_LAYOUT_UNIT` (`inLayerLayoutUnit`). -/
  inLayerLayoutUnit : Option LNodeId := none
  /-- `IN_LAYER_CONSTRAINT` (`inLayerConstraint`, `NONE`). -/
  inLayerConstraint : InLayerConstraint := .none
  /-- `IN_LAYER_SUCCESSOR_CONSTRAINTS` (`inLayerSuccessorConstraint`, default empty list). -/
  inLayerSuccessorConstraints : Array LNodeId := #[]
  /-- `EXT_PORT_SIDE` (`externalPortSide`, `UNDEFINED`). -/
  extPortSide : PortSide := .undefined
  /-- `EXT_PORT_SIZE` (`externalPortSize`, `(0,0)`). -/
  extPortSize : KVector := {}
  /-- `EXT_PORT_REPLACED_DUMMY` (`externalPortReplacedDummy`). -/
  extPortReplacedDummy : Option LNodeId := none
  /-- `PORT_RATIO_OR_POSITION` (`portRatioOrPosition`, `0.0`). -/
  portRatioOrPosition : Float := 0.0
  /-- `BARYCENTER_ASSOCIATES` (`barycenterAssociates`; Java `null` = empty). -/
  barycenterAssociates : Array LNodeId := #[]
  /-- `TOP_COMMENTS` (`TopSideComments`; Java `null` = empty). -/
  topComments : Array LNodeId := #[]
  /-- `BOTTOM_COMMENTS` (`BottomSideComments`; Java `null` = empty). -/
  bottomComments : Array LNodeId := #[]
  /-- `COMMENT_CONN_PORT` (`CommentConnectionPort`). -/
  commentConnPort : Option LPortId := none
  /-- `LONG_EDGE_SOURCE` (`longEdgeSource`). -/
  longEdgeSource : Option LPortId := none
  /-- `LONG_EDGE_TARGET` (`longEdgeTarget`). -/
  longEdgeTarget : Option LPortId := none
  /-- `LONG_EDGE_HAS_LABEL_DUMMIES` (`false`). -/
  longEdgeHasLabelDummies : Bool := false
  /-- `LONG_EDGE_BEFORE_LABEL_DUMMY` (`false`). -/
  longEdgeBeforeLabelDummy : Bool := false
  /-- `MODEL_ORDER` (`modelOrder`). -/
  modelOrder : Option Int := none
  /-- `TARJAN_LOWLINK` (`tarjan.lowlink`, `Integer.MAX_VALUE`). -/
  tarjanLowlink : Int := 2147483647
  /-- `TARJAN_ID` (`tarjan.id`, `-1`). -/
  tarjanId : Int := -1
  /-- `TARJAN_ON_STACK` (`tarjan.onstack`, `false`). -/
  tarjanOnStack : Bool := false
  /-- `IS_PART_OF_CYCLE` (`partOfCycle`, `false`). -/
  isPartOfCycle : Bool := false
  /-- `WEIGHT` (`medianHeuristic.weight`). -/
  weight : Option Float := none
  /-- `ORIGINAL_PORT_CONSTRAINTS` (`originalPortConstraints`). -/
  originalPortConstraints : Option PortConstraints := none
  /-- `PARTITION_DUMMY` (`partitionDummy`, `false`). -/
  partitionDummy : Bool := false
  /-- `LABEL_SIDE` (`labelSide`, `UNKNOWN`) as set on label dummy nodes. -/
  labelSide : LabelSide := .unknown
  deriving Inhabited

/-- Internal properties set on `LPort`s. -/
structure LPortInternals where
  /-- `ORIGIN`. -/
  origin : Option Origin := none
  /-- `INSIDE_CONNECTIONS` (`insideConnections`, `false`). -/
  insideConnections : Bool := false
  /-- `PORT_DUMMY` (`portDummy`). -/
  portDummy : Option LNodeId := none
  /-- `INPUT_COLLECT` (`inputCollect`, `false`). -/
  inputCollect : Bool := false
  /-- `OUTPUT_COLLECT` (`outputCollect`, `false`). -/
  outputCollect : Bool := false
  /-- `PORT_RATIO_OR_POSITION` (`portRatioOrPosition`, `0.0`). -/
  portRatioOrPosition : Float := 0.0
  /-- `LONG_EDGE_TARGET_NODE` (`longEdgeTargetNode`). -/
  longEdgeTargetNode : Option LNodeId := none
  /-- `TARGET_NODE_MODEL_ORDER` (`targetNode.modelOrder`), cached map node → model order. -/
  targetNodeModelOrder : Option (Array (LNodeId × Int)) := none
  /-- `MAX_EDGE_THICKNESS` (`maxEdgeThickness`, `0.0`). -/
  maxEdgeThickness : Float := 0.0
  /-- `MODEL_ORDER` (`modelOrder`). -/
  modelOrder : Option Int := none
  deriving Inhabited

/-- Internal properties set on `LEdge`s. -/
structure LEdgeInternals where
  /-- `ORIGIN`. -/
  origin : Option Origin := none
  /-- `REVERSED` (`reversed`, `false`). -/
  reversed : Bool := false
  /-- `TARGET_OFFSET` (`targetOffset`). -/
  targetOffset : Option KVector := none
  /-- `COORDINATE_SYSTEM_ORIGIN` (`coordinateOrigin`). -/
  coordinateSystemOrigin : Option LGraphId := none
  /-- `ORIGINAL_OPPOSITE_PORT` (`layerConstraints.opposidePort`). -/
  originalOppositePort : Option LPortId := none
  /-- `PARTITION_DUMMY` (`partitionDummy`, `false`). -/
  partitionDummy : Bool := false
  /-- `MODEL_ORDER` (`modelOrder`). -/
  modelOrder : Option Int := none
  /-- `SPLINE_SURVIVING_EDGE` (`splines.survivingEdge`). -/
  splineSurvivingEdge : Option LEdgeId := none
  /-- `SPLINE_EDGE_CHAIN` (`splines.edgeChain`; Java `null` = empty). -/
  splineEdgeChain : Array LEdgeId := #[]
  /-- `SPLINE_NS_PORT_Y_COORD` (`splines.nsPortY`). -/
  splineNsPortYCoord : Option Float := none
  /-- `IS_PART_OF_CYCLE` (`partOfCycle`, `false`) as reset on edges by `Tarjan.resetTarjan`. -/
  isPartOfCycle : Bool := false
  deriving Inhabited

/-- Internal properties set on `LLabel`s. -/
structure LLabelInternals where
  /-- `ORIGIN`. -/
  origin : Option Origin := none
  /-- `ORIGINAL_LABEL_EDGE` (`originalLabelEdge`). -/
  originalLabelEdge : Option LEdgeId := none
  /-- `END_LABEL_EDGE` (`endLabel.origin`). -/
  endLabelEdge : Option LEdgeId := none
  /-- `LABEL_SIDE` (`labelSide`, `UNKNOWN`). -/
  labelSide : LabelSide := .unknown
  deriving Inhabited

end Elk.Alg.Layered.Options
