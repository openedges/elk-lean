import Tests.Framework
import Elk.Alg.Layered
import Elk.Alg.Layered.Intermediate.ConstraintProcessors
/-!
Tests of the layered intermediate processors for edge/layer/in-layer constraints, partitions, comment
boxes, high-degree nodes and node promotion. The elk-rs tests under `tests/intermediate/` build `LGraph`s by
hand and run one processor; they are ported 1:1 (Rust test names in the check names). Pipeline-driven tests
(`node_promotion_test.rs`, `partition_test.rs`) are ported as their assertions on hand-built layered
graphs. All other expected values are derived by hand ("hand: …").
-/
namespace Tests.Layered.IntermediateConstraints

open Tests Elk.Graph Elk.Core.Math Elk.Core.Options Elk.Core.Util Elk.Alg.Layered Elk.Alg.Layered.Graph
  Elk.Alg.Layered.Options Elk.Alg.Layered.Intermediate

/-- Runs a processor with a null monitor. -/
def runProc (p : LayeredProcessor) (g : LGraphId) : LayeredM Unit := p.process g ProgressMonitor.null

/-- `add_layerless_node(graph, constraint)`. -/
def addLayerless (g : LGraphId) (constraint : LayerConstraint := .none) (n : LNode := {}) : LayeredM LNodeId := do
  let node ← LayeredM.createNode g n
  if constraint != .none then
    LayeredM.setNodeProp node LayeredOptions.LAYERING_LAYER_CONSTRAINT constraint
  LayeredM.modifyGraph g fun x => { x with layerlessNodes := x.layerlessNodes.push node }
  return node

/-- `add_port(node)` (optionally on a side). -/
def addPort (node : LNodeId) (side : PortSide := .undefined) : LayeredM LPortId := do
  let p ← LayeredM.createPort
  if side != .undefined then LayeredM.modifyPort p fun x => x.setSide side
  LayeredM.setPortNode p (some node)
  return p

/-- `connect(source, target)`. -/
def connect (s t : LPortId) : LayeredM LEdgeId := do
  let e ← LayeredM.createEdge
  LayeredM.setEdgeSource e (some s)
  LayeredM.setEdgeTarget e (some t)
  return e

/-- An edge between fresh ports of two nodes. -/
def connectNodes (s t : LNodeId) : LayeredM LEdgeId := do
  connect (← addPort s) (← addPort t)

/-- `new_graph_with_layers(count)`. -/
def graphWithLayers (count : Nat) : LayeredM (LGraphId × Array LayerId) := do
  let g ← LayeredM.createGraph
  let mut layers : Array LayerId := #[]
  for _ in [0:count] do
    let l ← LayeredM.createLayer g
    layers := layers.push l
  let ls := layers
  LayeredM.modifyGraph g fun x => { x with layers := ls }
  return (g, layers)

/-- `add_node(graph, layer, constraint)`: a node appended to a layer. -/
def addToLayer (g : LGraphId) (layer : LayerId) (constraint : LayerConstraint := .none) (n : LNode := {}) :
    LayeredM LNodeId := do
  let node ← LayeredM.createNode g n
  if constraint != .none then
    LayeredM.setNodeProp node LayeredOptions.LAYERING_LAYER_CONSTRAINT constraint
  LayeredM.setNodeLayer node (some layer)
  return node

/-- Sets `MODEL_ORDER`. -/
def setModelOrder (n : LNodeId) (mo : Int) : LayeredM Unit :=
  LayeredM.modifyNode n fun x => { x with internal := { x.internal with modelOrder := some mo } }

/-- Index of a node's layer in its graph. -/
def layerIndexOf (a : LGraphArena) (n : LNodeId) : Option Nat := (a.node n).layer.bind a.layerIndex

/-- Nodes of the graph's layers. -/
def layerNodes (a : LGraphArena) (g : LGraphId) : Array (Array LNodeId) := a.graphToNodeArray g

/-- Source and target node of an edge. -/
def endsOf (a : LGraphArena) (e : LEdgeId) : Option LNodeId × Option LNodeId :=
  ((a.edge e).source.bind (fun p => (a.port p).owner), (a.edge e).target.bind (fun p => (a.port p).owner))

/-- Port of `assert_layering_invariants` (`node_promotion_test.rs`): no layerless nodes, no empty layers and
no non-reversed edge pointing to a previous layer. -/
def layeringInvariantsHold (a : LGraphArena) (g : LGraphId) : Bool := Id.run do
  let gr := a.graph g
  if gr.layers.isEmpty then return true
  if !gr.layerlessNodes.isEmpty then return false
  for l in gr.layers do
    if (a.layer l).nodes.isEmpty then return false
  for l in gr.layers do
    let sourceIndex := (a.layerIndex l).getD 0
    for n in (a.layer l).nodes do
      for e in a.nodeOutgoingEdges n do
        if (a.edge e).internal.reversed then continue
        let targetIndex := ((endsOf a e).2.bind (layerIndexOf a)).getD sourceIndex
        if sourceIndex > targetIndex then return false
  return true

/-! ## EdgeAndLayerConstraintEdgeReverser -/

def edgeReverserTests : Suite := suite "layered.intermediate.EdgeAndLayerConstraintEdgeReverser" do
  -- reverser_makes_first_node_outgoing_only
  let ((first, edge), a) ← LayeredM.run (do
      let g ← LayeredM.createGraph
      let source ← addLayerless g
      let first ← addLayerless g .first
      let e ← connect (← addPort source) (← addPort first)
      runProc EdgeAndLayerConstraintEdgeReverser.processor g
      return (first, e))
  checkEq "reverser_makes_first_node_outgoing_only: incoming empty" (a.nodeIncomingEdges first).size 0
  checkEq "reverser_makes_first_node_outgoing_only: outgoing = [edge]" (a.nodeOutgoingEdges first) #[edge]
  check "reverser_makes_first_node_outgoing_only: REVERSED" (a.edge edge).internal.reversed
  check "hand: FIRST node gets EDGE_CONSTRAINT OUTGOING_ONLY" ((a.node first).internal.edgeConstraint == .outgoingOnly)
  -- reverser_makes_last_node_incoming_only
  let ((last, edge), a) ← LayeredM.run (do
      let g ← LayeredM.createGraph
      let last ← addLayerless g .last
      let target ← addLayerless g
      let e ← connect (← addPort last) (← addPort target)
      runProc EdgeAndLayerConstraintEdgeReverser.processor g
      return (last, e))
  checkEq "reverser_makes_last_node_incoming_only: outgoing empty" (a.nodeOutgoingEdges last).size 0
  checkEq "reverser_makes_last_node_incoming_only: incoming = [edge]" (a.nodeIncomingEdges last) #[edge]
  check "reverser_makes_last_node_incoming_only: REVERSED" (a.edge edge).internal.reversed
  check "hand: Java parity, LAST node also gets OUTGOING_ONLY" ((a.node last).internal.edgeConstraint == .outgoingOnly)
  -- reverser_keeps_first_separate_to_first_edge_direction
  let ((first, edge), a) ← LayeredM.run (do
      let g ← LayeredM.createGraph
      let firstSeparate ← addLayerless g .firstSeparate
      let first ← addLayerless g .first
      let e ← connect (← addPort firstSeparate) (← addPort first)
      runProc EdgeAndLayerConstraintEdgeReverser.processor g
      return (first, e))
  checkEq "reverser_keeps_first_separate_to_first_edge_direction: incoming = [edge]" (a.nodeIncomingEdges first) #[edge]
  checkEq "reverser_keeps_first_separate_to_first_edge_direction: outgoing empty" (a.nodeOutgoingEdges first).size 0
  check "reverser_keeps_first_separate_to_first_edge_direction: not REVERSED" (!(a.edge edge).internal.reversed)
  -- hand: LAST → label dummy and LAST → LAST_SEPARATE edges stay; LAST → normal is reversed
  let ((toLabel, toLastSep, toNormal), a) ← LayeredM.run (do
      let g ← LayeredM.createGraph
      let last ← addLayerless g .last
      let label ← addLayerless g .none { type := .label }
      let lastSep ← addLayerless g .lastSeparate
      let normal ← addLayerless g
      let e1 ← connectNodes last label
      let e2 ← connectNodes last lastSep
      let e3 ← connectNodes last normal
      runProc EdgeAndLayerConstraintEdgeReverser.processor g
      return (e1, e2, e3))
  check "hand: LAST → label dummy not reversed" (!(a.edge toLabel).internal.reversed)
  check "hand: LAST → LAST_SEPARATE not reversed" (!(a.edge toLastSep).internal.reversed)
  check "hand: LAST → normal reversed" (a.edge toNormal).internal.reversed
  -- hand: feedback node (FIXED_SIDE, east port with an incoming edge, west port with an outgoing edge)
  let ((n, e1, e2), a) ← LayeredM.run (do
      let g ← LayeredM.createGraph
      let x ← addLayerless g
      let n ← addLayerless g
      let y ← addLayerless g
      LayeredM.setNodeProp n LayeredOptions.PORT_CONSTRAINTS PortConstraints.fixedSide
      let east ← addPort n .east
      let west ← addPort n .west
      let e1 ← connect (← addPort x) east
      let e2 ← connect west (← addPort y)
      runProc EdgeAndLayerConstraintEdgeReverser.processor g
      return (n, e1, e2))
  check "hand: feedback node, both edges reversed" ((a.edge e1).internal.reversed && (a.edge e2).internal.reversed)
  checkEq "hand: feedback node, reversed edge now leaves the node" (endsOf a e1).1 (some n)
  -- hand: same, but the incoming edge comes from a FIRST node → no reversal
  let ((e1, e2), a) ← LayeredM.run (do
      let g ← LayeredM.createGraph
      let x ← addLayerless g .first
      let n ← addLayerless g
      let y ← addLayerless g
      LayeredM.setNodeProp n LayeredOptions.PORT_CONSTRAINTS PortConstraints.fixedSide
      let east ← addPort n .east
      let west ← addPort n .west
      let e1 ← connect (← addPort x) east
      let e2 ← connect west (← addPort y)
      runProc EdgeAndLayerConstraintEdgeReverser.processor g
      return (e1, e2))
  check "hand: feedback node next to a FIRST node is kept" (!(a.edge e1).internal.reversed && !(a.edge e2).internal.reversed)

/-! ## LayerConstraintPreprocessor / LayerConstraintPostprocessor -/

def layerConstraintPreprocessorTests : Suite := suite "layered.intermediate.LayerConstraintPreprocessor" do
  -- layer_constraint_preprocessor_hides_first_separate_and_remembers_opposite_port
  let ((g, hidden, opposite, oppositePort, edge), a) ← LayeredM.run (do
      let g ← LayeredM.createGraph
      let hidden ← addLayerless g .firstSeparate
      let opposite ← addLayerless g
      let hiddenPort ← addPort hidden
      let oppositePort ← addPort opposite
      let e ← connect hiddenPort oppositePort
      runProc LayerConstraintPreprocessor.processor g
      return (g, hidden, opposite, oppositePort, e))
  checkEq "hides_first_separate: layerless = [opposite]" (a.graph g).layerlessNodes #[opposite]
  checkEq "hides_first_separate: HIDDEN_NODES = [hidden]" (a.graph g).internal.hiddenNodes #[hidden]
  checkNone "hides_first_separate: edge target detached" (a.edge edge).target
  checkEq "hides_first_separate: ORIGINAL_OPPOSITE_PORT" (a.edge edge).internal.originalOppositePort (some oppositePort)
  checkEq "hides_first_separate: opposite constrained to FIRST"
    ((a.node opposite).props.getD LayeredOptions.LAYERING_LAYER_CONSTRAINT .none) LayerConstraint.first
  checkEq "hand: opposite port loses its edge" (a.port oppositePort).degree 0
  -- layer_constraint_preprocessor_does_not_force_layer_when_connected_to_both_hidden_sides
  let (opposite, a) ← LayeredM.run (do
      let g ← LayeredM.createGraph
      let firstHidden ← addLayerless g .firstSeparate
      let lastHidden ← addLayerless g .lastSeparate
      let opposite ← addLayerless g
      let _ ← connect (← addPort firstHidden) (← addPort opposite)
      let _ ← connect (← addPort opposite) (← addPort lastHidden)
      runProc LayerConstraintPreprocessor.processor g
      return opposite)
  check "does_not_force_layer_when_connected_to_both_hidden_sides"
    (!(a.node opposite).props.has LayeredOptions.LAYERING_LAYER_CONSTRAINT)
  -- layer_constraint_processor_hides_first_separate_nodes (layer_constraint_processor_test.rs)
  let ((g, hidden), a) ← LayeredM.run (do
      let (g, layers) ← graphWithLayers 1
      let _ ← addToLayer g layers[0]!
      let hidden ← addLayerless g .firstSeparate
      runProc LayerConstraintPreprocessor.processor g
      return (g, hidden))
  check "layer_constraint_processor_hides_first_separate_nodes" ((a.graph g).internal.hiddenNodes.contains hidden)
  -- hand: LAST_SEPARATE with an incoming edge: the source end is detached, the opposite becomes LAST;
  -- an opposite node that keeps another edge gets no constraint
  let ((g, opposite, keeper, oppositePort, edge), a) ← LayeredM.run (do
      let g ← LayeredM.createGraph
      let opposite ← addLayerless g
      let keeper ← addLayerless g
      let other ← addLayerless g
      let hidden ← addLayerless g .lastSeparate
      let oppositePort ← addPort opposite
      let e ← connect oppositePort (← addPort hidden)
      let _ ← connect (← addPort keeper) (← addPort hidden)
      let _ ← connectNodes keeper other
      runProc LayerConstraintPreprocessor.processor g
      return (g, opposite, keeper, oppositePort, e))
  checkEq "hand: LAST_SEPARATE hidden, three layerless nodes left" (a.graph g).layerlessNodes.size 3
  checkNone "hand: incoming hidden edge loses its source" (a.edge edge).source
  checkEq "hand: ORIGINAL_OPPOSITE_PORT = source port" (a.edge edge).internal.originalOppositePort (some oppositePort)
  checkEq "hand: isolated opposite becomes LAST"
    ((a.node opposite).props.getD LayeredOptions.LAYERING_LAYER_CONSTRAINT .none) LayerConstraint.last
  check "hand: opposite with remaining edges stays unconstrained"
    (!(a.node keeper).props.has LayeredOptions.LAYERING_LAYER_CONSTRAINT)
  -- hand: FIRST_SEPARATE with an incoming edge from a normal node is rejected
  let (g, a0) ← LayeredM.run (do
      let g ← LayeredM.createGraph
      let hidden ← addLayerless g .firstSeparate
      let n ← addLayerless g
      let _ ← connectNodes n hidden
      return g)
  checkThrows "hand: FIRST_SEPARATE with incoming edge throws"
    (do let _ ← LayeredM.run (runProc LayerConstraintPreprocessor.processor g) a0)
  -- hand: an external-port-to-external-port edge is acceptable
  let ((g, hidden), a) ← LayeredM.run (do
      let g ← LayeredM.createGraph
      let hidden ← addLayerless g .firstSeparate { type := .externalPort }
      let n ← addLayerless g .none { type := .externalPort }
      let _ ← connectNodes n hidden
      runProc LayerConstraintPreprocessor.processor g
      return (g, hidden))
  checkEq "hand: external port dummy edge accepted, node hidden" (a.graph g).internal.hiddenNodes #[hidden]

def layerConstraintPostprocessorTests : Suite := suite "layered.intermediate.LayerConstraintPostprocessor" do
  -- layer_constraint_postprocessor_moves_first_and_last_nodes_to_outer_layers (also
  -- layer_constraint_processor_moves_first_and_last_after_postprocessing)
  let ((g, layers, firstNode, lastNode), a) ← LayeredM.run (do
      let (g, layers) ← graphWithLayers 2
      let _ ← addToLayer g layers[0]!
      let _ ← addToLayer g layers[1]!
      let firstNode ← addToLayer g layers[1]! .first
      let lastNode ← addToLayer g layers[0]! .last
      runProc LayerConstraintPostprocessor.processor g
      return (g, layers, firstNode, lastNode))
  checkEq "moves_first_and_last_nodes_to_outer_layers: FIRST in first layer" (a.node firstNode).layer (some layers[0]!)
  checkEq "moves_first_and_last_nodes_to_outer_layers: LAST in last layer" (a.node lastNode).layer (some layers[1]!)
  checkEq "hand: no label layers added" (a.graph g).layers layers
  -- layer_constraint_postprocessor_restores_hidden_nodes_and_detached_edges
  let ((g, mainLayer, hidden, oppositePort, edge), a) ← LayeredM.run (do
      let (g, layers) ← graphWithLayers 1
      let opposite ← addToLayer g layers[0]!
      let hidden ← LayeredM.createNode g
      LayeredM.setNodeProp hidden LayeredOptions.LAYERING_LAYER_CONSTRAINT LayerConstraint.firstSeparate
      let hiddenPort ← addPort hidden
      let oppositePort ← addPort opposite
      let e ← connect hiddenPort oppositePort
      LayeredM.setEdgeTarget e none
      LayeredM.modifyEdge e fun x => { x with internal := { x.internal with originalOppositePort := some oppositePort } }
      LayeredM.modifyGraph g fun x => { x with internal := { x.internal with hiddenNodes := #[hidden] } }
      runProc LayerConstraintPostprocessor.processor g
      return (g, layers[0]!, hidden, oppositePort, e))
  check "restores_hidden_nodes: hidden in first layer"
    ((a.graph g).layers[0]?.map (fun l => (a.layer l).nodes.contains hidden) |>.getD false)
  checkEq "restores_hidden_nodes: edge target restored" (a.edge edge).target (some oppositePort)
  checkEq "hand: separate layer inserted before the main layer" (a.graph g).layers.size 2
  checkEq "hand: main layer second" (a.graph g).layers[1]? (some mainLayer)
  -- hand: FIRST node fed by a label dummy: the dummy goes to a new label layer in front, the emptied layer goes
  let ((g, n0, label, first), a) ← LayeredM.run (do
      let (g, layers) ← graphWithLayers 2
      let n0 ← addToLayer g layers[0]!
      let label ← addToLayer g layers[0]! .none { type := .label }
      let first ← addToLayer g layers[1]! .first
      let _ ← connectNodes label first
      runProc LayerConstraintPostprocessor.processor g
      return (g, n0, label, first))
  checkEq "hand: label layer + first layer" (layerNodes a g) #[#[label], #[n0, first]]
  -- hand: LAST_SEPARATE hidden node goes to a new last layer
  let ((g, hidden), a) ← LayeredM.run (do
      let (g, layers) ← graphWithLayers 1
      let _ ← addToLayer g layers[0]!
      let hidden ← LayeredM.createNode g
      LayeredM.setNodeProp hidden LayeredOptions.LAYERING_LAYER_CONSTRAINT LayerConstraint.lastSeparate
      LayeredM.modifyGraph g fun x => { x with internal := { x.internal with hiddenNodes := #[hidden] } }
      runProc LayerConstraintPostprocessor.processor g
      return (g, hidden))
  checkEq "hand: LAST_SEPARATE restored into an appended layer" (layerIndexOf a hidden) (some 1)
  checkEq "hand: two layers" (a.graph g).layers.size 2
  -- hand: FIRST node with an incoming edge from a normal node is rejected
  let (g, a0) ← LayeredM.run (do
      let (g, layers) ← graphWithLayers 2
      let n ← addToLayer g layers[0]!
      let first ← addToLayer g layers[1]! .first
      let _ ← connectNodes n first
      return g)
  checkThrows "hand: FIRST with a normal predecessor throws"
    (do let _ ← LayeredM.run (runProc LayerConstraintPostprocessor.processor g) a0)

/-! ## InLayerConstraintProcessor -/

/-- `add_node_with_constraint(graph, layer, constraint)`. -/
def addWithInLayer (g : LGraphId) (layer : LayerId) (c : InLayerConstraint) : LayeredM LNodeId := do
  let n ← LayeredM.createNode g
  LayeredM.modifyNode n fun x => { x with internal := { x.internal with inLayerConstraint := c } }
  LayeredM.setNodeLayer n (some layer)
  return n

def inLayerConstraintTests : Suite := suite "layered.intermediate.InLayerConstraintProcessor" do
  -- in_layer_constraint_processor_moves_top_to_front_and_bottom_to_back
  let ((layer, ns), a) ← LayeredM.run (do
      let (g, layers) ← graphWithLayers 1
      let l := layers[0]!
      let none1 ← addWithInLayer g l .none
      let top1 ← addWithInLayer g l .top
      let none2 ← addWithInLayer g l .none
      let top2 ← addWithInLayer g l .top
      let bottom1 ← addWithInLayer g l .bottom
      let none3 ← addWithInLayer g l .none
      let bottom2 ← addWithInLayer g l .bottom
      runProc InLayerConstraintProcessor.processor g
      return (l, #[top1, top2, none1, none2, none3, bottom1, bottom2]))
  let nodes := (a.layer layer).nodes
  for i in [0:7] do
    checkEq s!"moves_top_to_front_and_bottom_to_back: position {i}" nodes[i]? ns[i]?
  checkEq "hand: node layer kept" (a.node ns[0]!).layer (some layer)
  -- in_layer_constraint_processor_keeps_order_when_constraints_are_already_grouped
  let ((layer, ns), a) ← LayeredM.run (do
      let (g, layers) ← graphWithLayers 1
      let l := layers[0]!
      let top ← addWithInLayer g l .top
      let none ← addWithInLayer g l .none
      let bottom ← addWithInLayer g l .bottom
      runProc InLayerConstraintProcessor.processor g
      return (l, #[top, none, bottom]))
  checkEq "keeps_order_when_constraints_are_already_grouped" (a.layer layer).nodes ns

/-! ## Partition processors -/

/-- A layerless node with a partition. -/
def addPartitioned (g : LGraphId) (partition : Int) : LayeredM LNodeId := do
  let n ← addLayerless g
  LayeredM.setNodeProp n CoreOptions.PARTITIONING_PARTITION partition
  return n

def partitionTests : Suite := suite "layered.intermediate.Partition" do
  -- PartitionPreprocessor (test_partition_order_non_consecutive: p3 → p1 must be reversed)
  let ((p1, e), a) ← LayeredM.run (do
      let g ← LayeredM.createGraph
      let p1 ← addPartitioned g 1
      let p3 ← addPartitioned g 3
      let e ← connectNodes p3 p1
      runProc PartitionPreprocessor.processor g
      return (p1, e))
  check "test_partition_order_non_consecutive: p3 → p1 reversed" (a.edge e).internal.reversed
  checkEq "hand: reversed edge now starts at p1" (endsOf a e).1 (some p1)
  checkEq "hand: PRIORITY_DIRECTION = 1000" ((a.edge e).props.get LayeredOptions.PRIORITY_DIRECTION) (some 1000)
  -- hand: p2 → u → p0 (u unpartitioned) must be reversed via the BFS; the user priority 5 is added
  let ((eToU, eFromU, eForward), a) ← LayeredM.run (do
      let g ← LayeredM.createGraph
      let p0 ← addPartitioned g 0
      let p2 ← addPartitioned g 2
      let u ← addLayerless g
      let p5 ← addPartitioned g 5
      let eToU ← connectNodes p2 u
      LayeredM.setEdgeProp eToU LayeredOptions.PRIORITY_DIRECTION 5
      let eFromU ← connectNodes u p0
      let eForward ← connectNodes p0 p5
      runProc PartitionPreprocessor.processor g
      return (eToU, eFromU, eForward))
  check "hand: p2 → u reversed (p0 reachable over u)" (a.edge eToU).internal.reversed
  checkEq "hand: priority 1000 + 5" ((a.edge eToU).props.get LayeredOptions.PRIORITY_DIRECTION) (some 1005)
  check "hand: u → p0 kept (u is unpartitioned)" (!(a.edge eFromU).internal.reversed)
  check "hand: p0 → p5 kept" (!(a.edge eForward).internal.reversed)
  -- hand: an unpartitioned target from which no lower partition is reachable is kept
  let (e, a) ← LayeredM.run (do
      let g ← LayeredM.createGraph
      let _ ← addPartitioned g 0
      let p2 ← addPartitioned g 2
      let u ← addLayerless g
      let e ← connectNodes p2 u
      runProc PartitionPreprocessor.processor g
      return e)
  check "hand: p2 → u kept (no lower partition reachable)" (!(a.edge e).internal.reversed)
  -- PartitionMidprocessor + PartitionPostprocessor (partition_post_processor_test.rs `test_partition_order`)
  let ((g, left, right, aMid), a) ← LayeredM.run (do
      let g ← LayeredM.createGraph
      let left ← addPartitioned g 0
      let right ← addPartitioned g 1
      runProc PartitionMidprocessor.processor g
      let aMid ← get
      let la ← LayeredM.createLayer g
      let lb ← LayeredM.createLayer g
      LayeredM.modifyGraph g fun x => { x with layers := #[la, lb], layerlessNodes := #[] }
      LayeredM.setNodeLayer left (some la)
      LayeredM.setNodeLayer right (some lb)
      runProc PartitionPostprocessor.processor g
      return (g, left, right, aMid))
  let leftPort := (aMid.node left).ports[0]!
  let rightPort := (aMid.node right).ports[0]!
  let dummyEdge := (aMid.port leftPort).outgoingEdges[0]!
  check "hand: midprocessor adds one EAST port to the left node" ((aMid.node left).ports.size == 1 && (aMid.port leftPort).side == .east)
  check "hand: midprocessor adds one WEST port to the right node" ((aMid.node right).ports.size == 1 && (aMid.port rightPort).side == .west)
  checkEq "hand: dummy edge left → right" (endsOf aMid dummyEdge) (some left, some right)
  check "hand: dummy edge flagged PARTITION_DUMMY" (aMid.edge dummyEdge).internal.partitionDummy
  check "hand: dummy ports flagged PARTITION_DUMMY"
    (PartitionMidprocessor.portIsPartitionDummy (aMid.port leftPort) &&
      PartitionMidprocessor.portIsPartitionDummy (aMid.port rightPort))
  check "test_partition_order: partitions monotonic over layers"
    (layerNodes a g == #[#[left], #[right]])
  check "hand: postprocessor removes the dummy ports" ((a.node left).ports.isEmpty && (a.node right).ports.isEmpty)
  check "hand: dummy edge detached" ((a.edge dummyEdge).source.isNone && (a.edge dummyEdge).target.isNone)
  -- hand: partitions {0: a, b}, {2: c} (inserted 2 first), unpartitioned u: a→c, b→c
  let ((na, nb, nc, u), a) ← LayeredM.run (do
      let g ← LayeredM.createGraph
      let nc ← addPartitioned g 2
      let u ← addLayerless g
      let na ← addPartitioned g 0
      let nb ← addPartitioned g 0
      runProc PartitionMidprocessor.processor g
      return (na, nb, nc, u))
  let cIncoming := a.nodeIncomingEdges nc
  checkEq "hand: c gets one WEST port per source" (a.node nc).ports.size 2
  checkEq "hand: edges a → c, b → c in partition order" (cIncoming.map fun e => (endsOf a e).1) #[some na, some nb]
  checkEq "hand: unpartitioned node untouched" (a.node u).ports.size 0
  -- no_empty_layer_test (partition_post_processor_test.rs)
  let (g, a) ← LayeredM.run (do
      let (g, layers) ← graphWithLayers 2
      let first ← addToLayer g layers[0]!
      let second ← addToLayer g layers[1]!
      LayeredM.setNodeProp first CoreOptions.PARTITIONING_PARTITION 0
      LayeredM.setNodeProp second CoreOptions.PARTITIONING_PARTITION 1
      let fp ← addPort first .east
      let sp ← addPort second .west
      PartitionMidprocessor.setPortPartitionDummy fp
      PartitionMidprocessor.setPortPartitionDummy sp
      let e ← connect fp sp
      LayeredM.modifyEdge e fun x => { x with internal := { x.internal with partitionDummy := true } }
      runProc PartitionPostprocessor.processor g
      return g)
  check "no_empty_layer_test" ((a.graph g).layers.all fun l => !(a.layer l).nodes.isEmpty)

/-! ## ConstraintsPostprocessor -/

def constraintsPostprocessorTests : Suite := suite "layered.intermediate.ConstraintsPostprocessor" do
  -- assigns_layer_and_position_ids_only_to_normal_nodes
  let (ns, a) ← LayeredM.run (do
      let (g, layers) ← graphWithLayers 3
      let labelL0 ← addToLayer g layers[0]! .none { type := .label }
      let normalL0a ← addToLayer g layers[0]!
      let normalL0b ← addToLayer g layers[0]!
      let labelL1 ← addToLayer g layers[1]! .none { type := .label }
      let normalL2 ← addToLayer g layers[2]!
      runProc ConstraintsPostprocessor.processor g
      return #[labelL0, normalL0a, normalL0b, labelL1, normalL2])
  let ids := ns.map fun n =>
    ((a.node n).props.getD LayeredOptions.LAYERING_LAYER_ID (-1), (a.node n).props.getD LayeredOptions.CROSSING_MINIMIZATION_POSITION_ID (-1))
  checkEq "assigns_layer_and_position_ids: label in layer 0" ids[0]! ((-1 : Int), (-1 : Int))
  checkEq "assigns_layer_and_position_ids: first normal" ids[1]! ((0 : Int), (0 : Int))
  checkEq "assigns_layer_and_position_ids: second normal" ids[2]! ((0 : Int), (1 : Int))
  checkEq "assigns_layer_and_position_ids: label in layer 1" ids[3]! ((-1 : Int), (-1 : Int))
  checkEq "assigns_layer_and_position_ids: layer without normal nodes not counted" ids[4]! ((1 : Int), (0 : Int))

/-! ## Comment processors -/

/-- `add_layerless_node(graph, comment_box)`. -/
def addLayerlessComment (g : LGraphId) (commentBox : Bool) : LayeredM LNodeId := do
  let n ← addLayerless g
  if commentBox then LayeredM.setNodeProp n LayeredOptions.COMMENT_BOX true
  return n

def commentPreprocessorTests : Suite := suite "layered.intermediate.CommentPreprocessor" do
  -- comment_preprocessor_extracts_single_connection_comment
  let ((g, realNode, commentNode, realPort, edge), a) ← LayeredM.run (do
      let g ← LayeredM.createGraph
      let realNode ← addLayerlessComment g false
      let commentNode ← addLayerlessComment g true
      let realPort ← addPort realNode
      let commentPort ← addPort commentNode
      let e ← connect commentPort realPort
      LayeredM.modifyEdge e fun x => { x with bendPoints := #[⟨10.0, 20.0⟩] }
      runProc CommentPreprocessor.processor g
      return (g, realNode, commentNode, realPort, e))
  checkEq "extracts_single_connection_comment: layerless = [real]" (a.graph g).layerlessNodes #[realNode]
  checkEq "hand: no port constraints, no labels → TOP_COMMENTS" (a.node realNode).internal.topComments #[commentNode]
  checkEq "hand: BOTTOM_COMMENTS empty" (a.node realNode).internal.bottomComments.size 0
  checkEq "extracts_single_connection_comment: COMMENT_CONN_PORT" (a.node commentNode).internal.commentConnPort (some realPort)
  checkNone "extracts_single_connection_comment: edge target detached" (a.edge edge).target
  check "extracts_single_connection_comment: bend points cleared" (a.edge edge).bendPoints.isEmpty
  checkNone "hand: port without edges removed from the real node" (a.port realPort).owner
  -- comment_preprocessor_keeps_multi_connected_comment
  let ((g, commentNode), a) ← LayeredM.run (do
      let g ← LayeredM.createGraph
      let realA ← addLayerlessComment g false
      let realB ← addLayerlessComment g false
      let commentNode ← addLayerlessComment g true
      let _ ← connect (← addPort commentNode) (← addPort realA)
      let _ ← connect (← addPort commentNode) (← addPort realB)
      runProc CommentPreprocessor.processor g
      return (g, commentNode))
  check "keeps_multi_connected_comment: still layerless" ((a.graph g).layerlessNodes.contains commentNode)
  checkNone "keeps_multi_connected_comment: no COMMENT_CONN_PORT" (a.node commentNode).internal.commentConnPort
  -- hand: two comments on one node: top first, then bottom (fewer boxes there)
  let ((realNode, c1, c2), a) ← LayeredM.run (do
      let g ← LayeredM.createGraph
      let realNode ← addLayerlessComment g false
      let c1 ← addLayerlessComment g true
      let c2 ← addLayerlessComment g true
      let _ ← connectNodes c1 realNode
      let _ ← connectNodes c2 realNode
      runProc CommentPreprocessor.processor g
      return (realNode, c1, c2))
  check "hand: first comment on top, second at the bottom"
    ((a.node realNode).internal.topComments == #[c1] && (a.node realNode).internal.bottomComments == #[c2])
  -- hand: FIXED_SIDE node with a northern connection → comments only at the bottom
  let ((realNode, c1), a) ← LayeredM.run (do
      let g ← LayeredM.createGraph
      let realNode ← addLayerlessComment g false
      let other ← addLayerlessComment g false
      LayeredM.setNodeProp realNode LayeredOptions.PORT_CONSTRAINTS PortConstraints.fixedSide
      let _ ← connect (← addPort other) (← addPort realNode .north)
      let c1 ← addLayerlessComment g true
      let _ ← connect (← addPort c1) (← addPort realNode .east)
      runProc CommentPreprocessor.processor g
      return (realNode, c1))
  check "hand: northern connection → BOTTOM_COMMENTS"
    ((a.node realNode).internal.bottomComments == #[c1] && (a.node realNode).internal.topComments.isEmpty)
  -- hand: oddly connected edges of a multi-connected comment are reversed
  let ((odd, normal), a) ← LayeredM.run (do
      let g ← LayeredM.createGraph
      let c ← addLayerlessComment g true
      let x ← addLayerlessComment g false
      let y ← addLayerlessComment g false
      let z ← addLayerlessComment g false
      let cp ← addPort c
      let xp ← addPort x
      let odd ← connect cp xp
      let _ ← connect xp (← addPort z)
      let normal ← connect cp (← addPort y)
      runProc CommentPreprocessor.processor g
      return (odd, normal))
  check "hand: edge into a port with outgoing edges reversed" (a.edge odd).internal.reversed
  check "hand: edge into a plain port kept" (!(a.edge normal).internal.reversed)

/-- `add_comment_box(graph, w, h, side)`: a box node (not in a layer) with one port on `side`. -/
def addCommentBox (g : LGraphId) (w h : Float) (side : PortSide) : LayeredM (LNodeId × LPortId) := do
  let b ← LayeredM.createNode g { size := ⟨w, h⟩ }
  let p ← addPort b side
  return (b, p)

def commentPostprocessorTests : Suite := suite "layered.intermediate.CommentPostprocessor" do
  -- comment_postprocessor_reinserts_boxes_and_reconnects_edges
  let ((layer, node, boxes, nodePorts, edges), a) ← LayeredM.run (do
      let (g, layers) ← graphWithLayers 1
      LayeredM.setGraphProp g LayeredOptions.SPACING_COMMENT_COMMENT 5.0
      let node ← addToLayer g layers[0]! .none
        { position := ⟨100.0, 100.0⟩, size := ⟨60.0, 40.0⟩, margin := { top := 20.0, bottom := 30.0 } }
      let (top1, topPort1) ← addCommentBox g 20.0 10.0 .south
      let (top2, topPort2) ← addCommentBox g 10.0 8.0 .south
      let (bottom, bottomPort) ← addCommentBox g 30.0 12.0 .north
      let nodeTopPort1 ← LayeredM.createPort
      let nodeTopPort2 ← LayeredM.createPort
      let nodeBottomPort ← LayeredM.createPort
      LayeredM.modifyNode top1 fun x => { x with internal := { x.internal with commentConnPort := some nodeTopPort1 } }
      LayeredM.modifyNode top2 fun x => { x with internal := { x.internal with commentConnPort := some nodeTopPort2 } }
      LayeredM.modifyNode bottom fun x => { x with internal := { x.internal with commentConnPort := some nodeBottomPort } }
      let edgeTop1 ← LayeredM.createEdge
      let edgeTop2 ← LayeredM.createEdge
      let edgeBottom ← LayeredM.createEdge
      LayeredM.setEdgeSource edgeTop1 (some topPort1)
      LayeredM.setEdgeSource edgeTop2 (some topPort2)
      LayeredM.setEdgeTarget edgeBottom (some bottomPort)
      LayeredM.modifyNode node fun x => { x with internal := { x.internal with topComments := #[top1, top2], bottomComments := #[bottom] } }
      runProc CommentPostprocessor.processor g
      return (layers[0]!, node, #[top1, top2, bottom], #[nodeTopPort1, nodeTopPort2, nodeBottomPort],
        #[edgeTop1, edgeTop2, edgeBottom]))
  let layerNodes := (a.layer layer).nodes
  check "reinserts_boxes: all boxes in the layer" (boxes.all layerNodes.contains)
  checkEq "hand: boxes appended after the node (top then bottom)" layerNodes #[node, boxes[0]!, boxes[1]!, boxes[2]!]
  checkNone "hand: Java parity, box layer field not set" (a.node boxes[0]!).layer
  checkFloat "reinserts_boxes: top 1 x" (a.node boxes[0]!).position.x 112.5 1e-6
  checkFloat "reinserts_boxes: top 1 y" (a.node boxes[0]!).position.y 80.0 1e-6
  checkFloat "reinserts_boxes: top 2 x" (a.node boxes[1]!).position.x 137.5 1e-6
  checkFloat "reinserts_boxes: top 2 y" (a.node boxes[1]!).position.y 82.0 1e-6
  checkFloat "reinserts_boxes: bottom x" (a.node boxes[2]!).position.x 115.0 1e-6
  checkFloat "reinserts_boxes: bottom y" (a.node boxes[2]!).position.y 158.0 1e-6
  checkEq "reinserts_boxes: top 1 edge target" (a.edge edges[0]!).target (some nodePorts[0]!)
  checkEq "reinserts_boxes: top 2 edge target" (a.edge edges[1]!).target (some nodePorts[1]!)
  checkEq "reinserts_boxes: bottom edge source" (a.edge edges[2]!).source (some nodePorts[2]!)
  check "reinserts_boxes: connection ports attached to the node"
    (nodePorts.all fun p => (a.port p).owner == some node)
  -- hand: anchors 60/3 = 20 and 40 on the top border, 30 on the bottom border (y = height 40)
  checkFloat "hand: top connection port 1 x" (a.port nodePorts[0]!).position.x 20.0 1e-6
  checkFloat "hand: top connection port 2 x" (a.port nodePorts[1]!).position.x 40.0 1e-6
  checkFloat "hand: bottom connection port y" (a.port nodePorts[2]!).position.y 40.0 1e-6
  checkFloat "hand: top box port y = box height" (a.port (a.node boxes[0]!).ports[0]!).position.y 10.0 1e-6
  -- comment_postprocessor_leaves_layer_unchanged_without_comment_properties
  let ((layer, node), a) ← LayeredM.run (do
      let (g, layers) ← graphWithLayers 1
      let node ← addToLayer g layers[0]!
      runProc CommentPostprocessor.processor g
      return (layers[0]!, node))
  checkEq "leaves_layer_unchanged_without_comment_properties" (a.layer layer).nodes #[node]

def commentNodeMarginTests : Suite := suite "layered.intermediate.CommentNodeMarginCalculator" do
  -- comment_node_margin_calculator_extends_margins_for_comments
  let (node, a) ← LayeredM.run (do
      let (g, layers) ← graphWithLayers 1
      LayeredM.setGraphProp g LayeredOptions.SPACING_COMMENT_COMMENT 2.0
      LayeredM.setGraphProp g LayeredOptions.SPACING_COMMENT_NODE 3.0
      let node ← addToLayer g layers[0]! .none { size := ⟨50.0, 20.0⟩ }
      let topA ← addToLayer g layers[0]! .none { size := ⟨30.0, 8.0⟩ }
      let topB ← addToLayer g layers[0]! .none { size := ⟨20.0, 6.0⟩ }
      let bottom ← addToLayer g layers[0]! .none { size := ⟨10.0, 5.0⟩ }
      LayeredM.modifyNode node fun x => { x with internal := { x.internal with topComments := #[topA, topB], bottomComments := #[bottom] } }
      runProc CommentNodeMarginCalculator.processor g
      return node)
  let m := (a.node node).margin
  checkFloat "extends_margins_for_comments: top" m.top 11.0 1e-6
  checkFloat "extends_margins_for_comments: bottom" m.bottom 8.0 1e-6
  checkFloat "extends_margins_for_comments: left" m.left 1.0 1e-6
  checkFloat "extends_margins_for_comments: right" m.right 1.0 1e-6
  -- comment_node_margin_calculator_leaves_node_without_comments_unchanged
  let (node, a) ← LayeredM.run (do
      let (g, layers) ← graphWithLayers 1
      let node ← addToLayer g layers[0]! .none { size := ⟨40.0, 10.0⟩, margin := { top := 1.0, right := 2.0, bottom := 3.0, left := 4.0 } }
      runProc CommentNodeMarginCalculator.processor g
      return node)
  let m := (a.node node).margin
  check "leaves_node_without_comments_unchanged" (m.top == 1.0 && m.right == 2.0 && m.bottom == 3.0 && m.left == 4.0)
  -- hand: individual SPACING_COMMENT_NODE 7 overrides the default 10: top margin 5 + 7
  let (node, a) ← LayeredM.run (do
      let (g, layers) ← graphWithLayers 1
      let node ← addToLayer g layers[0]! .none { size := ⟨50.0, 20.0⟩ }
      let individual : IndividualSpacings := { props := PropertyMap.empty.set LayeredOptions.SPACING_COMMENT_NODE 7.0 }
      LayeredM.setNodeProp node LayeredOptions.SPACING_INDIVIDUAL individual
      let topA ← addToLayer g layers[0]! .none { size := ⟨10.0, 5.0⟩ }
      LayeredM.modifyNode node fun x => { x with internal := { x.internal with topComments := #[topA] } }
      runProc CommentNodeMarginCalculator.processor g
      return node)
  checkFloat "hand: individual comment-node spacing" (a.node node).margin.top 12.0 1e-6
  checkFloat "hand: narrow comment leaves side margins" (a.node node).margin.left 0.0 1e-6

/-! ## HighDegreeNodeLayeringProcessor -/

/-- Layers `[x, a1] [y] [H] [b1] [b2]`, edges `x→y, y→H, a1→H, H→b1, b1→b2`; `H` has degree 3. Returns the
graph, the original layers and the nodes `x, y, a1, H, b1, b2`. -/
def highDegreeGraph (treeHeight : Int) : LayeredM (LGraphId × Array LayerId × Array LNodeId) := do
  let (g, layers) ← graphWithLayers 5
  LayeredM.setGraphProp g LayeredOptions.HIGH_DEGREE_NODES_THRESHOLD 3
  LayeredM.setGraphProp g LayeredOptions.HIGH_DEGREE_NODES_TREE_HEIGHT treeHeight
  let x ← addToLayer g layers[0]!
  let a1 ← addToLayer g layers[0]!
  let y ← addToLayer g layers[1]!
  let h ← addToLayer g layers[2]!
  let b1 ← addToLayer g layers[3]!
  let b2 ← addToLayer g layers[4]!
  let _ ← connectNodes x y
  let _ ← connectNodes y h
  let _ ← connectNodes a1 h
  let _ ← connectNodes h b1
  let _ ← connectNodes b1 b2
  return (g, layers, #[x, y, a1, h, b1, b2])

def highDegreeTests : Suite := suite "layered.intermediate.HighDegreeNodeLayeringProcessor" do
  -- hand: incoming trees y←x (height 2) and a1 (height 1) → 2 new layers before H (roots next to H, in H's
  -- incoming edge order); outgoing tree b1→b2 (height 2) → 2 new layers after H; emptied layers removed
  let ((g, layers, ns), a) ← LayeredM.run (do
      let r ← highDegreeGraph 5
      runProc HighDegreeNodeLayeringProcessor.processor r.1
      return r)
  checkEq "hand: trees moved next to the hub" (layerNodes a g)
    #[#[ns[0]!], #[ns[1]!, ns[2]!], #[ns[3]!], #[ns[4]!], #[ns[5]!]]
  checkEq "hand: hub keeps its layer" (a.node ns[3]!).layer (some layers[2]!)
  check "hand: tree nodes are in new layers" (#[0, 1, 2, 4, 5].all fun i => !layers.contains ((a.node ns[i]!).layer.getD default))
  check "hand: layering invariants after tree moves" (layeringInvariantsHold a g)
  -- hand: tree height 1 only accepts the leaf a1 (one new layer before H); y, b1, b2 stay
  let ((g, _, ns), a) ← LayeredM.run (do
      let r ← highDegreeGraph 1
      runProc HighDegreeNodeLayeringProcessor.processor r.1
      return r)
  checkEq "hand: height 1 → only a1 moves" (layerNodes a g)
    #[#[ns[0]!], #[ns[1]!], #[ns[2]!], #[ns[3]!], #[ns[4]!], #[ns[5]!]]
  -- hand: default threshold 16 → nothing changes
  let ((g, layersBefore), a) ← LayeredM.run (do
      let (g, layers) ← graphWithLayers 3
      let n0 ← addToLayer g layers[0]!
      let n1 ← addToLayer g layers[1]!
      let n2 ← addToLayer g layers[2]!
      let _ ← connectNodes n0 n1
      let _ ← connectNodes n1 n2
      let before := (← get).graphToNodeArray g
      runProc HighDegreeNodeLayeringProcessor.processor g
      return (g, before))
  checkEq "hand: no high-degree node → unchanged" (layerNodes a g) layersBefore

/-! ## NodePromotion -/

/-- Layers `[a(0)] [b(1), d(3)] [c(2)]`, edges `a→b, b→c, a→d` (longest-path-source layering). -/
def promotionGraph (strategy : NodePromotionStrategy) : LayeredM (LGraphId × Array LNodeId) := do
  let (g, layers) ← graphWithLayers 3
  LayeredM.setGraphProp g LayeredOptions.LAYERING_NODE_PROMOTION_STRATEGY strategy
  let na ← addToLayer g layers[0]!
  let nb ← addToLayer g layers[1]!
  let nd ← addToLayer g layers[1]!
  let nc ← addToLayer g layers[2]!
  for (n, mo) in #[(na, 0), (nb, 1), (nc, 2), (nd, 3)] do setModelOrder n mo
  let _ ← connectNodes na nb
  let _ ← connectNodes nb nc
  let _ ← connectNodes na nd
  return (g, #[na, nb, nc, nd])

def nodePromotionTests : Suite := suite "layered.intermediate.NodePromotion" do
  -- node_promotion_model_order_left_to_right_preserves_layering_invariants (hand-built graph):
  -- d(3) is the largest model order of its layer and the next layer has c(2) < 3 → d moves next to c
  let ((g, ns), a) ← LayeredM.run (do
      let r ← promotionGraph .modelOrderLeftToRight
      runProc NodePromotion.processor r.1
      return r)
  checkEq "hand: LTR promotes d into c's layer" (layerNodes a g) #[#[ns[0]!], #[ns[1]!], #[ns[2]!, ns[3]!]]
  check "model_order_left_to_right_preserves_layering_invariants" (layeringInvariantsHold a g)
  -- node_promotion_model_order_right_to_left_preserves_layering_invariants (hand-built graph):
  -- layers [b(1)] [a(0), c(2)], edge b→c: a is minimal and b(1) > 0 → a moves to the first layer
  let ((g, nb, na, nc), a) ← LayeredM.run (do
      let (g, layers) ← graphWithLayers 2
      LayeredM.setGraphProp g LayeredOptions.LAYERING_NODE_PROMOTION_STRATEGY NodePromotionStrategy.modelOrderRightToLeft
      let nb ← addToLayer g layers[0]!
      let nc ← addToLayer g layers[1]!
      let na ← addToLayer g layers[1]!
      setModelOrder na 0
      setModelOrder nb 1
      setModelOrder nc 2
      let _ ← connectNodes nb nc
      runProc NodePromotion.processor g
      return (g, nb, na, nc))
  checkEq "hand: RTL promotes a, layers sorted ascending" (layerNodes a g) #[#[nb, na], #[nc]]
  check "model_order_right_to_left_preserves_layering_invariants" (layeringInvariantsHold a g)
  -- hand: promotion through a label dummy layer. Layers [x(2), a(0)] [l] [c(1)] [y(3)], edges a→l→c, x→y:
  -- pass 1 moves x behind l (y is 3 layers away), pass 2 moves x next to c (c(1) < 2); a stays (l's edge
  -- from a ends two layers away)
  let ((g, na, nl, nc, nx, ny), a) ← LayeredM.run (do
      let (g, layers) ← graphWithLayers 4
      LayeredM.setGraphProp g LayeredOptions.LAYERING_NODE_PROMOTION_STRATEGY NodePromotionStrategy.modelOrderLeftToRight
      let na ← addToLayer g layers[0]!
      let nx ← addToLayer g layers[0]!
      let nl ← addToLayer g layers[1]! .none { type := .label }
      let nc ← addToLayer g layers[2]!
      let ny ← addToLayer g layers[3]!
      setModelOrder na 0
      setModelOrder nc 1
      setModelOrder nx 2
      setModelOrder ny 3
      let _ ← connectNodes na nl
      let _ ← connectNodes nl nc
      let _ ← connectNodes nx ny
      runProc NodePromotion.processor g
      return (g, na, nl, nc, nx, ny))
  checkEq "hand: LTR through a label layer" (layerNodes a g) #[#[na], #[nl], #[nc, nx], #[ny]]
  check "hand: invariants after label-layer promotion" (layeringInvariantsHold a g)
  -- elk-rs parity: the Nikolov family is a no-op (Java would run promotionMagic)
  for strategy in #[NodePromotionStrategy.nikolov, .nikolovPixel, .nikolovImproved, .nikolovImprovedPixel, .noBoundary,
      .dummynodePercentage, .nodecountPercentage] do
    let ((g, ns), a) ← LayeredM.run (do
        let r ← promotionGraph strategy
        runProc NodePromotion.processor r.1
        return r)
    checkEq s!"elk-rs parity: {strategy} leaves the layering unchanged" (layerNodes a g)
      #[#[ns[0]!], #[ns[1]!, ns[3]!], #[ns[2]!]]
  -- Java: a single layer is still sorted by model order (descending for left-to-right) and rebuilt
  -- (elk-rs leaves graphs with fewer than two layers untouched)
  let ((g, ns), a) ← LayeredM.run (do
      let (g, layers) ← graphWithLayers 1
      LayeredM.setGraphProp g LayeredOptions.LAYERING_NODE_PROMOTION_STRATEGY NodePromotionStrategy.modelOrderLeftToRight
      let n0 ← addToLayer g layers[0]!
      let n1 ← addToLayer g layers[0]!
      setModelOrder n0 0
      setModelOrder n1 1
      runProc NodePromotion.processor g
      return (g, #[n0, n1]))
  checkEq "Java: single layer sorted by descending model order" (layerNodes a g) #[#[ns[1]!, ns[0]!]]

def suites : Array Tests.Suite :=
  #[edgeReverserTests, layerConstraintPreprocessorTests, layerConstraintPostprocessorTests, inLayerConstraintTests,
    partitionTests, constraintsPostprocessorTests, commentPreprocessorTests, commentPostprocessorTests,
    commentNodeMarginTests, highDegreeTests, nodePromotionTests]

end Tests.Layered.IntermediateConstraints
