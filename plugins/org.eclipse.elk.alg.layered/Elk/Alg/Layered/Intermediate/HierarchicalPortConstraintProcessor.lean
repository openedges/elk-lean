import Std.Data.HashMap
import Elk.Alg.Layered.LayeredPhases
import Elk.Core.Util.Sort
/-!
# `org.eclipse.elk.alg.layered.intermediate.HierarchicalPortConstraintProcessor`

Port of elk-rs `intermediate/hierarchical_port_constraint_processor.rs`. Processes the port
constraints of a nested graph's external port dummies:

* With order-fixed port constraints on the graph, the eastern and western external port dummies of
  the first and last layer are chained by in-layer successor constraints in the order of their
  `PORT_RATIO_OR_POSITION`.
* With side-fixed port constraints, every northern/southern external port dummy is replaced by
  fresh dummies in the layers before/after the nodes it is connected to (one per layer and
  original port); new layers are created in front of the first and after the last layer when
  needed. The original dummies are removed from their layers and remembered in
  `EXT_PORT_REPLACED_DUMMIES`.

Precondition: a layered graph; postcondition: north/south external port dummies replaced.
Slot: before phase 3. Same-slot dependency: before `LayerConstraintPostprocessor`.
-/
namespace Elk.Alg.Layered.Intermediate

open Elk.Graph Elk.Core Elk.Core.Alg Elk.Core.Math Elk.Core.Options Elk.Core.Util Elk.Alg.Layered
  Elk.Alg.Layered.Graph Elk.Alg.Layered.Options LayeredM

namespace HierarchicalPortConstraintProcessor

/-- `DUMMY_INPUT_PORT`: index of the input port of a replacement dummy. -/
def DUMMY_INPUT_PORT : Nat := 0
/-- `DUMMY_OUTPUT_PORT`: index of the output port of a replacement dummy. -/
def DUMMY_OUTPUT_PORT : Nat := 1

/-- The comparator of `processEasternAndWesternPortDummies(layer)` (Rust closure in
`process_eastern_and_western_port_dummies_layer`) on `(type, PORT_RATIO_OR_POSITION)` pairs:
external port dummies first, ordered by the Java comparison `pos1 == pos2 ? 0 : pos1 < pos2 ? -1 : 1`.

Rust returns `Less` when both nodes are no external port dummies (an inconsistent comparator); this
port returns `eq` there. Only the external-port prefix of the sorted list is used (the loop stops at
the first other node) and that prefix is the same either way (stable order by position). -/
def compareDummies (a b : NodeType × Float) : Ordering :=
  let (type1, pos1) := a
  let (type2, pos2) := b
  if type1 != .externalPort && type2 != .externalPort then .eq
  else if type2 != .externalPort then .lt
  else if type1 != .externalPort then .gt
  else if pos1 == pos2 then .eq
  else if pos1 < pos2 then .lt
  else .gt

/-- `processEasternAndWesternPortDummies(layer)` (Rust
`process_eastern_and_western_port_dummies_layer`): sorts the layer's nodes (stable) and chains the
eastern/western external port dummies with `IN_LAYER_SUCCESSOR_CONSTRAINTS`. -/
def processEasternAndWesternPortDummiesLayer (layer : LayerId) : LayeredM Unit := do
  let nodes := (← getLayer layer).nodes
  let mut keyed : Array (LNodeId × NodeType × Float) := #[]
  for n in nodes do
    let nd ← getNode n
    keyed := keyed.push (n, nd.type, nd.internal.portRatioOrPosition)
  let sorted := stableSort keyed fun (_, t1, p1) (_, t2, p2) => compareDummies (t1, p1) (t2, p2)
  let mut lastHierarchicalDummy : Option LNodeId := none
  for (node, _, _) in sorted do
    let nd ← getNode node
    if nd.type != .externalPort then break
    let extSide := nd.internal.extPortSide
    if extSide != .west && extSide != .east then continue
    if let some lastDummy := lastHierarchicalDummy then
      modifyNode lastDummy fun x => { x with internal := { x.internal with
        inLayerSuccessorConstraints := x.internal.inLayerSuccessorConstraints.push node } }
    lastHierarchicalDummy := some node

/-- `processEasternAndWesternPortDummies(layeredGraph)`: only for order-fixed port constraints, on
the first and (if different) the last layer. -/
def processEasternAndWesternPortDummies (graph : LGraphId) : LayeredM Unit := do
  let gr ← getGraph graph
  let portConstraints := gr.props.getD CoreOptions.PORT_CONSTRAINTS PortConstraints.undefined
  if !portConstraints.isOrderFixed then return
  let layers := gr.layers
  if layers.isEmpty then return
  processEasternAndWesternPortDummiesLayer layers[0]!
  if layers.size > 1 then
    processEasternAndWesternPortDummiesLayer layers[layers.size - 1]!

/-- `isNorthernSouthernDummy(node)` (Rust `is_northern_or_southern_dummy`). -/
def isNorthernOrSouthernDummy (node : LNodeId) : LayeredM Bool := do
  let nd ← getNode node
  let side := nd.internal.extPortSide
  return nd.type == .externalPort && (side == .north || side == .south)

/-- Key of the external port a dummy represents (Rust `origin_port_key`: the `ElkPort` origin id, or
the identity of an `LPort` origin; other origins yield no key and the edge is skipped). The two kinds
are tagged separately (Rust mixes ElkPort ids and pointer addresses in one `usize` space). -/
inductive OriginKey where
  | elkPort (idx : Nat)
  | lPort (idx : Nat)
  deriving BEq, Hashable, Repr, Inhabited

/-- Rust `origin_port_key`. -/
def originPortKey (node : LNodeId) : LayeredM (Option OriginKey) := do
  return match (← getNode node).internal.origin with
    | some (.elkPort p) => some (.elkPort p.idx)
    | some (.lPort p) => some (.lPort p.idx)
    | _ => none

/-- `createDummy(graph, originalDummy)` (Rust `create_dummy`): a new external port dummy with all
properties of the original (Java `copyProperties`: the public map and the typed internals),
`EXT_PORT_REPLACED_DUMMY` = the original, `FIXED_POS` port constraints, `CENTER` alignment and one
western input and one eastern output port. -/
def createDummy (graph : LGraphId) (originalDummy : LNodeId) : LayeredM LNodeId := do
  let orig ← getNode originalDummy
  let newDummy ← createNode graph
  modifyNode newDummy fun x => { x with props := orig.props, internal := orig.internal }
  modifyNode newDummy fun x => { x with
    internal := { x.internal with extPortReplacedDummy := some originalDummy }
    props := (x.props.set CoreOptions.PORT_CONSTRAINTS PortConstraints.fixedPos).set
      CoreOptions.ALIGNMENT Alignment.center
    type := .externalPort }
  let inputPort ← LayeredM.createPort
  setPortNode inputPort (some newDummy)
  modifyPort inputPort fun p => p.setSide .west
  let outputPort ← LayeredM.createPort
  setPortNode outputPort (some newDummy)
  modifyPort outputPort fun p => p.setSide .east
  return newDummy

/-- Mutable state of `processNorthernAndSouthernPortDummies`: per slot (`0` = new layer in front,
`i + 1` = layer `i`, `layerCount + 1` = new layer at the end) the origin → dummy map and the new
dummies in creation order. -/
structure NorthSouthState where
  extPortToDummyNodeMap : Array (Std.HashMap OriginKey LNodeId)
  newDummyNodes : Array (Array LNodeId)
  originalExternalPortDummies : Array LNodeId := #[]

/-- The replacement dummy of `dummy` in slot `slot`, created on first use. -/
def provideDummy (graph : LGraphId) (st : NorthSouthState) (slot : Nat) (key : OriginKey) (dummy : LNodeId) :
    LayeredM (LNodeId × NorthSouthState) := do
  match st.extPortToDummyNodeMap[slot]!.get? key with
  | some existing => return (existing, st)
  | none =>
    let d ← createDummy graph dummy
    let st := { st with
      extPortToDummyNodeMap := st.extPortToDummyNodeMap.modify slot (·.insert key d)
      newDummyNodes := st.newDummyNodes.modify slot (·.push d) }
    return (d, st)

/-- Rewires the edges of one non-dummy node (Rust inner loop body of
`process_northern_and_southern_port_dummies`): incoming edges from north/south dummies get the
output port of the previous-layer replacement, outgoing edges to them the input port of the
next-layer replacement. -/
def processNode (graph : LGraphId) (st : NorthSouthState) (currLayerIdx : Nat) (currentNode : LNodeId) :
    LayeredM NorthSouthState := do
  let mut st := st
  for edge in (← withArena (·.nodeIncomingEdges currentNode)) do
    let some sourcePort := (← getEdge edge).source | continue
    let some sourceNode := (← getPort sourcePort).owner | continue
    if !(← isNorthernOrSouthernDummy sourceNode) then continue
    let some key ← originPortKey sourceNode | continue
    let (prevLayerDummy, st') ← provideDummy graph st currLayerIdx key sourceNode
    st := st'
    if let some dummyPort := (← getNode prevLayerDummy).ports[DUMMY_OUTPUT_PORT]? then
      setEdgeSource edge (some dummyPort)
  for edge in (← withArena (·.nodeOutgoingEdges currentNode)) do
    let some targetPort := (← getEdge edge).target | continue
    let some targetNode := (← getPort targetPort).owner | continue
    if !(← isNorthernOrSouthernDummy targetNode) then continue
    let some key ← originPortKey targetNode | continue
    let (nextLayerDummy, st') ← provideDummy graph st (currLayerIdx + 2) key targetNode
    st := st'
    if let some dummyPort := (← getNode nextLayerDummy).ports[DUMMY_INPUT_PORT]? then
      setEdgeTarget edge (some dummyPort)
  return st

/-- `processNorthernAndSouthernPortDummies(layeredGraph)`: only for side-fixed port constraints. -/
def processNorthernAndSouthernPortDummies (graph : LGraphId) : LayeredM Unit := do
  let gr ← getGraph graph
  let portConstraints := gr.props.getD CoreOptions.PORT_CONSTRAINTS PortConstraints.undefined
  if !portConstraints.isSideFixed then return
  let layers := gr.layers
  let layerCount := layers.size
  if layerCount == 0 then return
  -- Rust: the graph of the first layer
  let graphRef := (← getLayer layers[0]!).owner
  let mut st : NorthSouthState := {
    extPortToDummyNodeMap := Array.replicate (layerCount + 2) {}
    newDummyNodes := Array.replicate (layerCount + 2) #[] }
  for currLayerIdx in [0:layerCount] do
    let layerNodes := (← getLayer layers[currLayerIdx]!).nodes
    for currentNode in layerNodes do
      if ← isNorthernOrSouthernDummy currentNode then
        st := { st with originalExternalPortDummies := st.originalExternalPortDummies.push currentNode }
        continue
      st ← processNode graphRef st currLayerIdx currentNode
  let newDummyNodes := st.newDummyNodes
  for index in [0:newDummyNodes.size] do
    let nodeList := newDummyNodes[index]!
    if nodeList.isEmpty then continue
    let layer ← (do
      if index == 0 then
        let layer ← createLayer graphRef
        modifyGraph graph fun g => { g with layers := g.layers.insertIdx! 0 layer }
        pure layer
      else if index == newDummyNodes.size - 1 then
        let layer ← createLayer graphRef
        modifyGraph graph fun g => { g with layers := g.layers.push layer }
        pure layer
      else pure layers[index - 1]!)
    for dummy in nodeList do
      setNodeLayer dummy (some layer)
  for originalDummy in st.originalExternalPortDummies do
    setNodeLayer originalDummy none
  let originals := st.originalExternalPortDummies
  modifyGraph graph fun g => { g with internal := { g.internal with extPortReplacedDummies := originals } }

/-- The `HierarchicalPortConstraintProcessor` (`process(layeredGraph, monitor)`). -/
def processor : LayeredProcessor :=
  { name := "HierarchicalPortConstraintProcessor"
    process := fun graph monitor => do
      let _ ← monitor.begin "Hierarchical port constraint processing" 1.0
      processEasternAndWesternPortDummies graph
      processNorthernAndSouthernPortDummies graph
      monitor.done }

end HierarchicalPortConstraintProcessor

builtin_initialize registerHierarchicalPortConstraintProcessor : Unit ←
  IntermediateProcessorStrategy.register .hierarchicalPortConstraintProcessor HierarchicalPortConstraintProcessor.processor

end Elk.Alg.Layered.Intermediate
