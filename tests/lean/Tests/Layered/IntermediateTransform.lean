import Tests.Framework
import Elk.Alg.Layered
import Elk.Alg.Layered.Intermediate.TransformProcessors
/-!
Tests of the layered intermediate processors `GraphTransformer`, `AlternatingLayerUnzipper` and
`SemiInteractiveCrossMinProcessor` on hand-built `LGraph`s. Expected values are derived by hand from
the Rust code ("hand: …"). The elk-rs unzipper tests drive the full pipeline
(`alternating_layer_unzipper_test.rs`); the hand-built one (`exactly_enough_nodes_fill_all_sublayers`)
is ported as is, the pipeline-driven ones are replaced by hand-built graphs with exact layer contents.
-/
namespace Tests.Layered.IntermediateTransform

open Tests Elk.Graph Elk.Core.Math Elk.Core.Options Elk.Core.Util Elk.Core.Alg Elk.Alg.Layered
  Elk.Alg.Layered.Graph Elk.Alg.Layered.Options Elk.Alg.Layered.Intermediate
open Elk (ElkEnum EnumSet)

/-! ## GraphTransformer -/

/-- Element ids of the transformer sample graph. -/
structure Sample where
  g : LGraphId
  a : LNodeId
  b : LNodeId
  x : LNodeId
  pN : LPortId
  pE : LPortId
  pS : LPortId
  pW : LPortId
  pB : LPortId
  e : LEdgeId
  nodeLabel : LLabelId
  portLabel : LLabelId
  edgeLabel : LLabelId

/-- Creates a port on `owner`. -/
def mkPort (owner : LNodeId) (side : PortSide) (pos size : KVector) : LayeredM LPortId := do
  let p ← LayeredM.createPort ((({ position := pos, size := size } : LPort)).setSide side)
  LayeredM.setPortNode p (some owner)
  return p

/-- The sample: graph size `(100,60)`, offset `(5,3)`, padding `(t1,r2,b3,l4)`; node `A` at
`(10,20)` size `(30,40)` with ports on all four sides, a node label, `POSITION`, `ALIGNMENT`,
`NODE_SIZE_MINIMUM` and label placement; node `B` at `(70,10)`; an edge `A.pE → B.pB` with bend
points, junction points and a label; an external port dummy `X` (west, `FIRST_SEPARATE`). -/
def buildSample (direction : Direction) (congruency : DirectionCongruency := .readingDirection) :
    LayeredM Sample := do
  let g ← LayeredM.createGraph { size := ⟨100, 60⟩, offset := ⟨5, 3⟩, padding := ⟨1, 2, 3, 4⟩ }
  LayeredM.setGraphProp g LayeredOptions.DIRECTION direction
  LayeredM.setGraphProp g LayeredOptions.DIRECTION_CONGRUENCY congruency
  LayeredM.setGraphProp g LayeredOptions.NODE_LABELS_PADDING ⟨5, 6, 7, 8⟩
  let aProps := (((PropertyMap.empty.set LayeredOptions.NODE_LABELS_PLACEMENT
      (EnumSet.of #[NodeLabelPlacement.hLeft, .vTop, .inside])).set LayeredOptions.ALIGNMENT Alignment.left).set
      LayeredOptions.POSITION ⟨7, 8⟩).set LayeredOptions.NODE_SIZE_MINIMUM ⟨11, 12⟩
  let a ← LayeredM.createNode g { position := ⟨10, 20⟩, size := ⟨30, 40⟩, padding := ⟨1, 2, 3, 4⟩, props := aProps }
  let b ← LayeredM.createNode g { position := ⟨70, 10⟩, size := ⟨20, 20⟩ }
  let xProps := PropertyMap.empty.set LayeredOptions.LAYERING_LAYER_CONSTRAINT LayerConstraint.firstSeparate
  let xNode : LNode := { position := ⟨0, 50⟩, size := ⟨6, 6⟩, type := .externalPort, props := xProps }
  let x ← LayeredM.createNode g { xNode with internal := { extPortSide := .west } }
  LayeredM.modifyGraph g fun gr => { gr with layerlessNodes := #[a, b, x] }
  let pN ← mkPort a .north ⟨5, -2⟩ ⟨4, 2⟩
  let pEBase : LPort := { position := ⟨30, 10⟩, size := ⟨4, 4⟩, side := .east, anchor := ⟨1, 3⟩ }
  let pE ← LayeredM.createPort { pEBase with explicitlySuppliedPortAnchor := true,
                                             props := PropertyMap.empty.set LayeredOptions.PORT_INDEX 2 }
  LayeredM.setPortNode pE (some a)
  let pS ← mkPort a .south ⟨15, 40⟩ ⟨2, 4⟩
  let pW ← mkPort a .west ⟨-4, 20⟩ ⟨4, 2⟩
  let pB ← mkPort b .west ⟨-4, 8⟩ ⟨4, 4⟩
  let jps := PropertyMap.empty.set LayeredOptions.JUNCTION_POINTS #[⟨55, 50⟩]
  let e ← LayeredM.createEdge { bendPoints := #[⟨50, 30⟩, ⟨60, 70⟩], props := jps }
  LayeredM.setEdgeSource e (some pE)
  LayeredM.setEdgeTarget e (some pB)
  let nodeLabel ← LayeredM.createLabel "A" { position := ⟨3, 4⟩, size := ⟨10, 5⟩ }
  LayeredM.modifyNode a fun n => { n with labels := #[nodeLabel] }
  let portLabel ← LayeredM.createLabel "pE" { position := ⟨2, 1⟩, size := ⟨6, 3⟩ }
  LayeredM.modifyPort pE fun p => { p with labels := #[portLabel] }
  let edgeLabel ← LayeredM.createLabel "e" { position := ⟨52, 33⟩, size := ⟨8, 4⟩ }
  LayeredM.modifyEdge e fun ed => { ed with labels := #[edgeLabel] }
  return ⟨g, a, b, x, pN, pE, pS, pW, pB, e, nodeLabel, portLabel, edgeLabel⟩

/-- Runs a processor on the graph. -/
def runProc (p : LayeredProcessor) (g : LGraphId) : LayeredM Unit := p.process g ProgressMonitor.null

/-- Every transformed value of the sample, as strings (property values read with defaults). -/
def snapshot (ar : LGraphArena) (s : Sample) : Array String := Id.run do
  let gr := ar.graph s.g
  let mut out : Array String := #[
    s!"graph size={gr.size} offset={gr.offset} padding={gr.padding}",
    s!"graph nlp={gr.props.getD LayeredOptions.NODE_LABELS_PADDING {}} side={ElkEnum.javaName (gr.props.getD LayeredOptions.EDGE_LABELS_SIDE_SELECTION .smartDown)}"]
  for n in #[s.a, s.b, s.x] do
    let nd := ar.node n
    out := out.push s!"node {n} pos={nd.position} size={nd.size} padding={nd.padding} \
      POSITION={nd.props.get LayeredOptions.POSITION} align={ElkEnum.javaName (nd.props.getD LayeredOptions.ALIGNMENT .center)} \
      min={nd.props.getD LayeredOptions.NODE_SIZE_MINIMUM {}} \
      nlp={(nd.props.getD LayeredOptions.NODE_LABELS_PLACEMENT EnumSet.empty).toJavaString} \
      lc={ElkEnum.javaName (nd.props.getD LayeredOptions.LAYERING_LAYER_CONSTRAINT .none)} \
      ilc={ElkEnum.javaName nd.internal.inLayerConstraint} ext={nd.internal.extPortSide}"
  for p in #[s.pN, s.pE, s.pS, s.pW, s.pB] do
    let pt := ar.port p
    out := out.push s!"port {p} pos={pt.position} size={pt.size} anchor={pt.anchor} side={pt.side} \
      index={pt.props.get LayeredOptions.PORT_INDEX}"
  let ed := ar.edge s.e
  out := out.push s!"edge bends={ed.bendPoints} jps={ed.props.getD LayeredOptions.JUNCTION_POINTS #[]}"
  for l in #[s.nodeLabel, s.portLabel, s.edgeLabel] do
    let lb := ar.label l
    out := out.push s!"label {l} pos={lb.position} size={lb.size}"
  return out

/-- `TO_INTERNAL_LTR` followed by `TO_INPUT_DIRECTION` restores every value. -/
def roundTrip (direction : Direction) (congruency : DirectionCongruency) : TestM Unit := do
  let (s, a0) ← LayeredM.run (buildSample direction congruency)
  let ((), a1) ← LayeredM.run (runProc (GraphTransformer.processor .toInternalLtr) s.g) a0
  let ((), a2) ← LayeredM.run (runProc (GraphTransformer.processor .toInputDirection) s.g) a1
  let name := s!"{ElkEnum.javaName direction}/{ElkEnum.javaName congruency}"
  checkEq s!"round trip restores the input ({name})" (snapshot a2 s) (snapshot a0 s)
  if direction != .right then
    check s!"internal state differs from the input ({name})" (snapshot a1 s != snapshot a0 s)

def transformerLeft : Suite := suite "layered.intermediate.graphTransformer.left" do
  let (s, a0) ← LayeredM.run (buildSample .left)
  let ((), a) ← LayeredM.run (runProc (GraphTransformer.processor .toInternalLtr) s.g) a0
  -- hand: offset = (100 - 5) - 5 = 90
  checkEq "hand: A x = 90 - 30 - 10 = 50" (a.node s.a).position ⟨50, 20⟩
  checkEq "hand: A padding left/right swapped" (a.node s.a).padding ⟨1, 4, 3, 2⟩
  checkEq "hand: A POSITION x = 60 - 7" ((a.node s.a).props.get LayeredOptions.POSITION) (some ⟨53, 8⟩)
  checkEq "hand: A ALIGNMENT LEFT -> RIGHT" (ElkEnum.javaName ((a.node s.a).props.getD LayeredOptions.ALIGNMENT .center)) "RIGHT"
  check "hand: A label placement H_LEFT -> H_RIGHT"
    ((a.node s.a).props.getD LayeredOptions.NODE_LABELS_PLACEMENT EnumSet.empty ==
      EnumSet.of #[NodeLabelPlacement.hRight, .vTop, .inside])
  checkEq "hand: pE x = 30 - 4 - 30 = -4" (a.port s.pE).position ⟨-4, 10⟩
  checkEq "hand: pE explicit anchor x = 4 - 1" (a.port s.pE).anchor ⟨3, 3⟩
  checkEq "hand: pE EAST -> WEST" (a.port s.pE).side .west
  checkEq "hand: pE PORT_INDEX negated" ((a.port s.pE).props.get LayeredOptions.PORT_INDEX) (some (-2))
  checkEq "hand: pW WEST -> EAST, x = 26 + 4" (a.port s.pW).position ⟨30, 20⟩
  checkEq "hand: pW default anchor recomputed for EAST" (a.port s.pW).anchor ⟨4, 1⟩
  checkEq "hand: pN stays NORTH" (a.port s.pN).side .north
  checkEq "hand: pN x = 26 - 5" (a.port s.pN).position ⟨21, -2⟩
  checkEq "hand: bend points x = 90 - x" (a.edge s.e).bendPoints #[⟨40, 30⟩, ⟨30, 70⟩]
  checkEq "hand: junction points x = 90 - 55" ((a.edge s.e).props.getD LayeredOptions.JUNCTION_POINTS #[]) #[⟨35, 50⟩]
  checkEq "hand: edge label x = 90 - 8 - 52" (a.label s.edgeLabel).position ⟨30, 33⟩
  checkEq "hand: port label x = 4 - 6 - 2" (a.label s.portLabel).position ⟨-4, 1⟩
  checkEq "hand: node label x = 30 - 10 - 3" (a.label s.nodeLabel).position ⟨17, 4⟩
  checkEq "hand: B x = 90 - 20 - 70" (a.node s.b).position ⟨0, 10⟩
  checkEq "hand: X ext port side WEST -> EAST" (a.node s.x).internal.extPortSide .east
  checkEq "hand: X FIRST_SEPARATE -> LAST_SEPARATE"
    (ElkEnum.javaName ((a.node s.x).props.getD LayeredOptions.LAYERING_LAYER_CONSTRAINT .none)) "LAST_SEPARATE"
  checkEq "hand: graph padding mirrored" (a.graph s.g).padding ⟨1, 4, 3, 2⟩
  checkEq "hand: NODE_LABELS_PADDING mirrored" ((a.graph s.g).props.get LayeredOptions.NODE_LABELS_PADDING) (some ⟨5, 8, 7, 6⟩)
  checkEq "hand: graph size unchanged" (a.graph s.g).size ⟨100, 60⟩

def transformerDown : Suite := suite "layered.intermediate.graphTransformer.down" do
  let (s, a0) ← LayeredM.run (buildSample .down)
  let ((), a) ← LayeredM.run (runProc (GraphTransformer.processor .toInternalLtr) s.g) a0
  checkEq "hand: A position transposed" (a.node s.a).position ⟨20, 10⟩
  checkEq "hand: A size transposed" (a.node s.a).size ⟨40, 30⟩
  checkEq "hand: A padding (t,r,b,l) = (l,b,r,t)" (a.node s.a).padding ⟨4, 3, 2, 1⟩
  checkEq "hand: NODE_SIZE_MINIMUM transposed" ((a.node s.a).props.get LayeredOptions.NODE_SIZE_MINIMUM) (some ⟨12, 11⟩)
  checkEq "hand: B gets NODE_SIZE_MINIMUM (0,0) stored" ((a.node s.b).props.has LayeredOptions.NODE_SIZE_MINIMUM) true
  checkEq "hand: ALIGNMENT LEFT -> TOP" (ElkEnum.javaName ((a.node s.a).props.getD LayeredOptions.ALIGNMENT .center)) "TOP"
  check "hand: label placement transposed (+H_PRIORITY)"
    ((a.node s.a).props.getD LayeredOptions.NODE_LABELS_PLACEMENT EnumSet.empty ==
      EnumSet.of #[NodeLabelPlacement.inside, .hPriority, .hLeft, .vTop])
  checkEq "hand: pE EAST -> SOUTH" (a.port s.pE).side .south
  checkEq "hand: pE explicit anchor transposed" (a.port s.pE).anchor ⟨3, 1⟩
  checkEq "hand: pN NORTH -> WEST, anchor (0, h/2)" ((a.port s.pN).side, (a.port s.pN).anchor) (.west, ⟨0, 2⟩)
  checkEq "hand: pS SOUTH -> EAST, anchor (w, h/2)" ((a.port s.pS).side, (a.port s.pS).anchor) (.east, ⟨4, 1⟩)
  checkEq "hand: pW WEST -> NORTH, anchor (w/2, 0)" ((a.port s.pW).side, (a.port s.pW).anchor) (.north, ⟨1, 0⟩)
  checkEq "hand: bend points transposed" (a.edge s.e).bendPoints #[⟨30, 50⟩, ⟨70, 60⟩]
  checkEq "hand: edge label size transposed" (a.label s.edgeLabel).size ⟨4, 8⟩
  checkEq "hand: X ext port side WEST -> NORTH" (a.node s.x).internal.extPortSide .north
  checkEq "hand: X FIRST_SEPARATE -> NONE + in-layer TOP"
    (ElkEnum.javaName ((a.node s.x).props.getD LayeredOptions.LAYERING_LAYER_CONSTRAINT .none),
      ElkEnum.javaName (a.node s.x).internal.inLayerConstraint) ("NONE", "TOP")
  checkEq "hand: graph offset/size transposed" ((a.graph s.g).offset, (a.graph s.g).size) (⟨3, 5⟩, ⟨60, 100⟩)
  checkEq "hand: graph padding transposed" (a.graph s.g).padding ⟨4, 3, 2, 1⟩
  checkEq "hand: EDGE_LABELS_SIDE_SELECTION SMART_DOWN -> SMART_UP"
    ((a.graph s.g).props.get? LayeredOptions.EDGE_LABELS_SIDE_SELECTION).isSome true
  checkEq "hand: side selection value"
    (ElkEnum.javaName ((a.graph s.g).props.getD LayeredOptions.EDGE_LABELS_SIDE_SELECTION .alwaysUp)) "SMART_UP"

def transformerUp : Suite := suite "layered.intermediate.graphTransformer.up" do
  let (s, a0) ← LayeredM.run (buildSample .up)
  let ((), a) ← LayeredM.run (runProc (GraphTransformer.processor .toInternalLtr) s.g) a0
  -- hand: transpose, then mirror y with offset = (100 - 5) - 5 = 90
  checkEq "hand: A y = 90 - 30 - 10" (a.node s.a).position ⟨20, 50⟩
  checkEq "hand: pE EAST -> SOUTH -> NORTH" (a.port s.pE).side .north
  checkEq "hand: pE anchor (3,1) -> y = 4 - 1" (a.port s.pE).anchor ⟨3, 3⟩
  checkEq "hand: bend points (30,90-50),(70,90-60)" (a.edge s.e).bendPoints #[⟨30, 40⟩, ⟨70, 30⟩]
  checkEq "hand: ALIGNMENT LEFT -> TOP -> BOTTOM" (ElkEnum.javaName ((a.node s.a).props.getD LayeredOptions.ALIGNMENT .center)) "BOTTOM"
  checkEq "hand: X in-layer TOP -> BOTTOM" (ElkEnum.javaName (a.node s.x).internal.inLayerConstraint) "BOTTOM"
  checkEq "hand: X ext side WEST -> NORTH -> SOUTH" (a.node s.x).internal.extPortSide .south

def transformerRotation : Suite := suite "layered.intermediate.graphTransformer.rotation" do
  let (s, a0) ← LayeredM.run (buildSample .down .rotation)
  let ((), a) ← LayeredM.run (runProc (GraphTransformer.processor .toInternalLtr) s.g) a0
  -- hand: rotate90 clockwise = transpose, then mirror x with offset = (60 - 3) - 3 = 54
  checkEq "hand: A x = 54 - 40 - 20" (a.node s.a).position ⟨-6, 10⟩
  checkEq "hand: pN NORTH -> WEST -> EAST" (a.port s.pN).side .east
  checkEq "hand: pE EAST -> SOUTH (mirror x keeps)" (a.port s.pE).side .south
  checkEq "hand: bend points x = 54 - x" (a.edge s.e).bendPoints #[⟨24, 50⟩, ⟨-16, 60⟩]
  let (s2, b0) ← LayeredM.run (buildSample .left .rotation)
  let ((), b) ← LayeredM.run (runProc (GraphTransformer.processor .toInternalLtr) s2.g) b0
  -- hand: LEFT with rotation mirrors x and y (y offset = (60 - 3) - 3 = 54)
  checkEq "hand: LEFT/rotation A = (50, 54 - 40 - 20)" (b.node s2.a).position ⟨50, -6⟩
  checkEq "hand: LEFT/rotation pN NORTH -> SOUTH" (b.port s2.pN).side .south

def transformerRoundTrips : Suite := suite "layered.intermediate.graphTransformer.roundTrip" do
  for d in #[Direction.right, .left, .down, .up] do
    for c in #[DirectionCongruency.readingDirection, .rotation] do
      roundTrip d c

def transformerMisc : Suite := suite "layered.intermediate.graphTransformer.misc" do
  -- graph width 0: offset = max(x + width + margin.right) - offset.x
  let ((g, n1, n2), a0) ← LayeredM.run (do
    let g ← LayeredM.createGraph { offset := ⟨2, 0⟩ }
    LayeredM.setGraphProp g LayeredOptions.DIRECTION Direction.left
    let l ← LayeredM.createLayer g
    LayeredM.modifyGraph g fun gr => { gr with layers := #[l] }
    let n1 ← LayeredM.createNode g { position := ⟨0, 0⟩, size := ⟨10, 10⟩ }
    let n2 ← LayeredM.createNode g { position := ⟨30, 0⟩, size := ⟨10, 10⟩, margin := ⟨0, 5, 0, 0⟩ }
    LayeredM.setNodeLayer n1 (some l)
    LayeredM.setNodeLayer n2 (some l)
    -- n1 is also layerless: processed once (Rust de-duplication)
    LayeredM.modifyGraph g fun gr => { gr with layerlessNodes := #[n1] }
    return (g, n1, n2))
  let ((), a) ← LayeredM.run (runProc (GraphTransformer.processor .toInternalLtr) g) a0
  -- hand: offset = max(10, 45) - 2 = 43
  checkEq "hand: zero-width graph, n1 x = 43 - 10 - 0 (mirrored once)" (a.node n1).position ⟨33, 0⟩
  checkEq "hand: zero-width graph, n2 x = 43 - 10 - 30" (a.node n2).position ⟨3, 0⟩
  checkEq "processor name" (GraphTransformer.processor .toInternalLtr).name "GraphTransformer"
  checkEq "mode debug name" GraphTransformer.Mode.toInputDirection.debugName "ToInputDirection"
  let pre ← IntermediateProcessorStrategy.create .directionPreprocessor
  let post ← IntermediateProcessorStrategy.create .directionPostprocessor
  checkEq "registered pre/post processors" (pre.name, post.name) ("GraphTransformer", "GraphTransformer")
  check "transpose port side maps UNDEFINED to UNDEFINED" (GraphTransformer.transposePortSide .undefined == .undefined)
  checkEq "transposeNodeLabelPlacement keeps an unset placement"
    ((GraphTransformer.transposeNodeLabelPlacement {}).has LayeredOptions.NODE_LABELS_PLACEMENT) false

/-! ## AlternatingLayerUnzipper -/

/-- An edge between fresh ports of `s` (east) and `t` (west). -/
def mkEdge (s t : LNodeId) : LayeredM LEdgeId := do
  let ps ← LayeredM.createPort ((({} : LPort)).setSide .east)
  LayeredM.setPortNode ps (some s)
  let pt ← LayeredM.createPort ((({} : LPort)).setSide .west)
  LayeredM.setPortNode pt (some t)
  let e ← LayeredM.createEdge
  LayeredM.setEdgeSource e (some ps)
  LayeredM.setEdgeTarget e (some pt)
  return e

/-- A graph with the given layers of fresh `(30,30)` nodes. -/
def mkLayered (counts : Array Nat) : LayeredM (LGraphId × Array LayerId × Array (Array LNodeId)) := do
  let g ← LayeredM.createGraph
  let mut layers := #[]
  let mut nodes := #[]
  for c in counts do
    let l ← LayeredM.createLayer g
    layers := layers.push l
    let mut ns := #[]
    for _ in [0:c] do
      let n ← LayeredM.createNode g { size := ⟨30, 30⟩ }
      LayeredM.setNodeLayer n (some l)
      ns := ns.push n
    nodes := nodes.push ns
  LayeredM.modifyGraph g fun gr => { gr with layers := layers }
  return (g, layers, nodes)

/-- The nodes of every layer of `g`. -/
def layerNodes (a : LGraphArena) (g : LGraphId) : Array (Array LNodeId) := a.graphToNodeArray g

def unzipperExactlyEnough : Suite := suite "layered.intermediate.alternatingLayerUnzipper.exactlyEnough" do
  -- Rust `exactly_enough_nodes_fill_all_sublayers`
  for split in #[(2 : Int), 3, 4] do
    for count in #[split - 1, split] do
      let ((g, _, nodes), a0) ← LayeredM.run (mkLayered #[count.toNat])
      let ns := nodes[0]!
      let ((), a0) ← LayeredM.run (do for n in ns do LayeredM.setNodeProp n LayeredOptions.LAYER_UNZIPPING_LAYER_SPLIT split) a0
      let ((), a) ← LayeredM.run (runProc AlternatingLayerUnzipper.processor g) a0
      checkEq s!"exactly_enough_nodes_fill_all_sublayers: layer count (split {split}, count {count})"
        (a.graph g).layers.size (if count == split then split.toNat else 1)
      if count == split then
        let distinct := (List.range (ns.size - 1)).all fun i => (a.node ns[i]!).layer != (a.node ns[i + 1]!).layer
        check s!"exactly_enough_nodes_fill_all_sublayers: neighbours in different layers (split {split})" distinct
        check s!"placeholders removed (split {split})" ((layerNodes a g).all fun l => l.size == 1)

def unzipperTwoSplit : Suite := suite "layered.intermediate.alternatingLayerUnzipper.twoSplit" do
  -- like Rust `simple_two_split`: source S, middle M0..M2 (split 2 on M0), sink T
  let ((g, es, s, ms, t), a0) ← LayeredM.run (do
    let (g, _, nodes) ← mkLayered #[1, 3, 1]
    let s := nodes[0]![0]!
    let ms := nodes[1]!
    let t := nodes[2]![0]!
    LayeredM.setNodeProp ms[0]! LayeredOptions.LAYER_UNZIPPING_LAYER_SPLIT (2 : Int)
    let mut es := #[]
    for m in ms do es := es.push (← mkEdge s m)
    for m in ms do es := es.push (← mkEdge m t)
    return (g, es, s, ms, t))
  let ((), a) ← LayeredM.run (runProc AlternatingLayerUnzipper.processor g) a0
  let ls := layerNodes a g
  checkEq "hand: four layers" ls.size 4
  checkEq "hand: layer 0 = [S]" ls[0]! #[s]
  checkEq "hand: layer 3 = [T]" ls[3]! #[t]
  let l1 := ls[1]!
  let l2 := ls[2]!
  -- hand: L1 = [M0, D(S->M1), M2], new layer = [D(M0->T), M1, D(M2->T)]
  checkEq "hand: layer 1 keeps M0 and M2 around the dummy" (l1[0]!, l1[2]!) (ms[0]!, ms[2]!)
  checkEq "hand: new layer holds M1 in the middle" l2[1]! ms[1]!
  check "hand: the other nodes are long edge dummies"
    (#[l1[1]!, l2[0]!, l2[2]!].all fun n => (a.node n).type == .longEdge)
  let d1 := l1[1]!
  checkEq "hand: dummy origin is the split edge S->M1" (a.node d1).internal.origin.isSome true
  check "hand: dummy origin S->M1" (match (a.node d1).internal.origin with | some (.lEdge e) => e == es[1]! | _ => false)
  checkEq "hand: S->M1 now ends at the dummy" ((a.edge es[1]!).target.bind fun p => (a.port p).owner) (some d1)
  checkEq "hand: long edge source = S's port" (a.node d1).internal.longEdgeSource (a.edge es[1]!).source
  checkEq "hand: dummy has a west input and an east output port"
    ((a.node d1).ports.map fun p => (a.port p).side) #[PortSide.west, .east]
  checkEq "hand: dummy height = edge thickness 1" (a.node d1).size.y 1.0
  check "hand: PORT_CONSTRAINTS FIXED_POS on the dummy"
    ((a.node d1).props.getD LayeredOptions.PORT_CONSTRAINTS .undefined == .fixedPos)
  let d0 := l2[0]!
  checkEq "hand: M0->T split by a dummy in the new layer" ((a.edge es[3]!).target.bind fun p => (a.port p).owner) (some d0)
  checkEq "hand: long edge target of D(M0->T) = T's port" (a.node d0).internal.longEdgeTarget (some (a.node t).ports[0]!)

def unzipperExtraEdge : Suite := suite "layered.intermediate.alternatingLayerUnzipper.extraEdge" do
  -- like Rust `multiple_outgoing_edges`: A has two outgoing edges, B none
  let ((g, a', b', t), a0) ← LayeredM.run (do
    let (g, _, nodes) ← mkLayered #[2, 1]
    let a := nodes[0]![0]!
    let b := nodes[0]![1]!
    let t := nodes[1]![0]!
    LayeredM.setNodeProp a LayeredOptions.LAYER_UNZIPPING_LAYER_SPLIT (2 : Int)
    let _ ← mkEdge a t
    let _ ← mkEdge a t
    return (g, a, b, t))
  let ((), a) ← LayeredM.run (runProc AlternatingLayerUnzipper.processor g) a0
  let ls := layerNodes a g
  -- hand: L0 = [A] (placeholders removed), new layer = [D1, D2, B], L2 = [T]
  checkEq "hand: three layers" ls.size 3
  checkEq "hand: layer 0 = [A]" ls[0]! #[a']
  checkEq "hand: new layer size" ls[1]!.size 3
  checkEq "hand: B last in the new layer" ls[1]![2]! b'
  checkEq "hand: layer 2 = [T]" ls[2]! #[t]
  check "hand: no placeholder left in a layer"
    (ls.all fun l => l.all fun n => (a.node n).type != .placeholder && (a.node n).type != .nonshiftingPlaceholder)
  check "hand: removed placeholders have no layer"
    (a.nodes.all fun nd => !(nd.type == .placeholder || nd.type == .nonshiftingPlaceholder) || nd.layer.isNone)

def unzipperHeuristic : Suite := suite "layered.intermediate.alternatingLayerUnzipper.minimizeEdgeLength" do
  let setSpacings (g : LGraphId) : LayeredM Unit := do
    LayeredM.setGraphProp g LayeredOptions.SPACING_EDGE_NODE_BETWEEN_LAYERS 10.0
    LayeredM.setGraphProp g LayeredOptions.SPACING_EDGE_EDGE_BETWEEN_LAYERS 10.0
    LayeredM.setGraphProp g LayeredOptions.SPACING_NODE_NODE_BETWEEN_LAYERS 20.0
    LayeredM.setGraphProp g LayeredOptions.SPACING_NODE_NODE 20.0
    LayeredM.setGraphProp g LayeredOptions.SPACING_EDGE_NODE 10.0
  -- hand: 2 nodes (30x30): (30 + max(20, max(20, 20))) / (30 + 20) = 1 >= 2/4 -> not split
  let (g, a0) ← LayeredM.run (do
    let (g, _, nodes) ← mkLayered #[2]
    setSpacings g
    LayeredM.setNodeProp nodes[0]![0]! LayeredOptions.LAYER_UNZIPPING_MINIMIZE_EDGE_LENGTH true
    return g)
  let ((), a) ← LayeredM.run (runProc AlternatingLayerUnzipper.processor g) a0
  checkEq "hand: wide layer is not split" (a.graph g).layers.size 1
  -- hand: 8 nodes (10x30): (10 + max(20, max(80, 20))) / 50 = 1.8 < 8/4 -> split
  let (g2, b0) ← LayeredM.run (do
    let (g, _, nodes) ← mkLayered #[8]
    setSpacings g
    for n in nodes[0]! do LayeredM.modifyNode n fun x => { x with size := ⟨10, 30⟩ }
    LayeredM.setNodeProp nodes[0]![0]! LayeredOptions.LAYER_UNZIPPING_MINIMIZE_EDGE_LENGTH true
    return g)
  let ((), b) ← LayeredM.run (runProc AlternatingLayerUnzipper.processor g2) b0
  checkEq "hand: tall layer is split into 2" ((layerNodes b g2).map (·.size)) #[4, 4]
  -- split value 1 and 0: nothing changes
  let (g3, c0) ← LayeredM.run (do
    let (g, _, nodes) ← mkLayered #[3]
    LayeredM.setNodeProp nodes[0]![0]! LayeredOptions.LAYER_UNZIPPING_LAYER_SPLIT (0 : Int)
    return g)
  let ((), c) ← LayeredM.run (runProc AlternatingLayerUnzipper.processor g3) c0
  checkEq "split value 0 is skipped (Rust n <= 0)" ((layerNodes c g3).map (·.size)) #[3]
  checkEq "registered unzipper" (← IntermediateProcessorStrategy.create .alternatingLayerUnzipper).name "AlternatingLayerUnzipper"

/-! ## SemiInteractiveCrossMinProcessor -/

def semiInteractive : Suite := suite "layered.intermediate.semiInteractiveCrossMin" do
  let ((g, ns), a0) ← LayeredM.run (do
    let (g, _, nodes) ← mkLayered #[5]
    let ns := nodes[0]!
    LayeredM.setNodeProp ns[0]! LayeredOptions.POSITION ⟨0, 30⟩
    -- ns[1] has no POSITION
    LayeredM.setNodeProp ns[2]! LayeredOptions.POSITION ⟨0, 5⟩
    LayeredM.modifyNode ns[2]! fun x => { x with type := .longEdge }
    LayeredM.setNodeProp ns[3]! LayeredOptions.POSITION ⟨0, 10⟩
    LayeredM.setNodeProp ns[4]! LayeredOptions.POSITION ⟨0, 30⟩
    return (g, ns))
  let ((), a) ← LayeredM.run (runProc SemiInteractiveCrossMinProcessor.processor g) a0
  -- hand: normal positioned nodes sorted by y (stable): n3 (10), n0 (30), n4 (30)
  checkEq "hand: n3 -> n0" (a.node ns[3]!).internal.inLayerSuccessorConstraints #[ns[0]!]
  checkEq "hand: n0 -> n4 (stable for equal y)" (a.node ns[0]!).internal.inLayerSuccessorConstraints #[ns[4]!]
  checkEq "hand: last node has no successor" (a.node ns[4]!).internal.inLayerSuccessorConstraints #[]
  checkEq "hand: dummy and unpositioned nodes untouched"
    ((a.node ns[1]!).internal.inLayerSuccessorConstraints.size + (a.node ns[2]!).internal.inLayerSuccessorConstraints.size) 0
  checkEq "hand: graph flag set" (a.graph g).internal.inLayerSuccessorConstraintsBetweenNonDummies true
  -- one positioned node only: Rust adds no constraint and leaves the flag unset (Java would set it)
  let (g2, b0) ← LayeredM.run (do
    let (g, _, nodes) ← mkLayered #[2]
    LayeredM.setNodeProp nodes[0]![0]! LayeredOptions.POSITION ⟨0, 1⟩
    return g)
  let ((), b) ← LayeredM.run (runProc SemiInteractiveCrossMinProcessor.processor g2) b0
  checkEq "hand: single positioned node leaves the flag unset" (b.graph g2).internal.inLayerSuccessorConstraintsBetweenNonDummies false
  checkEq "registered semi-interactive processor"
    (← IntermediateProcessorStrategy.create .semiInteractiveCrossminProcessor).name "SemiInteractiveCrossMinProcessor"

def suites : Array Suite :=
  #[transformerLeft, transformerDown, transformerUp, transformerRotation, transformerRoundTrips, transformerMisc,
    unzipperExactlyEnough, unzipperTwoSplit, unzipperExtraEdge, unzipperHeuristic, semiInteractive]

end Tests.Layered.IntermediateTransform
