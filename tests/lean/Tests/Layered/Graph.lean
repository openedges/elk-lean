import Tests.Framework
import Elk.Alg.Layered
/-! Tests of `org.eclipse.elk.alg.layered.graph`: arena relations, queries, Tarjan and the trace recorder. -/
namespace Tests.Layered.Graph

open Tests Elk.Graph Elk.Core.Math Elk.Core.Options Elk.Json Elk.Alg.Layered Elk.Alg.Layered.Graph Elk.Alg.Layered.Options

/-- A graph with two layers, three nodes, ports and two edges plus one layerless node. -/
def buildSample : LayeredM (LGraphId × Array LNodeId × Array LPortId × Array LEdgeId) := do
  let g ← LayeredM.createGraph
  let l0 ← LayeredM.createLayer g
  let l1 ← LayeredM.createLayer g
  LayeredM.modifyGraph g fun x => { x with layers := #[l0, l1], padding := ⟨12, 10, 8, 6⟩, size := ⟨100, 50⟩ }
  let n0 ← LayeredM.createNode g { size := ⟨30, 20⟩, position := ⟨1, 2⟩ }
  let n1 ← LayeredM.createNode g { size := ⟨40, 25⟩ }
  let n2 ← LayeredM.createNode g { size := ⟨10, 10⟩, type := .longEdge }
  let n3 ← LayeredM.createNode g { size := ⟨5, 5⟩ }
  LayeredM.setNodeLayer n0 (some l0)
  LayeredM.setNodeLayer n1 (some l1)
  LayeredM.setNodeLayer n2 (some l1)
  LayeredM.modifyGraph g fun x => { x with layerlessNodes := #[n3] }
  let p0 ← LayeredM.createPort { side := .east, size := ⟨4, 4⟩ }
  let p1 ← LayeredM.createPort { side := .west }
  let p2 ← LayeredM.createPort { side := .west }
  LayeredM.setPortNode p0 (some n0)
  LayeredM.setPortNode p1 (some n1)
  LayeredM.setPortNode p2 (some n2)
  let e0 ← LayeredM.createEdge { id := 7 }
  let e1 ← LayeredM.createEdge { id := 8, bendPoints := #[⟨3, 4⟩] }
  LayeredM.setEdgeSource e0 (some p0)
  LayeredM.setEdgeTarget e0 (some p1)
  LayeredM.setEdgeSource e1 (some p0)
  LayeredM.setEdgeTarget e1 (some p2)
  let lb ← LayeredM.createLabel "A"
  LayeredM.modifyNode n0 fun x => { x with labels := #[lb] }
  return (g, #[n0, n1, n2, n3], #[p0, p1, p2], #[e0, e1])

def arenaTests : Suite := suite "layered.graph.arena" do
  let ((g, nodes, ports, edges), a) ← LayeredM.run buildSample
  let n0 := nodes[0]!; let n1 := nodes[1]!; let n2 := nodes[2]!
  let p0 := ports[0]!; let p1 := ports[1]!; let p2 := ports[2]!
  let e0 := edges[0]!; let e1 := edges[1]!
  checkEq "layer 0 nodes" (a.layer (a.graph g).layers[0]!).nodes #[n0]
  checkEq "layer 1 nodes" (a.layer (a.graph g).layers[1]!).nodes #[n1, n2]
  checkEq "node layer index" (a.nodeIndex n2) (some 1)
  checkEq "layer index" (a.layerIndex (a.graph g).layers[1]!) (some 1)
  checkEq "node graph via stored graph" (a.nodeGraph n0) (some g)
  checkEq "port owner" (a.port p0).owner (some n0)
  checkEq "owner ports" (a.node n0).ports #[p0]
  checkEq "outgoing edges of p0" (a.port p0).outgoingEdges #[e0, e1]
  checkEq "incoming edges of p1" (a.port p1).incomingEdges #[e0]
  checkEq "node outgoing edges" (a.nodeOutgoingEdges n0) #[e0, e1]
  checkEq "node incoming edges" (a.nodeIncomingEdges n2) #[e1]
  checkEq "ports by type input" (a.nodePortsByType n1 .input) #[p1]
  checkEq "ports by type output on n1" (a.nodePortsByType n1 .output) #[]
  checkEq "ports by side" (a.nodePortsBySide n0 .east) #[p0]
  checkEq "predecessor ports" (a.portPredecessorPorts p2) #[p0]
  checkEq "successor ports" (a.portSuccessorPorts p0) #[p1, p2]
  checkEq "port index" (a.portIndex p0) (some 0)
  checkEq "edge other port" (a.edgeOtherPort e0 p0) (some p1)
  checkEq "edge other node" (a.edgeOtherNode e1 n2) (some n0)
  check "not a self loop" (!a.edgeIsSelfLoop e0)
  check "in-layer edge (n1,n2 same layer? no: n0->n1 differ)" (!a.edgeIsInLayerEdge e0)
  checkEq "absolute anchor" (a.portAbsoluteAnchor p0) (some ⟨1, 2⟩)
  checkEq "node designation = label text" (a.nodeDesignation n0) "A"
  checkEq "node toString with type" (a.nodeToString n2) "n(long_edge)_1"
  checkEq "port toString" (a.portToString p1) "p_0[n_0] << 0[n_A]"
  checkEq "edge toString" (a.edgeToString e0) "e_ 0[n_A] -> 0[n_0]"
  checkEq "layer toString" (a.layerToString (a.graph g).layers[1]!) "L_1[n_0, n(long_edge)_1]"
  checkEq "graph toString" (a.graphToString g) "G[layerless[n_-1], layers[L_0[n_A], L_1[n_0, n(long_edge)_1]]]"
  checkEq "actual size (width + left + right, height + top + bottom)" (a.graph g).actualSize ⟨116, 70⟩
  -- relation changes
  let ((), a2) ← LayeredM.run (do
      LayeredM.setNodeLayer n0 (some (a.graph g).layers[1]!)
      LayeredM.setPortNode p0 (some n1)
      LayeredM.setEdgeTarget e0 (some p2)
      LayeredM.setEdgeSource e1 none) a
  checkEq "moved node leaves layer 0" (a2.layer (a2.graph g).layers[0]!).nodes #[]
  checkEq "moved node appended to layer 1" (a2.layer (a2.graph g).layers[1]!).nodes #[n1, n2, n0]
  checkEq "port moved to n1" (a2.node n1).ports #[p1, p0]
  checkEq "old owner lost the port" (a2.node n0).ports #[]
  checkEq "edge retarget updates incoming lists" ((a2.port p1).incomingEdges, (a2.port p2).incomingEdges) (#[], #[e1, e0])
  checkEq "edge source cleared" ((a2.edge e1).source, (a2.port p0).outgoingEdges) (none, #[e0])
  -- setLayer at index + bounds check
  let ((), a3) ← LayeredM.run (LayeredM.setNodeLayerAtIndex n0 0 (some (a.graph g).layers[1]!)) a
  checkEq "insert at index 0" (a3.layer (a3.graph g).layers[1]!).nodes #[n0, n1, n2]
  checkThrows "index out of bounds throws" (do let _ ← LayeredM.run (LayeredM.setNodeLayerAtIndex n0 5 (some (a.graph g).layers[1]!)) a; pure ())
  -- port side cache
  let ((view, cachedView), _) ← LayeredM.run (do
      let before ← LayeredM.withArena (·.nodePortSideView n0 .east)
      LayeredM.cachePortSides n0
      let after ← LayeredM.withArena (·.nodePortSideView n0 .east)
      return (before, after)) a
  checkEq "port side view uncached" view #[p0]
  checkEq "port side view cached" cachedView #[p0]

def tarjanTests : Suite := suite "layered.graph.Tarjan" do
  -- a 3-cycle n0 -> n1 -> n2 -> n0 plus an isolated n3; edge e2 reversed by the cycle breaker candidate list
  let ((g, nodes, result), _) ← LayeredM.run (do
      let g ← LayeredM.createGraph
      let mut ns : Array LNodeId := #[]
      for _ in [0:4] do ns := ns.push (← LayeredM.createNode g)
      LayeredM.modifyGraph g fun x => { x with layerlessNodes := ns }
      let mkEdge (s t : LNodeId) : LayeredM LEdgeId := do
        let ps ← LayeredM.createPort
        let pt ← LayeredM.createPort
        LayeredM.setPortNode ps (some s)
        LayeredM.setPortNode pt (some t)
        let e ← LayeredM.createEdge
        LayeredM.setEdgeSource e (some ps)
        LayeredM.setEdgeTarget e (some pt)
        return e
      let _ ← mkEdge ns[0]! ns[1]!
      let _ ← mkEdge ns[1]! ns[2]!
      let _ ← mkEdge ns[2]! ns[0]!
      let (_, t) ← Tarjan.run (Tarjan.tarjan g) (Tarjan.new #[])
      return (g, ns, t))
  checkEq "one scc" result.stronglyConnectedComponents.size 1
  checkEq "scc members (stack pop order)" result.stronglyConnectedComponents[0]! #[nodes[2]!, nodes[1]!, nodes[0]!]
  checkEq "scc id lookup" (result.nodeToSccId.get? nodes[1]!) (some 0)
  checkEq "isolated node not in a scc" (result.nodeToSccId.get? nodes[3]!) none
  let _ := g

def traceTests : Suite := suite "layered.graph.TraceRecorder" do
  let ((g, _, _, _), a) ← LayeredM.run buildSample
  let v := TraceRecorder.snapshot a g 3 "org::x::PortSideProcessor"
  checkEq "step" (v.get? "step") (some (Value.ofNat 3))
  checkEq "processor" (v.get? "processor") (some (.str "org::x::PortSideProcessor"))
  checkEq "layers count" ((v.get? "layers").bind fun x => match x with | .arr xs => some xs.size | _ => none) (some 2)
  checkEq "layerless nodes" ((v.get? "nodes").bind fun x => match x with | .arr xs => some xs.size | _ => none) (some 1)
  checkEq "edges" ((v.get? "edges").bind fun x => match x with | .arr xs => some xs.size | _ => none) (some 2)
  checkEq "first layer node id" (v.getAt [.key "layers", .idx 0, .key "nodes", .idx 0, .key "id"]) (some (.str "N0"))
  checkEq "layerless node id follows layer nodes" (v.getAt [.key "nodes", .idx 0, .key "id"]) (some (.str "N3"))
  checkEq "edge id uses the element id" (v.getAt [.key "edges", .idx 0, .key "id"]) (some (.str "E7"))
  checkEq "edge endpoints" (v.getAt [.key "edges", .idx 0, .key "targetPort"]) (some (.str "P1"))
  checkEq "graph size includes padding" (v.getAt [.key "graphSize", .key "width"]) (some (Value.ofFloat 116))
  checkEq "layer index of a layered node" (v.getAt [.key "layers", .idx 1, .key "nodes", .idx 1, .key "layer"]) (some (Value.ofNat 1))
  checkEq "layerless node layer -1" (v.getAt [.key "nodes", .idx 0, .key "layer"]) (some (Value.ofInt (-1)))
  checkEq "port side string" (v.getAt [.key "layers", .idx 0, .key "nodes", .idx 0, .key "ports", .idx 0, .key "side"]) (some (.str "EAST"))
  checkEq "file name" (TraceRecorder.fileName 7 "org::x::Foo Bar") "step_007_Foo_Bar.json"
  checkEq "file name 3 digits" (TraceRecorder.fileName 123 "A") "step_123_A.json"
  let rendered := TraceRecorder.render (.obj #[("b", TraceRecorder.numberOrSpecial (0.0 / 0.0)), ("a", TraceRecorder.numberOrSpecial (1.0 / 0.0)), ("c", TraceRecorder.numberOrSpecial 2.5)])
  checkEq "sentinels and sorted keys" rendered "{\n  \"a\": Infinity,\n  \"b\": NaN,\n  \"c\": 2.5\n}"

def suites : Array Suite := #[arenaTests, tarjanTests, traceTests]

end Tests.Layered.Graph
