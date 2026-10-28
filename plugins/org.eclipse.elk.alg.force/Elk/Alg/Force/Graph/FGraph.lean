import Elk.Graph
import Elk.Core.Math.KVector
import Elk.Core.Math.ElkMath
import Elk.Core.Util.Random
import Elk.Alg.Force.Graph.FArena
import Elk.Alg.Force.Options.ForceOptions
/-!
# `org.eclipse.elk.alg.force.graph.FGraph`

Port of `f_graph.rs` (elk-rs): the force graph, an `FArena` plus the ordered lists of its nodes,
edges, labels and bend points, the graph's own option map and the adjacency matrix used by the force
models. The internal properties `ORIGIN`, `RANDOM`, `BB_UPLEFT` and `BB_LOWRIGHT` are typed fields
(see `Options.InternalProperties`).

Algorithms run in `FM := StateRefT FGraph IO`; the pure operations below take and return the graph.
The geometry helpers (`edgeSourcePoint`, `distributeBendpoints`, `refreshLabelPosition`, ...) only touch
the arena and are defined on `FArena` so that updates stay in place.
-/
/-! Float literals as global constants (FL): inside branches, loops and specialised code the compiler
shares a literal's `Nat`/`Bool` arguments with unrelated variables (CSE) and then parses it on every
evaluation (`FastFloat.ofScientificImpl`); a top-level constant is a load (PLAN §7.1 items 17, 22). -/
private def fl0p0 : Float := 0.0
private def fl0p5 : Float := 0.5
private def fl2p0 : Float := 2.0

namespace Elk.Alg.Force.Graph

open Elk.Graph Elk.Core.Math Elk.Core.Util Elk.Alg.Force.Options

/-! ### Geometry helpers (`FGraph::edge_source_point` etc.) -/

namespace FArena

/-- `FGraph::edge_source_point`: where the edge leaves the source node (centre line clipped at the
source's box), or `none` if an end point is missing. -/
def edgeSourcePoint (a : FArena) (e : FEdgeId) : Option KVector := do
  let s ← a.edgeSource[e.idx]!
  let t ← a.edgeTarget[e.idx]!
  let sourcePos := a.nodePosition[s.idx]!
  let sourceSize := a.nodeSize[s.idx]!
  let targetPos := a.nodePosition[t.idx]!
  let v := ElkMath.clipVector (targetPos - sourcePos) sourceSize.x sourceSize.y
  return v + sourcePos

/-- `FGraph::edge_target_point`: where the edge enters the target node. -/
def edgeTargetPoint (a : FArena) (e : FEdgeId) : Option KVector := do
  let s ← a.edgeSource[e.idx]!
  let t ← a.edgeTarget[e.idx]!
  let sourcePos := a.nodePosition[s.idx]!
  let targetPos := a.nodePosition[t.idx]!
  let targetSize := a.nodeSize[t.idx]!
  let v := ElkMath.clipVector (sourcePos - targetPos) targetSize.x targetSize.y
  return v + targetPos

/-- `FGraph::edge_to_vector_chain`: source point, bend points, target point. -/
def edgeToVectorChain (a : FArena) (e : FEdgeId) : Option KVectorChain := do
  let source ← a.edgeSourcePoint e
  let target ← a.edgeTargetPoint e
  let bends := (a.edgeBendpoints[e.idx]!).map fun b => a.bendPosition[b.idx]!
  return #[source] ++ bends ++ #[target]

/-- `FGraph::distribute_bendpoints`: spreads the bend points of the edge evenly on the straight line
between the centres of its end nodes. -/
def distributeBendpoints (a : FArena) (e : FEdgeId) : FArena := Id.run do
  let bends := a.edgeBendpoints[e.idx]!
  let count := bends.size
  if count == 0 then return a
  let (some s, some t) := (a.edgeSource[e.idx]!, a.edgeTarget[e.idx]!) | return a
  let sourcePos := a.nodePosition[s.idx]!
  let targetPos := a.nodePosition[t.idx]!
  let incr := (targetPos - sourcePos).scale (1.0 / (count + 1).toFloat)
  let mut pos := sourcePos
  let mut a := a
  for bid in bends do
    a := { a with bendPosition := a.bendPosition.set! bid.idx ⟨pos.x + incr.x, pos.y + incr.y⟩ }
    pos := pos + incr
  return a

/-- `FGraph::refresh_label_position`: places an edge label on the connection of its edge's end nodes
(centred when `EDGE_LABELS_INLINE`, otherwise beside the edge's midpoint). -/
def refreshLabelPosition (a : FArena) (l : FLabelId) : FArena := Id.run do
  let some e := a.labelEdge[l.idx]! | return a
  let placeInline := (a.labelProperties[l.idx]!).getD ForceOptions.EDGE_LABELS_INLINE false
  let (some s, some t) := (a.edgeSource[e.idx]!, a.edgeTarget[e.idx]!) | return a
  let src := a.nodePosition[s.idx]!
  let tgt := a.nodePosition[t.idx]!
  let size := a.labelSize[l.idx]!
  if placeInline then
    let srcToTgt := (tgt - src).scale fl0p5
    let toLabelCenter := size.scale fl0p5
    let newPos := (src + srcToTgt) - toLabelCenter
    return { a with labelPosition := a.labelPosition.set! l.idx newPos }
  let spacing := (a.edgeProperties[e.idx]!).getD ForceOptions.SPACING_EDGE_LABEL fl0p0
  let pos : KVector :=
    if src.x >= tgt.x then
      if src.y >= tgt.y then
        ⟨tgt.x + ((src.x - tgt.x) / fl2p0) + spacing, tgt.y + ((src.y - tgt.y) / fl2p0) - spacing - size.y⟩
      else
        ⟨tgt.x + ((src.x - tgt.x) / fl2p0) + spacing, src.y + ((tgt.y - src.y) / fl2p0) + spacing⟩
    else if src.y >= tgt.y then
      ⟨src.x + ((tgt.x - src.x) / fl2p0) + spacing, tgt.y + ((src.y - tgt.y) / fl2p0) + spacing⟩
    else
      ⟨src.x + ((tgt.x - src.x) / fl2p0) + spacing, src.y + ((tgt.y - src.y) / fl2p0) - spacing - size.y⟩
  return { a with labelPosition := a.labelPosition.set! l.idx pos }

end FArena

/-- `FGraph`. -/
structure FGraph where
  arena : FArena := {}
  nodes : Array FNodeId := #[]
  edges : Array FEdgeId := #[]
  labels : Array FLabelId := #[]
  bendpoints : Array FBendpointId := #[]
  /-- The graph's option map (copied from the `ElkGraph` root). -/
  props : PropertyMap := {}
  /-- `InternalProperties.ORIGIN` of the graph. -/
  origin : Option Origin := none
  /-- `InternalProperties.RANDOM`. -/
  random : Option Random := none
  /-- `InternalProperties.BB_UPLEFT`. -/
  bbUpleft : Option KVector := none
  /-- `InternalProperties.BB_LOWRIGHT`. -/
  bbLowright : Option KVector := none
  /-- `adjacency[i][j]`: summed edge priorities from node id `i` to node id `j`. -/
  adjacency : Array (Array Int) := #[]
  deriving Inhabited

/-- The algorithm monad of the force algorithms: the force graph as mutable state. -/
abbrev FM := StateRefT FGraph IO

namespace FGraph

/-- `copy_properties(other)`: `putAll` of the option map and of the internal properties that are set
in `other`. -/
def copyProperties (g other : FGraph) : FGraph :=
  { g with
    props := g.props.copyFrom other.props
    origin := other.origin.orElse fun _ => g.origin
    random := other.random.orElse fun _ => g.random
    bbUpleft := other.bbUpleft.orElse fun _ => g.bbUpleft
    bbLowright := other.bbLowright.orElse fun _ => g.bbLowright }

/-- `FGraph::particle_ids`: the nodes, then the labels, then the bend points of the graph lists. -/
def particleIds (g : FGraph) : Array FParticleId := Id.run do
  let mut ids : Array FParticleId := Array.mkEmpty (g.nodes.size + g.labels.size + g.bendpoints.size)
  for n in g.nodes do ids := ids.push (.node n)
  for l in g.labels do ids := ids.push (.label l)
  for b in g.bendpoints do ids := ids.push (.bend b)
  return ids

/-- `FGraph::get_connection`: the connection weight of two particles; summed adjacency (both
directions) for two nodes, the edge's priority for two bend points of the same edge, otherwise 0. -/
def getConnection (g : FGraph) (p1 p2 : FParticleId) : Int :=
  match p1, p2 with
  | .node n1, .node n2 =>
    let id1 := g.arena.nodeId[n1.idx]!
    let id2 := g.arena.nodeId[n2.idx]!
    if id1 >= g.adjacency.size || id2 >= g.adjacency.size then 0
    else (g.adjacency[id1]!)[id2]! + (g.adjacency[id2]!)[id1]!
  | .bend b1, .bend b2 =>
    match g.arena.bendEdge[b1.idx]!, g.arena.bendEdge[b2.idx]! with
    | some e1, some e2 =>
      if e1 == e2 then (g.arena.edgeProperties[e1.idx]!).getD ForceOptions.PRIORITY 1 else 0
    | _, _ => 0
  | _, _ => 0

/-- `FGraph::calc_adjacency`: the adjacency matrix indexed by node ids, entries are summed edge
priorities (default priority 1) from source id to target id. -/
def calcAdjacency (g : FGraph) : FGraph := Id.run do
  let n := g.nodes.size
  let mut adjacency : Array (Array Int) := Array.replicate n (Array.replicate n 0)
  for eid in g.edges do
    let sourceId := (g.arena.edgeSource[eid.idx]!).map fun nid => g.arena.nodeId[nid.idx]!
    let targetId := (g.arena.edgeTarget[eid.idx]!).map fun nid => g.arena.nodeId[nid.idx]!
    let priority := (g.arena.edgeProperties[eid.idx]!).getD ForceOptions.PRIORITY 1
    if let (some sid, some tid) := (sourceId, targetId) then
      if sid < n && tid < n then
        adjacency := adjacency.modify sid (·.modify tid (· + priority))
  return { g with adjacency }

/-- `FGraph::edge_source_point`. -/
def edgeSourcePoint (g : FGraph) (e : FEdgeId) : Option KVector := g.arena.edgeSourcePoint e

/-- `FGraph::edge_target_point`. -/
def edgeTargetPoint (g : FGraph) (e : FEdgeId) : Option KVector := g.arena.edgeTargetPoint e

/-- `FGraph::edge_to_vector_chain`. -/
def edgeToVectorChain (g : FGraph) (e : FEdgeId) : Option KVectorChain := g.arena.edgeToVectorChain e

/-- `FGraph::distribute_bendpoints`. -/
def distributeBendpoints (g : FGraph) (e : FEdgeId) : FGraph :=
  { g with arena := g.arena.distributeBendpoints e }

/-- `FGraph::refresh_label_position`. -/
def refreshLabelPosition (g : FGraph) (l : FLabelId) : FGraph :=
  { g with arena := g.arena.refreshLabelPosition l }

end FGraph

end Elk.Alg.Force.Graph
