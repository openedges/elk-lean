import Elk.Graph
import Elk.Core.Math.KVector
import Elk.Alg.Force.Options.InternalProperties
/-!
# `org.eclipse.elk.alg.force.graph.{FNode, FEdge, FLabel, FBendpoint, FParticle}` (arena)

Port of `f_arena.rs` (elk-rs): the elements of the force graph live in struct-of-arrays storage and
are referenced by typed ids. Java's `FParticle` base class (position, size, displacement, properties,
radius) is the `FParticleId` sum type: a particle is a node, a label or a bend point.

Rust `MapPropertyHolder`s are `PropertyMap`s; the `ORIGIN` internal property is the typed
`*Origin` array (see `Options.InternalProperties`). The unused placeholder `FArena::get_connection`
of Rust (it always returns 0, the real one is `FGraph::get_connection`) is not ported.
-/
namespace Elk.Alg.Force.Graph

open Elk.Graph Elk.Core.Math Elk.Alg.Force.Options

/-- Index of an `FNode` in `FArena.node*`. -/
structure FNodeId where
  idx : Nat
  deriving BEq, Hashable, Repr, Inhabited, DecidableEq

/-- Index of an `FEdge` in `FArena.edge*`. -/
structure FEdgeId where
  idx : Nat
  deriving BEq, Hashable, Repr, Inhabited, DecidableEq

/-- Index of an `FLabel` in `FArena.label*`. -/
structure FLabelId where
  idx : Nat
  deriving BEq, Hashable, Repr, Inhabited, DecidableEq

/-- Index of an `FBendpoint` in `FArena.bend*`. -/
structure FBendpointId where
  idx : Nat
  deriving BEq, Hashable, Repr, Inhabited, DecidableEq

/-- `FParticle`: a node, a label or a bend point. -/
inductive FParticleId where
  | node (n : FNodeId)
  | label (l : FLabelId)
  | bend (b : FBendpointId)
  deriving BEq, Hashable, Repr, Inhabited, DecidableEq

/-- Struct-of-arrays storage of all force graph elements (elk-rs `FArena`). -/
structure FArena where
  nodePosition : Array KVector := #[]
  nodeSize : Array KVector := #[]
  nodeDisplacement : Array KVector := #[]
  nodeProperties : Array PropertyMap := #[]
  nodeOrigin : Array (Option Origin) := #[]
  nodeId : Array Nat := #[]
  nodeLabel : Array (Option String) := #[]
  nodeParent : Array (Option FNodeId) := #[]
  nodeChildren : Array (Array FNodeId) := #[]
  edgeProperties : Array PropertyMap := #[]
  edgeOrigin : Array (Option Origin) := #[]
  edgeSource : Array (Option FNodeId) := #[]
  edgeTarget : Array (Option FNodeId) := #[]
  edgeBendpoints : Array (Array FBendpointId) := #[]
  edgeLabels : Array (Array FLabelId) := #[]
  labelPosition : Array KVector := #[]
  labelSize : Array KVector := #[]
  labelDisplacement : Array KVector := #[]
  labelProperties : Array PropertyMap := #[]
  labelOrigin : Array (Option Origin) := #[]
  labelText : Array (Option String) := #[]
  labelEdge : Array (Option FEdgeId) := #[]
  bendPosition : Array KVector := #[]
  bendSize : Array KVector := #[]
  bendDisplacement : Array KVector := #[]
  bendProperties : Array PropertyMap := #[]
  bendEdge : Array (Option FEdgeId) := #[]
  deriving Inhabited

namespace FArena

/-- `FArena::add_node`: a new node with zero geometry; its `nodeId` is its own index. -/
def addNode (a : FArena) : FArena × FNodeId :=
  let id : FNodeId := ⟨a.nodePosition.size⟩
  ({ a with
      nodePosition := a.nodePosition.push {}
      nodeSize := a.nodeSize.push {}
      nodeDisplacement := a.nodeDisplacement.push {}
      nodeProperties := a.nodeProperties.push {}
      nodeOrigin := a.nodeOrigin.push none
      nodeId := a.nodeId.push id.idx
      nodeLabel := a.nodeLabel.push none
      nodeParent := a.nodeParent.push none
      nodeChildren := a.nodeChildren.push #[] }, id)

/-- `FArena::node_count`. -/
def nodeCount (a : FArena) : Nat := a.nodePosition.size

/-- `FArena::add_edge`. -/
def addEdge (a : FArena) : FArena × FEdgeId :=
  let id : FEdgeId := ⟨a.edgeProperties.size⟩
  ({ a with
      edgeProperties := a.edgeProperties.push {}
      edgeOrigin := a.edgeOrigin.push none
      edgeSource := a.edgeSource.push none
      edgeTarget := a.edgeTarget.push none
      edgeBendpoints := a.edgeBendpoints.push #[]
      edgeLabels := a.edgeLabels.push #[] }, id)

/-- `FArena::set_edge_source`. -/
def setEdgeSource (a : FArena) (e : FEdgeId) (n : FNodeId) : FArena :=
  { a with edgeSource := a.edgeSource.set! e.idx (some n) }

/-- `FArena::set_edge_target`. -/
def setEdgeTarget (a : FArena) (e : FEdgeId) (n : FNodeId) : FArena :=
  { a with edgeTarget := a.edgeTarget.set! e.idx (some n) }

/-- `FArena::edge_count`. -/
def edgeCount (a : FArena) : Nat := a.edgeProperties.size

/-- `FArena::add_label`: a new label of the edge (also appended to `edgeLabels`). -/
def addLabel (a : FArena) (e : FEdgeId) : FArena × FLabelId :=
  let id : FLabelId := ⟨a.labelPosition.size⟩
  ({ a with
      labelPosition := a.labelPosition.push {}
      labelSize := a.labelSize.push {}
      labelDisplacement := a.labelDisplacement.push {}
      labelProperties := a.labelProperties.push {}
      labelOrigin := a.labelOrigin.push none
      labelText := a.labelText.push none
      labelEdge := a.labelEdge.push (some e)
      edgeLabels := a.edgeLabels.modify e.idx (·.push id) }, id)

/-- `FArena::label_count`. -/
def labelCount (a : FArena) : Nat := a.labelPosition.size

/-- `FArena::add_bendpoint`: a new bend point of the edge (also appended to `edgeBendpoints`). -/
def addBendpoint (a : FArena) (e : FEdgeId) : FArena × FBendpointId :=
  let id : FBendpointId := ⟨a.bendPosition.size⟩
  ({ a with
      bendPosition := a.bendPosition.push {}
      bendSize := a.bendSize.push {}
      bendDisplacement := a.bendDisplacement.push {}
      bendProperties := a.bendProperties.push {}
      bendEdge := a.bendEdge.push (some e)
      edgeBendpoints := a.edgeBendpoints.modify e.idx (·.push id) }, id)

/-- `FArena::bend_count`. -/
def bendCount (a : FArena) : Nat := a.bendPosition.size

/-- `FArena::particle_ids`: all nodes, then all labels, then all bend points of the arena. -/
def particleIds (a : FArena) : Array FParticleId := Id.run do
  let mut ids : Array FParticleId := Array.mkEmpty (a.nodeCount + a.labelCount + a.bendCount)
  for i in [0:a.nodeCount] do ids := ids.push (.node ⟨i⟩)
  for i in [0:a.labelCount] do ids := ids.push (.label ⟨i⟩)
  for i in [0:a.bendCount] do ids := ids.push (.bend ⟨i⟩)
  return ids

/-- `FArena::particle_position`. -/
def particlePosition (a : FArena) : FParticleId → KVector
  | .node n => a.nodePosition[n.idx]!
  | .label l => a.labelPosition[l.idx]!
  | .bend b => a.bendPosition[b.idx]!

/-- `FArena::particle_position_mut` as a setter. -/
def setParticlePosition (a : FArena) (p : FParticleId) (v : KVector) : FArena :=
  match p with
  | .node n => { a with nodePosition := a.nodePosition.set! n.idx v }
  | .label l => { a with labelPosition := a.labelPosition.set! l.idx v }
  | .bend b => { a with bendPosition := a.bendPosition.set! b.idx v }

/-- `FArena::particle_size`. -/
def particleSize (a : FArena) : FParticleId → KVector
  | .node n => a.nodeSize[n.idx]!
  | .label l => a.labelSize[l.idx]!
  | .bend b => a.bendSize[b.idx]!

/-- `FArena::particle_displacement`. -/
def particleDisplacement (a : FArena) : FParticleId → KVector
  | .node n => a.nodeDisplacement[n.idx]!
  | .label l => a.labelDisplacement[l.idx]!
  | .bend b => a.bendDisplacement[b.idx]!

/-- `FArena::particle_displacement_mut` as a setter. -/
def setParticleDisplacement (a : FArena) (p : FParticleId) (v : KVector) : FArena :=
  match p with
  | .node n => { a with nodeDisplacement := a.nodeDisplacement.set! n.idx v }
  | .label l => { a with labelDisplacement := a.labelDisplacement.set! l.idx v }
  | .bend b => { a with bendDisplacement := a.bendDisplacement.set! b.idx v }

/-- `FArena::particle_properties`. -/
def particleProperties (a : FArena) : FParticleId → PropertyMap
  | .node n => a.nodeProperties[n.idx]!
  | .label l => a.labelProperties[l.idx]!
  | .bend b => a.bendProperties[b.idx]!

/-- `FArena::particle_radius`: half the diagonal of the particle's size. -/
def particleRadius (a : FArena) (p : FParticleId) : Float :=
  let size := a.particleSize p
  Float.sqrt (size.x * size.x + size.y * size.y) / 2.0

end FArena

/-! ### Flat array access for the O(n²) loops of the force models -/

/-- An index below `a.usize` is in bounds. -/
theorem FloatArray.usize_lt_size {a : FloatArray} {i : USize} (h : i < a.usize) : i.toNat < a.size := by
  have h1 : i.toNat < a.usize.toNat := (USize.lt_iff_toNat_lt).mp h
  have h2 : a.usize.toNat ≤ a.size := by
    simp only [FloatArray.usize, Nat.toUSize]
    exact Nat.mod_le _ _
  omega

/-- `a[i]` with a `USize` index (`0.0` out of bounds, like `FloatArray.get!`): compiles to a size
compare and a direct load, without the `Nat` boxing checks of `get!`. -/
@[inline] def fgetU (a : FloatArray) (i : USize) (dflt : Float) : Float :=
  if h : i < a.usize then a.uget i (FloatArray.usize_lt_size h) else dflt

/-- `a.set! i v` with a `USize` index (unchanged out of bounds). -/
@[inline] def fsetU (a : FloatArray) (i : USize) (v : Float) : FloatArray :=
  if h : i < a.usize then a.uset i v (FloatArray.usize_lt_size h) else a

end Elk.Alg.Force.Graph
