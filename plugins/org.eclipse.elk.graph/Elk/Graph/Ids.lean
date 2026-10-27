/-!
# Arena identifiers (org.eclipse.elk.graph)

Every ElkGraph element lives in an arena (`Array`) inside `Elk.Graph.ElkGraph`
and is referenced by a typed index. Ids are plain `Nat` wrappers: they are
unboxed by the compiler, cheap to copy and never form reference cycles.
-/
namespace Elk.Graph

/-- Index of an `ElkNode` in `ElkGraph.nodes`. -/
structure NodeId where
  idx : Nat
  deriving BEq, Hashable, Repr, Inhabited, DecidableEq, Ord

/-- Index of an `ElkPort` in `ElkGraph.ports`. -/
structure PortId where
  idx : Nat
  deriving BEq, Hashable, Repr, Inhabited, DecidableEq, Ord

/-- Index of an `ElkEdge` in `ElkGraph.edges`. -/
structure EdgeId where
  idx : Nat
  deriving BEq, Hashable, Repr, Inhabited, DecidableEq, Ord

/-- Index of an `ElkLabel` in `ElkGraph.labels`. -/
structure LabelId where
  idx : Nat
  deriving BEq, Hashable, Repr, Inhabited, DecidableEq, Ord

/-- Index of an `ElkEdgeSection` in `ElkGraph.sections`. -/
structure SectionId where
  idx : Nat
  deriving BEq, Hashable, Repr, Inhabited, DecidableEq, Ord

instance : ToString NodeId := ⟨fun i => s!"N{i.idx}"⟩
instance : ToString PortId := ⟨fun i => s!"P{i.idx}"⟩
instance : ToString EdgeId := ⟨fun i => s!"E{i.idx}"⟩
instance : ToString LabelId := ⟨fun i => s!"L{i.idx}"⟩
instance : ToString SectionId := ⟨fun i => s!"S{i.idx}"⟩

instance : LT NodeId := ⟨fun a b => a.idx < b.idx⟩
instance : LT PortId := ⟨fun a b => a.idx < b.idx⟩
instance : LT EdgeId := ⟨fun a b => a.idx < b.idx⟩
instance : LT LabelId := ⟨fun a b => a.idx < b.idx⟩
instance : LT SectionId := ⟨fun a b => a.idx < b.idx⟩
instance (a b : NodeId) : Decidable (a < b) := inferInstanceAs (Decidable (a.idx < b.idx))
instance (a b : PortId) : Decidable (a < b) := inferInstanceAs (Decidable (a.idx < b.idx))
instance (a b : EdgeId) : Decidable (a < b) := inferInstanceAs (Decidable (a.idx < b.idx))
instance (a b : LabelId) : Decidable (a < b) := inferInstanceAs (Decidable (a.idx < b.idx))
instance (a b : SectionId) : Decidable (a < b) := inferInstanceAs (Decidable (a.idx < b.idx))

/-- `ElkConnectableShape`: an edge end point is either a node or a port. -/
inductive ConnectableId where
  | node (id : NodeId)
  | port (id : PortId)
  deriving BEq, Hashable, Repr, Inhabited, DecidableEq

/-- Reference to any `ElkGraphElement` (node, port, edge or label). -/
inductive ElementId where
  | node (id : NodeId)
  | port (id : PortId)
  | edge (id : EdgeId)
  | label (id : LabelId)
  deriving BEq, Hashable, Repr, Inhabited, DecidableEq

namespace ConnectableId

def toElement : ConnectableId → ElementId
  | .node n => .node n
  | .port p => .port p

def node? : ConnectableId → Option NodeId
  | .node n => some n
  | _ => none

def port? : ConnectableId → Option PortId
  | .port p => some p
  | _ => none

def isNode : ConnectableId → Bool
  | .node _ => true
  | .port _ => false

def isPort : ConnectableId → Bool
  | .port _ => true
  | .node _ => false

end ConnectableId

namespace ElementId

def node? : ElementId → Option NodeId
  | .node n => some n
  | _ => none

def port? : ElementId → Option PortId
  | .port p => some p
  | _ => none

def edge? : ElementId → Option EdgeId
  | .edge e => some e
  | _ => none

def label? : ElementId → Option LabelId
  | .label l => some l
  | _ => none

def connectable? : ElementId → Option ConnectableId
  | .node n => some (.node n)
  | .port p => some (.port p)
  | _ => none

end ElementId

instance : ToString ConnectableId where
  toString
    | .node n => toString n
    | .port p => toString p

instance : ToString ElementId where
  toString
    | .node n => toString n
    | .port p => toString p
    | .edge e => toString e
    | .label l => toString l

end Elk.Graph
