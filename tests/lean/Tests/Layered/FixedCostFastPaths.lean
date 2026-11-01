import Tests.Framework
import Elk.Alg.Layered
import Tests.Layered.IntermediatePreserveOrder
/-!
Differential tests of the per-layout fixed-cost fast paths of round 16 FIX against their kept
references: `GraphConfigurator.prepareGraphForLayout` with the assembler-free `assembleFast`
(slot bit sets over the `IntermediateProcessorStrategy` ordinals) against the generic
`AlgorithmAssembler` path (`fast := false`), and `phaseIndependentSlotBits` against the slot sets of
`getPhaseIndependentLayoutProcessorConfiguration`, on random option maps (every option the
configurator and the phase configurations read, the phase strategies, graph properties, parents,
flexible nodes).
-/
namespace Tests.Layered.FixedCostFastPaths

open Tests Elk Elk.Graph Elk.Core Elk.Core.Util Elk.Core.Options Elk.Core.Alg Elk.Core.Labels Elk.Alg.Layered
open Elk.Alg.Layered.Graph Elk.Alg.Layered.Options Elk.Alg.Layered.Intermediate
open Tests.Layered.IntermediatePreserveOrder (rnd)

/-- Sets `p` to a random constant of its enumeration (or leaves it unset). -/
private def randomEnum {α : Type} [ElkEnum α] [PropCodec α] (props : PropertyMap) (p : Property α) (s : UInt64) :
    PropertyMap × UInt64 :=
  let values : Array α := ElkEnum.values
  let (k, s) := rnd s (values.size + 2)
  match values[k]? with
  | some v => (props.set p v, s)
  | none => (props, s)

/-- Sets a Boolean option to a random value (or leaves it unset). -/
private def randomBool (props : PropertyMap) (p : Property Bool) (s : UInt64) : PropertyMap × UInt64 :=
  let (k, s) := rnd s 3
  (if k == 0 then props else props.set p (k == 1), s)

/-- A random graph for the configurator: random options, graph properties, an optional parent node
and layerless nodes with random flexibilities. -/
private def randomConfigGraph (seed : UInt64) : LayeredM LGraphId := do
  let mut s := seed
  let mut props : PropertyMap := {}
  (props, s) := randomEnum props CoreOptions.HIERARCHY_HANDLING s
  (props, s) := randomEnum props LayeredOptions.CROSSING_MINIMIZATION_GREEDY_SWITCH_HIERARCHICAL_TYPE s
  (props, s) := randomEnum props LayeredOptions.CROSSING_MINIMIZATION_GREEDY_SWITCH_TYPE s
  (props, s) := randomBool props LayeredOptions.CROSSING_MINIMIZATION_SEMI_INTERACTIVE s
  (props, s) := randomEnum props LayeredOptions.CROSSING_MINIMIZATION_STRATEGY s
  (props, s) := randomEnum props LayeredOptions.CYCLE_BREAKING_STRATEGY s
  (props, s) := randomEnum props LayeredOptions.LAYERING_STRATEGY s
  (props, s) := randomEnum props LayeredOptions.NODE_PLACEMENT_STRATEGY s
  (props, s) := randomEnum props CoreOptions.EDGE_ROUTING s
  (props, s) := randomEnum props CoreOptions.DIRECTION s
  (props, s) := randomBool props LayeredOptions.FEEDBACK_EDGES s
  (props, s) := randomBool props CoreOptions.INTERACTIVE_LAYOUT s
  (props, s) := randomBool props LayeredOptions.GENERATE_POSITION_AND_LAYER_IDS s
  (props, s) := randomEnum props LayeredOptions.LAYERING_NODE_PROMOTION_STRATEGY s
  (props, s) := randomEnum props LayeredOptions.COMPACTION_POST_COMPACTION_STRATEGY s
  (props, s) := randomBool props LayeredOptions.HIGH_DEGREE_NODES_TREATMENT s
  (props, s) := randomEnum props LayeredOptions.LAYER_UNZIPPING_STRATEGY s
  (props, s) := randomEnum props LayeredOptions.WRAPPING_STRATEGY s
  (props, s) := randomEnum props LayeredOptions.CONSIDER_MODEL_ORDER_STRATEGY s
  (props, s) := randomEnum props LayeredOptions.NODE_PLACEMENT_NETWORK_SIMPLEX_NODE_FLEXIBILITY_RECOMPUTE_NODE_PLACEMENT s
  (props, s) := randomEnum props LayeredOptions.NODE_PLACEMENT_NETWORK_SIMPLEX_NODE_FLEXIBILITY_DEFAULT s
  let (t, s1) := rnd s 4; s := s1
  if t == 0 then props := props.set LayeredOptions.CROSSING_MINIMIZATION_GREEDY_SWITCH_ACTIVATION_THRESHOLD ((t : Int) * 2)
  let (lm, s1) := rnd s 4; s := s1
  if lm == 0 then props := props.setRaw LabelManagementOptions.LABEL_MANAGER.key (.bool true)
  let mut gp : Array GraphProperties := #[]
  for v in (ElkEnum.values : Array GraphProperties) do
    let (k, s1) := rnd s 3; s := s1
    if k == 0 then gp := gp.push v
  let (withParent, s1) := rnd s 3; s := s1
  let parent ← if withParent == 0 then do
      let outer ← LayeredM.createGraph
      some <$> LayeredM.createNode outer
    else pure none
  let g ← LayeredM.createGraph { props, parentNode := parent }
  LayeredM.modifyGraph g fun x => { x with internal := { x.internal with graphProperties := EnumSet.of gp } }
  let (nodeCount, s1) := rnd s 4; s := s1
  let mut nodes : Array LNodeId := #[]
  for _ in [0:nodeCount] do
    let mut np : PropertyMap := {}
    (np, s) := randomEnum np LayeredOptions.NODE_PLACEMENT_NETWORK_SIMPLEX_NODE_FLEXIBILITY s
    nodes := nodes.push (← LayeredM.createNode g { props := np })
  LayeredM.modifyGraph g fun x => { x with layerlessNodes := nodes }
  return g

/-- The processor list as comparable values: name and hierarchy awareness. -/
private def describe (ps : Array LayeredProcessor) : Array (String × Bool) :=
  ps.map fun p => (p.name, p.isHierarchyAware)

/-- `prepareGraphForLayout` (fast) = the generic assembler path, and the phase-independent slot sets
= the generic configuration's slot sets (2,000 random graphs, exceptions included). -/
def fastAssemblyTests : Suite := suite "layered.graphConfigurator.fastAssembly" do
  let mut bad := 0
  let mut badBits := 0
  let mut lists := 0
  let mut distinct : Std.HashSet (Array (String × Bool)) := {}
  for k in [0:2000] do
    let seed : UInt64 := (k.toUInt64 + 5) * 0x9e3779b97f4a7c15
    let (g, a) ← LayeredM.run (randomConfigGraph seed)
    let run (fast : Bool) : IO (Except String (Array (String × Bool) × LGraphArena)) := do
      try
        let c ← GraphConfigurator.new
        let (ps, a') ← LayeredM.run (c.prepareGraphForLayout g fast) a
        return .ok (describe ps, a')
      catch e => return .error (toString e)
    let fast ← run true
    let generic ← run false
    match fast, generic with
    | .ok (f, fa), .ok (r, ra) =>
      lists := lists + 1
      distinct := distinct.insert f
      if f != r || (fa.graph g).props.entries.size != (ra.graph g).props.entries.size then bad := bad + 1
    | .error e1, .error e2 => if e1 != e2 then bad := bad + 1
    | _, _ => bad := bad + 1
    let (bitsFast, _) ← LayeredM.run (GraphConfigurator.phaseIndependentSlotBits g) a
    let (config, _) ← LayeredM.run (GraphConfigurator.getPhaseIndependentLayoutProcessorConfiguration g) a
    if bitsFast != GraphConfigurator.SlotBits.ofConfiguration config then badBits := badBits + 1
  checkEq "prepareGraphForLayout fast = generic assembler (2,000 random option maps)" bad 0
  checkEq "phaseIndependentSlotBits = slot sets of the generic configuration" badBits 0
  check s!"the random option maps give many processor lists ({distinct.size} distinct of {lists})"
    (distinct.size > 500 && lists > 1500)

def suites : Array Suite := #[fastAssemblyTests]

end Tests.Layered.FixedCostFastPaths
