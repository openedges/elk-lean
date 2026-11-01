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

open Tests Elk Elk.Graph Elk.Core Elk.Core.Math Elk.Core.Util Elk.Core.Options Elk.Core.Alg Elk.Core.Labels Elk.Alg.Layered
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

/-! ### `LabelAndNodeSizeProcessor` arena fast path -/

/-- A random subset of an enumeration (each constant with probability 1/3), unset with
probability 1/4. -/
private def randomSet {α : Type} [ElkEnum α] [PropCodec (EnumSet α)] (props : PropertyMap) (p : Property (EnumSet α))
    (s : UInt64) : PropertyMap × UInt64 := Id.run do
  let (unset, s1) := rnd s 4
  let mut s := s1
  if unset == 0 then return (props, s)
  let mut members : Array α := #[]
  for v in (ElkEnum.values : Array α) do
    let (k, s1) := rnd s 3; s := s1
    if k == 0 then members := members.push v
  return (props.set p (EnumSet.of members), s)

/-- A random coordinate: quarter steps in `[-10, 40)`. -/
private def coord (s : UInt64) : Float × UInt64 :=
  let (v, s) := rnd s 200
  (v.toFloat / 4.0 - 10.0, s)

/-- Random spacing options (in a node's or the graph's option map, or in individual spacings). -/
private def randomSpacings (props : PropertyMap) (s : UInt64) : PropertyMap × UInt64 := Id.run do
  let mut s := s
  let mut props := props
  for p in #[CoreOptions.SPACING_LABEL_NODE, CoreOptions.SPACING_LABEL_LABEL, CoreOptions.SPACING_PORT_PORT,
      CoreOptions.SPACING_LABEL_PORT_HORIZONTAL, CoreOptions.SPACING_LABEL_PORT_VERTICAL] do
    let (k, s1) := rnd s 3; s := s1
    if k == 0 then
      let (v, s1) := rnd s 12; s := s1
      props := props.set p (v.toFloat * 1.5)
  let (k, s1) := rnd s 4; s := s1
  if k == 0 then
    let (t, s1) := rnd s 8; let (b, s2) := rnd s1 8; s := s2
    props := props.set CoreOptions.SPACING_PORTS_SURROUNDING
      ({ top := t.toFloat, bottom := b.toFloat, left := b.toFloat, right := t.toFloat } : ElkMargin)
  let (k, s1) := rnd s 4; s := s1
  if k == 0 then
    let (t, s1) := rnd s 8; s := s1
    props := props.set CoreOptions.NODE_LABELS_PADDING
      ({ top := t.toFloat, bottom := 2.0, left := 1.0, right := t.toFloat } : ElkPadding)
  return (props, s)

/-- A random layered graph for `LabelAndNodeSizeProcessor`: one or two layers of mostly NORMAL nodes
with random size options, port and label settings, ports on random sides (rarely UNDEFINED, which
throws), port and node labels, edges, comment nodes and individual spacings. -/
private def randomSizeGraph (seed : UInt64) : LayeredM LGraphId := do
  let mut s := seed
  let mut gprops : PropertyMap := {}
  (gprops, s) := randomSpacings gprops s
  (gprops, s) := randomEnum gprops CoreOptions.DIRECTION s
  (gprops, s) := randomBool gprops CoreOptions.NODE_SIZE_FIXED_GRAPH_SIZE s
  let g ← LayeredM.createGraph { props := gprops }
  let (nl, s1) := rnd s 2; s := s1
  let mut layers : Array LayerId := #[]
  for _ in [0:nl + 1] do layers := layers.push (← LayeredM.createLayer g)
  LayeredM.modifyGraph g fun x => { x with layers := layers }
  let mut ports : Array LPortId := #[]
  for l in layers do
    let (nn, s1) := rnd s 4; s := s1
    for _ in [0:nn + 1] do
      let mut np : PropertyMap := {}
      (np, s) := randomSet np CoreOptions.NODE_SIZE_CONSTRAINTS s
      (np, s) := randomSet np CoreOptions.NODE_SIZE_OPTIONS s
      (np, s) := randomEnum np CoreOptions.PORT_CONSTRAINTS s
      -- mostly valid label placements (an invalid one throws for the whole graph)
      let (validPl, s1) := rnd s 8; s := s1
      if validPl == 0 then
        (np, s) := randomSet np CoreOptions.PORT_LABELS_PLACEMENT s
        (np, s) := randomSet np CoreOptions.NODE_LABELS_PLACEMENT s
      else
        let portPls : Array (Array PortLabelPlacement) := #[#[.outside], #[.inside], #[.outside, .nextToPortIfPossible],
          #[.inside, .nextToPortIfPossible], #[.outside, .alwaysSameSide], #[.outside, .spaceEfficient], #[]]
        let nodePls : Array (Array NodeLabelPlacement) := #[#[.inside, .vCenter, .hCenter], #[.outside, .vTop, .hCenter],
          #[.inside, .vTop, .hLeft], #[.outside, .vBottom, .hRight, .hPriority], #[.inside, .vBottom, .hRight], #[]]
        let (a, s1) := rnd s (portPls.size + 1); let (b, s2) := rnd s1 (nodePls.size + 1); s := s2
        if let some pl := portPls[a]? then np := np.set CoreOptions.PORT_LABELS_PLACEMENT (EnumSet.of pl)
        if let some pl := nodePls[b]? then np := np.set CoreOptions.NODE_LABELS_PLACEMENT (EnumSet.of pl)
      (np, s) := randomBool np CoreOptions.PORT_LABELS_TREAT_AS_GROUP s
      (np, s) := randomBool np CoreOptions.TOPDOWN_LAYOUT s
      (np, s) := randomBool np CoreOptions.INSIDE_SELF_LOOPS_ACTIVATE s
      (np, s) := randomEnum np CoreOptions.PORT_ALIGNMENT_DEFAULT s
      (np, s) := randomEnum np CoreOptions.PORT_ALIGNMENT_NORTH s
      (np, s) := randomEnum np CoreOptions.PORT_ALIGNMENT_EAST s
      (np, s) := randomSpacings np s
      let (mins, s1) := rnd s 4; s := s1
      if mins == 0 then
        let (w, s1) := rnd s 60; s := s1
        np := np.set CoreOptions.NODE_SIZE_MINIMUM ({ x := w.toFloat, y := (w / 2).toFloat } : KVector)
      let (ind, s1) := rnd s 5; s := s1
      if ind == 0 then
        let (ip, s1) := randomSpacings {} s; s := s1
        np := np.set CoreOptions.SPACING_INDIVIDUAL ({ props := ip } : IndividualSpacings)
      let (t, s1) := rnd s 8; s := s1
      let (w, s1) := coord s; let (h, s2) := coord s1; let (cmp, s3) := rnd s2 4; s := s3
      let nodeType : NodeType := if t == 0 then .longEdge else .normal
      let n ← LayeredM.createNode g
        { props := np, size := ⟨w.abs, h.abs⟩, type := nodeType, internal := { compoundNode := cmp == 0 } }
      LayeredM.setNodeLayer n (some l)
      let (nlabels, s1) := rnd s 3; s := s1
      for _ in [0:nlabels] do
        let (w, s1) := coord s; let (h, s2) := coord s1; s := s2
        let lb ← LayeredM.createLabel "l" { size := ⟨w.abs, h.abs⟩ }
        LayeredM.modifyNode n fun x => { x with labels := x.labels.push lb }
      let (nports, s1) := rnd s 5; s := s1
      for _ in [0:nports] do
        let (side, s1) := rnd s 41; s := s1
        let sd : PortSide := match side % 4 with
          | 0 => .north | 1 => .east | 2 => .south | _ => .west
        let sd := if side == 40 then .undefined else sd
        let (x, s1) := coord s; let (y, s2) := coord s1; let (w, s3) := coord s2; let (bo, s4) := rnd s3 4
        let (ratio, s5) := rnd s4 5; let (inside, s6) := rnd s5 3
        s := s6
        let pprops : PropertyMap := if bo == 0 then ({} : PropertyMap).set CoreOptions.PORT_BORDER_OFFSET (x / 4.0) else {}
        let pinternal : LPortInternals := { portRatioOrPosition := ratio.toFloat / 4.0, insideConnections := inside == 0 }
        let psize : KVector := ⟨w.abs / 2.0, w.abs / 3.0⟩
        let p ← LayeredM.createPort { position := ⟨x, y⟩, size := psize, props := pprops, internal := pinternal }
        LayeredM.modifyPort p fun x => x.setSide sd
        LayeredM.setPortNode p (some n)
        ports := ports.push p
        let (plabels, s1) := rnd s 3; s := s1
        for _ in [0:plabels] do
          let (w, s1) := coord s; let (h, s2) := coord s1; s := s2
          let lb ← LayeredM.createLabel "p" { size := ⟨w.abs, h.abs / 2.0⟩ }
          LayeredM.modifyPort p fun x => { x with labels := x.labels.push lb }
      -- a comment node attached to the node (adapted without graph)
      let (c, s1) := rnd s 10; s := s1
      if c == 0 then
        let cn ← LayeredM.createNode g { size := ⟨10.0, 5.0⟩ }
        LayeredM.modifyNode n fun x => { x with internal := { x.internal with topComments := #[cn] } }
  if !ports.isEmpty then
    let (ne, s1) := rnd s (ports.size + 1); s := s1
    for _ in [0:ne] do
      let (i, s1) := rnd s ports.size; let (j, s2) := rnd s1 ports.size; s := s2
      let e ← LayeredM.createEdge
      LayeredM.setEdgeSource e (some ports[i]!)
      LayeredM.setEdgeTarget e (some ports[j]!)
  return g

/-- The bit patterns of every node, port and label size and position and every node padding. -/
private def arenaBits (a : LGraphArena) : Array UInt64 := Id.run do
  let mut out : Array UInt64 := #[]
  for nd in a.nodes do
    out := out ++ #[nd.size.x.toBits, nd.size.y.toBits, nd.position.x.toBits, nd.position.y.toBits,
      nd.padding.top.toBits, nd.padding.bottom.toBits, nd.padding.left.toBits, nd.padding.right.toBits,
      nd.props.entries.size.toUInt64, nd.ports.size.toUInt64]
  for pt in a.ports do
    out := out ++ #[pt.size.x.toBits, pt.size.y.toBits, pt.position.x.toBits, pt.position.y.toBits]
  for lb in a.labels do
    out := out ++ #[lb.size.x.toBits, lb.size.y.toBits, lb.position.x.toBits, lb.position.y.toBits]
  return out

/-- `LabelAndNodeSizeProcessor` with the arena fast path = the generic adapter pipeline (sizes,
positions, paddings and exception texts) on 3,000 random graphs. -/
def arenaNodeSizeTests : Suite := suite "layered.labelAndNodeSize.arenaFastPath" do
  let mut bad := 0
  let mut ok := 0
  let mut errors := 0
  let mut changed := 0
  for k in [0:3000] do
    let seed : UInt64 := (k.toUInt64 + 17) * 0xbf58476d1ce4e5b9
    let (g, a) ← LayeredM.run (randomSizeGraph seed)
    let run (fast : Bool) : IO (Except String (Array UInt64)) := do
      try
        let flags : LabelAndNodeSizeFlags := { LabelAndNodeSizeFlags.global with arenaFastPath := fast }
        let ((), a') ← LayeredM.run (LabelAndNodeSizeProcessor.processWith flags g ProgressMonitor.null) a
        return .ok (arenaBits a')
      catch e => return .error (toString e)
    let fast ← run true
    let generic ← run false
    match fast, generic with
    | .ok f, .ok r =>
      ok := ok + 1
      if f != r then bad := bad + 1
      if f != arenaBits a then changed := changed + 1
    | .error e1, .error e2 =>
      errors := errors + 1
      if e1 != e2 then bad := bad + 1
    | _, _ => bad := bad + 1
  checkEq s!"arena fast path = generic pipeline ({ok} layouts, {errors} exceptions)" bad 0
  check s!"the random graphs are laid out and change ({changed} of {ok})" (ok > 1500 && changed > 1000)
  check s!"the random graphs throw sometimes ({errors})" (errors > 50)

def suites : Array Suite := #[fastAssemblyTests, arenaNodeSizeTests]

end Tests.Layered.FixedCostFastPaths
