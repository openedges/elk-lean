import Tests.Framework
import Elk.Core
import Elk.Api
/-! Test suites for `org.eclipse.elk.core.alg` and the `ElkGraphAdapters` (ported from elk-rs
`plugins/org.eclipse.elk.core/tests/all`): `algorithm_assembler_test.rs`,
`layout_processor_configuration_test.rs` (both over `common/alg_test_util.rs`) and
`elk_graph_adapters_test.rs`. The Rust `String` test graph is an `IO.Ref String`. -/
namespace Tests.Core.Alg

open Tests Elk Elk.Graph Elk.Core.Alg Elk.Core.Util Elk.Core.Util.Adapters Elk.Core.Math Elk.Core.Options
open Elk.Core.Data

/-- `TestPhases` of `alg_test_util.rs`. -/
elk_enum TestPhases := phase1 phase2
/-- `TestProcessors` of `alg_test_util.rs`. -/
elk_enum TestProcessors := processor1 processor2 processor3

/-- Rust `Display` of `TestPhases` (`PHASE_1`, ...). -/
def phaseText : TestPhases → String
  | .phase1 => "PHASE_1"
  | .phase2 => "PHASE_2"

/-- Rust `Display` of `TestProcessors` (`PROCESSOR_1`, ...). -/
def processorText : TestProcessors → String
  | .processor1 => "PROCESSOR_1"
  | .processor2 => "PROCESSOR_2"
  | .processor3 => "PROCESSOR_3"

/-- `TestProcessors::from_phase`. -/
def processorOfPhase : TestPhases → TestProcessors
  | .phase1 => .processor1
  | .phase2 => .processor2

/-- The test graph (`TestGraph = String`). -/
abbrev TestGraph := IO.Ref String

/-- Creation counters (`PHASE_CREATE_COUNTS`, `PROCESSOR_CREATE_COUNTS`). -/
structure Counters where
  phases : IO.Ref (Array Nat)
  processors : IO.Ref (Array Nat)

/-- `reset_create_counts` (a fresh counter set per test replaces the global lock). -/
def Counters.new : IO Counters := do
  return ⟨← IO.mkRef #[0, 0], ← IO.mkRef #[0, 0, 0]⟩

/-- `processor_factory(...)`: a processor appending its name to the graph. -/
def Counters.processorFactory (c : Counters) : LayoutProcessorFactory IO TestGraph TestProcessors :=
  fun p => do
    c.processors.modify fun a => a.modify (ElkEnum.ordinal p) (· + 1)
    return { name := processorText p, process := fun g _ => g.modify (· ++ processorText p) }

/-- `phase_factory(...)`: its configuration puts `from_phase(phase)` before the phase. -/
def Counters.phaseFactory (c : Counters) (phase : TestPhases) :
    LayoutPhaseFactory IO TestPhases TestGraph TestProcessors :=
  LayoutPhaseFactory.ofEnum "TestPhases" phase (do
    c.phases.modify fun a => a.modify (ElkEnum.ordinal phase) (· + 1)
    return {
      name := phaseText phase
      process := fun g _ => g.modify (· ++ phaseText phase)
      getLayoutProcessorConfiguration := fun _ =>
        pure (some (LayoutProcessorConfiguration.create.addBefore phase (processorOfPhase phase))) })

/-- Configuration over the test enums. -/
abbrev Cfg := LayoutProcessorConfiguration TestPhases TestProcessors

/-- A new assembler over the test enums. -/
def newAssembler (c : Counters) : IO (AlgorithmAssembler IO TestPhases TestGraph TestProcessors) :=
  AlgorithmAssembler.create c.processorFactory

/-- Both phases set on a fresh assembler. -/
def assemblerWithPhases (c : Counters) : IO (AlgorithmAssembler IO TestPhases TestGraph TestProcessors) := do
  let a ← newAssembler c
  a.setPhase .phase1 (c.phaseFactory .phase1)
  a.setPhase .phase2 (c.phaseFactory .phase2)
  return a

/-- Runs each processor on a fresh graph and returns what it wrote. -/
def runEach (algorithm : Array (LayoutProcessor IO TestGraph)) : IO (Array String) := do
  let mut out := #[]
  for p in algorithm do
    let buf ← IO.mkRef ""
    p.process buf ProgressMonitor.null
    out := out.push (← buf.get)
  return out

/-- `algorithm_assembler_test.rs` plus extra ordering checks. -/
def assemblerTests : Suite := suite "core.alg.AlgorithmAssembler" do
  let g ← IO.mkRef ""
  -- test_enable_caching
  let c ← Counters.new
  let a ← assemblerWithPhases c
  let alg ← a.build g
  checkEq "test_enable_caching: size" alg.size 4
  let pc ← c.phases.get
  let rc ← c.processors.get
  let alg2 ← a.build g
  checkEq "test_enable_caching: size 2" alg2.size 4
  check "test_enable_caching: phase counts unchanged" ((← c.phases.get) == pc)
  check "test_enable_caching: processor counts unchanged" ((← c.processors.get) == rc)
  -- test_disable_caching
  let c ← Counters.new
  let a ← newAssembler c
  a.withCaching false
  a.setPhase .phase1 (c.phaseFactory .phase1)
  a.setPhase .phase2 (c.phaseFactory .phase2)
  let _ ← a.build g
  let pc ← c.phases.get
  let rc ← c.processors.get
  let _ ← a.build g
  let pc2 ← c.phases.get
  let rc2 ← c.processors.get
  check "test_disable_caching: phase1" (pc2[0]! > pc[0]!)
  check "test_disable_caching: phase2" (pc2[1]! > pc[1]!)
  check "test_disable_caching: processor1" (rc2[0]! > rc[0]!)
  check "test_disable_caching: processor2" (rc2[1]! > rc[1]!)
  -- test_fail_on_missing_phase (should_panic)
  let c ← Counters.new
  let a ← newAssembler c
  a.setPhase .phase1 (c.phaseFactory .phase1)
  checkThrows "test_fail_on_missing_phase" (do let _ ← a.build g)
  let msg ← try (do let _ ← a.build g; pure "") catch e => pure (toString e)
  checkEq "test_fail_on_missing_phase: message" msg
    "java.lang.IllegalStateException: Expected 2 phases to be configured; only found 1"
  -- test_dont_fail_on_missing_phase
  let a ← newAssembler c
  a.withFailOnMissingPhase false
  a.setPhase .phase1 (c.phaseFactory .phase1)
  check "test_dont_fail_on_missing_phase: non-empty" (!(← a.build g).isEmpty)
  -- test_clear_cache
  let c ← Counters.new
  let a ← assemblerWithPhases c
  let _ ← a.build g
  let pc ← c.phases.get
  let rc ← c.processors.get
  a.clearCache
  let _ ← a.build g
  let pc2 ← c.phases.get
  let rc2 ← c.processors.get
  check "test_clear_cache: phase1" (pc2[0]! > pc[0]!)
  check "test_clear_cache: phase2" (pc2[1]! > pc[1]!)
  check "test_clear_cache: processor1" (rc2[0]! > rc[0]!)
  check "test_clear_cache: processor2" (rc2[1]! > rc[1]!)
  -- test_reset_with_fail_on_missing_phase (should_panic)
  let a ← assemblerWithPhases c
  a.withFailOnMissingPhase true
  a.reset
  checkThrows "test_reset_with_fail_on_missing_phase" (do let _ ← a.build g)
  -- test_reset_without_fail_on_missing_phase
  let a ← assemblerWithPhases c
  a.withFailOnMissingPhase false
  a.reset
  checkEq "test_reset_without_fail_on_missing_phase" (← a.build g).size 0
  -- test_add_processor_configuration
  let c ← Counters.new
  let a ← newAssembler c
  a.addProcessorConfiguration
    (LayoutProcessorConfiguration.create.addBefore TestPhases.phase1 TestProcessors.processor3)
  a.setPhase .phase1 (c.phaseFactory .phase1)
  a.setPhase .phase2 (c.phaseFactory .phase2)
  let alg ← a.build g
  let expected := #["PROCESSOR_1", "PROCESSOR_3", "PHASE_1", "PROCESSOR_2", "PHASE_2"]
  let outs ← runEach alg
  checkEq "test_add_processor_configuration: size" outs.size 5
  for i in [0:outs.size] do
    checkEq s!"test_add_processor_configuration: step {i}" outs[i]! expected[i]!
  -- extra: processors after the last phase come last, duplicates removed, sorted by ordinal
  let a ← assemblerWithPhases c
  let cfg : Cfg :=
    (LayoutProcessorConfiguration.create.addBefore TestPhases.phase2 TestProcessors.processor3)
      |>.addBefore TestPhases.phase2 TestProcessors.processor2
      |>.addBefore TestPhases.phase2 TestProcessors.processor2
      |>.addAfter TestPhases.phase2 TestProcessors.processor1
      |>.addAfter TestPhases.phase2 TestProcessors.processor1
  a.addProcessorConfiguration cfg
  let outs ← runEach (← a.build g)
  checkEq "extra: ordering" outs
    #["PROCESSOR_1", "PHASE_1", "PROCESSOR_2", "PROCESSOR_3", "PHASE_2", "PROCESSOR_1"]
  -- extra: a built algorithm runs end to end on one graph
  let buf ← IO.mkRef ""
  for p in (← a.build buf) do p.process buf ProgressMonitor.null
  checkEq "extra: end-to-end" (← buf.get) "PROCESSOR_1PHASE_1PROCESSOR_2PROCESSOR_3PHASE_2PROCESSOR_1"

/-- `layout_processor_configuration_test.rs`. -/
def configurationTests : Suite := suite "core.alg.LayoutProcessorConfiguration" do
  let cnt (c : Cfg) (b : Bool) (p : TestPhases) : Nat :=
    if b then (c.processorsBefore p).size else (c.processorsAfter p).size
  let ok (e : Except String Cfg) : Cfg := match e with | .ok c => c | .error _ => {}
  let isErr {α : Type} (e : Except String α) : Bool := match e with | .error _ => true | .ok _ => false
  -- test_before
  let c : Cfg := LayoutProcessorConfiguration.create
  let c := ok ((c.before .phase1).add .processor1)
  let c := ok (ok ((c.before .phase2).add .processor2) |>.add .processor3)
  checkEq "test_before: 1" (cnt c true .phase1) 1
  checkEq "test_before: 2" (cnt c false .phase1) 2
  checkEq "test_before: 3" (cnt c true .phase2) 2
  checkEq "test_before: 4" (cnt c false .phase2) 0
  -- test_after
  let c : Cfg := LayoutProcessorConfiguration.create
  let c := ok ((c.after .phase1).add .processor1)
  let c := ok (ok ((c.after .phase2).add .processor2) |>.add .processor3)
  checkEq "test_after: 1" (cnt c true .phase1) 0
  checkEq "test_after: 2" (cnt c false .phase1) 1
  checkEq "test_after: 3" (cnt c true .phase2) 1
  checkEq "test_after: 4" (cnt c false .phase2) 2
  -- test_add_before
  let c : Cfg := (LayoutProcessorConfiguration.create.before .phase1).addBefore .phase2 .processor1
  checkEq "test_add_before: 1" (cnt c true .phase1) 0
  checkEq "test_add_before: 2" (cnt c false .phase1) 1
  checkEq "test_add_before: 3" (cnt c true .phase2) 1
  checkEq "test_add_before: 4" (cnt c false .phase2) 0
  -- test_add_before_panics (should_panic): addBefore resets the current slot, so add fails
  check "test_add_before_panics" (isErr (c.add .processor2))
  -- test_add_after
  let c : Cfg := (LayoutProcessorConfiguration.create.before .phase1).addAfter .phase1 .processor1
  checkEq "test_add_after: 1" (cnt c true .phase1) 0
  checkEq "test_add_after: 2" (cnt c false .phase1) 1
  checkEq "test_add_after: 3" (cnt c true .phase2) 1
  checkEq "test_add_after: 4" (cnt c false .phase2) 0
  -- test_add_after_panics (should_panic)
  check "test_add_after_panics" (isErr (c.add .processor2))
  -- test_add_all
  let c : Cfg := LayoutProcessorConfiguration.create
  let c := ok ((c.after .phase1).add .processor1)
  let c := ok (ok ((c.after .phase2).add .processor2) |>.add .processor3)
  let c2 : Cfg := LayoutProcessorConfiguration.create.addAll c
  checkEq "test_add_all: 1" (cnt c2 true .phase1) 0
  checkEq "test_add_all: 2" (cnt c2 false .phase1) 1
  checkEq "test_add_all: 3" (cnt c2 true .phase2) 1
  checkEq "test_add_all: 4" (cnt c2 false .phase2) 2
  -- extra: add without before/after is an error; duplicates are ignored
  check "extra: add without before/after"
    (isErr ((LayoutProcessorConfiguration.create : Cfg).add .processor1))
  let d : Cfg := (LayoutProcessorConfiguration.create.addBefore .phase1 .processor1).addBefore .phase1 .processor1
  checkEq "extra: duplicates ignored" (d.processorsBefore .phase1).size 1

/-- Runs a graph-building computation on an empty graph. -/
def inGraph {α : Type} (body : ElkM α) : IO α := do
  let (r, _) ← body.run {}
  return r

/-- Sets `PORT_SIDE` and `PORT_INDEX` of a port (`set_port_attrs`). -/
def setPortAttrs (p : PortId) (side : PortSide) (index : Int) : ElkM Unit := do
  ElkM.setProp (.port p) CoreOptions.PORT_SIDE side
  ElkM.setProp (.port p) CoreOptions.PORT_INDEX index

/-- `elk_graph_adapters_test.rs` plus `PortComparator.compare` checks. -/
def adapterTests : Suite := suite "core.util.adapters.ElkGraphAdapters" do
  LayoutMetaDataService.ensureInitialized
  let ad ← ElkGraphAdapters.new
  -- elk_graph_adapter_lists_child_nodes
  let n ← inGraph do
    let root ← ElkM.createNode none
    let _ ← ElkM.createNode (some root)
    let _ ← ElkM.createNode (some root)
    return (← ad.getNodes root).size
  checkEq "elk_graph_adapter_lists_child_nodes" n 2
  -- node_adapter_sorts_ports_when_fixed_order
  let r ← inGraph do
    let root ← ElkM.createNode none
    let node ← ElkM.createNode (some root)
    let p1 ← ElkM.createPort (some node)
    let p2 ← ElkM.createPort (some node)
    let p3 ← ElkM.createPort (some node)
    ElkM.setNodeProp node CoreOptions.PORT_CONSTRAINTS PortConstraints.fixedOrder
    setPortAttrs p1 .west 2
    setPortAttrs p2 .east 0
    setPortAttrs p3 .west 1
    ad.sortPortList node
    return ((← ad.nodePorts node) == #[p2, p3, p1])
  check "node_adapter_sorts_ports_when_fixed_order" r
  -- node_adapter_lists_ports_and_labels
  let (np, nl) ← inGraph do
    let root ← ElkM.createNode none
    let node ← ElkM.createNode (some root)
    let _ ← ElkM.createPort (some node)
    let _ ← ElkM.createLabel (some (.node node)) "L1"
    return ((← ad.nodePorts node).size, (← ad.nodeLabels node).size)
  checkEq "node_adapter_lists_ports_and_labels: ports" np 1
  checkEq "node_adapter_lists_ports_and_labels: labels" nl 1
  -- node_adapter_padding_and_margin_roundtrip
  let padding : ElkPadding := { top := 1.0, right := 4.0, bottom := 3.0, left := 2.0 }
  let margin : ElkMargin := { top := 5.0, right := 8.0, bottom := 7.0, left := 6.0 }
  let (pad, mar) ← inGraph do
    let root ← ElkM.createNode none
    let node ← ElkM.createNode (some root)
    ad.setPadding node padding
    ad.setNodeMargin node margin
    return (← ad.getPadding node, ← ad.getNodeMargin node)
  check "node_adapter_padding_and_margin_roundtrip: padding" (pad == padding)
  check "node_adapter_padding_and_margin_roundtrip: margin" (mar == margin)
  -- port_adapter_margin_and_border_offset
  let pmargin : ElkMargin := { top := 1.0, right := 4.0, bottom := 3.0, left := 2.0 }
  let (pm, off) ← inGraph do
    let root ← ElkM.createNode none
    let node ← ElkM.createNode (some root)
    let port ← ElkM.createPort (some node)
    ad.setPortMargin port pmargin
    return (← ad.getPortMargin port, ← ad.port.getProperty port CoreOptions.PORT_BORDER_OFFSET)
  check "port_adapter_margin_and_border_offset: margin" (pm == pmargin)
  checkSome "port_adapter_margin_and_border_offset: offset present" off
  checkFloat "port_adapter_margin_and_border_offset: offset" (off.getD 1.0) 0.0
  -- port_adapter_detects_compound_connections
  let r ← inGraph do
    let root ← ElkM.createNode none
    let parent ← ElkM.createNode (some root)
    let child ← ElkM.createNode (some parent)
    let port ← ElkM.createPort (some parent)
    let _ ← ElkM.createSimpleEdge (.port port) (.node child)
    ad.hasCompoundConnections port
  check "port_adapter_detects_compound_connections" r
  -- port_adapter_detects_inside_self_loop_connections
  let r ← inGraph do
    let root ← ElkM.createNode none
    let node ← ElkM.createNode (some root)
    let port ← ElkM.createPort (some node)
    let e ← ElkM.createSimpleEdge (.port port) (.node node)
    ElkM.setProp (.edge e) CoreOptions.INSIDE_SELF_LOOPS_YO true
    ad.hasCompoundConnections port
  check "port_adapter_detects_inside_self_loop_connections" r
  let r ← inGraph do
    let root ← ElkM.createNode none
    let node ← ElkM.createNode (some root)
    let port ← ElkM.createPort (some node)
    let _ ← ElkM.createSimpleEdge (.port port) (.node node)
    ad.hasCompoundConnections port
  check "extra: self loop without INSIDE_SELF_LOOPS_YO is not compound" (!r)
  -- port_adapter_reports_side
  let s ← inGraph do
    let root ← ElkM.createNode none
    let node ← ElkM.createNode (some root)
    let port ← ElkM.createPort (some node)
    ElkM.setProp (.port port) CoreOptions.PORT_SIDE PortSide.east
    ad.portSide port
  check "port_adapter_reports_side" (s == PortSide.east)
  -- label_adapter_reads_text_and_side
  let (cnt, txt, side) ← inGraph do
    let root ← ElkM.createNode none
    let node ← ElkM.createNode (some root)
    let _ ← ElkM.createLabel (some (.node node)) "Hello"
    let ls ← ad.nodeLabels node
    return (ls.size, ← ad.labelText ls[0]!, ← ad.labelSide ls[0]!)
  checkEq "label_adapter_reads_text_and_side: count" cnt 1
  checkEq "label_adapter_reads_text_and_side: text" txt "Hello"
  check "label_adapter_reads_text_and_side: side" (side == LabelSide.unknown)
  -- node_adapter_compound_detection_respects_inside_self_loops
  let r ← inGraph do
    let root ← ElkM.createNode none
    let node ← ElkM.createNode (some root)
    let before ← ad.isCompoundNode node
    ElkM.setNodeProp node CoreOptions.INSIDE_SELF_LOOPS_ACTIVATE true
    return (before, ← ad.isCompoundNode node)
  check "extra: leaf node is not compound" (!r.1)
  check "node_adapter_compound_detection_respects_inside_self_loops" r.2
  -- extra: PortComparator.compare
  let (g0, root) := ElkGraphUtil.createGraph
  let (g0, node) := g0.createNode (some root)
  let mk (g : ElkGraph) (side : PortSide) (idx : Option Int) (x y : Float) : ElkGraph × PortId :=
    let (g, p) := g.createPort (some node)
    let g := g.setPortProp p CoreOptions.PORT_SIDE side
    let g := match idx with | some i => g.setPortProp p CoreOptions.PORT_INDEX i | none => g
    (g.modifyPort p fun pt => { pt with x := x, y := y }, p)
  let (g, west) := mk g0 .west none 0.0 0.0
  let (g, north) := mk g .north none 5.0 0.0
  let (g, north2) := mk g .north none 2.0 0.0
  let (g, east1) := mk g .east (some 1) 0.0 9.0
  let (g, east2) := mk g .east (some 2) 0.0 1.0
  let (g, east3) := mk g .east none 0.0 3.0
  let (g, east4) := mk g .east none 0.0 4.0
  let (g, south1) := mk g .south none 1.0 0.0
  let (g, south2) := mk g .south none 3.0 0.0
  let (g, west1) := mk g .west none 0.0 1.0
  let (g, west2) := mk g .west none 0.0 3.0
  let cmp := PortComparator.compare g
  check "PortComparator: side ordinal north < west" (cmp north west == .lt)
  check "PortComparator: side ordinal west > north" (cmp west north == .gt)
  check "PortComparator: PORT_INDEX wins over coordinate" (cmp east1 east2 == .lt)
  check "PortComparator: PORT_INDEX only when both set" (cmp east3 east4 == .lt)
  check "PortComparator: north by increasing x" (cmp north2 north == .lt)
  check "PortComparator: east by increasing y" (cmp east3 east4 == .lt)
  check "PortComparator: south by decreasing x" (cmp south2 south1 == .lt)
  check "PortComparator: west by decreasing y" (cmp west2 west1 == .lt)
  check "PortComparator: equal" (cmp north north == .eq)

/-- All suites of this file. -/
def suites : Array Tests.Suite := #[assemblerTests, configurationTests, adapterTests]

end Tests.Core.Alg
