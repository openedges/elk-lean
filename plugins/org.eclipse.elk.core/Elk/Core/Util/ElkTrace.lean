/-!
# `ElkTrace` (elk-rs `core::util::elk_trace`)

Centralized trace/debug flags. All `ELK_TRACE_*` / `ELK_DEBUG_*` environment
variables are read once at startup (`ElkTrace.global`). Boolean flags are set
when the variable exists (even if empty); string flags hold the value.

Not included (as in Rust): `ELK_TRACE_DIR` (read per model by the parity trace
infrastructure).
-/
namespace Elk.Core.Util

/-- Trace flags read from the environment. -/
structure ElkTrace where
  /-- `ELK_TRACE`. -/
  trace : Bool := false
  /-- `ELK_TRACE_PHASES`. -/
  phases : Bool := false
  /-- `ELK_TRACE_PHASE_TIMING`. -/
  phaseTiming : Bool := false
  /-- `ELK_TRACE_PROCESSORS`. -/
  processors : Bool := false
  /-- `ELK_TRACE_PROCESSOR_TIMING`. -/
  processorTiming : Bool := false
  /-- `ELK_TRACE_NODES`. -/
  nodes : Bool := false
  /-- `ELK_TRACE_EDGE_WIRING`. -/
  edgeWiring : Bool := false
  /-- `ELK_TRACE_RESIZE`. -/
  resize : Bool := false
  /-- `ELK_TRACE_RECURSIVE_LAYOUT`. -/
  recursiveLayout : Bool := false
  /-- `ELK_TRACE_NODE_SIZE`. -/
  nodeSize : Bool := false
  /-- `ELK_TRACE_SIZING`. -/
  sizing : Bool := false
  /-- `ELK_TRACE_SIZING_LABELS`. -/
  sizingLabels : Bool := false
  /-- `ELK_TRACE_CROSSMIN`. -/
  crossmin : Bool := false
  /-- `ELK_TRACE_CROSSMIN_TIMING`. -/
  crossminTiming : Bool := false
  /-- `ELK_TRACE_CROSSMIN_STATS`. -/
  crossminStats : Bool := false
  /-- `ELK_TRACE_CROSSMIN_CONSTRAINTS`. -/
  crossminConstraints : Bool := false
  /-- `ELK_TRACE_CROSSINGS_BREAKDOWN`. -/
  crossingsBreakdown : Bool := false
  /-- `ELK_TRACE_GREEDY_SWITCH`. -/
  greedySwitch : Bool := false
  /-- `ELK_TRACE_GREEDY_PORTS`. -/
  greedyPorts : Bool := false
  /-- `ELK_TRACE_PORT_RANKS`. -/
  portRanks : Bool := false
  /-- `ELK_TRACE_FORSTER_GROUPS`. -/
  forsterGroups : Bool := false
  /-- `ELK_TRACE_CYCLE_CHOICES`. -/
  cycleChoices : Bool := false
  /-- `ELK_TRACE_CYCLE_REVERSALS`. -/
  cycleReversals : Bool := false
  /-- `ELK_TRACE_BK`. -/
  bk : Bool := false
  /-- `ELK_TRACE_BK_ALIGN`. -/
  bkAlign : Bool := false
  /-- `ELK_TRACE_BK_CLASSES`. -/
  bkClasses : Bool := false
  /-- `ELK_TRACE_BK_CONFLICTS`. -/
  bkConflicts : Bool := false
  /-- `ELK_TRACE_BK_GUARD`. -/
  bkGuard : Bool := false
  /-- `ELK_TRACE_BK_INNER`. -/
  bkInner : Bool := false
  /-- `ELK_TRACE_BK_LAYOUTS`. -/
  bkLayouts : Bool := false
  /-- `ELK_TRACE_BK_PLACE_BLOCK`. -/
  bkPlaceBlock : Bool := false
  /-- `ELK_TRACE_BK_NODE_STATE`. -/
  bkNodeState : Bool := false
  /-- `ELK_TRACE_BK_THRESH`. -/
  bkThresh : Bool := false
  /-- `ELK_TRACE_NETWORK_SIMPLEX`. -/
  networkSimplex : Bool := false
  /-- `ELK_TRACE_ORTHO`. -/
  ortho : Bool := false
  /-- `ELK_TRACE_COMPOUND_WIDTH`. -/
  compoundWidth : Bool := false
  /-- `ELK_TRACE_EDGE_APPLY`. -/
  edgeApply : Bool := false
  /-- `ELK_TRACE_EDGE_OFFSETS`. -/
  edgeOffsets : Bool := false
  /-- `ELK_TRACE_EDGE_ORIGIN_MAP`. -/
  edgeOriginMap : Bool := false
  /-- `ELK_TRACE_INSIDE_YO`. -/
  insideYo : Bool := false
  /-- `ELK_TRACE_EXTERNAL_PORTS`. -/
  externalPorts : Bool := false
  /-- `ELK_TRACE_HN`. -/
  hn : Bool := false
  /-- `ELK_TRACE_HIER_PORT_ORTHO`. -/
  hierPortOrtho : Bool := false
  /-- `ELK_TRACE_ILC`. -/
  ilc : Bool := false
  /-- `ELK_TRACE_NS`. -/
  ns : Bool := false
  /-- `ELK_TRACE_LONG_EDGE_SPLIT`. -/
  longEdgeSplit : Bool := false
  /-- `ELK_TRACE_LABEL_DUMMY_SWITCHER`. -/
  labelDummySwitcher : Bool := false
  /-- `ELK_TRACE_LAYER_HEIGHT`. -/
  layerHeight : Bool := false
  /-- `ELK_TRACE_CORE_PORT_SORT`. -/
  corePortSort : Bool := false
  /-- `ELK_TRACE_IMPORT_EDGE_SELECTION`. -/
  importEdgeSelection : Bool := false
  /-- `ELK_TRACE_IMPORT_PORT_ORDER`. -/
  importPortOrder : Bool := false
  /-- `ELK_TRACE_JSON_EDGE_ADJUST`. -/
  jsonEdgeAdjust : Bool := false
  /-- `ELK_TRACE_STRESS`. -/
  stress : Bool := false
  /-- `ELK_DEBUG_EDGES`. -/
  debugEdges : Bool := false
  /-- `ELK_TRACE_NODES_FILTER`. -/
  nodesFilter : Option String := none
  /-- `ELK_TRACE_BARYCENTER_LAYER_PATTERN`. -/
  barycenterLayerPattern : Option String := none
  /-- `ELK_TRACE_BK_NODE_FILTER`. -/
  bkNodeFilter : Option String := none
  /-- `ELK_DEBUG_CROSSMIN_FORCE_SWEEP`. -/
  debugCrossminForceSweep : Option String := none
  /-- `ELK_DEBUG_CYCLE_FORCE_REVERSE_ORIGINS`. -/
  debugCycleForceReverseOrigins : Option String := none
  /-- `ELK_DEBUG_CYCLE_RANDOM_PREFETCH`. -/
  debugCycleRandomPrefetch : Option String := none
  deriving Inhabited

namespace ElkTrace

/-- `ElkTrace::from_env`: reads all flags from the environment. -/
def fromEnv : IO ElkTrace := do
  return {
    trace := (← IO.getEnv "ELK_TRACE").isSome
    phases := (← IO.getEnv "ELK_TRACE_PHASES").isSome
    phaseTiming := (← IO.getEnv "ELK_TRACE_PHASE_TIMING").isSome
    processors := (← IO.getEnv "ELK_TRACE_PROCESSORS").isSome
    processorTiming := (← IO.getEnv "ELK_TRACE_PROCESSOR_TIMING").isSome
    nodes := (← IO.getEnv "ELK_TRACE_NODES").isSome
    edgeWiring := (← IO.getEnv "ELK_TRACE_EDGE_WIRING").isSome
    resize := (← IO.getEnv "ELK_TRACE_RESIZE").isSome
    recursiveLayout := (← IO.getEnv "ELK_TRACE_RECURSIVE_LAYOUT").isSome
    nodeSize := (← IO.getEnv "ELK_TRACE_NODE_SIZE").isSome
    sizing := (← IO.getEnv "ELK_TRACE_SIZING").isSome
    sizingLabels := (← IO.getEnv "ELK_TRACE_SIZING_LABELS").isSome
    crossmin := (← IO.getEnv "ELK_TRACE_CROSSMIN").isSome
    crossminTiming := (← IO.getEnv "ELK_TRACE_CROSSMIN_TIMING").isSome
    crossminStats := (← IO.getEnv "ELK_TRACE_CROSSMIN_STATS").isSome
    crossminConstraints := (← IO.getEnv "ELK_TRACE_CROSSMIN_CONSTRAINTS").isSome
    crossingsBreakdown := (← IO.getEnv "ELK_TRACE_CROSSINGS_BREAKDOWN").isSome
    greedySwitch := (← IO.getEnv "ELK_TRACE_GREEDY_SWITCH").isSome
    greedyPorts := (← IO.getEnv "ELK_TRACE_GREEDY_PORTS").isSome
    portRanks := (← IO.getEnv "ELK_TRACE_PORT_RANKS").isSome
    forsterGroups := (← IO.getEnv "ELK_TRACE_FORSTER_GROUPS").isSome
    cycleChoices := (← IO.getEnv "ELK_TRACE_CYCLE_CHOICES").isSome
    cycleReversals := (← IO.getEnv "ELK_TRACE_CYCLE_REVERSALS").isSome
    bk := (← IO.getEnv "ELK_TRACE_BK").isSome
    bkAlign := (← IO.getEnv "ELK_TRACE_BK_ALIGN").isSome
    bkClasses := (← IO.getEnv "ELK_TRACE_BK_CLASSES").isSome
    bkConflicts := (← IO.getEnv "ELK_TRACE_BK_CONFLICTS").isSome
    bkGuard := (← IO.getEnv "ELK_TRACE_BK_GUARD").isSome
    bkInner := (← IO.getEnv "ELK_TRACE_BK_INNER").isSome
    bkLayouts := (← IO.getEnv "ELK_TRACE_BK_LAYOUTS").isSome
    bkPlaceBlock := (← IO.getEnv "ELK_TRACE_BK_PLACE_BLOCK").isSome
    bkNodeState := (← IO.getEnv "ELK_TRACE_BK_NODE_STATE").isSome
    bkThresh := (← IO.getEnv "ELK_TRACE_BK_THRESH").isSome
    networkSimplex := (← IO.getEnv "ELK_TRACE_NETWORK_SIMPLEX").isSome
    ortho := (← IO.getEnv "ELK_TRACE_ORTHO").isSome
    compoundWidth := (← IO.getEnv "ELK_TRACE_COMPOUND_WIDTH").isSome
    edgeApply := (← IO.getEnv "ELK_TRACE_EDGE_APPLY").isSome
    edgeOffsets := (← IO.getEnv "ELK_TRACE_EDGE_OFFSETS").isSome
    edgeOriginMap := (← IO.getEnv "ELK_TRACE_EDGE_ORIGIN_MAP").isSome
    insideYo := (← IO.getEnv "ELK_TRACE_INSIDE_YO").isSome
    externalPorts := (← IO.getEnv "ELK_TRACE_EXTERNAL_PORTS").isSome
    hn := (← IO.getEnv "ELK_TRACE_HN").isSome
    hierPortOrtho := (← IO.getEnv "ELK_TRACE_HIER_PORT_ORTHO").isSome
    ilc := (← IO.getEnv "ELK_TRACE_ILC").isSome
    ns := (← IO.getEnv "ELK_TRACE_NS").isSome
    longEdgeSplit := (← IO.getEnv "ELK_TRACE_LONG_EDGE_SPLIT").isSome
    labelDummySwitcher := (← IO.getEnv "ELK_TRACE_LABEL_DUMMY_SWITCHER").isSome
    layerHeight := (← IO.getEnv "ELK_TRACE_LAYER_HEIGHT").isSome
    corePortSort := (← IO.getEnv "ELK_TRACE_CORE_PORT_SORT").isSome
    importEdgeSelection := (← IO.getEnv "ELK_TRACE_IMPORT_EDGE_SELECTION").isSome
    importPortOrder := (← IO.getEnv "ELK_TRACE_IMPORT_PORT_ORDER").isSome
    jsonEdgeAdjust := (← IO.getEnv "ELK_TRACE_JSON_EDGE_ADJUST").isSome
    stress := (← IO.getEnv "ELK_TRACE_STRESS").isSome
    debugEdges := (← IO.getEnv "ELK_DEBUG_EDGES").isSome
    nodesFilter := (← IO.getEnv "ELK_TRACE_NODES_FILTER")
    barycenterLayerPattern := (← IO.getEnv "ELK_TRACE_BARYCENTER_LAYER_PATTERN")
    bkNodeFilter := (← IO.getEnv "ELK_TRACE_BK_NODE_FILTER")
    debugCrossminForceSweep := (← IO.getEnv "ELK_DEBUG_CROSSMIN_FORCE_SWEEP")
    debugCycleForceReverseOrigins := (← IO.getEnv "ELK_DEBUG_CYCLE_FORCE_REVERSE_ORIGINS")
    debugCycleRandomPrefetch := (← IO.getEnv "ELK_DEBUG_CYCLE_RANDOM_PREFETCH")
  }

end ElkTrace

/-- The process-wide flags (`ElkTrace::global()`), computed once at startup. -/
builtin_initialize ElkTrace.global : ElkTrace ← ElkTrace.fromEnv

end Elk.Core.Util
