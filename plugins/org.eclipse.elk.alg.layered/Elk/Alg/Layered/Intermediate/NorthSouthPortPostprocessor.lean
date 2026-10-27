import Elk.Alg.Layered.LayeredPhases
import Elk.Alg.Layered.Graph.LGraphUtil
/-!
# `org.eclipse.elk.alg.layered.intermediate.NorthSouthPortPostprocessor`

Port of elk-rs `intermediate/north_south_port_postprocessor.rs`. Removes the `NORTH_SOUTH_PORT`
dummy nodes again: the edges of each dummy port are reconnected to the port the dummy was created
for (`ORIGIN`) and get a bend point at `(origin anchor x, dummy y)` (appended for incoming,
prepended for outgoing edges), plus an equal junction point when all ports of the dummy come from
the same origin port. With spline routing only `SPLINE_NS_PORT_Y_COORD` is recorded on the origin
port and no bend points are added.

Rust behaviour followed here (deviations from Java): there is no `processSelfLoop` branch for
dummies whose `ORIGIN` is an edge (their ports have no edges left, so nothing is reconnected), and
"same origin" requires every port of a dummy with at least two ports to originate from the same
`LPort`.
-/
namespace Elk.Alg.Layered.Intermediate

open Elk.Graph Elk.Core Elk.Core.Alg Elk.Core.Util Elk.Core.Math Elk.Core.Options Elk.Alg.Layered
  Elk.Alg.Layered.Graph Elk.Alg.Layered.Options LayeredM

namespace NorthSouthPortPostprocessor

/-- `origin_guard.set_property(SPLINE_NS_PORT_Y_COORD, Some(y))` on the origin port
(`LPortInternals.splineNsPortYCoord`). -/
def setSplineNsPortYCoord (port : LPortId) (y : Float) : LayeredM Unit :=
  modifyPort port fun p => { p with internal := { p.internal with splineNsPortYCoord := some y } }

/-- `ports_same_origin(ports)`: at least two ports, all with the same `LPort` origin. -/
def portsSameOrigin (ports : Array LPortId) : LayeredM Bool := do
  if ports.size < 2 then return false
  let mut originPort : Option LPortId := none
  for port in ports do
    let some (Origin.lPort originRef) := (← getPort port).internal.origin | return false
    match originPort with
    | some existing => if existing != originRef then return false
    | none => originPort := some originRef
  return true

/-- Appends a junction point to an edge's `JUNCTION_POINTS` (created when unset). -/
private def addJunctionPoint (edge : LEdgeId) (point : KVector) : LayeredM Unit :=
  modifyEdge edge fun e =>
    let junctionPoints := (e.props.get LayeredOptions.JUNCTION_POINTS).getD KVectorChain.empty
    { e with props := e.props.set LayeredOptions.JUNCTION_POINTS (junctionPoints.push point) }

/-- The x coordinate of the origin port's absolute anchor (`(0, 0)` when it has no owner). -/
private def originAnchorX (originPort : LPortId) : LayeredM Float := do
  return ((← withArena (·.portAbsoluteAnchor originPort)).getD {}).x

/-- `process_input_port(port, dummy_y, add_junction)` (Java `processInputPort`). -/
def processInputPort (port : LPortId) (dummyY : Float) (addJunction : Bool) : LayeredM Unit := do
  let some (Origin.lPort originPort) := (← getPort port).internal.origin | return
  let x ← originAnchorX originPort
  for edge in (← getPort port).incomingEdges do
    setEdgeTarget edge (some originPort)
    modifyEdge edge fun e => { e with bendPoints := e.bendPoints.push ⟨x, dummyY⟩ }
    if addJunction then addJunctionPoint edge ⟨x, dummyY⟩

/-- `process_output_port(port, dummy_y, add_junction)` (Java `processOutputPort`). -/
def processOutputPort (port : LPortId) (dummyY : Float) (addJunction : Bool) : LayeredM Unit := do
  let some (Origin.lPort originPort) := (← getPort port).internal.origin | return
  let x ← originAnchorX originPort
  for edge in (← getPort port).outgoingEdges do
    setEdgeSource edge (some originPort)
    modifyEdge edge fun e => { e with bendPoints := e.bendPoints.insertIdx! 0 ⟨x, dummyY⟩ }
    if addJunction then addJunctionPoint edge ⟨x, dummyY⟩

/-- `process_spline_input_port(port, dummy_y)` (Java `processSplineInputPort`). -/
def processSplineInputPort (port : LPortId) (dummyY : Float) : LayeredM Unit := do
  let some (Origin.lPort originPort) := (← getPort port).internal.origin | return
  setSplineNsPortYCoord originPort dummyY
  for edge in (← getPort port).incomingEdges do
    setEdgeTarget edge (some originPort)

/-- `process_spline_output_port(port, dummy_y)` (Java `processSplineOutputPort`). -/
def processSplineOutputPort (port : LPortId) (dummyY : Float) : LayeredM Unit := do
  let some (Origin.lPort originPort) := (← getPort port).internal.origin | return
  setSplineNsPortYCoord originPort dummyY
  for edge in (← getPort port).outgoingEdges do
    setEdgeSource edge (some originPort)

/-- `process(graph, monitor)`: per layer over a copy of its node list; every north/south dummy is
removed from its layer after its ports are processed. -/
def process (graph : LGraphId) (monitor : ProgressMonitor) : LayeredM Unit := do
  let _ ← monitor.begin "Odd port side processing" 1.0
  let routing := ((← getGraph graph).props.get LayeredOptions.EDGE_ROUTING).getD EdgeRouting.polyline
  for layer in (← getGraph graph).layers do
    let nodeArray := (← getLayer layer).nodes
    for node in nodeArray do
      let nd ← getNode node
      if nd.type != .northSouthPort then continue
      let ports := nd.ports
      let dummyY := nd.position.y
      if routing == .splines then
        for port in ports do
          let pt ← getPort port
          let hasIn := !pt.incomingEdges.isEmpty
          let hasOut := !pt.outgoingEdges.isEmpty
          if hasIn then processSplineInputPort port dummyY
          if hasOut then processSplineOutputPort port dummyY
        setNodeLayer node none
        continue
      let sameOrigin ← portsSameOrigin ports
      for port in ports do
        let pt ← getPort port
        let hasIn := !pt.incomingEdges.isEmpty
        let hasOut := !pt.outgoingEdges.isEmpty
        if hasIn then processInputPort port dummyY sameOrigin
        if hasOut then processOutputPort port dummyY sameOrigin
      setNodeLayer node none
  monitor.done

/-- The `NorthSouthPortPostprocessor` processor. -/
def processor : LayeredProcessor := { name := "NorthSouthPortPostprocessor", process := process }

end NorthSouthPortPostprocessor

builtin_initialize registerNorthSouthPortPostprocessor : Unit ←
  IntermediateProcessorStrategy.register .northSouthPortPostprocessor NorthSouthPortPostprocessor.processor

end Elk.Alg.Layered.Intermediate
