import Elk.Alg.Layered.Options.InternalProperties
import Elk.Alg.Layered.Graph.LMargin
/-! # `org.eclipse.elk.alg.layered.graph.LPort` -/
namespace Elk.Alg.Layered.Graph

open Elk.Graph Elk.Core.Math Elk.Core.Options Elk.Alg.Layered.Options

/-- `LPort`. Edge lists keep insertion order (`incomingEdges`/`outgoingEdges`). -/
structure LPort where
  id : Int := 0
  props : PropertyMap := {}
  position : KVector := {}
  size : KVector := {}
  /-- `getNode()` (owner). -/
  owner : Option LNodeId := none
  side : PortSide := .undefined
  anchor : KVector := {}
  explicitlySuppliedPortAnchor : Bool := false
  margin : LMargin := {}
  labels : Array LLabelId := #[]
  incomingEdges : Array LEdgeId := #[]
  outgoingEdges : Array LEdgeId := #[]
  /-- `isConnectedToExternalNodes()` (default `true`). -/
  connectedToExternalNodes : Bool := true
  internal : LPortInternals := {}
  deriving Inhabited

namespace LPort

/-- `LPort.setSide(side)`: also moves the default anchor unless it was supplied explicitly. -/
def setSide (p : LPort) (side : PortSide) : LPort :=
  let p := { p with side := side }
  if p.explicitlySuppliedPortAnchor then p
  else
    let s := p.size
    match side with
    | .north => { p with anchor := ⟨s.x / 2.0, 0.0⟩ }
    | .east => { p with anchor := ⟨s.x, s.y / 2.0⟩ }
    | .south => { p with anchor := ⟨s.x / 2.0, s.y⟩ }
    | .west => { p with anchor := ⟨0.0, s.y / 2.0⟩ }
    | .undefined => p

/-- `getDegree()`. -/
def degree (p : LPort) : Nat := p.incomingEdges.size + p.outgoingEdges.size

/-- `getNetFlow()`: incoming minus outgoing edges. -/
def netFlow (p : LPort) : Int := (p.incomingEdges.size : Int) - (p.outgoingEdges.size : Int)

/-- `getConnectedEdges()`: incoming then outgoing. -/
def connectedEdges (p : LPort) : Array LEdgeId := p.incomingEdges ++ p.outgoingEdges

end LPort

end Elk.Alg.Layered.Graph
