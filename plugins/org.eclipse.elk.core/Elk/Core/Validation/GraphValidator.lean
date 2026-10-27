import Elk.Graph.Monad
import Elk.Core.Options.CoreOptions
import Elk.Core.Data.LayoutMetaDataService
import Elk.Core.Util.ElkUtil
import Elk.Core.Util.GraphElementVisitor
import Elk.Core.Validation.GraphIssue
/-!
# `org.eclipse.elk.core.validation.GraphValidator`

Validating visitor checking edges (connectedness, containment, section end
points) and running the algorithm specific validators of the resolved layout
algorithms.

Algorithm specific validators: Java instantiates `LayoutAlgorithmData.validatorClass`
(elk-rs calls a validator factory stored in the algorithm data). Here
`LayoutAlgorithmData.validatorId` names a factory registered with
`registerValidatorFactory`. `RESOLVED_ALGORITHM` holds the algorithm id, which is
looked up in `LayoutMetaDataService`.
-/
namespace Elk.Core.Validation

open Elk Elk.Graph Elk.Core.Options Elk.Core.Data Elk.Core.Util

/-- Validator factories by validator id (`LayoutAlgorithmData.validatorId`). -/
builtin_initialize validatorFactoriesRef : IO.Ref (Array (String × IO GraphElementVisitor)) ← IO.mkRef #[]

/-- Registers (or replaces) the factory creating the validator `validatorId`
(Java `validatorClass` instantiation). -/
def registerValidatorFactory (validatorId : String) (factory : IO GraphElementVisitor) : IO Unit :=
  validatorFactoriesRef.modify fun fs =>
    match fs.findIdx? (·.1 == validatorId) with
    | some i => fs.set! i (validatorId, factory)
    | none => fs.push (validatorId, factory)

/-- The factory registered for `validatorId`. -/
def validatorFactory? (validatorId : String) : IO (Option (IO GraphElementVisitor)) := do
  return ((← validatorFactoriesRef.get).find? (·.1 == validatorId)).map (·.2)

/-- Mutable state of a `GraphValidator`. -/
structure GraphValidatorState where
  issues : Array GraphIssue := #[]
  /-- `algorithmSpecificValidators` with the number of their issues already copied,
  keyed by algorithm id. -/
  validators : Array (String × GraphElementVisitor × Nat) := #[]

/-- `org.eclipse.elk.core.validation.GraphValidator`. -/
structure GraphValidator where
  state : IO.Ref GraphValidatorState

namespace GraphValidator

/-- `new GraphValidator()`. -/
def new : IO GraphValidator := do return { state := ← IO.mkRef {} }

/-- `getIssues()`. -/
def issues (v : GraphValidator) : IO (Array GraphIssue) := do return (← v.state.get).issues

private def addIssue (v : GraphValidator) (issue : GraphIssue) : IO Unit :=
  v.state.modify fun s => { s with issues := s.issues.push issue }

private def shapeKind : ConnectableId → String
  | .node _ => "ElkNode"
  | .port _ => "ElkPort"

/-- `checkEdge(edge)`. -/
def checkEdge (v : GraphValidator) (e : EdgeId) : ElkM Unit := do
  let g ← get
  let edge := g.edge e
  let el := some (ElementId.edge e)
  if !edge.isConnected then
    v.addIssue { element := el, message := "Edge is not connected.", severity := .error }
  else
    let bestContainer := ElkGraphUtil.findBestEdgeContainment g e
    if bestContainer != edge.containingNode then
      let message := match bestContainer with
        | some best => ElkUtil.printElementPathInto g (.node best) "Edge should be contained in "
        | none => "Edge should be contained in "
      v.addIssue { element := el, message, severity := .warning }
  for s in edge.sections do
    let sec := g.edgeSection s
    if let some incoming := sec.incomingShape then
      if !edge.sources.contains incoming then
        v.addIssue { element := el, severity := .error,
                     message := s!"{shapeKind incoming} declared as incoming shape is not a source of this edge." }
      if !sec.incomingSections.isEmpty then
        v.addIssue { element := el, severity := .error,
                     message := s!"An edge section cannot be connected to an {shapeKind incoming} and other sections at the same time." }
    if let some outgoing := sec.outgoingShape then
      if !edge.targets.contains outgoing then
        v.addIssue { element := el, severity := .error,
                     message := s!"{shapeKind outgoing} declared as outgoing shape is not a target of this edge." }
      if !sec.outgoingSections.isEmpty then
        v.addIssue { element := el, severity := .error,
                     message := s!"An edge section cannot be connected to an {shapeKind outgoing} and other sections at the same time." }

/-- `RESOLVED_ALGORITHM` of a node. -/
private def resolvedAlgorithm (g : ElkGraph) (node : NodeId) : Option String :=
  (g.node node).props.get CoreOptions.RESOLVED_ALGORITHM

/-- `getValidator(algorithmData)`: the cached validator of the algorithm, created on first use. -/
private def getValidator (v : GraphValidator) (algoData : LayoutAlgorithmData) : IO (Option GraphElementVisitor) := do
  if let some (_, validator, _) := (← v.state.get).validators.find? (·.1 == algoData.id) then
    return some validator
  let some validatorId := algoData.validatorId | return none
  let some factory ← validatorFactory? validatorId | return none
  let validator ← factory
  v.state.modify fun s => { s with validators := s.validators.push (algoData.id, validator, 0) }
  return some validator

/-- `runAlgorithmSpecificChecks(element, parent)`: runs the validator of the algorithm
resolved for `parent` and copies its new issues. -/
def runAlgorithmSpecificChecks (v : GraphValidator) (el : ElementId) (parent : NodeId) : ElkM Unit := do
  let some algoId := resolvedAlgorithm (← get) parent | return
  let some algoData ← LayoutMetaDataService.getAlgorithmData algoId | return
  let some validator ← v.getValidator algoData | return
  validator.visit el
  let some issues ← validator.getIssues | return
  v.state.modify fun s =>
    match s.validators.findIdx? (·.1 == algoData.id) with
    | some i =>
      let (id, val, count) := s.validators[i]!
      if count < issues.size then
        { s with issues := s.issues ++ issues.extract count issues.size,
                 validators := s.validators.set! i (id, val, issues.size) }
      else s
    | none => s

/-- `visit(element)`. -/
def visit (v : GraphValidator) (el : ElementId) : ElkM Unit := do
  if let .edge e := el then v.checkEdge e
  let parent := ElkGraphUtil.containingGraph (← get) el
  if let some parentNode := parent then
    v.runAlgorithmSpecificChecks el parentNode
  if let .node node := el then
    let g ← get
    let parentAlgorithm := parent.bind (resolvedAlgorithm g)
    let nodeAlgorithm := resolvedAlgorithm g node
    if parent.isNone || parentAlgorithm != nodeAlgorithm then
      v.runAlgorithmSpecificChecks el node

/-- The validator as an `IValidatingGraphElementVisitor`. -/
def toVisitor (v : GraphValidator) : GraphElementVisitor := { visit := v.visit, issues := some v.issues }

end GraphValidator

end Elk.Core.Validation
