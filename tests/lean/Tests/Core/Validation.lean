import Tests.Framework
import Elk.Core
/-! Test suites for `org.eclipse.elk.core.validation` (ported from elk-rs
`plugins/org.eclipse.elk.core/tests/all`): `graph_validator_test.rs`,
`layout_option_validator_test.rs`. -/
namespace Tests.Core.Validation

open Tests Elk Elk.Graph Elk.Core.Util Elk.Core.Options Elk.Core.Data Elk.Core.Validation

private def runVisitors (g : ElkGraph) (root : NodeId) (visitors : Array GraphElementVisitor) : IO ElkGraph := do
  let (_, g) ← ElkM.run (ElkUtil.applyVisitors root visitors) g
  return g

private def validate (g : ElkGraph) (root : NodeId) : IO (Array GraphIssue) := do
  let v ← GraphValidator.new
  let _ ← runVisitors g root #[v.toVisitor]
  v.issues

private def contains (s sub : String) : Bool := (s.splitOn sub).length > 1

/-- graph_validator_test.rs `FooValidator`: reports `FOO!` for nodes with identifier `foo`. -/
private def fooValidator : IO GraphElementVisitor := do
  let issues ← IO.mkRef (#[] : Array GraphIssue)
  return {
    visit := fun el => do
      if let .node n := el then
        if (← ElkM.getNode n).identifier == some "foo" then
          issues.modify (·.push { element := some el, message := "FOO!", severity := .error })
    issues := some issues.get }

/-- graph_validator_test.rs `FooProvider`: registers `test.foo.algorithm` with a validator. -/
private def registerFooProvider : IO Unit := do
  registerValidatorFactory "test.foo.validator" fooValidator
  LayoutMetaDataService.registerLayoutMetaDataProvider
    { apply := (·.registerAlgorithm { id := "test.foo.algorithm", validatorId := some "test.foo.validator" }) }

/-- Two sibling nodes connected by a simple edge. -/
private def twoNodeGraph : ElkGraph × NodeId × NodeId × NodeId × EdgeId :=
  let (g, graph) := ElkGraphUtil.createGraph
  let (g, n1) := g.createNode (some graph)
  let (g, n2) := g.createNode (some graph)
  let (g, e) := ElkGraphUtil.createSimpleEdge g (.node n1) (.node n2)
  (g, graph, n1, n2, e)

private def checkSingleIssue (name : String) (issues : Array GraphIssue) (severity : Severity)
    (accept : String → Bool) : TestM Unit := do
  checkEq s!"{name}: one issue" issues.size 1
  if h : 0 < issues.size then
    checkEq s!"{name}: severity" issues[0].severity severity
    report s!"{name}: message" (accept issues[0].message) issues[0].message

def graphValidatorTests : Suite := suite "core.validation.GraphValidator" do
  -- graph_validator_unconnected_edge
  let (g, graph) := ElkGraphUtil.createGraph
  let (g, _) := g.createEdge (some graph)
  checkSingleIssue "unconnected edge" (← validate g graph) .error (· == "Edge is not connected.")
  -- graph_validator_custom_validation
  registerFooProvider
  let (g, graph) := ElkGraphUtil.createGraph
  let (g, node) := g.createNode (some graph)
  let g := g.modifyNode node fun n => { n with identifier := some "foo" }
  let g := g.setNodeProp graph CoreOptions.ALGORITHM "test.foo.algorithm"
  let resolver ← LayoutAlgorithmResolver.new
  let validator ← GraphValidator.new
  let _ ← runVisitors g graph #[resolver.toVisitor, validator.toVisitor]
  checkSingleIssue "custom validation" (← validator.issues) .error (· == "FOO!")
  -- graph_validator_edge_containment_warning
  let (g, graph, n1, _, e) := twoNodeGraph
  let g := g.setEdgeContainingNode e (some n1)
  checkSingleIssue "edge containment" (← validate g graph) .warning (contains · "Edge should be contained in")
  -- graph_validator_section_incoming_shape_not_source
  let (g, graph, _, n2, e) := twoNodeGraph
  let (g, s) := g.createSection (some e)
  let g := g.modifySection s fun sec => { sec with incomingShape := some (.node n2) }
  checkSingleIssue "incoming shape" (← validate g graph) .error (contains · "incoming shape is not a source")
  -- graph_validator_section_outgoing_shape_not_target
  let (g, graph, n1, _, e) := twoNodeGraph
  let (g, s) := g.createSection (some e)
  let g := g.modifySection s fun sec => { sec with outgoingShape := some (.node n1) }
  checkSingleIssue "outgoing shape" (← validate g graph) .error (contains · "outgoing shape is not a target")
  -- graph_validator_section_incoming_conflict
  let (g, graph, n1, _, e) := twoNodeGraph
  let (g, s) := g.createSection (some e)
  let (g, other) := g.createSection (some e)
  let g := g.modifySection s fun sec => { sec with incomingShape := some (.node n1), incomingSections := #[other] }
  checkSingleIssue "incoming conflict" (← validate g graph) .error (contains · "cannot be connected to an ElkNode")
  -- (Lean) applyVisitorsWithValidation fails with the issue path
  let (g, graph) := ElkGraphUtil.createGraph
  let (g, _) := g.createEdge (some graph)
  let v ← GraphValidator.new
  let (r, _) ← ElkM.run (ElkUtil.applyVisitorsWithValidation graph #[v.toVisitor]) g
  match r with
  | .error ex => checkEq "validation exception message" ex.message "ERROR: Edge is not connected.\n\tat Root Node > Edge"
  | .ok _ => report "validation exception" false "expected a GraphValidationException"

/-- Registers `ASPECT_RATIO` (double, lower bound `> 0`) if the registry lacks it. -/
private def ensureAspectRatio : IO Unit := do
  if (← LayoutMetaDataService.getOptionData CoreOptions.ASPECT_RATIO.id).isNone then
    LayoutMetaDataService.registerLayoutMetaDataProvider
      { apply := (·.registerOption (LayoutOptionData.mk' CoreOptions.ASPECT_RATIO.id .double "Aspect Ratio" ""
          #[.parents] (lowerBound := some (OptionBound.greaterThan 0.0)))) }

def layoutOptionValidatorTests : Suite := suite "core.validation.LayoutOptionValidator" do
  ensureAspectRatio
  let runValidator (g : ElkGraph) (graph : NodeId) : IO (Array GraphIssue) := do
    let v ← LayoutOptionValidator.new
    let _ ← runVisitors g graph #[v.toVisitor]
    v.issues
  -- layout_option_validator_invalid_type
  let some optionData ← LayoutMetaDataService.getOptionData CoreOptions.ASPECT_RATIO.id
    | report "aspect ratio option data" false "missing"
  let (g, graph) := ElkGraphUtil.createGraph
  let g := g.modifyNode graph fun n => { n with props := n.props.setRawById optionData.id (.string "foo") }
  checkSingleIssue "invalid type" (← runValidator g graph) .error
    (· == "The assigned value foo of the option 'Aspect Ratio' does not match the type Double.")
  -- layout_option_validator_exclusive_lower_bound
  let (g, graph) := ElkGraphUtil.createGraph
  let g := g.setNodeProp graph CoreOptions.ASPECT_RATIO 0.0
  checkSingleIssue "exclusive lower bound" (← runValidator g graph) .error
    (· == "The assigned value 0.0 of the option 'Aspect Ratio' is less than the lower bound 0.0 (exclusive).")
  -- (Lean) Rust `{:?}` float formatting used in the messages
  checkEq "debug 1.5" (floatToRustDebug 1.5) "1.5"
  checkEq "debug 20" (floatToRustDebug 20.0) "20.0"
  checkEq "debug 1e16" (floatToRustDebug 1e16) "1e16"
  checkEq "debug 1.5e-7" (floatToRustDebug 1.5e-7) "1.5e-7"
  checkEq "debug -2.5e20" (floatToRustDebug (-2.5e20)) "-2.5e20"

def suites : Array Tests.Suite := #[graphValidatorTests, layoutOptionValidatorTests]

end Tests.Core.Validation
