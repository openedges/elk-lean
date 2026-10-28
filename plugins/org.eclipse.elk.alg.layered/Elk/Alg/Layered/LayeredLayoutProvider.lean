import Elk.Alg.Layered.ElkLayered
import Elk.Alg.Layered.Graph.Transform
import Elk.Alg.Layered.Components
import Elk.Alg.Layered.Compound
import Elk.Core.LayoutProvider
/-!
# `LayeredLayoutProvider`

Port of `org.eclipse.elk.alg.layered.LayeredLayoutProvider` (elk-rs `layered_layout_provider.rs`):
imports the `ElkNode` into an `LGraph` (`ElkGraphTransformer`), runs `ElkLayered.doLayout` or
`doCompoundLayout` (`HIERARCHY_HANDLING = INCLUDE_CHILDREN`) and applies the result back.

elk-rs first stores the layered defaults `EDGE_ROUTING = ORTHOGONAL` and
`SEPARATE_CONNECTED_COMPONENTS = true` on the root node when they are unset
(`apply_layered_algorithm_defaults`); this is reproduced so that the stored option maps match.
-/
namespace Elk.Alg.Layered

open Elk.Graph Elk.Core Elk.Core.Options Elk.Core.Util
open Elk.Alg.Layered.Graph Elk.Alg.Layered.Graph.Transform Elk.Alg.Layered.Options

namespace LayeredLayoutProvider

/-- elk-rs `apply_layered_algorithm_defaults`: stores the layered algorithm's option defaults on the
root node when the user did not set them. -/
def applyLayeredAlgorithmDefaults (root : NodeId) : ElkM Unit := do
  let hasRouting ← (fun g => (g.node root).props.has LayeredOptions.EDGE_ROUTING) <$> get
  if !hasRouting then
    modify (·.modifyNode root fun n => { n with props := n.props.set LayeredOptions.EDGE_ROUTING EdgeRouting.orthogonal })
  let hasSeparate ← (fun g => (g.node root).props.has LayeredOptions.SEPARATE_CONNECTED_COMPONENTS) <$> get
  if !hasSeparate then
    modify (·.modifyNode root fun n => { n with props := n.props.set LayeredOptions.SEPARATE_CONNECTED_COMPONENTS true })

/-- `new ElkLayered()` with the components and compound collaborators. -/
def elkLayered : IO ElkLayered :=
  ElkLayered.new Components.ComponentsProcessor.split Components.ComponentsProcessor.combine
    Compound.CompoundGraphPreprocessor.processor Compound.CompoundGraphPostprocessor.processor

/-- Java names the nodes of the child graph in the `UnsupportedGraphException` of
`ElkLayered.reviewAndCorrectHierarchicalProcessors` by their ElkGraph identifiers, which the
layered arena does not know: the message is rendered again here with
`ElkGraphTransformer.getOriginIdentifier` (the arena still holds the state of the failed check).
Other errors pass unchanged. -/
private def withHierarchicalProcessorMessage (layeredGraph : LGraphId) (x : LImportM Unit) : LImportM Unit :=
  tryCatch x fun err => do
    let prefix_ := s!"{unsupportedGraphExceptionClass}: The hierarchy aware processor "
    if !(toString err).startsWith prefix_ then throw err
    let graphs ← liftLayered (ElkLayered.collectAllGraphsBottomUp layeredGraph)
    let some (graph, strategy) ← liftLayered (ElkLayered.hierarchicalProcessorViolation layeredGraph graphs)
      | throw err
    let elkGraph ← liftElk get
    let child ← liftLayered (LayeredM.withArena (·.graphToStringWith (ElkGraphTransformer.getOriginIdentifier elkGraph) graph))
    throwUnsupportedGraph (ElkLayered.hierarchicalProcessorMessage strategy child)

/-- Java names the node of a processor exception by `LNode.getDesignation()` (first label text, else
the identifier path of the origin `ElkNode`, `ElkGraphTransformer.getOriginIdentifier`, else the
index); the processor recorded the node in `LGraphArena.errorNode` and named it by
`nodeDesignation` (the arena has no ElkGraph), so `Node '<that name>'` is replaced here by the Java
designation. Other errors pass unchanged. -/
private def withNodeDesignations (x : LImportM Unit) : LImportM Unit :=
  tryCatch x fun err => do
    let some node ← liftLayered (LayeredM.withArena (·.errorNode)) | throw err
    let msg := toString err
    let plain := s!"Node '{← liftLayered (LayeredM.withArena (·.nodeDesignation node))}'"
    if (msg.splitOn plain).length < 2 then throw err
    let elkGraph ← liftElk get
    let designation ← liftLayered (LayeredM.withArena
      (·.nodeDesignationWith (ElkGraphTransformer.getOriginIdentifier elkGraph) node))
    throw (IO.userError (msg.replace plain s!"Node '{designation}'"))

/-- `layout(ElkNode, IElkProgressMonitor)`. -/
def layout (root : NodeId) (monitor : ProgressMonitor) : ElkM Unit := do
  applyLayeredAlgorithmDefaults root
  let transformer ← ElkGraphTransformer.create
  let algorithm ← elkLayered
  let hierarchyHandling : HierarchyHandling ←
    (fun g => (g.node root).props.getD LayeredOptions.HIERARCHY_HANDLING HierarchyHandling.inherit) <$> get
  let run : LImportM Unit := do
    let layeredGraph ← transformer.importGraph root
    withNodeDesignations do
      if hierarchyHandling == HierarchyHandling.includeChildren then
        withHierarchicalProcessorMessage layeredGraph
          (liftLayered (algorithm.doCompoundLayout layeredGraph (some monitor)))
      else
        liftLayered (algorithm.doLayout layeredGraph (some monitor))
    if !(← monitor.isCanceled) then
      transformer.applyLayout layeredGraph
  let _ ← StateRefT'.run run (default : LGraphArena)

/-- `startLayoutTest(ElkNode)` (white-box testing): imports the graph and prepares the processor
sequence without running it; the arena is the `LImportM` state. -/
def startLayoutTest (root : NodeId) : LImportM TestExecutionState := do
  let transformer ← ElkGraphTransformer.create
  let layeredGraph ← transformer.importGraph root
  let algorithm ← elkLayered
  liftLayered (algorithm.prepareLayoutTest layeredGraph)

/-- The `org.eclipse.elk.layered` layout provider. -/
def provider : LayoutProvider := { id := LayeredOptions.ALGORITHM_ID, layout := layout }

end LayeredLayoutProvider

builtin_initialize registerLayeredLayoutProvider : Unit ←
  LayoutProvider.register LayeredOptions.ALGORITHM_ID (fun _ => LayeredLayoutProvider.provider)

end Elk.Alg.Layered
