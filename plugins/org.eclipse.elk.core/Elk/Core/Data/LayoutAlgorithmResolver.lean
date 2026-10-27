import Elk.Graph.Monad
import Elk.Core.Exceptions
import Elk.Core.Options.CoreOptions
import Elk.Core.Data.LayoutMetaDataService
import Elk.Core.Util.ElkUtil
import Elk.Core.Util.GraphElementVisitor
/-!
# `org.eclipse.elk.core.data.LayoutAlgorithmResolver`

Graph element visitor that resolves `CoreOptions.ALGORITHM` (by id suffix) and
stores the resolved algorithm id in `CoreOptions.RESOLVED_ALGORITHM`. Errors
(Java `UnsupportedConfigurationException`s) are collected as strings of the form
`org.eclipse.elk.core.UnsupportedConfigurationException: <message>`.
-/
namespace Elk.Core.Data

open Elk Elk.Graph Elk.Core Elk.Core.Options Elk.Core.Util

/-- `org.eclipse.elk.core.data.LayoutAlgorithmResolver`. -/
structure LayoutAlgorithmResolver where
  errorsRef : IO.Ref (Array String)

namespace LayoutAlgorithmResolver

/-- `new LayoutAlgorithmResolver()`. -/
def new : IO LayoutAlgorithmResolver := do return { errorsRef := ← IO.mkRef #[] }

/-- `getErrors()`. -/
def errors (r : LayoutAlgorithmResolver) : IO (Array String) := r.errorsRef.get

/-- elk-rs `take_errors()`: returns and clears the errors. -/
def takeErrors (r : LayoutAlgorithmResolver) : IO (Array String) := r.errorsRef.modifyGet fun es => (es, #[])

/-- `getDefaultLayoutAlgorithmID()`. -/
def defaultLayoutAlgorithmId : String := "org.eclipse.elk.layered"

/-- Resolves `algorithmId` by suffix and stores it in `RESOLVED_ALGORITHM`; `false` if unknown. -/
private def resolveAndSetAlgorithm (algorithmId : String) (node : NodeId) : ElkM Bool := do
  match ← LayoutMetaDataService.getAlgorithmDataBySuffix algorithmId with
  | some data =>
    ElkM.setNodeProp node CoreOptions.RESOLVED_ALGORITHM data.id
    return true
  | none => return false

/-- Only nodes with children (or with active inside self loops) need an algorithm. -/
private def mustResolve (node : NodeId) : ElkM Bool := do
  let n ← ElkM.getNode node
  let hasResolved := n.props.has CoreOptions.RESOLVED_ALGORITHM
  let insideSelfLoops := (n.props.get CoreOptions.INSIDE_SELF_LOOPS_ACTIVATE).getD false
  return !hasResolved && (!n.children.isEmpty || insideSelfLoops)

/-- `resolveAlgorithm(node)`: the configured algorithm, or the default one for nodes
that need an algorithm; the error message otherwise. -/
def resolveAlgorithm (node : NodeId) : ElkM (Except String Unit) := do
  let algorithmId := ((← ElkM.getNode node).props.get CoreOptions.ALGORITHM).map String.jtrim
    |>.filter (!·.isEmpty)
  if let some id := algorithmId then
    if ← resolveAndSetAlgorithm id node then return .ok ()
  if !(← mustResolve node) then return .ok ()
  let g ← get
  match algorithmId with
  | none =>
    if ← resolveAndSetAlgorithm defaultLayoutAlgorithmId node then return .ok ()
    let message := ElkUtil.printElementPathInto g (.node node)
      s!"Unable to load default layout algorithm {defaultLayoutAlgorithmId} for unconfigured node "
    return .error s!"{unsupportedConfigurationExceptionClass}: {message}"
  | some id =>
    let message := ElkUtil.printElementPathInto g (.node node) s!"Layout algorithm '{id}' not found for "
    return .error s!"{unsupportedConfigurationExceptionClass}: {message}"

/-- `visit(element)`: resolves the algorithm of every node without `NO_LAYOUT`. -/
def visit (r : LayoutAlgorithmResolver) (el : ElementId) : ElkM Unit := do
  let .node node := el | return
  if ((← ElkM.getNode node).props.get CoreOptions.NO_LAYOUT).getD false then return
  if let .error e ← resolveAlgorithm node then
    r.errorsRef.modify (·.push e)

/-- The resolver as an `IGraphElementVisitor`. -/
def toVisitor (r : LayoutAlgorithmResolver) : GraphElementVisitor := { visit := r.visit }

end LayoutAlgorithmResolver

end Elk.Core.Data
