import Elk.Graph.Monad
import Elk.Core.Validation.GraphIssue
/-!
# `org.eclipse.elk.core.util.IGraphElementVisitor`

A visitor is a record of closures over the `ElkM` state monad. Stateful
visitors (resolvers, validators) keep their state in an `IO.Ref` captured by
the closures; validating visitors (`IValidatingGraphElementVisitor`) expose
their issues through `issues`.
-/
namespace Elk.Core.Util

open Elk.Graph Elk.Core.Validation

/-- `org.eclipse.elk.core.util.IGraphElementVisitor`. -/
structure GraphElementVisitor where
  /-- `visit(element)`. -/
  visit : ElementId → ElkM Unit
  /-- `IValidatingGraphElementVisitor.getIssues()`; `none` for non-validating visitors
  (elk-rs `issues()` default implementation). -/
  issues : Option (IO (Array GraphIssue)) := none

namespace GraphElementVisitor

instance : Inhabited GraphElementVisitor := ⟨{ visit := fun _ => pure () }⟩

/-- A visitor from a closure (elk-rs `impl IGraphElementVisitor for FnMut`). -/
def ofFn (f : ElementId → ElkM Unit) : GraphElementVisitor := { visit := f }

/-- `issues()`: the current issues of a validating visitor, `none` otherwise. -/
def getIssues (v : GraphElementVisitor) : IO (Option (Array GraphIssue)) :=
  match v.issues with
  | some get => some <$> get
  | none => pure none

/-- `true` for `IValidatingGraphElementVisitor`s. -/
def isValidating (v : GraphElementVisitor) : Bool := v.issues.isSome

end GraphElementVisitor

end Elk.Core.Util

namespace Elk.Core.Validation

/-- `org.eclipse.elk.core.validation.IValidatingGraphElementVisitor`: a visitor whose
`issues` accessor is set. -/
abbrev IValidatingGraphElementVisitor := Elk.Core.Util.GraphElementVisitor

end Elk.Core.Validation
