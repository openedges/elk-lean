import Elk.Graph.Ids
import Elk.Graph.Enum
/-!
# `org.eclipse.elk.core.validation.{GraphIssue, GraphValidationException}`

A graph issue references the offending element by its arena id
(`Option ElementId`, `none` for issues that concern the whole graph).
`GraphValidationException` is a plain value: `ElkUtil.applyVisitorsWithValidation`
returns it in an `Except` (elk-rs returns `Result<(), GraphValidationException>`).
-/
namespace Elk.Core.Validation

open Elk Elk.Graph

/-- `GraphIssue.Severity`. `toString` is the Java/Rust `Display` (`ERROR`, `WARNING`). -/
elk_enum Severity := error warning

namespace Severity

/-- `Severity.getUserString()`. -/
def userString : Severity → String
  | .error => "Error"
  | .warning => "Warning"

end Severity

/-- `org.eclipse.elk.core.validation.GraphIssue`. -/
structure GraphIssue where
  /-- `getElement()`: the element the issue refers to (`none` = whole graph). -/
  element : Option ElementId
  /-- `getMessage()`. -/
  message : String
  /-- `getSeverity()`. -/
  severity : Severity
  deriving Inhabited, BEq, Repr

/-- Fully qualified Java class name of `GraphValidationException`. -/
def graphValidationExceptionClass : String := "org.eclipse.elk.core.validation.GraphValidationException"

/-- `org.eclipse.elk.core.validation.GraphValidationException`. -/
structure GraphValidationException where
  /-- `getMessage()`. -/
  message : String
  /-- `getIssues()`. -/
  issues : Array GraphIssue
  deriving Inhabited

namespace GraphValidationException

instance : ToString GraphValidationException := ⟨(·.message)⟩

/-- The exception as an `IO.Error` (`<class>: <message>` convention of `Elk.Core.Exceptions`). -/
def toIOError (e : GraphValidationException) : IO.Error :=
  IO.userError s!"{graphValidationExceptionClass}: {e.message}"

end GraphValidationException

end Elk.Core.Validation
