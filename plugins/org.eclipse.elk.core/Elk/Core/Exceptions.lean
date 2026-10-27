import Elk.Core.Util.FastFloat
/-!
# ELK exceptions

ELK reports invalid graphs/configurations with Java exceptions. The Lean port
raises `IO.userError` whose message starts with the fully qualified Java class
name, exactly like the elk-rs JSON API reports them
(`org.eclipse.elk.core.UnsupportedConfigurationException: ...`).
-/
namespace Elk.Core

def unsupportedGraphExceptionClass : String := "org.eclipse.elk.core.UnsupportedGraphException"
def unsupportedConfigurationExceptionClass : String := "org.eclipse.elk.core.UnsupportedConfigurationException"
def illegalStateExceptionClass : String := "java.lang.IllegalStateException"
def illegalArgumentExceptionClass : String := "java.lang.IllegalArgumentException"
def nullPointerExceptionClass : String := "java.lang.NullPointerException"
def indexOutOfBoundsExceptionClass : String := "java.lang.IndexOutOfBoundsException"
def unsupportedOperationExceptionClass : String := "java.lang.UnsupportedOperationException"

/-- Builds the error for a Java exception class and message. -/
def javaException (cls msg : String) : IO.Error := IO.userError s!"{cls}: {msg}"

/-- `throw new UnsupportedGraphException(msg)`. -/
def throwUnsupportedGraph {m : Type → Type} [MonadExcept IO.Error m] {α : Type} (msg : String) : m α :=
  throw (javaException unsupportedGraphExceptionClass msg)

/-- `throw new UnsupportedConfigurationException(msg)`. -/
def throwUnsupportedConfiguration {m : Type → Type} [MonadExcept IO.Error m] {α : Type} (msg : String) : m α :=
  throw (javaException unsupportedConfigurationExceptionClass msg)

/-- `throw new IllegalStateException(msg)`. -/
def throwIllegalState {m : Type → Type} [MonadExcept IO.Error m] {α : Type} (msg : String) : m α :=
  throw (javaException illegalStateExceptionClass msg)

/-- `throw new IllegalArgumentException(msg)`. -/
def throwIllegalArgument {m : Type → Type} [MonadExcept IO.Error m] {α : Type} (msg : String) : m α :=
  throw (javaException illegalArgumentExceptionClass msg)

/-- `throw new NullPointerException(msg)` — used where Java would dereference `null`. -/
def throwNullPointer {m : Type → Type} [MonadExcept IO.Error m] {α : Type} (msg : String) : m α :=
  throw (javaException nullPointerExceptionClass msg)

/-- Generic runtime failure keeping the Java class-name convention. -/
def throwJava {m : Type → Type} [MonadExcept IO.Error m] {α : Type} (cls msg : String) : m α :=
  throw (javaException cls msg)

/-- Message of an `IO.Error` (for API error reporting). -/
def errorMessage (e : IO.Error) : String := toString e

end Elk.Core
