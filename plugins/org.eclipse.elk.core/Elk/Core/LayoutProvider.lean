import Elk.Graph
import Elk.Core.Util
import Elk.Core.Data
/-!
# `org.eclipse.elk.core.AbstractLayoutProvider` and the provider registry

A layout provider lays out the children of a node of the `ElkGraph` arena.
Providers are plain records of functions; the registry maps algorithm ids to
provider factories (replacing elk-rs's `InstancePool`/`AlgorithmFactory`).
Algorithm plugins register themselves through `Elk.Api.ensureInitialized`.
-/
namespace Elk.Core

open Elk.Graph Elk.Core.Util

/-- `AbstractLayoutProvider`. -/
structure LayoutProvider where
  /-- Algorithm id, for diagnostics. -/
  id : String
  /-- `initialize(String parameter)`. -/
  init : Option String → IO Unit := fun _ => pure ()
  /-- `layout(ElkNode layoutGraph, IElkProgressMonitor progressMonitor)`. -/
  layout : NodeId → ProgressMonitor → ElkM Unit
  /-- `dispose()`. -/
  dispose : IO Unit := pure ()

namespace LayoutProvider

builtin_initialize registryRef : IO.Ref (Std.HashMap String (Unit → LayoutProvider)) ← IO.mkRef {}

/-- Registers (or overrides) the provider factory of an algorithm. -/
def register (algorithmId : String) (factory : Unit → LayoutProvider) : IO Unit :=
  registryRef.modify (·.insert algorithmId factory)

/-- Creates a provider for the algorithm, if one is registered. -/
def create (algorithmId : String) : IO (Option LayoutProvider) := do
  return ((← registryRef.get).get? algorithmId).map (· ())

def isRegistered (algorithmId : String) : IO Bool := do
  return (← registryRef.get).contains algorithmId

def registeredIds : IO (Array String) := do
  return (← registryRef.get).toArray.map (·.1)

end LayoutProvider

end Elk.Core
