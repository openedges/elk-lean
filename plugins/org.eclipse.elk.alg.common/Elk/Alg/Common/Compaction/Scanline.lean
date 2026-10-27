import Elk.Core.Util.Sort
/-!
# `org.eclipse.elk.alg.common.compaction.Scanline`

Generic scanline (elk-rs `scanline.rs`): sorts the points with the comparator (stable, like
Rust `sort_by`) and feeds them to the event handler(s) in that order. The handler is a
structure of closures in an arbitrary monad, which carries the handler state (Rust
`&mut self`).
-/
namespace Elk.Alg.Common.Compaction

open Elk.Core.Util

/-- `Scanline.EventHandler<T>`. -/
structure EventHandler (m : Type → Type) (α : Type) where
  /-- `handle(point)`. -/
  handle : α → m Unit

namespace Scanline

/-- `Scanline::execute(points, comparator, handler)`. -/
def execute {m : Type → Type} [Monad m] {α : Type} [Inhabited α] (points : Array α)
    (comparator : α → α → Ordering) (handler : EventHandler m α) : m Unit := do
  let points := stableSort points comparator
  for p in points do
    handler.handle p

/-- `Scanline::execute_with_handlers(points, comparator, handlers)`: every point is passed to
all handlers (in order) before the next point is processed. -/
def executeWithHandlers {m : Type → Type} [Monad m] {α : Type} [Inhabited α] (points : Array α)
    (comparator : α → α → Ordering) (handlers : Array (EventHandler m α)) : m Unit := do
  let points := stableSort points comparator
  for p in points do
    for h in handlers do
      h.handle p

end Scanline

end Elk.Alg.Common.Compaction
