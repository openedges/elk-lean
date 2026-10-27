import Elk.Alg.RectPacking.Util.RectPackingArena
/-!
# `rows_storage` (elk-rs `util/rows_storage.rs`, no Java counterpart)

Java stores the packed rows directly in a graph property (`InternalProperties.ROWS`); elk-rs keeps
them in a thread-local map keyed by the address of the graph node and stores only the key in the
property. elk-lean keeps the map in the `RectPackingArena` (`storedRows`, insertion ordered) and
uses the graph node's arena index as the key. `withRowsGuard` is Rust `RowsGuard`: the rows
stored for the graph are removed when the guarded action ends (also on exceptions).
-/
namespace Elk.Alg.RectPacking.Util

open Elk.Graph
open RectPackingM

namespace RowsStorage

/-- `graph_key(graph)`. -/
@[inline] def graphKey (graph : NodeId) : Int := graph.idx

/-- `store_rows(graph, rows)`: stores (replacing) the rows of the graph and returns the key. -/
def storeRows (graph : NodeId) (rows : Array RectRowId) : RectPackingM Int := do
  let key := graphKey graph
  modifyThe RectPackingArena fun a =>
    match a.storedRows.findIdx? (·.1 == key) with
    | some i => { a with storedRows := a.storedRows.set! i (key, rows) }
    | none => { a with storedRows := a.storedRows.push (key, rows) }
  return key

/-- `get_rows(key)`. -/
def getRows (key : Int) : RectPackingM (Option (Array RectRowId)) := do
  return ((← getThe RectPackingArena).storedRows.find? (·.1 == key)).map (·.2)

/-- `take_rows(key)`: removes and returns the rows stored under the key. -/
def takeRows (key : Int) : RectPackingM (Option (Array RectRowId)) := do
  let rows ← getRows key
  modifyThe RectPackingArena fun a => { a with storedRows := a.storedRows.filter (·.1 != key) }
  return rows

/-- `RowsGuard::new(graph)` + drop: runs `x` and removes the rows stored for the graph
afterwards. -/
def withRowsGuard {α : Type} (graph : NodeId) (x : RectPackingM α) : RectPackingM α := do
  try x finally
    let _ ← takeRows (graphKey graph)

end RowsStorage

end Elk.Alg.RectPacking.Util
