import Elk.Api
/-!
# C entry points shared by the NAPI and WASM bindings (`org.eclipse.elk.ffi`)

The four functions of the elk-rs bindings (`plugins/org.eclipse.elk.napi/src/lib.rs`,
`plugins/org.eclipse.elk.wasm/src/lib.rs`) exported with C names. Every function returns an
`Except String String` object: `Except.ok json` (constructor tag 1) or `Except.error message`
(tag 0), each with the string in field 0. The C glue (`c/elk_lean.c`) turns them into
`elk_lean_*` functions with plain `char *` results. Outputs are serialised like serde_json
without `preserve_order` (elk-rs): compact, object keys sorted. `elk_ffi_convert_elkt` (elk-lean
addition, ELK Text → ELK JSON) renders like `elk convert` instead, as selected by its flag bits.

C signatures (Lean ≥ 4.2x compiles `BaseIO` without a world token):
```c
lean_object *elk_ffi_layout_json(lean_obj_arg graph, lean_obj_arg options);   /* consumes both */
lean_object *elk_ffi_known_layout_algorithms(lean_obj_arg unit);
lean_object *elk_ffi_known_layout_options(lean_obj_arg unit);
lean_object *elk_ffi_known_layout_categories(lean_obj_arg unit);
lean_object *elk_ffi_convert_elkt(lean_obj_arg elkt, uint32_t flags);       /* consumes elkt */
lean_object *elk_ffi_set_threads(uint32_t threads);                          /* returns box(0) */
lean_object *elk_ffi_layout_json_threads(lean_obj_arg graph, lean_obj_arg options, uint32_t threads);
lean_object *elk_version(void);   /* persistent string constant */
```
`elk_ffi_set_threads` / `elk_ffi_layout_json_threads` (elk-lean, agent PAR) configure the parallel
sibling layout (`Elk.Core.Parallel`, `docs/parallel-layout.md`); the library default without them is
sequential. The C glue calls them from `elk_lean_init_threads` / `elk_lean_layout_json_threads`
after starting the Lean task manager.
-/
namespace Elk.Ffi

open Elk.Json

/-- Version string exported to C as `elk_version`. -/
@[export elk_version]
def version : String := Elk.Api.version

/-- Runs an API action, turning thrown errors into `Except.error`. -/
def guard (act : IO (Except String String)) : BaseIO (Except String String) := do
  match ← act.toBaseIO with
  | .ok r => return r
  | .error e => return .error (toString e)

/-- elk-rs `layout_api::layout_json(graph_json, options_json)` (NAPI `layout_json`). -/
@[export elk_ffi_layout_json]
def layoutJson (graph options : String) : BaseIO (Except String String) :=
  guard (Elk.Api.layoutJson graph options (sortKeys := true))

/-- elk-rs `layout_api::known_layout_algorithms()`. -/
@[export elk_ffi_known_layout_algorithms]
def knownLayoutAlgorithms (_ : Unit) : BaseIO (Except String String) :=
  guard do return .ok ((← Elk.Api.knownLayoutAlgorithmsValue).render (sortKeys := true))

/-- elk-rs `layout_api::known_layout_options()`. -/
@[export elk_ffi_known_layout_options]
def knownLayoutOptions (_ : Unit) : BaseIO (Except String String) :=
  guard do return .ok ((← Elk.Api.knownLayoutOptionsValue).render (sortKeys := true))

/-- elk-rs `layout_api::known_layout_categories()`. -/
@[export elk_ffi_known_layout_categories]
def knownLayoutCategories (_ : Unit) : BaseIO (Except String String) :=
  guard do return .ok ((← Elk.Api.knownLayoutCategoriesValue).render (sortKeys := true))

/-- elk-lean addition: ELK Text → ELK JSON (`Elk.Api.convertElkt`, `elk convert`). `flags`:
bit 0 `--defaults`, bit 1 `--pretty`, bit 2 `--sort-keys` (`Elk.Api.ConvertFlags.ofBits`); `0` is
the output of `elk convert INPUT.elkt`. Errors are the CLI's message
(`ELK Text parse error: <line>:<col>: <message>`). -/
@[export elk_ffi_convert_elkt]
def convertElkt (text : String) (flags : UInt32) : BaseIO (Except String String) :=
  guard (Elk.Api.convertElktWith text (Elk.Api.ConvertFlags.ofBits flags))

/-- elk-lean addition (agent PAR): the thread cap of the parallel sibling layout
(`Elk.Core.Parallel.configure`; `0` = `ELK_LEAN_THREADS` or `min(hardware threads, 8)`, `1` =
sequential). Called by `elk_lean_init_threads` once the task manager runs. -/
@[export elk_ffi_set_threads]
def setThreads (threads : UInt32) : BaseIO Unit := do
  let _ ← (Elk.Core.Parallel.configure threads.toNat).toBaseIO

/-- `layoutJson` with the thread cap `threads` for this call (`0` = the configured cap,
`Elk.Core.Parallel.withThreads`). The result does not depend on it. -/
@[export elk_ffi_layout_json_threads]
def layoutJsonThreads (graph options : String) (threads : UInt32) : BaseIO (Except String String) :=
  guard (Elk.Core.Parallel.withThreads threads.toNat (Elk.Api.layoutJson graph options (sortKeys := true)))

end Elk.Ffi
