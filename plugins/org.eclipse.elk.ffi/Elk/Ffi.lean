import Elk.Api
/-!
# C entry points shared by the NAPI and WASM bindings (`org.eclipse.elk.ffi`)

The four functions of the elk-rs bindings (`plugins/org.eclipse.elk.napi/src/lib.rs`,
`plugins/org.eclipse.elk.wasm/src/lib.rs`) exported with C names. Every function returns an
`Except String String` object: `Except.ok json` (constructor tag 1) or `Except.error message`
(tag 0), each with the string in field 0. The C glue (`c/elk_lean.c`) turns them into
`elk_lean_*` functions with plain `char *` results. Outputs are serialised like serde_json
without `preserve_order` (elk-rs): compact, object keys sorted.

C signatures (Lean ≥ 4.2x compiles `BaseIO` without a world token):
```c
lean_object *elk_ffi_layout_json(b_lean_obj_arg graph, b_lean_obj_arg options);
lean_object *elk_ffi_known_layout_algorithms(lean_obj_arg unit);
lean_object *elk_ffi_known_layout_options(lean_obj_arg unit);
lean_object *elk_ffi_known_layout_categories(lean_obj_arg unit);
lean_object *elk_version(void);   /* persistent string constant */
```
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
def layoutJson (graph options : @& String) : BaseIO (Except String String) :=
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

end Elk.Ffi
