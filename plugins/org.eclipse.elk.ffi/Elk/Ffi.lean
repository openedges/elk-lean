import Elk.Api
/-! C-exported entry points shared by the NAPI and WASM bindings (filled in Phase 8). -/
namespace Elk.Ffi
/-- Version string exported to C as `elk_version`. -/
@[export elk_version]
def version : String := Elk.Api.version
end Elk.Ffi
