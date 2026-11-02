import Elk.Json
import Elk.Text
/-!
# ELK Text → ELK JSON conversion (`convertElkt`)

The conversion behind `elk convert` and the `convertElkt` entry point of the C API, the NAPI
addon, the WASM build and the npm package (no counterpart in ELK Java / elk-rs: elk-live runs the
Xtext language server for this). The browser demo (`plugins/org.eclipse.elk.live`) uses it to
parse `.elkt` text without a server.
-/
namespace Elk.Api

/-- Flags of `convertElkt` as one bit set (`elk_lean_convert_elkt_flags` of the C API):
bit 0 `defaults`, bit 1 `pretty`, bit 2 `sortKeys`. -/
structure ConvertFlags where
  /-- Apply the elk-live default sizes (`Elk.Text.applyDefaults`: nodes 30, ports 5, labels
  `9 * length` x `16`) to shapes without a size (`elk convert --defaults`). -/
  defaults : Bool := false
  /-- Indented output (`--pretty`). -/
  pretty : Bool := false
  /-- Object keys sorted (`--sort-keys`); otherwise in exporter order. -/
  sortKeys : Bool := false

/-- Decodes the C flag bits (`ELK_LEAN_CONVERT_DEFAULTS` = 1, `…_PRETTY` = 2,
`…_SORT_KEYS` = 4); other bits are ignored. -/
def ConvertFlags.ofBits (bits : UInt32) : ConvertFlags :=
  { defaults := bits &&& 1 != 0, pretty := bits &&& 2 != 0, sortKeys := bits &&& 4 != 0 }

/-- Parses ELK Text (`Elk.Text.parseElkt`) and renders the graph as ELK JSON
(`Elk.Json.JsonExporter`), exactly what `elk convert [--defaults] [--pretty] [--sort-keys]` writes.
A parse or linking error is `.error "ELK Text parse error: <line>:<col>: <message>"`. -/
def convertElkt (text : String) (defaults : Bool := false) (pretty : Bool := false)
    (sortKeys : Bool := false) : IO (Except String String) := do
  -- Java's text loader keeps unknown options and unparsable values as `LayoutOptionProxy`
  -- (`PropertyKeyValueConverter` / `PropertyValueValueConverter`), and ELK's JSON export writes
  -- them under the raw key; `elk convert` / `convertElkt` do the same
  match ← Elk.Text.parseElkt text { keepUnknownOptions := true } with
  | .error e => return .error s!"ELK Text parse error: {e}"
  | .ok (root, g) =>
    let g := if defaults then Elk.Text.applyDefaults g root else g
    let v ← Elk.Json.JsonExporter.exportValue g root {}
    return .ok (if pretty then v.renderPretty sortKeys else v.render sortKeys)

/-- `convertElkt` with the flags as a structure. -/
def convertElktWith (text : String) (flags : ConvertFlags) : IO (Except String String) :=
  convertElkt text flags.defaults flags.pretty flags.sortKeys

end Elk.Api
