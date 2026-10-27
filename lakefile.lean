import Lake
open System Lake DSL

/-!
# elk-lean

Pure Lean 4 port of the Eclipse Layout Kernel (ELK) 0.12.0.

The package mirrors the ELK / elk-rs plugin structure: every `lean_lib` below
corresponds to one `org.eclipse.elk.*` plugin and lives in its own
`plugins/org.eclipse.elk.<name>/` directory. Lean module names use the
`Elk.<Plugin>` prefix (`Elk.Core.Math.KVector` ↔ `org.eclipse.elk.core.math.KVector`).

Layering (imports only go downwards):

  Elk.Graph ─┐
  Elk.Core.Math (leaf) ◄─ Elk.Graph.Properties
  Elk.Core ◄─ Elk.Alg.Common ◄─ Elk.Alg.* ◄─ Elk.Json ◄─ Elk.Api ◄─ CLI / Elk.Ffi
-/

package «elk-lean» where
  version := v!"0.12.0"
  leanOptions := #[
    ⟨`autoImplicit, false⟩,
    ⟨`relaxedAutoImplicit, false⟩,
    ⟨`maxHeartbeats, 800000⟩,
    ⟨`maxRecDepth, 4096⟩
  ]
  -- leanc already passes -O3 -DNDEBUG; -fPIC keeps the objects reusable for
  -- the NAPI/WASM shared libraries built from the same object files.
  moreLeancArgs := #["-fPIC"]

/-! ## C helper library (`org.eclipse.elk.core/c`)

Small C shim for things Lean's standard library does not provide with the
exact semantics ELK needs: shortest round-trip `double` formatting
(serde_json/ryu style) and correctly rounded `strtod`. -/

input_file elk_core_ffi.c where
  path := "plugins" / "org.eclipse.elk.core" / "c" / "elk_core_ffi.c"
  text := true

target elk_core_ffi.o pkg : FilePath := do
  let srcJob ← elk_core_ffi.c.fetch
  let oFile := pkg.buildDir / "c" / "elk_core_ffi.o"
  let weakArgs := #["-I", (← getLeanIncludeDir).toString]
  buildO oFile srcJob weakArgs #["-fPIC", "-O2", "-std=c11"] "cc" getLeanTrace

target libelkcoreffi pkg : FilePath := do
  let ffiO ← elk_core_ffi.o.fetch
  let name := nameToStaticLib "elkcoreffi"
  buildStaticLib (pkg.staticLibDir / name) #[ffiO]

/-! ## Plugin libraries -/

/-- `org.eclipse.elk.graph`: ElkGraph data model (arena) and the property system. -/
lean_lib ElkGraph where
  srcDir := "plugins/org.eclipse.elk.graph"
  roots := #[`Elk.Graph]
  globs := #[.andSubmodules `Elk.Graph]

/-- `org.eclipse.elk.core`: options, metadata registry, math, utilities, layout engine. -/
lean_lib ElkCore where
  srcDir := "plugins/org.eclipse.elk.core"
  roots := #[`Elk.Core]
  globs := #[.andSubmodules `Elk.Core]
  moreLinkObjs := #[libelkcoreffi]

/-- `org.eclipse.elk.graph.json`: ELK JSON import/export (elkjs format). -/
lean_lib ElkJson where
  srcDir := "plugins/org.eclipse.elk.graph.json"
  roots := #[`Elk.Json]
  globs := #[.andSubmodules `Elk.Json]

/-- `org.eclipse.elk.alg.common`: shared algorithm infrastructure (node spacing, network simplex, compaction, ...). -/
lean_lib ElkAlgCommon where
  srcDir := "plugins/org.eclipse.elk.alg.common"
  roots := #[`Elk.Alg.Common]
  globs := #[.andSubmodules `Elk.Alg.Common]

/-- `org.eclipse.elk.alg.layered`: the layered (Sugiyama) algorithm. -/
lean_lib ElkAlgLayered where
  srcDir := "plugins/org.eclipse.elk.alg.layered"
  roots := #[`Elk.Alg.Layered]
  globs := #[.andSubmodules `Elk.Alg.Layered]

/-- `org.eclipse.elk.alg.force`: force and stress algorithms. -/
lean_lib ElkAlgForce where
  srcDir := "plugins/org.eclipse.elk.alg.force"
  roots := #[`Elk.Alg.Force]
  globs := #[.andSubmodules `Elk.Alg.Force]

/-- `org.eclipse.elk.alg.mrtree`: tree algorithm. -/
lean_lib ElkAlgMrTree where
  srcDir := "plugins/org.eclipse.elk.alg.mrtree"
  roots := #[`Elk.Alg.MrTree]
  globs := #[.andSubmodules `Elk.Alg.MrTree]

/-- `org.eclipse.elk.alg.radial`: radial algorithm. -/
lean_lib ElkAlgRadial where
  srcDir := "plugins/org.eclipse.elk.alg.radial"
  roots := #[`Elk.Alg.Radial]
  globs := #[.andSubmodules `Elk.Alg.Radial]

/-- `org.eclipse.elk.alg.rectpacking`: rectangle packing. -/
lean_lib ElkAlgRectPacking where
  srcDir := "plugins/org.eclipse.elk.alg.rectpacking"
  roots := #[`Elk.Alg.RectPacking]
  globs := #[.andSubmodules `Elk.Alg.RectPacking]

/-- `org.eclipse.elk.alg.spore`: overlap removal and compaction. -/
lean_lib ElkAlgSpore where
  srcDir := "plugins/org.eclipse.elk.alg.spore"
  roots := #[`Elk.Alg.Spore]
  globs := #[.andSubmodules `Elk.Alg.Spore]

/-- `org.eclipse.elk.alg.disco`: disconnected components layout. -/
lean_lib ElkAlgDisco where
  srcDir := "plugins/org.eclipse.elk.alg.disco"
  roots := #[`Elk.Alg.Disco]
  globs := #[.andSubmodules `Elk.Alg.Disco]

/-- `org.eclipse.elk.alg.topdownpacking`: top-down packing. -/
lean_lib ElkAlgTopdownPacking where
  srcDir := "plugins/org.eclipse.elk.alg.topdownpacking"
  roots := #[`Elk.Alg.TopdownPacking]
  globs := #[.andSubmodules `Elk.Alg.TopdownPacking]

/-- `org.eclipse.elk.alg.vertiflex`: vertically flexible tree layout. -/
lean_lib ElkAlgVertiFlex where
  srcDir := "plugins/org.eclipse.elk.alg.vertiflex"
  roots := #[`Elk.Alg.VertiFlex]
  globs := #[.andSubmodules `Elk.Alg.VertiFlex]

/-- `org.eclipse.elk.alg.libavoid`: libavoid connector (stub, external tool). -/
lean_lib ElkAlgLibavoid where
  srcDir := "plugins/org.eclipse.elk.alg.libavoid"
  roots := #[`Elk.Alg.Libavoid]
  globs := #[.andSubmodules `Elk.Alg.Libavoid]

/-- `org.eclipse.elk.alg.graphviz.{dot,layouter}`: Graphviz connector (stub, external tool). -/
lean_lib ElkAlgGraphviz where
  srcDir := "plugins/org.eclipse.elk.alg.graphviz"
  roots := #[`Elk.Alg.Graphviz]
  globs := #[.andSubmodules `Elk.Alg.Graphviz]

/-- `org.eclipse.elk.graph.text`: the `.elkt` text format (parser/serialiser). -/
lean_lib ElkText where
  srcDir := "plugins/org.eclipse.elk.graph.text"
  roots := #[`Elk.Text]
  globs := #[.andSubmodules `Elk.Text]

/-- Facade: algorithm registration, elkjs-compatible string API, trace support. -/
lean_lib ElkApi where
  srcDir := "plugins/org.eclipse.elk.api"
  roots := #[`Elk.Api]
  globs := #[.andSubmodules `Elk.Api]

/-- C-exported entry points (`@[export elk_...]`) shared by the NAPI and WASM bindings. -/
lean_lib ElkFfi where
  srcDir := "plugins/org.eclipse.elk.ffi"
  roots := #[`Elk.Ffi]
  globs := #[.andSubmodules `Elk.Ffi]

/-! ## Executables -/

/-- Command line interface: `lake exe elk`. -/
@[default_target]
lean_exe elk where
  srcDir := "plugins/org.eclipse.elk.cli"
  root := `Main
  moreLinkObjs := #[libelkcoreffi]

/-- Test suites (`tests/lean/Tests/**`). -/
lean_lib ElkTests where
  srcDir := "tests/lean"
  roots := #[`Tests]
  globs := #[.andSubmodules `Tests]

/-- Unit/regression test driver: `lake test`. -/
@[test_driver]
lean_exe elktest where
  srcDir := "tests/lean"
  root := `Tests.Main
  moreLinkObjs := #[libelkcoreffi]
