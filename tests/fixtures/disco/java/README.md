# Random DisCo inputs pinned to ELK Java (agent DIS)

Inputs of the random DisCo sets (`scripts/gen_disco_graphs.py`, `scripts/run_random_java_parity.sh
--sets c`, seeds 1–10; the name ends with set and graph, e.g. `c7_g0355` = `gen/c7/g0355.json`)
whose elk-lean result differed from ELK Java 0.12.0 before agent DIS, two per kind, plus hand-made
ones. `<name>.java.json` / `<name>.java.error` come from unmodified ELK Java in a fresh JVM
(`scripts/run_java_baseline.sh`); suite `disco.java` (`Tests/lean/Tests/Disco.lean`) compares at
tolerance `0` or compares the exception text.

| prefix | Java behaviour that elk-lean did not follow |
|---|---|
| `packing_order_*`, `aspect_ratio_*`, `component_layout_{box,fixed,layered,rectpacking}_*` | `PolyominoCompactor` sorts largest first (`.reversed()` low-level comparator) |
| `fill_false_*` | `org.eclipse.elk.polyomino.fill` is a registered option (`PolyominoOptions` provider) |
| `random_component_layout_*` | `RandomLayoutProvider.RAND_FACT = 0.2f` widened to `double` (bend point jitter) |
| `nested_extensions_*` | DisCo on a compound child: extensions in both directions, port snapping |
| `root_outgoing_extensions_*` | edges from children to ports of the layout root are DisCo extensions (no exception) |
| `npe_root_incoming_edge_*` | an edge from a port of the layout root: `NullPointerException` in `ElkGraphComponentsProcessor` |
| `layered_root_external_ports_*` | `layered` as component layout algorithm on a root with external ports: `ElkGraphImporter.transformExternalPort` reads `elkgraph.getParent()` → `NullPointerException` |
| `grid_bounds_center_*` | `PlanarGrid` center-based accessors: message of the translated point plus `Given center based coordinates were (x, y).` |
| `hyperedge_fixed_*` | `fixed` as component layout algorithm: `FixedLayoutProvider` calls `getSourceNode` on every incoming edge (`IllegalArgumentException` for a hyperedge, before DisCo's own `NullPointerException`) |
| `empty_grid_int_bounds` | hand-made: no blocked grid cell, `getFilledBounds` in Java `int` arithmetic (`MAX_VALUE`, sizes `2`) |
| `aspect_ratio_{zero,nan,negative,tiny,huge}` | hand-made: `elk.aspectRatio` `0`, `NaN`, `-1`, `1e-9`, `1e9` reach DisCo (no option validation on Java's JSON path): infinite/NaN cell height (NaN and huge coordinates), `NegativeArraySizeException: -7`, `OutOfMemoryError: Requested array size exceeds VM limit`, `OutOfMemoryError: Java heap space` (elk-lean refuses grids above 2^26 words with Java's text instead of allocating them) |

Not pinned because ELK Java itself depends on the JVM context: ports with two or more extension
edges (the first edge of `incomingExtensionsMapping`, a `HashMap` keyed by identity hash, decides the
port position — the same input gives two different layouts in fresh JVMs after a different number of
earlier layouts), the exception text of a parallel stream in `computeIncidences` (thrown in a
`ForkJoinPool` worker: bare `java.lang.NullPointerException`, or `IllegalArgumentException:
java.lang.IllegalArgumentException: …` from `ForkJoinTask`'s rethrow), and which extension's grid
bounds error comes first (`HashSet<DCElement>` order of `DCComponent`).
