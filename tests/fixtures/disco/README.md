# DisCo fixtures

`<name>.json` is an ELK JSON graph that selects `elk.algorithm = disco`. Its expectation is the
result of unmodified ELK Java 0.12.0 (`scripts/run_java_baseline.sh`, one fresh JVM):
`<name>.java.json` is Java's layout (Gson output, indent 1, sorted keys) and `<name>.java.error`
Java's exception text. `Tests.Disco` (`disco.fixtures`) lays out every `<name>.json` with
`Elk.Api.layoutJson` and compares at tolerance `0` (`Tests.JsonCompare.checkJson`), or compares the
exception text. `java/` holds random DisCo inputs (suite `disco.java`, see `java/README.md`).

## History

The fixtures were written for the DisCo port (agent F3) against a patched elk-rs oracle (the stock
`model_parity_layout_runner` panics for every DisCo layout, `Couldn't clone property
'org.eclipse.elk.polyomino.lowLevelSort'`), partly re-pinned to elk-lean outputs by RJ1 and SPV, and
re-pinned to ELK Java by agent DIS. Before DIS, 7 of the 42 layouts Java produces were equal to
Java and none of the 16 Java exceptions; now all 58 are. What the elk-rs port did differently
(`docs/robustness-random-graphs.md` §17):

* `PolyominoCompactor` sorts with the low-level comparator `.reversed()` (largest polyominoes
  first; elk-rs ascending) — the difference of almost every multi-component fixture;
* `PolyominoOptions` is registered (Java loads it through the `ServiceLoader` entry of
  `org.eclipse.elk.alg.common`), so `org.eclipse.elk.polyomino.fill = false` takes effect
  (`fill_false`, `rand_38`); the sort and traversal options still never reach the packer (Java reads
  them from an empty `Polyominoes` holder), so `sort_options` equals the default packing;
* an edge whose source is the layout root (`external_ports`, 14 `rand_*`) makes Java's
  `getSourceNode(edge).getParent().equals(...)` throw a `NullPointerException`;
* `rand_16`: the grid bounds message of `TwoBitGrid` (Java reads a cell right of the width inside
  the last 32-cell word as empty and fails on the write).

## Cases

| name | what it covers |
|---|---|
| `basic` | connected pair + isolated nodes, `fixed` component layout |
| `nolayout` | no component layout algorithm, bend points, nodes at given positions |
| `box_components` | `box` as component layout algorithm, `spacing.nodeNode` |
| `aspect_wide`, `aspect_tall` | `aspectRatio` 3.0 and 0.4 (cell size scaling, grid shape) |
| `fill_false`, `fill_true` | `polyomino.fill` |
| `spacing_padding` | `spacing.componentComponent`, asymmetric padding, edge thickness 6 with bend points |
| `labels` | node, port, edge and port label shapes |
| `ports` | ports with several edges, edges with bend points |
| `external_ports` | edges between ports of the layout graph and inner nodes (Java: `NullPointerException` for the edges that start at the root) |
| `many` | 16 components of random size |
| `sort_options` | `lowLevelSort`, `highLevelSort`, `traversalStrategy` options (no effect in Java) |
| `single`, `empty`, `zero_size`, `chain`, `strategy_explicit` | degenerate and small graphs, self loop |
| `rand_00` .. `rand_39` | random graphs (2 to 14 nodes; ports, labels, edges with random sections and thickness, `fixed`/`box`/no component algorithm, aspect ratio, component spacing, padding, polyomino options, external ports on all four sides), generated with seeds 1000..1039 |
