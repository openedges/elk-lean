# DisCo fixtures

`<name>.json` is an ELK JSON graph that selects `elk.algorithm = disco`; `<name>.expected.json` is
the layout computed by the elk-rs oracle (pretty printed). `Tests.Disco` (`disco.fixtures`)
lays out every `<name>.json` with `Elk.Api.layoutJson` and compares the result with the expected
file within an absolute tolerance of `1e-6` (as `scripts/compare_model_parity_layouts.py`).

## Why the oracle needs a patch

The stock oracle (`.reference/elk-rs-target/release/model_parity_layout_runner`, elk-rs
`eb586b6d`) cannot lay out any graph with DisCo:

```
Couldn't clone property 'org.eclipse.elk.polyomino.lowLevelSort'. Make sure its type is registered with ElkReflect.
```

`DisCoPolyominoCompactor` packs the polyominoes with a `Polyominoes` holder without properties,
so `PolyominoCompactor` reads the *defaults* of the three polyomino enum options, and
`Property::get_default` panics because `LowLevelSortingCriterion`, `HighLevelSortingCriterion`
and `TraversalStrategy` are only registered with `ElkReflect` when
`PolyominoOptions::apply` runs, which nobody does (the Rust unit test
`shared_defaults_and_owned_values_preserve_every_registered_provider` documents this as an
"existing reflection error").

The expected files were produced with a copy of the oracle in which `init_reflect` of
`plugins/org.eclipse.elk.alg.disco/.../options/disco_meta_data_provider.rs` additionally registers
those three types (`ElkReflect::register(Some(|| T::Default), Some(|v: &T| *v))`, the same calls as
`polyomino_options.rs`). Nothing else differs; the layout code is the original one. Rebuild:

```sh
# copy ../elk-rs without target/ and .git to a scratch directory, apply the patch, then
CARGO_TARGET_DIR=<scratch>/target mise exec -- cargo build --release \
  -p org-eclipse-elk-graph-json --bin model_parity_layout_runner
ORACLE_RUNNER=<scratch>/target/release/model_parity_layout_runner sh scripts/oracle_layout.sh in.json out.json
```

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
| `external_ports` | edges between ports of the layout graph and inner nodes (extensions in all four directions, port snapping) |
| `many` | 16 components of random size |
| `sort_options` | `lowLevelSort`, `highLevelSort`, `traversalStrategy` options |
| `single`, `empty`, `zero_size`, `chain`, `strategy_explicit` | degenerate and small graphs, self loop |
| `rand_00` .. `rand_39` | random graphs (2 to 14 nodes; ports, labels, edges with random sections and thickness, `fixed`/`box`/no component algorithm, aspect ratio, component spacing, padding, polyomino options, external ports on all four sides), generated with seeds 1000..1039 |
| `rand_16`, `rand_29` (`.expected.error`) | the oracle panics with a grid index out of bounds (`PlanarGrid::weakly_block_area` is asked to block an area outside the polyomino grid while an extension is added); the Lean layout must fail with the same message |

Notes on the oracle behaviour that the fixtures pin down: the `polyomino.*` sort and traversal
options never reach the packer (the `Polyominoes` holder has no properties, so `PolyominoCompactor`
always uses the defaults); only `polyomino.fill` and `aspectRatio` are read from the graph.

## RJ1: re-pinned outputs

Since RJ1 (node micro layout on Java's cell system, box/fixed option defaults of ELK Java) the
expected files of `box_components`, `external_ports` and `rand_10`, `rand_13`, `rand_17`,
`rand_19`, `rand_20`, `rand_23`, `rand_24`, `rand_27`, `rand_33`, `rand_34`, `rand_35` are elk-lean
outputs, no longer elk-rs ones. They were checked against ELK Java 0.12.0 where Java lays them out:
`rand_20` differs only in the graph size, the others still differ from Java (DisCo itself;
`external_ports`, `rand_17`, `rand_23`, `rand_27`, `rand_33`, `rand_34`: Java throws a
`NullPointerException`).

## SPV: re-pinned outputs

The component layout algorithm (`fixed`, `box`) lays out the whole DisCo graph first, and ELK Java's
`getProperty` stores the cloned default padding of that algorithm (`FixedLayouterOptions.PADDING` /
`BoxLayouterOptions.PADDING` = 15) on the graph (`EMapPropertyHolderImpl`); DisCo's own padding read
afterwards finds 15, not 12. elk-lean now does the same (`ElkM.getNodePropSticky` in the box, fixed and
random providers), which grows the graph size by 6. 35 expected files are the new elk-lean outputs
(`tests/fixtures/opt_java_status.tsv`, rows `SPV re-pin`): `ports`, `rand_19`, `rand_20`, `single`,
`zero_size` equal ELK Java exactly, the graph size equals Java's in 13 of the 42 fixtures Java lays out
(2 before); the others still differ from Java in the DisCo packing itself (outside SPV).
