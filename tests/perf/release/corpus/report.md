# Corpus performance report

- machine: Apple M1, 8 cores, 8 GiB, macOS 27.0
- models: 1447 (1447 on both engines)

| engine | total ms | models |
|---|---|---|
| rust_api | 3531.7 | 1447 |
| lean_api | 2534.3 | 1447 |

- total lean/rust_api (paired models): 0.72x (2534.3 ms vs 3531.7 ms)
- per-model ratio: geometric mean 0.65x, median 0.66x, min 0.38x, max 1.07x

| ratio | models |
|---|---|
| 0 – 0.8 | 1350 |
| 0.8 – 1.0 | 95 |
| 1.0 – 1.2 | 2 |
| 1.2 – 1.5 | 0 |
| 1.5 – 2.0 | 0 |
| 2.0 – 3.0 | 0 |
| ≥ 3.0 | 0 |

| slowest by ratio | lean ms | rust_api ms | ratio |
|---|---|---|---|
| tests_layered_interactive_layout_nodePositions | 0.126 | 0.117 | 1.07x |
| tests_layered_hyperedge_merging_hyperedge_labels | 0.331 | 0.327 | 1.01x |
| realworld_ptolemy_flattened_ptolemy_electricpowersystem_GeneratorRegulatorProtectorWithBusNotAsAspect.json | 1.601 | 1.727 | 0.93x |
| tests_layered_north_south_ports_south_multiple | 0.527 | 0.588 | 0.90x |
| tests_layered_node_placement_flexible_ports_graph04 | 0.246 | 0.278 | 0.89x |
| realworld_ptolemy_flattened_de_primetest_PrimeTest.json | 2.134 | 2.416 | 0.88x |
| realworld_ptolemy_flattened_pn_countermachine_CounterMachineWithException.json | 20.913 | 23.804 | 0.88x |
| realworld_ptolemy_flattened_gr_inversekinematics_InverseKinematics.json | 32.699 | 37.765 | 0.87x |
| realworld_ptolemy_flattened_pn_stack_Stack.json | 3.054 | 3.534 | 0.86x |
| tests_layered_hierarchical_ports_hierarchy06 | 0.396 | 0.459 | 0.86x |
| realworld_ptolemy_flattened_ptides_trex_TREXNoNetworkAllDigital | 9.068 | 10.552 | 0.86x |
| tests_layered_north_south_ports_linear_segments_cycle | 0.316 | 0.368 | 0.86x |
| realworld_ptolemy_flattened_pn_countermachine_CounterMachine | 19.449 | 22.714 | 0.86x |
| realworld_ptolemy_flattened_unit_staticunits_StaticUnits.json | 1.030 | 1.203 | 0.86x |
| realworld_ptolemy_flattened_ptango_chat_ChatServer.json | 2.034 | 2.380 | 0.85x |

| largest absolute gap | lean ms | rust_api ms | ratio |
|---|---|---|---|
| tests_layered_interactive_layout_nodePositions | 0.126 | 0.117 | 1.07x |
| tests_layered_hyperedge_merging_hyperedge_labels | 0.331 | 0.327 | 1.01x |
| tests_layered_interactive_layout_sameLayerEdges | 0.072 | 0.090 | 0.79x |
| examples_user-hints_interactive-constraints_interactiveRectpacking_hierarchy | 0.023 | 0.045 | 0.50x |
| examples_user-hints_interactive-constraints_interactiveRectpacking_oneBigNode | 0.030 | 0.055 | 0.55x |
| tickets_core_489_paddingAndMinSize_Small | 0.032 | 0.059 | 0.54x |
| tickets_core_489_paddingAndMinSize_Large | 0.033 | 0.061 | 0.55x |
| tickets_core_457_boxLayouterIgnoresMinimumSize | 0.034 | 0.062 | 0.55x |
| tests_layered_partitioning_nonConsecutivePartitions | 0.072 | 0.100 | 0.72x |
| tests_layered_interactive_layout_firstLayer | 0.065 | 0.095 | 0.69x |
| tests_layered_node_placement_flexible_ports_graph04 | 0.246 | 0.278 | 0.89x |
| tickets_core_475_fixedLayoutWithLongLabels | 0.024 | 0.056 | 0.43x |
| tests_layered_interactive_layout_firstPosition | 0.057 | 0.089 | 0.64x |
| tickets_core_245_surroundingPortSpace | 0.031 | 0.063 | 0.49x |
| tickets_core_269_portAlignmendIsIgnored | 0.029 | 0.062 | 0.47x |

- lean_api total vs baseline (1447 common models): -6.7%
- regression gate (5%): pass
