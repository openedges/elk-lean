# Corpus performance report

- machine: Apple M1, 8 cores, 8 GiB, macOS 27.0
- models: 1447 (1447 on both engines)

| engine | total ms | models |
|---|---|---|
| rust_api | 3518.2 | 1447 |
| lean_api | 3453.4 | 1447 |

- total lean/rust_api (paired models): 0.98x (3453.4 ms vs 3518.2 ms)
- per-model ratio: geometric mean 0.95x, median 0.95x, min 0.67x, max 1.71x

| ratio | models |
|---|---|
| 0 – 0.8 | 46 |
| 0.8 – 1.0 | 889 |
| 1.0 – 1.2 | 503 |
| 1.2 – 1.5 | 7 |
| 1.5 – 2.0 | 2 |
| 2.0 – 3.0 | 0 |
| ≥ 3.0 | 0 |

| slowest by ratio | lean ms | rust_api ms | ratio |
|---|---|---|---|
| tests_layered_interactive_layout_sameLayerEdges | 0.156 | 0.091 | 1.71x |
| tickets_layered_213_componentsCompaction | 1.966 | 1.199 | 1.64x |
| examples_user-hints_model-order_modelOrderCrossingMinimization | 5.389 | 3.623 | 1.49x |
| tests_layered_compaction_oned_labels_edgeLabelAndSplines | 0.368 | 0.266 | 1.39x |
| tests_layered_compaction_oned_labels_edgeLabelShouldBeCentered | 0.210 | 0.164 | 1.28x |
| tickets_layered_411_north_south_port_anchor_a | 0.235 | 0.186 | 1.26x |
| examples_user-hints_interactive-constraints_interactiveLayeredLayout_circle_pseudo_positions | 0.198 | 0.160 | 1.23x |
| examples_ports_allowNonFlowPortsToSwitchSides | 0.256 | 0.210 | 1.22x |
| tests_layered_inverted_ports_east_input | 0.160 | 0.133 | 1.20x |
| tests_layered_compaction_oned_labels_edgeLabelSideSelection01 | 0.248 | 0.208 | 1.20x |
| tests_layered_compaction_oned_nsport_south_port | 0.197 | 0.165 | 1.19x |
| tickets_layered_528_nodeEdgeOverlap | 0.734 | 0.621 | 1.18x |
| tickets_layered_288_selfLoopsCauseNPE_a | 0.259 | 0.220 | 1.17x |
| tests_layered_north_south_ports_linear_segments_cycle | 0.429 | 0.366 | 1.17x |
| tickets_layered_528_violatedNodeOrder | 0.327 | 0.280 | 1.17x |

| largest absolute gap | lean ms | rust_api ms | ratio |
|---|---|---|---|
| realworld_ptolemy_flattened_gr_inversekinematics_InverseKinematics | 40.325 | 37.659 | 1.07x |
| realworld_ptolemy_flattened_gr_inversekinematics_InverseKinematics.json | 40.268 | 37.670 | 1.07x |
| realworld_ptolemy_hierarchical_pn_countermachine_CounterMachineWithException.json | 23.030 | 20.608 | 1.12x |
| realworld_ptolemy_flattened_pn_countermachine_CounterMachineWithException | 26.330 | 23.920 | 1.10x |
| realworld_ptolemy_hierarchical_pn_countermachine_CounterMachineWithException | 22.948 | 20.591 | 1.11x |
| realworld_ptolemy_hierarchical_pn_countermachine_CounterMachine | 19.380 | 17.489 | 1.11x |
| realworld_ptolemy_hierarchical_pn_countermachine_CounterMachine.json | 19.402 | 17.513 | 1.11x |
| examples_user-hints_model-order_modelOrderCrossingMinimization | 5.389 | 3.623 | 1.49x |
| realworld_ptolemy_flattened_pn_countermachine_CounterMachine.json | 23.789 | 22.324 | 1.07x |
| realworld_ptolemy_flattened_pn_countermachine_CounterMachineWithException.json | 25.233 | 23.942 | 1.05x |
| realworld_ptolemy_hierarchical_de_linefault_LineFault | 14.299 | 13.095 | 1.09x |
| realworld_ptolemy_hierarchical_de_linefault_LineFault.json | 14.334 | 13.135 | 1.09x |
| realworld_ptolemy_flattened_ptides_printingpress_PrintingPress | 26.691 | 25.524 | 1.05x |
| realworld_ptolemy_flattened_ptides_printingpress_PrintingPress.json | 26.666 | 25.689 | 1.04x |
| realworld_ptolemy_hierarchical_de_trilateration_Trilateration | 55.841 | 54.886 | 1.02x |

- lean_api total vs baseline (1447 common models): -3.1%
- regression gate (5%): pass
