# Corpus performance report

- machine: Apple M1, 8 cores, 8 GiB, macOS 27.0
- models: 1447 (1447 on both engines)

| engine | total ms | models |
|---|---|---|
| rust_api | 3522.4 | 1447 |
| lean_api | 3418.0 | 1447 |

- total lean/rust_api (paired models): 0.97x (3418.0 ms vs 3522.4 ms)
- per-model ratio: geometric mean 0.93x, median 0.93x, min 0.63x, max 1.25x

| ratio | models |
|---|---|
| 0 – 0.8 | 99 |
| 0.8 – 1.0 | 951 |
| 1.0 – 1.2 | 395 |
| 1.2 – 1.5 | 2 |
| 1.5 – 2.0 | 0 |
| 2.0 – 3.0 | 0 |
| ≥ 3.0 | 0 |

| slowest by ratio | lean ms | rust_api ms | ratio |
|---|---|---|---|
| tickets_layered_411_north_south_port_anchor_a | 0.234 | 0.186 | 1.25x |
| tickets_layered_213_componentsCompaction | 1.458 | 1.197 | 1.22x |
| realworld_ptolemy_flattened_pn_countermachine_CounterMachinePrelim.json | 5.199 | 4.355 | 1.19x |
| examples_user-hints_model-order_modelOrderCrossingMinimization | 4.290 | 3.637 | 1.18x |
| tickets_layered_528_nodeEdgeOverlap | 0.727 | 0.617 | 1.18x |
| tickets_layered_528_violatedNodeOrder | 0.323 | 0.281 | 1.15x |
| tests_layered_north_south_ports_linear_segments_cycle | 0.421 | 0.366 | 1.15x |
| realworld_ptolemy_flattened_ddf_eratosthenes_Eratosthenes | 1.408 | 1.230 | 1.15x |
| realworld_ptolemy_flattened_ddf_eratosthenes_Eratosthenes.json | 1.396 | 1.221 | 1.14x |
| realworld_ptolemy_hierarchical_ddf_eratosthenes_Eratosthenes | 1.717 | 1.505 | 1.14x |
| realworld_ptolemy_hierarchical_ddf_eratosthenes_Eratosthenes.json | 1.709 | 1.500 | 1.14x |
| realworld_ptolemy_flattened_pn_countermachine_CounterMachinePrelim | 4.956 | 4.360 | 1.14x |
| realworld_ptolemy_flattened_continuous_continuousinsidede_ContinuousInsideDE | 1.606 | 1.419 | 1.13x |
| tests_layered_compaction_oned_labels_edgeLabelAndSplines | 0.299 | 0.264 | 1.13x |
| tests_layered_compaction_oned_labels_edgeLabelShouldBeCentered | 0.186 | 0.165 | 1.13x |

| largest absolute gap | lean ms | rust_api ms | ratio |
|---|---|---|---|
| realworld_ptolemy_flattened_gr_inversekinematics_InverseKinematics.json | 40.430 | 37.892 | 1.07x |
| realworld_ptolemy_flattened_gr_inversekinematics_InverseKinematics | 40.162 | 37.816 | 1.06x |
| realworld_ptolemy_hierarchical_pn_countermachine_CounterMachineWithException.json | 22.726 | 20.544 | 1.11x |
| realworld_ptolemy_flattened_pn_countermachine_CounterMachineWithException | 25.824 | 23.666 | 1.09x |
| realworld_ptolemy_hierarchical_pn_countermachine_CounterMachineWithException | 22.642 | 20.605 | 1.10x |
| realworld_ptolemy_flattened_ptides_printingpress_PrintingPress.json | 27.297 | 25.524 | 1.07x |
| realworld_ptolemy_hierarchical_pn_countermachine_CounterMachine.json | 19.498 | 17.849 | 1.09x |
| realworld_ptolemy_hierarchical_ptango_temperaturesimulation_EPlusSimulation | 45.273 | 43.860 | 1.03x |
| realworld_ptolemy_hierarchical_pn_countermachine_CounterMachine | 19.197 | 17.832 | 1.08x |
| realworld_ptolemy_flattened_pn_countermachine_CounterMachineWithException.json | 24.844 | 23.659 | 1.05x |
| realworld_ptolemy_flattened_ptides_printingpress_PrintingPress | 26.503 | 25.359 | 1.05x |
| realworld_ptolemy_hierarchical_de_linefault_LineFault | 14.217 | 13.110 | 1.08x |
| realworld_ptolemy_hierarchical_de_linefault_LineFault.json | 14.168 | 13.143 | 1.08x |
| realworld_ptolemy_hierarchical_de_trilateration_Trilateration.json | 55.875 | 54.884 | 1.02x |
| realworld_ptolemy_flattened_pn_countermachine_CounterMachine | 23.049 | 22.152 | 1.04x |

- lean_api total vs baseline (1447 common models): +0.2%
- regression gate (5%): pass
