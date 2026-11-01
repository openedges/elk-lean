# Corpus performance report

- machine: Apple M1, 8 cores, 8 GiB, macOS 27.0
- models: 1447 (1447 on both engines)

| engine | total ms | models |
|---|---|---|
| rust_api | 3526.6 | 1447 |
| lean_api | 3362.0 | 1447 |

- total lean/rust_api (paired models): 0.95x (3362.0 ms vs 3526.6 ms)
- per-model ratio: geometric mean 0.91x, median 0.91x, min 0.63x, max 1.20x

| ratio | models |
|---|---|
| 0 – 0.8 | 140 |
| 0.8 – 1.0 | 1015 |
| 1.0 – 1.2 | 292 |
| 1.2 – 1.5 | 0 |
| 1.5 – 2.0 | 0 |
| 2.0 – 3.0 | 0 |
| ≥ 3.0 | 0 |

| slowest by ratio | lean ms | rust_api ms | ratio |
|---|---|---|---|
| tests_layered_compaction_oned_labels_edgeLabelAndSplines | 0.318 | 0.265 | 1.20x |
| tickets_layered_411_north_south_port_anchor_a | 0.223 | 0.188 | 1.19x |
| tickets_layered_213_componentsCompaction | 1.424 | 1.202 | 1.18x |
| realworld_ptolemy_flattened_de_ramprollback_RampRollback.json | 1.303 | 1.103 | 1.18x |
| examples_user-hints_model-order_modelOrderCrossingMinimization | 4.157 | 3.627 | 1.15x |
| tickets_layered_528_nodeEdgeOverlap | 0.706 | 0.618 | 1.14x |
| tests_layered_compaction_oned_labels_edgeLabelShouldBeCentered | 0.185 | 0.164 | 1.13x |
| realworld_ptolemy_hierarchical_ddf_eratosthenes_Eratosthenes | 1.696 | 1.504 | 1.13x |
| realworld_ptolemy_flattened_pn_blindcommunication_BlindCommunication.json | 3.454 | 3.070 | 1.13x |
| tickets_layered_403_stackedSelfLoopLabels | 0.281 | 0.250 | 1.12x |
| tickets_layered_528_violatedNodeOrder | 0.312 | 0.279 | 1.12x |
| realworld_ptolemy_flattened_ddf_eratosthenes_Eratosthenes | 1.377 | 1.233 | 1.12x |
| tests_layered_splines_north_south_ports_3 | 0.273 | 0.245 | 1.11x |
| realworld_ptolemy_flattened_ddf_eratosthenes_Eratosthenes.json | 1.355 | 1.219 | 1.11x |
| realworld_ptolemy_hierarchical_ddf_eratosthenes_Eratosthenes.json | 1.663 | 1.500 | 1.11x |

| largest absolute gap | lean ms | rust_api ms | ratio |
|---|---|---|---|
| realworld_ptolemy_flattened_gr_inversekinematics_InverseKinematics.json | 40.418 | 38.053 | 1.06x |
| realworld_ptolemy_flattened_gr_inversekinematics_InverseKinematics | 40.609 | 38.754 | 1.05x |
| realworld_ptolemy_hierarchical_pn_countermachine_CounterMachineWithException.json | 22.358 | 20.579 | 1.09x |
| realworld_ptolemy_hierarchical_pn_countermachine_CounterMachineWithException | 22.214 | 20.676 | 1.07x |
| realworld_ptolemy_hierarchical_pn_countermachine_CounterMachine.json | 18.793 | 17.528 | 1.07x |
| realworld_ptolemy_hierarchical_pn_countermachine_CounterMachine | 18.782 | 17.632 | 1.07x |
| realworld_ptolemy_flattened_pn_countermachine_CounterMachineWithException | 24.903 | 23.850 | 1.04x |
| realworld_ptolemy_hierarchical_de_linefault_LineFault | 13.922 | 13.088 | 1.06x |
| realworld_ptolemy_flattened_pn_countermachine_CounterMachineWithException.json | 24.671 | 23.876 | 1.03x |
| realworld_ptolemy_flattened_ptides_printingpress_PrintingPress | 26.114 | 25.433 | 1.03x |
| realworld_ptolemy_hierarchical_de_linefault_LineFault.json | 14.026 | 13.366 | 1.05x |
| realworld_ptolemy_flattened_ptides_printingpress_PrintingPress.json | 26.044 | 25.400 | 1.03x |
| realworld_ptolemy_flattened_pn_countermachine_CounterMachine | 22.986 | 22.345 | 1.03x |
| realworld_ptolemy_hierarchical_ptides_trex_TREXNoNetworkAllDigital | 17.252 | 16.650 | 1.04x |
| realworld_ptolemy_flattened_pn_countermachine_CounterMachine.json | 22.809 | 22.273 | 1.02x |

- lean_api total vs baseline (1447 common models): -1.0%
- regression gate (5%): pass
