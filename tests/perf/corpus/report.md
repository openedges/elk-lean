# Corpus performance report

- machine: Apple M1, 8 cores, 8 GiB, macOS 27.0
- models: 1447 (1447 on both engines)

| engine | total ms | models |
|---|---|---|
| rust_api | 3512.5 | 1447 |
| lean_api | 3563.2 | 1447 |

- total lean/rust_api (paired models): 1.01x (3563.2 ms vs 3512.5 ms)
- per-model ratio: geometric mean 1.00x, median 1.00x, min 0.67x, max 1.61x

| ratio | models |
|---|---|
| 0 – 0.8 | 28 |
| 0.8 – 1.0 | 670 |
| 1.0 – 1.2 | 734 |
| 1.2 – 1.5 | 13 |
| 1.5 – 2.0 | 2 |
| 2.0 – 3.0 | 0 |
| ≥ 3.0 | 0 |

| slowest by ratio | lean ms | rust_api ms | ratio |
|---|---|---|---|
| examples_user-hints_model-order_modelOrderCrossingMinimization | 5.845 | 3.620 | 1.61x |
| tickets_layered_213_componentsCompaction | 1.876 | 1.200 | 1.56x |
| tests_layered_compaction_oned_labels_edgeLabelAndSplines | 0.375 | 0.268 | 1.40x |
| tests_layered_compaction_oned_labels_edgeLabelShouldBeCentered | 0.213 | 0.164 | 1.30x |
| tickets_layered_528_violatedNodeOrder | 0.350 | 0.280 | 1.25x |
| tickets_layered_411_north_south_port_anchor_a | 0.244 | 0.196 | 1.25x |
| tests_layered_compaction_oned_labels_labels1 | 0.715 | 0.574 | 1.25x |
| tests_layered_compaction_oned_labels_edgeLabelSideSelection01 | 0.258 | 0.207 | 1.24x |
| tests_layered_compaction_oned_labels_labels2 | 0.613 | 0.502 | 1.22x |
| tests_layered_splines_north_south_ports_3 | 0.300 | 0.246 | 1.22x |
| realworld_ptolemy_flattened_sdf_orthogonalcom_OrthogonalCom | 1.280 | 1.054 | 1.21x |
| tests_layered_compaction_oned_selfloop_selfloop_spline | 0.219 | 0.181 | 1.21x |
| tests_layered_preserve_order_oneCrossing | 0.424 | 0.350 | 1.21x |
| tests_layered_compaction_oned_selfloop_selfloop_orthogonal | 0.184 | 0.153 | 1.20x |
| tests_layered_north_south_ports_linear_segments_cycle | 0.442 | 0.367 | 1.20x |

| largest absolute gap | lean ms | rust_api ms | ratio |
|---|---|---|---|
| realworld_ptolemy_hierarchical_pn_countermachine_CounterMachineWithException | 23.358 | 20.456 | 1.14x |
| realworld_ptolemy_hierarchical_pn_countermachine_CounterMachineWithException.json | 23.361 | 20.553 | 1.14x |
| realworld_ptolemy_hierarchical_pn_countermachine_CounterMachine | 19.936 | 17.425 | 1.14x |
| realworld_ptolemy_hierarchical_pn_countermachine_CounterMachine.json | 19.919 | 17.474 | 1.14x |
| examples_user-hints_model-order_modelOrderCrossingMinimization | 5.845 | 3.620 | 1.61x |
| realworld_ptolemy_hierarchical_de_trilateration_Trilateration | 57.225 | 55.041 | 1.04x |
| realworld_ptolemy_hierarchical_ptango_temperaturesimulation_EPlusSimulation | 46.119 | 43.977 | 1.05x |
| realworld_ptolemy_hierarchical_de_trilateration_Trilateration.json | 56.931 | 54.944 | 1.04x |
| realworld_ptolemy_hierarchical_ptango_temperaturesimulation_EPlusSimulation.json | 45.885 | 44.153 | 1.04x |
| realworld_ptolemy_hierarchical_de_printingpress_PrintingPress-Validation.json | 40.192 | 38.623 | 1.04x |
| realworld_ptolemy_flattened_ptides_printingpress_PrintingPress.json | 26.812 | 25.278 | 1.06x |
| realworld_ptolemy_hierarchical_de_printingpress_PrintingPress-Validation | 39.675 | 38.166 | 1.04x |
| realworld_ptolemy_hierarchical_de_linefault_LineFault | 14.543 | 13.101 | 1.11x |
| realworld_ptolemy_flattened_de_printingpress_PrintingPress-Validation.json | 25.215 | 23.806 | 1.06x |
| realworld_ptolemy_hierarchical_de_linefault_LineFault.json | 14.608 | 13.204 | 1.11x |

- lean_api total vs baseline (1447 common models): -17.7%
- regression gate (5%): pass
