# Corpus performance report

- machine: Apple M1, 8 cores, 8 GiB, macOS 27.0
- models: 1447 (1447 on both engines)

| engine | total ms | models |
|---|---|---|
| rust_api | 3562.6 | 1447 |
| lean_api | 3272.6 | 1447 |

- total lean/rust_api (paired models): 0.92x (3272.6 ms vs 3562.6 ms)
- per-model ratio: geometric mean 0.87x, median 0.87x, min 0.57x, max 1.44x

| ratio | models |
|---|---|
| 0 – 0.8 | 346 |
| 0.8 – 1.0 | 937 |
| 1.0 – 1.2 | 162 |
| 1.2 – 1.5 | 2 |
| 1.5 – 2.0 | 0 |
| 2.0 – 3.0 | 0 |
| ≥ 3.0 | 0 |

| slowest by ratio | lean ms | rust_api ms | ratio |
|---|---|---|---|
| tickets_layered_160_externalPortDummyNullPointer | 0.248 | 0.173 | 1.44x |
| realworld_ptolemy_flattened_ptolemy_fuelsystem_FuelSystemErrorHandling.json | 4.765 | 3.912 | 1.22x |
| tickets_layered_411_north_south_port_anchor_a | 0.213 | 0.186 | 1.15x |
| tickets_layered_213_componentsCompaction | 1.365 | 1.203 | 1.13x |
| realworld_ptolemy_flattened_ptides_multiplatformtdma_MultiPlatformTDMA.json | 3.623 | 3.212 | 1.13x |
| realworld_ptolemy_flattened_pn_countermachine_CounterMachinePrelim.json | 4.935 | 4.386 | 1.12x |
| realworld_ptolemy_flattened_pn_countermachine_CounterMachinePrelim | 4.964 | 4.419 | 1.12x |
| tests_layered_splines_hyperedges_hyperedges_2 | 0.328 | 0.294 | 1.12x |
| realworld_ptolemy_flattened_ptolemy_test_auto32_GeneratorRegulatorProtectorSimXFMU | 1.302 | 1.174 | 1.11x |
| examples_user-hints_model-order_modelOrderCrossingMinimization | 4.003 | 3.628 | 1.10x |
| tickets_layered_528_nodeEdgeOverlap | 0.695 | 0.630 | 1.10x |
| realworld_ptolemy_flattened_sr_tokenring_TokenRing_complicated.json | 2.707 | 2.463 | 1.10x |
| realworld_ptolemy_flattened_de_CommunicationAnomalyDetectionCQM | 3.410 | 3.111 | 1.10x |
| realworld_ptolemy_flattened_ptides_multiplatformtdma_MultiPlatformTDMA | 3.524 | 3.217 | 1.10x |
| realworld_ptolemy_flattened_continuous_continuousinsidede_ContinuousInsideDE | 1.579 | 1.443 | 1.09x |

| largest absolute gap | lean ms | rust_api ms | ratio |
|---|---|---|---|
| realworld_ptolemy_flattened_gr_inversekinematics_InverseKinematics | 39.827 | 38.139 | 1.04x |
| realworld_ptolemy_flattened_gr_inversekinematics_InverseKinematics.json | 39.637 | 38.116 | 1.04x |
| realworld_ptolemy_hierarchical_pn_countermachine_CounterMachineWithException.json | 22.164 | 21.250 | 1.04x |
| realworld_ptolemy_hierarchical_de_linefault_LineFault | 14.152 | 13.248 | 1.07x |
| realworld_ptolemy_flattened_ptolemy_fuelsystem_FuelSystemErrorHandling.json | 4.765 | 3.912 | 1.22x |
| realworld_ptolemy_hierarchical_pn_countermachine_CounterMachine | 18.355 | 17.560 | 1.05x |
| realworld_ptolemy_flattened_pn_countermachine_CounterMachine.json | 23.287 | 22.538 | 1.03x |
| realworld_ptolemy_flattened_pn_countermachine_CounterMachinePrelim.json | 4.935 | 4.386 | 1.12x |
| realworld_ptolemy_flattened_pn_countermachine_CounterMachinePrelim | 4.964 | 4.419 | 1.12x |
| realworld_ptolemy_flattened_pn_countermachine_CounterMachineWithException.json | 25.190 | 24.651 | 1.02x |
| realworld_ptolemy_hierarchical_pn_countermachine_CounterMachinePrelim.json | 7.263 | 6.752 | 1.08x |
| realworld_ptolemy_flattened_ptides_cosimulation_CoSimulation.json | 8.968 | 8.480 | 1.06x |
| realworld_ptolemy_flattened_ptides_printingpress_PrintingPress.json | 26.080 | 25.626 | 1.02x |
| realworld_ptolemy_hierarchical_pn_countermachine_CounterMachineWithException | 21.489 | 21.056 | 1.02x |
| realworld_ptolemy_flattened_ptides_multiplatformtdma_MultiPlatformTDMA.json | 3.623 | 3.212 | 1.13x |

- lean_api total vs baseline (1447 common models): +1.5%
- regression gate (5%): pass
