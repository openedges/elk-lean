# Corpus performance report

- machine: Apple M1, 8 cores, 8 GiB, macOS 27.0
- models: 1447 (1447 on both engines)

| engine | total ms | models |
|---|---|---|
| rust_api | 3540.8 | 1447 |
| lean_api | 3433.8 | 1447 |

- total lean/rust_api (paired models): 0.97x (3433.8 ms vs 3540.8 ms)
- per-model ratio: geometric mean 0.93x, median 0.94x, min 0.61x, max 1.68x

| ratio | models |
|---|---|
| 0 – 0.8 | 81 |
| 0.8 – 1.0 | 942 |
| 1.0 – 1.2 | 416 |
| 1.2 – 1.5 | 7 |
| 1.5 – 2.0 | 1 |
| 2.0 – 3.0 | 0 |
| ≥ 3.0 | 0 |

| slowest by ratio | lean ms | rust_api ms | ratio |
|---|---|---|---|
| realworld_ptolemy_flattened_ptolemy_electricpowersystem_GeneratorRegulatorProtectorWithBusNotAsAspect.json | 2.894 | 1.722 | 1.68x |
| realworld_ptolemy_flattened_sr_guardedcount_GuardedCountTimed.json | 1.352 | 0.964 | 1.40x |
| realworld_ptolemy_flattened_ptolemy_execdemos_demos_GuardedCount.json | 1.615 | 1.271 | 1.27x |
| realworld_ptolemy_flattened_ptolemy_electricpowersystem_GeneratorRegulatorProtectorWithBusNotAsAspect | 2.187 | 1.733 | 1.26x |
| tickets_layered_411_north_south_port_anchor_a | 0.234 | 0.185 | 1.26x |
| realworld_ptolemy_flattened_ptolemy_execdemos_demos_GuardedCount | 1.557 | 1.274 | 1.22x |
| realworld_ptolemy_hierarchical_de_timingparadox_TimingParadox.json | 4.715 | 3.858 | 1.22x |
| tickets_layered_213_componentsCompaction | 1.461 | 1.203 | 1.21x |
| examples_user-hints_model-order_modelOrderCrossingMinimization | 4.291 | 3.614 | 1.19x |
| realworld_ptolemy_flattened_continuous_staticunits_StaticUnits | 1.444 | 1.223 | 1.18x |
| realworld_ptolemy_flattened_ptolemy_electricpowersystem_GeneratorRegulatorProtectorWithSpecificationAsAspect | 1.563 | 1.334 | 1.17x |
| realworld_ptolemy_flattened_ptolemy_execdemos_demos_Inspection | 1.549 | 1.329 | 1.17x |
| tests_layered_edge_label_placement_northSouthPorts_down_down_01 | 0.344 | 0.296 | 1.16x |
| tickets_layered_528_violatedNodeOrder | 0.323 | 0.278 | 1.16x |
| realworld_ptolemy_flattened_gt_diningphilosophers_DiningPhilosophers | 3.071 | 2.650 | 1.16x |

| largest absolute gap | lean ms | rust_api ms | ratio |
|---|---|---|---|
| realworld_ptolemy_flattened_gr_inversekinematics_InverseKinematics.json | 40.720 | 38.010 | 1.07x |
| realworld_ptolemy_hierarchical_pn_countermachine_CounterMachineWithException.json | 23.218 | 20.677 | 1.12x |
| realworld_ptolemy_flattened_gr_inversekinematics_InverseKinematics | 40.427 | 38.052 | 1.06x |
| realworld_ptolemy_hierarchical_pn_countermachine_CounterMachineWithException | 22.696 | 20.903 | 1.09x |
| realworld_ptolemy_hierarchical_pn_countermachine_CounterMachine | 19.196 | 17.609 | 1.09x |
| realworld_ptolemy_hierarchical_pn_countermachine_CounterMachine.json | 19.163 | 17.622 | 1.09x |
| realworld_ptolemy_hierarchical_de_linefault_LineFault | 14.343 | 13.112 | 1.09x |
| realworld_ptolemy_hierarchical_de_linefault_LineFault.json | 14.390 | 13.175 | 1.09x |
| realworld_ptolemy_flattened_ptolemy_electricpowersystem_GeneratorRegulatorProtectorWithBusNotAsAspect.json | 2.894 | 1.722 | 1.68x |
| realworld_ptolemy_flattened_ptides_printingpress_PrintingPress.json | 26.564 | 25.498 | 1.04x |
| realworld_ptolemy_flattened_ptides_printingpress_PrintingPress | 26.572 | 25.559 | 1.04x |
| realworld_ptolemy_flattened_pn_countermachine_CounterMachineWithException.json | 24.842 | 23.904 | 1.04x |
| realworld_ptolemy_hierarchical_de_timingparadox_TimingParadox.json | 4.715 | 3.858 | 1.22x |
| realworld_ptolemy_flattened_pn_countermachine_CounterMachine | 23.003 | 22.218 | 1.04x |
| realworld_ptolemy_hierarchical_ptides_trex_TREXNoNetworkAllDigital.json | 17.397 | 16.647 | 1.05x |

- lean_api total vs baseline (1447 common models): -0.2%
- regression gate (5%): pass
