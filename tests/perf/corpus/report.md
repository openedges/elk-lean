# Corpus performance report

- machine: Apple M1, 8 cores, 8 GiB, macOS 27.0
- models: 1447 (1447 on both engines)

| engine | total ms | models |
|---|---|---|
| rust_api | 3533.0 | 1447 |
| lean_api | 3238.0 | 1447 |

- total lean/rust_api (paired models): 0.92x (3238.0 ms vs 3533.0 ms)
- per-model ratio: geometric mean 0.87x, median 0.87x, min 0.61x, max 1.13x

| ratio | models |
|---|---|
| 0 – 0.8 | 370 |
| 0.8 – 1.0 | 932 |
| 1.0 – 1.2 | 145 |
| 1.2 – 1.5 | 0 |
| 1.5 – 2.0 | 0 |
| 2.0 – 3.0 | 0 |
| ≥ 3.0 | 0 |

| slowest by ratio | lean ms | rust_api ms | ratio |
|---|---|---|---|
| realworld_ptolemy_flattened_ptolemy_test_auto_GeneratorRegulatorFMUProtector.json | 1.531 | 1.350 | 1.13x |
| tickets_layered_411_north_south_port_anchor_a | 0.210 | 0.186 | 1.13x |
| realworld_ptolemy_hierarchical_continuous_squarewave_SquareWave.json | 1.224 | 1.088 | 1.13x |
| tickets_layered_213_componentsCompaction | 1.348 | 1.199 | 1.12x |
| realworld_ptolemy_flattened_psdf_blindcommunication_BlindCommunication.json | 3.424 | 3.074 | 1.11x |
| realworld_ptolemy_flattened_continuous_units_Units.json | 0.736 | 0.662 | 1.11x |
| realworld_ptolemy_flattened_pn_countermachine_CounterMachinePrelim.json | 4.895 | 4.405 | 1.11x |
| tests_layered_north_south_ports_nsp3 | 0.269 | 0.243 | 1.10x |
| examples_user-hints_model-order_modelOrderCrossingMinimization | 3.986 | 3.627 | 1.10x |
| realworld_ptolemy_flattened_pn_stack_Stack.json | 3.963 | 3.607 | 1.10x |
| tickets_layered_528_nodeEdgeOverlap | 0.683 | 0.624 | 1.09x |
| realworld_ptolemy_flattened_ptolemy_test_auto_GeneratorRegulatorFMUProtector | 1.479 | 1.360 | 1.09x |
| tickets_layered_528_violatedNodeOrder | 0.301 | 0.278 | 1.09x |
| realworld_ptolemy_flattened_pn_countermachine_CounterMachinePrelim | 4.738 | 4.386 | 1.08x |
| tests_layered_preserve_order_oneCrossing | 0.383 | 0.355 | 1.08x |

| largest absolute gap | lean ms | rust_api ms | ratio |
|---|---|---|---|
| realworld_ptolemy_flattened_gr_inversekinematics_InverseKinematics | 39.153 | 38.009 | 1.03x |
| realworld_ptolemy_flattened_pn_countermachine_CounterMachineWithException.json | 24.565 | 23.751 | 1.03x |
| realworld_ptolemy_flattened_pn_countermachine_CounterMachineWithException | 24.590 | 23.784 | 1.03x |
| realworld_ptolemy_hierarchical_pn_countermachine_CounterMachineWithException | 21.334 | 20.661 | 1.03x |
| realworld_ptolemy_flattened_ptides_cosimulation_CoSimulation | 8.953 | 8.432 | 1.06x |
| realworld_ptolemy_flattened_pn_countermachine_CounterMachinePrelim.json | 4.895 | 4.405 | 1.11x |
| realworld_ptolemy_hierarchical_pn_countermachine_CounterMachinePrelim.json | 6.817 | 6.430 | 1.06x |
| examples_user-hints_model-order_modelOrderCrossingMinimization | 3.986 | 3.627 | 1.10x |
| realworld_ptolemy_flattened_pn_stack_Stack.json | 3.963 | 3.607 | 1.10x |
| realworld_ptolemy_flattened_pn_countermachine_CounterMachinePrelim | 4.738 | 4.386 | 1.08x |
| realworld_ptolemy_flattened_psdf_blindcommunication_BlindCommunication.json | 3.424 | 3.074 | 1.11x |
| realworld_ptolemy_flattened_ptides_trex_TREX | 10.787 | 10.447 | 1.03x |
| realworld_ptolemy_hierarchical_de_linefault_LineFault.json | 13.395 | 13.113 | 1.02x |
| realworld_ptolemy_hierarchical_pn_countermachine_CounterMachine | 17.940 | 17.664 | 1.02x |
| realworld_ptolemy_flattened_pn_countermachine_CounterMachine.json | 23.272 | 23.001 | 1.01x |

- lean_api total vs baseline (1447 common models): -3.3%
- regression gate (5%): pass
