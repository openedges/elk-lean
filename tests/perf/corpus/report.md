# Corpus performance report

- machine: Apple M1, 8 cores, 8 GiB, macOS 27.0
- models: 1447 (1447 on both engines)

| engine | total ms | models |
|---|---|---|
| rust_api | 3531.5 | 1447 |
| lean_api | 3245.6 | 1447 |

- total lean/rust_api (paired models): 0.92x (3245.6 ms vs 3531.5 ms)
- per-model ratio: geometric mean 0.87x, median 0.87x, min 0.52x, max 1.32x

| ratio | models |
|---|---|
| 0 – 0.8 | 367 |
| 0.8 – 1.0 | 930 |
| 1.0 – 1.2 | 147 |
| 1.2 – 1.5 | 3 |
| 1.5 – 2.0 | 0 |
| 2.0 – 3.0 | 0 |
| ≥ 3.0 | 0 |

| slowest by ratio | lean ms | rust_api ms | ratio |
|---|---|---|---|
| tickets_layered_160_externalPortDummyNullPointer | 0.231 | 0.175 | 1.32x |
| tests_layered_compaction_oned_labels_edgeLabelAndSplines | 0.344 | 0.264 | 1.30x |
| tests_layered_edge_label_placement_edgeLabelSideSelection01 | 0.231 | 0.185 | 1.25x |
| realworld_ptolemy_flattened_pn_blindcommunication_BlindCommunication | 3.645 | 3.122 | 1.17x |
| tickets_layered_411_north_south_port_anchor_a | 0.212 | 0.185 | 1.14x |
| realworld_ptolemy_flattened_ptolemy_execdemos_demos_SigmaDelta.json | 1.997 | 1.761 | 1.13x |
| tests_layered_compaction_oned_labels_edgeLabelShouldBeCentered | 0.184 | 0.164 | 1.12x |
| tickets_layered_213_componentsCompaction | 1.357 | 1.217 | 1.12x |
| tickets_layered_528_nodeEdgeOverlap | 0.685 | 0.616 | 1.11x |
| realworld_ptolemy_flattened_lib_decg_DECGPi | 2.408 | 2.174 | 1.11x |
| examples_user-hints_model-order_modelOrderCrossingMinimization | 3.994 | 3.635 | 1.10x |
| realworld_ptolemy_hierarchical_pn_stack_Stack | 4.371 | 3.988 | 1.10x |
| realworld_ptolemy_flattened_pn_blindcommunication_BlindCommunication.json | 3.325 | 3.045 | 1.09x |
| realworld_ptolemy_flattened_gr_inversekinematics_InverseKinematics.json | 41.330 | 37.976 | 1.09x |
| realworld_ptolemy_flattened_pn_countermachine_CounterMachinePrelim | 4.751 | 4.369 | 1.09x |

| largest absolute gap | lean ms | rust_api ms | ratio |
|---|---|---|---|
| realworld_ptolemy_flattened_gr_inversekinematics_InverseKinematics.json | 41.330 | 37.976 | 1.09x |
| realworld_ptolemy_flattened_gr_inversekinematics_InverseKinematics | 39.601 | 37.982 | 1.04x |
| realworld_ptolemy_hierarchical_pn_countermachine_CounterMachineWithException.json | 21.691 | 20.666 | 1.05x |
| realworld_ptolemy_flattened_pn_countermachine_CounterMachineWithException.json | 24.856 | 23.879 | 1.04x |
| realworld_ptolemy_hierarchical_pn_countermachine_CounterMachineWithException | 21.344 | 20.539 | 1.04x |
| realworld_ptolemy_flattened_pn_countermachine_CounterMachineWithException | 24.511 | 23.740 | 1.03x |
| realworld_ptolemy_hierarchical_pn_countermachine_CounterMachine.json | 18.190 | 17.501 | 1.04x |
| realworld_ptolemy_flattened_ptides_cosimulation_CoSimulation | 9.061 | 8.456 | 1.07x |
| realworld_ptolemy_hierarchical_pn_countermachine_CounterMachine | 18.189 | 17.614 | 1.03x |
| realworld_ptolemy_flattened_pn_blindcommunication_BlindCommunication | 3.645 | 3.122 | 1.17x |
| realworld_ptolemy_hierarchical_wireless_personalareanetwork_Bluetooth2devices.json | 5.681 | 5.247 | 1.08x |
| realworld_ptolemy_hierarchical_pn_stack_Stack | 4.371 | 3.988 | 1.10x |
| realworld_ptolemy_flattened_pn_countermachine_CounterMachinePrelim | 4.751 | 4.369 | 1.09x |
| realworld_ptolemy_hierarchical_wireless_personalareanetwork_Bluetooth2devices | 5.604 | 5.238 | 1.07x |
| examples_user-hints_model-order_modelOrderCrossingMinimization | 3.994 | 3.635 | 1.10x |

- lean_api total vs baseline (1447 common models): +0.7%
- regression gate (5%): pass
