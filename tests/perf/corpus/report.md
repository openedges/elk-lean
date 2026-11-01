# Corpus performance report

- machine: Apple M1, 8 cores, 8 GiB, macOS 27.0
- models: 1447 (1447 on both engines)

| engine | total ms | models |
|---|---|---|
| rust_api | 3545.2 | 1447 |
| lean_api | 3269.0 | 1447 |

- total lean/rust_api (paired models): 0.92x (3269.0 ms vs 3545.2 ms)
- per-model ratio: geometric mean 0.88x, median 0.88x, min 0.58x, max 1.23x

| ratio | models |
|---|---|
| 0 – 0.8 | 344 |
| 0.8 – 1.0 | 900 |
| 1.0 – 1.2 | 202 |
| 1.2 – 1.5 | 1 |
| 1.5 – 2.0 | 0 |
| 2.0 – 3.0 | 0 |
| ≥ 3.0 | 0 |

| slowest by ratio | lean ms | rust_api ms | ratio |
|---|---|---|---|
| realworld_ptolemy_hierarchical_ddf_eratosthenes_Eratosthenes | 1.860 | 1.509 | 1.23x |
| tickets_layered_213_componentsCompaction | 1.436 | 1.202 | 1.19x |
| tickets_layered_411_north_south_port_anchor_a | 0.221 | 0.186 | 1.19x |
| tickets_layered_528_nodeEdgeOverlap | 0.723 | 0.618 | 1.17x |
| realworld_ptolemy_flattened_wireless_personalareanetwork_Bluetooth2devices | 5.511 | 4.744 | 1.16x |
| tests_layered_north_south_ports_linear_segments_cycle | 0.426 | 0.368 | 1.16x |
| realworld_ptolemy_flattened_continuous_continuousinsidede_ContinuousInsideDE.json | 1.641 | 1.427 | 1.15x |
| realworld_ptolemy_hierarchical_wireless_personalareanetwork_Bluetooth2devices | 6.049 | 5.269 | 1.15x |
| realworld_ptolemy_hierarchical_ddf_eratosthenes_Eratosthenes.json | 1.710 | 1.499 | 1.14x |
| realworld_ptolemy_hierarchical_wireless_network_SimpleModel | 5.187 | 4.568 | 1.14x |
| realworld_ptolemy_flattened_psdf_blindcommunication_BlindCommunication | 3.464 | 3.059 | 1.13x |
| realworld_ptolemy_hierarchical_wireless_personalareanetwork_Bluetooth2devices.json | 5.956 | 5.291 | 1.13x |
| tickets_layered_528_violatedNodeOrder | 0.315 | 0.280 | 1.12x |
| tickets_layered_665_includeChildrenDoesntStop | 0.175 | 0.157 | 1.12x |
| tests_layered_preserve_order_oneCrossing | 0.392 | 0.352 | 1.11x |

| largest absolute gap | lean ms | rust_api ms | ratio |
|---|---|---|---|
| realworld_ptolemy_flattened_pn_countermachine_CounterMachineWithException | 25.758 | 23.998 | 1.07x |
| realworld_ptolemy_flattened_gr_inversekinematics_InverseKinematics | 39.375 | 37.960 | 1.04x |
| realworld_ptolemy_flattened_gr_inversekinematics_InverseKinematics.json | 39.309 | 37.910 | 1.04x |
| realworld_ptolemy_hierarchical_pn_countermachine_CounterMachineWithException | 21.937 | 20.621 | 1.06x |
| realworld_ptolemy_flattened_pn_countermachine_CounterMachineWithException.json | 24.815 | 23.848 | 1.04x |
| realworld_ptolemy_flattened_ptides_printingpress_PrintingPress | 26.602 | 25.663 | 1.04x |
| realworld_ptolemy_flattened_pn_countermachine_CounterMachine | 23.246 | 22.341 | 1.04x |
| realworld_ptolemy_hierarchical_pn_countermachine_CounterMachine.json | 18.873 | 17.979 | 1.05x |
| realworld_ptolemy_hierarchical_wireless_personalareanetwork_Bluetooth2devices | 6.049 | 5.269 | 1.15x |
| realworld_ptolemy_flattened_wireless_personalareanetwork_Bluetooth2devices | 5.511 | 4.744 | 1.16x |
| realworld_ptolemy_hierarchical_wireless_personalareanetwork_Bluetooth2devices.json | 5.956 | 5.291 | 1.13x |
| realworld_ptolemy_hierarchical_pn_countermachine_CounterMachineWithException.json | 21.757 | 21.092 | 1.03x |
| realworld_ptolemy_flattened_ptides_trex_TREXNetworkV1 | 10.908 | 10.273 | 1.06x |
| realworld_ptolemy_hierarchical_wireless_network_SimpleModel | 5.187 | 4.568 | 1.14x |
| realworld_ptolemy_flattened_pn_countermachine_CounterMachine.json | 22.892 | 22.284 | 1.03x |

- lean_api total vs baseline (1447 common models): +1.1%
- regression gate (5%): pass
