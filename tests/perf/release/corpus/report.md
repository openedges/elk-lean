# Corpus performance report

- machine: Apple M1, 8 cores, 8 GiB, macOS 27.0
- models: 1447 (1447 on both engines)

| engine | total ms | models |
|---|---|---|
| rust_api | 3736.4 | 1447 |
| lean_api | 2717.6 | 1447 |

- total lean/rust_api (paired models): 0.73x (2717.6 ms vs 3736.4 ms)
- per-model ratio: geometric mean 0.65x, median 0.65x, min 0.38x, max 0.90x

| ratio | models |
|---|---|
| 0 – 0.8 | 1332 |
| 0.8 – 1.0 | 115 |
| 1.0 – 1.2 | 0 |
| 1.2 – 1.5 | 0 |
| 1.5 – 2.0 | 0 |
| 2.0 – 3.0 | 0 |
| ≥ 3.0 | 0 |

| slowest by ratio | lean ms | rust_api ms | ratio |
|---|---|---|---|
| realworld_ptolemy_flattened_gr_inversekinematics_InverseKinematics | 36.182 | 40.084 | 0.90x |
| realworld_ptolemy_flattened_pn_stack_Stack.json | 3.287 | 3.674 | 0.89x |
| realworld_ptolemy_flattened_pn_stack_Stack | 3.282 | 3.688 | 0.89x |
| realworld_ptolemy_flattened_continuous_continuousinsidede_ContinuousInsideDE | 1.321 | 1.489 | 0.89x |
| realworld_ptolemy_flattened_pn_countermachine_CounterMachine.json | 20.744 | 23.421 | 0.89x |
| realworld_ptolemy_flattened_pn_countermachine_CounterMachineWithException | 22.485 | 25.414 | 0.88x |
| realworld_ptolemy_flattened_pn_countermachine_CounterMachineWithException.json | 22.902 | 26.024 | 0.88x |
| realworld_ptolemy_flattened_modal_abp_ABP.json | 1.893 | 2.165 | 0.87x |
| realworld_ptolemy_flattened_ptides_trex_TREXNoNetworkAllDigital.json | 9.725 | 11.147 | 0.87x |
| tickets_layered_213_componentsCompaction | 1.110 | 1.273 | 0.87x |
| realworld_ptolemy_flattened_modal_abp_ABP | 1.896 | 2.176 | 0.87x |
| realworld_ptolemy_flattened_pn_countermachine_CounterMachine | 20.692 | 23.777 | 0.87x |
| realworld_ptolemy_flattened_gr_inversekinematics_InverseKinematics.json | 35.081 | 40.340 | 0.87x |
| realworld_ptolemy_flattened_ptango_chat_ChatServer | 2.141 | 2.479 | 0.86x |
| realworld_ptolemy_flattened_ptolemy_fuelsystem_FuelSystemErrorHandling.json | 3.551 | 4.119 | 0.86x |

| largest absolute gap | lean ms | rust_api ms | ratio |
|---|---|---|---|
| examples_user-hints_interactive-constraints_interactiveRectpacking_hierarchy | 0.024 | 0.047 | 0.52x |
| examples_user-hints_interactive-constraints_interactiveRectpacking_oneBigNode | 0.032 | 0.056 | 0.57x |
| tickets_core_489_paddingAndMinSize_Small | 0.033 | 0.063 | 0.52x |
| tickets_core_489_paddingAndMinSize_Large | 0.034 | 0.065 | 0.52x |
| tickets_core_269_portAlignmendIsIgnored | 0.030 | 0.062 | 0.48x |
| tickets_layered_411_north_south_port_anchor_a | 0.159 | 0.193 | 0.83x |
| tickets_layered_418_northPortsWithSelfLoops | 0.083 | 0.118 | 0.70x |
| tickets_core_245_surroundingPortSpace | 0.033 | 0.068 | 0.48x |
| tests_layered_interactive_layout_sameLayerEdges | 0.057 | 0.093 | 0.61x |
| tests_layered_interactive_layout_firstPosition | 0.055 | 0.092 | 0.60x |
| tests_layered_interactive_layout_lastLayer | 0.052 | 0.088 | 0.59x |
| tests_layered_interactive_layout_firstLayer | 0.060 | 0.097 | 0.62x |
| tickets_layered_665_includeChildrenDoesntStop | 0.131 | 0.168 | 0.78x |
| tickets_layered_302_brokenSplineSelfLoops | 0.050 | 0.088 | 0.57x |
| tickets_layered_079_selfLoopLabels | 0.051 | 0.089 | 0.58x |
