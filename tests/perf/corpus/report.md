# Corpus performance report

- machine: Apple M1, 8 cores, 8 GiB, macOS 27.0
- models: 1447 (1447 on both engines)

| engine | total ms | models |
|---|---|---|
| rust_api | 3520.1 | 1447 |
| lean_api | 4327.7 | 1447 |

- total lean/rust_api (paired models): 1.23x (4327.7 ms vs 3520.1 ms)
- per-model ratio: geometric mean 1.09x, median 1.07x, min 0.45x, max 2.30x

| ratio | models |
|---|---|
| 0 – 0.8 | 30 |
| 0.8 – 1.0 | 402 |
| 1.0 – 1.2 | 657 |
| 1.2 – 1.5 | 344 |
| 1.5 – 2.0 | 10 |
| 2.0 – 3.0 | 4 |
| ≥ 3.0 | 0 |

| slowest by ratio | lean ms | rust_api ms | ratio |
|---|---|---|---|
| realworld_ptolemy_flattened_pn_countermachine_CounterMachine | 51.608 | 22.396 | 2.30x |
| realworld_ptolemy_flattened_pn_countermachine_CounterMachine.json | 50.441 | 22.163 | 2.28x |
| realworld_ptolemy_flattened_pn_countermachine_CounterMachineWithException.json | 53.730 | 23.751 | 2.26x |
| realworld_ptolemy_flattened_pn_countermachine_CounterMachineWithException | 53.599 | 23.867 | 2.25x |
| realworld_ptolemy_flattened_syntactic_LoopSyntactic2.json | 2.262 | 1.259 | 1.80x |
| realworld_ptolemy_flattened_gr_inversekinematics_InverseKinematics.json | 66.571 | 37.545 | 1.77x |
| realworld_ptolemy_flattened_gr_inversekinematics_InverseKinematics | 66.522 | 37.547 | 1.77x |
| realworld_ptolemy_flattened_pn_stack_Stack.json | 5.581 | 3.529 | 1.58x |
| tickets_layered_213_componentsCompaction | 1.925 | 1.221 | 1.58x |
| tickets_layered_411_north_south_port_anchor_a | 0.291 | 0.186 | 1.57x |
| realworld_ptolemy_flattened_pn_stack_Stack | 5.502 | 3.525 | 1.56x |
| realworld_ptolemy_flattened_ptides_cosimulation_CoSimulation | 13.241 | 8.532 | 1.55x |
| realworld_ptolemy_flattened_syntactic_LoopSyntactic2 | 1.920 | 1.272 | 1.51x |
| realworld_ptolemy_flattened_ptango_chat_ChatServer.json | 3.504 | 2.328 | 1.50x |
| realworld_ptolemy_flattened_ptango_chat_ChatServer | 3.520 | 2.350 | 1.50x |

| largest absolute gap | lean ms | rust_api ms | ratio |
|---|---|---|---|
| realworld_ptolemy_flattened_pn_countermachine_CounterMachineWithException.json | 53.730 | 23.751 | 2.26x |
| realworld_ptolemy_flattened_pn_countermachine_CounterMachineWithException | 53.599 | 23.867 | 2.25x |
| realworld_ptolemy_flattened_pn_countermachine_CounterMachine | 51.608 | 22.396 | 2.30x |
| realworld_ptolemy_flattened_gr_inversekinematics_InverseKinematics.json | 66.571 | 37.545 | 1.77x |
| realworld_ptolemy_flattened_gr_inversekinematics_InverseKinematics | 66.522 | 37.547 | 1.77x |
| realworld_ptolemy_flattened_pn_countermachine_CounterMachine.json | 50.441 | 22.163 | 2.28x |
| realworld_ptolemy_flattened_de_trilateration_Trilateration.json | 69.293 | 46.669 | 1.48x |
| realworld_ptolemy_flattened_de_trilateration_Trilateration | 68.823 | 46.488 | 1.48x |
| realworld_ptolemy_hierarchical_de_trilateration_Trilateration.json | 71.490 | 55.005 | 1.30x |
| realworld_ptolemy_hierarchical_de_trilateration_Trilateration | 71.373 | 54.936 | 1.30x |
| realworld_ptolemy_flattened_continuous_starmac_Starmac.json | 38.589 | 26.711 | 1.44x |
| realworld_ptolemy_flattened_continuous_starmac_Starmac | 38.450 | 26.665 | 1.44x |
| realworld_ptolemy_flattened_ptango_temperaturesimulation_EPlusSimulation.json | 42.932 | 31.274 | 1.37x |
| realworld_ptolemy_flattened_ptango_temperaturesimulation_EPlusSimulation | 42.523 | 31.245 | 1.36x |
| realworld_ptolemy_hierarchical_ptango_temperaturesimulation_EPlusSimulation | 55.292 | 44.139 | 1.25x |
