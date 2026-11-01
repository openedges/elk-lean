# Corpus performance report

- machine: Apple M1, 8 cores, 8 GiB, macOS 27.0
- models: 1447 (1447 on both engines)

| engine | total ms | models |
|---|---|---|
| rust_api | 3533.5 | 1447 |
| lean_api | 3107.0 | 1447 |

- total lean/rust_api (paired models): 0.88x (3107.0 ms vs 3533.5 ms)
- per-model ratio: geometric mean 0.83x, median 0.83x, min 0.55x, max 1.29x

| ratio | models |
|---|---|
| 0 – 0.8 | 589 |
| 0.8 – 1.0 | 794 |
| 1.0 – 1.2 | 62 |
| 1.2 – 1.5 | 2 |
| 1.5 – 2.0 | 0 |
| 2.0 – 3.0 | 0 |
| ≥ 3.0 | 0 |

| slowest by ratio | lean ms | rust_api ms | ratio |
|---|---|---|---|
| tests_layered_north_south_ports_linear_segments_cycle | 0.473 | 0.366 | 1.29x |
| realworld_ptolemy_flattened_continuous_continuousinsidede_ContinuousInsideDE.json | 1.726 | 1.416 | 1.22x |
| tests_layered_compaction_oned_labels_edgeLabelAndSplines | 0.326 | 0.277 | 1.18x |
| realworld_ptolemy_flattened_lib_decg_DECGPi | 2.445 | 2.169 | 1.13x |
| realworld_ptolemy_hierarchical_ddf_eratosthenes_Eratosthenes | 1.697 | 1.506 | 1.13x |
| realworld_ptolemy_flattened_unit_staticunits_StaticUnits2 | 1.295 | 1.163 | 1.11x |
| realworld_ptolemy_hierarchical_ddf_eratosthenes_Eratosthenes.json | 1.665 | 1.500 | 1.11x |
| tickets_layered_411_north_south_port_anchor_a | 0.204 | 0.186 | 1.10x |
| realworld_ptolemy_flattened_unit_staticunits_StaticUnits2.json | 1.260 | 1.151 | 1.09x |
| tickets_layered_213_componentsCompaction | 1.308 | 1.202 | 1.09x |
| realworld_ptolemy_flattened_continuous_continuousinsidede_ContinuousInsideDE | 1.549 | 1.427 | 1.09x |
| realworld_ptolemy_flattened_lib_decg_DECGPi.json | 2.331 | 2.155 | 1.08x |
| tests_layered_self_loops_inside_outside | 0.192 | 0.180 | 1.07x |
| realworld_ptolemy_flattened_unit_staticunits_StaticUnits.json | 1.279 | 1.198 | 1.07x |
| realworld_ptolemy_flattened_gt_mapreduce_MapReduce.json | 1.282 | 1.202 | 1.07x |

| largest absolute gap | lean ms | rust_api ms | ratio |
|---|---|---|---|
| realworld_ptolemy_hierarchical_pn_countermachine_CounterMachine.json | 17.916 | 17.541 | 1.02x |
| realworld_ptolemy_flattened_continuous_continuousinsidede_ContinuousInsideDE.json | 1.726 | 1.416 | 1.22x |
| realworld_ptolemy_flattened_lib_decg_DECGPi | 2.445 | 2.169 | 1.13x |
| realworld_ptolemy_hierarchical_pn_countermachine_CounterMachineWithException | 20.805 | 20.539 | 1.01x |
| realworld_ptolemy_flattened_pn_countermachine_CounterMachinePrelim | 4.626 | 4.408 | 1.05x |
| realworld_ptolemy_flattened_pn_countermachine_CounterMachinePrelim.json | 4.584 | 4.380 | 1.05x |
| realworld_ptolemy_hierarchical_ddf_eratosthenes_Eratosthenes | 1.697 | 1.506 | 1.13x |
| realworld_ptolemy_flattened_lib_decg_DECGPi.json | 2.331 | 2.155 | 1.08x |
| realworld_ptolemy_hierarchical_ddf_eratosthenes_Eratosthenes.json | 1.665 | 1.500 | 1.11x |
| realworld_ptolemy_flattened_continuous_cartracking_CarTracking | 3.444 | 3.302 | 1.04x |
| realworld_ptolemy_flattened_unit_staticunits_StaticUnits2 | 1.295 | 1.163 | 1.11x |
| realworld_ptolemy_flattened_continuous_continuousinsidede_ContinuousInsideDE | 1.549 | 1.427 | 1.09x |
| realworld_ptolemy_flattened_unit_staticunits_StaticUnits2.json | 1.260 | 1.151 | 1.09x |
| tests_layered_north_south_ports_linear_segments_cycle | 0.473 | 0.366 | 1.29x |
| tickets_layered_213_componentsCompaction | 1.308 | 1.202 | 1.09x |

- lean_api total vs baseline (1447 common models): -3.5%
- regression gate (5%): pass
