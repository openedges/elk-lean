# Performance report

- machine: Apple M1, 8 cores, 8 GiB, macOS 27.0
- engines: rust_native, rust_api, lean_api

| scenario | rust_native ms | rust_api ms | lean_api ms | lean/rust_api | lean vs baseline |
|---|---|---|---|---|---|
| layered_small | 0.480 | 0.612 | 0.480 | 0.78x | -1.7% |
| layered_medium | 3.521 | 4.127 | 3.668 | 0.89x | +0.1% |
| layered_large | 17.541 | 20.222 | 18.553 | 0.92x | +0.5% |
| layered_xlarge | 298.553 | 319.086 | 291.830 | 0.91x | +3.6% |
| force_medium | 3.175 | 3.563 | 2.938 | 0.82x | +2.5% |
| force_large | 13.865 | 15.755 | 12.322 | 0.78x | +1.7% |
| force_xlarge | 150.239 | 157.956 | 130.712 | 0.83x | +4.4% |
| stress_medium | 3.839 | 4.280 | 4.083 | 0.95x | +2.7% |
| stress_large | 15.964 | 18.367 | 17.080 | 0.93x | +4.6% |
| stress_xlarge | 183.162 | 192.939 | 196.234 | 1.02x | +4.9% |
| mrtree_medium | 0.232 | 0.477 | 0.335 | 0.70x | +1.4% |
| mrtree_large | 0.898 | 1.909 | 1.328 | 0.70x | +0.8% |
| mrtree_xlarge | 4.876 | 10.879 | 6.895 | 0.63x | +1.5% |
| radial_medium | 1.438 | 1.749 | 0.264 | 0.15x | +3.3% |
| radial_large | 3.173 | 4.333 | 1.344 | 0.31x | +1.3% |
| radial_xlarge | 13.728 | 19.589 | 13.198 | 0.67x | +1.5% |
| rectpacking_medium | 0.179 | 0.282 | 0.191 | 0.68x | +3.4% |
| rectpacking_large | 0.731 | 1.115 | 0.776 | 0.70x | +3.4% |
| rectpacking_xlarge | 5.082 | 7.347 | 4.299 | 0.59x | +0.8% |
| routing_polyline | 2.987 | 3.630 | 3.364 | 0.93x | +3.1% |
| routing_orthogonal | 3.292 | 4.024 | 3.767 | 0.94x | +2.9% |
| routing_splines | 3.900 | 4.648 | 3.831 | 0.82x | +0.8% |
| crossmin_layer_sweep | 3.288 | 4.057 | 3.699 | 0.91x | +1.1% |
| crossmin_none | 1.848 | 2.559 | 2.118 | 0.83x | +0.8% |
| hierarchy_flat | 1.647 | 2.034 | 1.931 | 0.95x | +0.6% |
| hierarchy_nested | 0.917 | 1.209 | 0.986 | 0.82x | +0.4% |

- geometric mean lean/rust_api: 0.73x over 26 scenarios
- regression gate (5%): pass
