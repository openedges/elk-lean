# Performance report

- machine: Apple M1, 8 cores, 8 GiB, macOS 27.0
- engines: rust_native, rust_api, lean_api

| scenario | rust_native ms | rust_api ms | lean_api ms | lean/rust_api | lean vs baseline |
|---|---|---|---|---|---|
| layered_small | 0.444 | 0.546 | 0.493 | 0.90x | +0.2% |
| layered_medium | 3.199 | 3.753 | 3.654 | 0.97x | +1.2% |
| layered_large | 15.815 | 18.332 | 18.245 | 1.00x | -2.2% |
| layered_xlarge | 265.171 | 280.994 | 280.094 | 1.00x | -2.6% |
| force_medium | 2.983 | 3.298 | 2.853 | 0.86x | +0.8% |
| force_large | 12.915 | 14.383 | 12.061 | 0.84x | -0.6% |
| force_xlarge | 143.870 | 147.264 | 125.553 | 0.85x | -0.1% |
| stress_medium | 3.623 | 3.941 | 3.990 | 1.01x | +1.4% |
| stress_large | 15.204 | 16.639 | 16.326 | 0.98x | -1.2% |
| stress_xlarge | 174.756 | 179.145 | 187.154 | 1.04x | -0.5% |
| mrtree_medium | 0.217 | 0.443 | 0.381 | 0.86x | -22.2% |
| mrtree_large | 0.857 | 1.833 | 1.515 | 0.83x | -33.0% |
| mrtree_xlarge | 4.612 | 9.310 | 7.681 | 0.83x | -45.7% |
| radial_medium | 1.406 | 1.628 | 0.297 | 0.18x | -20.8% |
| radial_large | 3.031 | 3.946 | 1.490 | 0.38x | -45.8% |
| radial_xlarge | 13.035 | 17.728 | 13.614 | 0.77x | -65.3% |
| rectpacking_medium | 0.167 | 0.255 | 0.201 | 0.79x | -0.4% |
| rectpacking_large | 0.685 | 1.019 | 0.822 | 0.81x | -0.5% |
| rectpacking_xlarge | 4.858 | 6.595 | 4.561 | 0.69x | -1.5% |
| routing_polyline | 2.839 | 3.256 | 3.226 | 0.99x | -0.1% |
| routing_orthogonal | 3.115 | 3.629 | 3.633 | 1.00x | -0.2% |
| routing_splines | 3.728 | 4.235 | 3.876 | 0.92x | +2.5% |
| crossmin_layer_sweep | 3.137 | 3.639 | 3.643 | 1.00x | -0.1% |
| crossmin_none | 1.752 | 2.298 | 2.162 | 0.94x | -2.2% |
| hierarchy_flat | 1.577 | 1.846 | 1.916 | 1.04x | -0.4% |
| hierarchy_nested | 0.892 | 1.072 | 0.992 | 0.93x | -1.7% |

- geometric mean lean/rust_api: 0.82x over 26 scenarios
- regression gate (5%): pass
