# Performance report

- machine: Apple M1, 8 cores, 8 GiB, macOS 27.0
- engines: rust_native, rust_api, lean_api

| scenario | rust_native ms | rust_api ms | lean_api ms | lean/rust_api | lean vs baseline |
|---|---|---|---|---|---|
| layered_small | 0.444 | 0.543 | 0.511 | 0.94x | -14.7% |
| layered_medium | 3.208 | 3.717 | 3.735 | 1.00x | -10.7% |
| layered_large | 15.810 | 18.265 | 18.763 | 1.03x | -9.2% |
| layered_xlarge | 264.759 | 281.678 | 291.084 | 1.03x | -3.6% |
| force_medium | 2.971 | 3.288 | 2.832 | 0.86x | -1.7% |
| force_large | 12.871 | 14.398 | 12.156 | 0.84x | -2.4% |
| force_xlarge | 142.650 | 147.496 | 125.647 | 0.85x | -0.4% |
| stress_medium | 3.645 | 3.935 | 3.983 | 1.01x | -1.2% |
| stress_large | 15.146 | 16.681 | 16.570 | 0.99x | -1.5% |
| stress_xlarge | 176.393 | 179.486 | 188.717 | 1.05x | -0.2% |
| mrtree_medium | 0.226 | 0.443 | 0.387 | 0.87x | -11.0% |
| mrtree_large | 0.894 | 1.751 | 1.559 | 0.89x | -11.8% |
| mrtree_xlarge | 4.609 | 9.333 | 8.290 | 0.89x | -11.1% |
| radial_medium | 1.383 | 1.629 | 0.285 | 0.18x | -14.1% |
| radial_large | 3.041 | 3.941 | 1.129 | 0.29x | -15.9% |
| radial_xlarge | 13.075 | 17.926 | 5.708 | 0.32x | -15.8% |
| rectpacking_medium | 0.168 | 0.255 | 0.243 | 0.95x | -6.3% |
| rectpacking_large | 0.687 | 1.018 | 0.981 | 0.96x | -6.4% |
| rectpacking_xlarge | 4.873 | 6.602 | 5.169 | 0.78x | -10.1% |
| routing_polyline | 2.812 | 3.260 | 3.356 | 1.03x | -10.6% |
| routing_orthogonal | 3.094 | 3.626 | 3.811 | 1.05x | -8.5% |
| routing_splines | 3.708 | 4.238 | 3.891 | 0.92x | -27.4% |
| crossmin_layer_sweep | 3.100 | 3.661 | 3.752 | 1.03x | -10.0% |
| crossmin_none | 1.806 | 2.322 | 2.231 | 0.96x | -16.5% |
| hierarchy_flat | 1.662 | 1.896 | 1.976 | 1.04x | -12.1% |
| hierarchy_nested | 0.873 | 1.073 | 1.006 | 0.94x | -20.2% |

- geometric mean lean/rust_api: 0.82x over 26 scenarios
- regression gate (5%): pass
