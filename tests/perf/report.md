# Performance report

- machine: Apple M1, 8 cores, 8 GiB, macOS 27.0
- engines: rust_native, rust_api, lean_api

| scenario | rust_native ms | rust_api ms | lean_api ms | lean/rust_api | lean vs baseline |
|---|---|---|---|---|---|
| layered_small | 0.445 | 0.555 | 0.457 | 0.82x | -4.7% |
| layered_medium | 3.206 | 3.730 | 3.501 | 0.94x | -4.4% |
| layered_large | 15.761 | 18.117 | 17.795 | 0.98x | -3.6% |
| layered_xlarge | 265.197 | 281.253 | 278.484 | 0.99x | -1.1% |
| force_medium | 2.967 | 3.297 | 2.868 | 0.87x | +0.1% |
| force_large | 12.888 | 14.544 | 11.634 | 0.80x | -3.9% |
| force_xlarge | 142.835 | 147.955 | 124.011 | 0.84x | -0.9% |
| stress_medium | 3.636 | 3.933 | 3.879 | 0.99x | -2.4% |
| stress_large | 15.320 | 16.683 | 15.949 | 0.96x | -2.3% |
| stress_xlarge | 175.687 | 180.284 | 185.864 | 1.03x | -0.7% |
| mrtree_medium | 0.217 | 0.443 | 0.307 | 0.69x | -7.1% |
| mrtree_large | 0.859 | 1.743 | 1.216 | 0.70x | -7.7% |
| mrtree_xlarge | 4.595 | 9.682 | 6.235 | 0.64x | -8.2% |
| radial_medium | 1.392 | 1.571 | 0.235 | 0.15x | -8.0% |
| radial_large | 3.029 | 3.944 | 1.233 | 0.31x | -7.0% |
| radial_xlarge | 13.028 | 17.750 | 12.268 | 0.69x | -5.7% |
| rectpacking_medium | 0.167 | 0.255 | 0.160 | 0.63x | -13.6% |
| rectpacking_large | 0.684 | 1.012 | 0.656 | 0.65x | -12.5% |
| rectpacking_xlarge | 4.867 | 6.601 | 3.741 | 0.57x | -12.3% |
| routing_polyline | 2.832 | 3.279 | 3.114 | 0.95x | -4.5% |
| routing_orthogonal | 3.119 | 3.645 | 3.495 | 0.96x | -4.5% |
| routing_splines | 3.753 | 4.322 | 3.632 | 0.84x | -4.5% |
| crossmin_layer_sweep | 3.129 | 3.677 | 3.492 | 0.95x | -4.6% |
| crossmin_none | 1.755 | 2.300 | 2.093 | 0.91x | -0.4% |
| hierarchy_flat | 1.590 | 1.851 | 1.778 | 0.96x | -7.4% |
| hierarchy_nested | 0.884 | 1.080 | 0.933 | 0.86x | -4.9% |

- geometric mean lean/rust_api: 0.75x over 26 scenarios
- regression gate (5%): pass
