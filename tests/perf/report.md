# Performance report

- machine: Apple M1, 8 cores, 8 GiB, macOS 27.0
- engines: rust_native, rust_api, lean_api

| scenario | rust_native ms | rust_api ms | lean_api ms | lean/rust_api | lean vs baseline |
|---|---|---|---|---|---|
| layered_small | 0.443 | 0.559 | 0.433 | 0.77x | -3.2% |
| layered_medium | 3.235 | 3.719 | 3.427 | 0.92x | -1.1% |
| layered_large | 15.716 | 18.152 | 17.578 | 0.97x | -0.1% |
| layered_xlarge | 265.222 | 281.832 | 281.906 | 1.00x | +1.2% |
| force_medium | 3.027 | 3.346 | 2.784 | 0.83x | +0.2% |
| force_large | 12.934 | 14.667 | 11.608 | 0.79x | +0.3% |
| force_xlarge | 143.305 | 148.315 | 124.352 | 0.84x | +0.3% |
| stress_medium | 3.609 | 3.938 | 3.888 | 0.99x | +0.3% |
| stress_large | 15.187 | 16.746 | 15.921 | 0.95x | +0.3% |
| stress_xlarge | 175.534 | 181.318 | 186.880 | 1.03x | +0.5% |
| mrtree_medium | 0.216 | 0.443 | 0.302 | 0.68x | +0.4% |
| mrtree_large | 0.860 | 1.746 | 1.188 | 0.68x | +0.1% |
| mrtree_xlarge | 4.585 | 9.372 | 6.113 | 0.65x | -1.0% |
| radial_medium | 1.371 | 1.577 | 0.230 | 0.15x | +0.3% |
| radial_large | 3.033 | 3.939 | 1.211 | 0.31x | +0.5% |
| radial_xlarge | 13.033 | 17.740 | 12.293 | 0.69x | +0.2% |
| rectpacking_medium | 0.167 | 0.255 | 0.155 | 0.61x | -1.3% |
| rectpacking_large | 0.685 | 1.016 | 0.637 | 0.63x | -1.2% |
| rectpacking_xlarge | 4.854 | 6.617 | 3.707 | 0.56x | +0.6% |
| routing_polyline | 2.824 | 3.246 | 3.044 | 0.94x | -1.6% |
| routing_orthogonal | 3.114 | 3.609 | 3.460 | 0.96x | -0.6% |
| routing_splines | 3.744 | 4.232 | 3.581 | 0.85x | -1.4% |
| crossmin_layer_sweep | 3.193 | 3.641 | 3.455 | 0.95x | -0.9% |
| crossmin_none | 1.758 | 2.295 | 2.074 | 0.90x | +1.1% |
| hierarchy_flat | 1.574 | 1.847 | 1.727 | 0.94x | -1.6% |
| hierarchy_nested | 0.873 | 1.079 | 0.901 | 0.83x | -1.4% |

- geometric mean lean/rust_api: 0.74x over 26 scenarios
- regression gate (5%): pass
