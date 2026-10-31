# Performance report

- machine: Apple M1, 8 cores, 8 GiB, macOS 27.0
- engines: rust_native, rust_api, lean_api

| scenario | rust_native ms | rust_api ms | lean_api ms | lean/rust_api | lean vs baseline |
|---|---|---|---|---|---|
| layered_small | 0.462 | 0.565 | 0.488 | 0.86x | -0.3% |
| layered_medium | 3.335 | 3.857 | 3.704 | 0.96x | +1.1% |
| layered_large | 16.421 | 18.823 | 18.801 | 1.00x | +1.8% |
| layered_xlarge | 281.843 | 296.593 | 291.857 | 0.98x | +3.6% |
| force_medium | 3.099 | 3.598 | 2.922 | 0.81x | +2.0% |
| force_large | 13.460 | 15.021 | 12.111 | 0.81x | -0.0% |
| force_xlarge | 149.598 | 152.175 | 128.860 | 0.85x | +2.9% |
| stress_medium | 3.970 | 4.075 | 4.052 | 0.99x | +2.0% |
| stress_large | 15.825 | 17.293 | 16.646 | 0.96x | +1.9% |
| stress_xlarge | 181.173 | 185.585 | 193.290 | 1.04x | +3.3% |
| mrtree_medium | 0.225 | 0.457 | 0.331 | 0.72x | -0.9% |
| mrtree_large | 0.892 | 1.820 | 1.317 | 0.72x | -0.2% |
| mrtree_xlarge | 4.856 | 9.944 | 6.832 | 0.69x | +0.6% |
| radial_medium | 1.387 | 1.681 | 0.256 | 0.15x | -2.9% |
| radial_large | 3.138 | 4.192 | 1.327 | 0.32x | -3.1% |
| radial_xlarge | 13.541 | 18.662 | 13.004 | 0.70x | -0.9% |
| rectpacking_medium | 0.173 | 0.264 | 0.185 | 0.70x | -0.3% |
| rectpacking_large | 0.709 | 1.054 | 0.750 | 0.71x | -0.7% |
| rectpacking_xlarge | 5.057 | 6.849 | 4.263 | 0.62x | -1.1% |
| routing_polyline | 2.917 | 3.417 | 3.285 | 0.96x | +0.7% |
| routing_orthogonal | 3.212 | 3.775 | 3.667 | 0.97x | +0.2% |
| routing_splines | 3.846 | 4.413 | 3.838 | 0.87x | +1.0% |
| crossmin_layer_sweep | 3.223 | 3.812 | 3.666 | 0.96x | +0.2% |
| crossmin_none | 1.814 | 2.396 | 2.101 | 0.88x | -2.4% |
| hierarchy_flat | 1.640 | 1.914 | 1.925 | 1.01x | +0.3% |
| hierarchy_nested | 0.913 | 1.119 | 0.982 | 0.88x | -3.0% |

- geometric mean lean/rust_api: 0.77x over 26 scenarios
- regression gate (5%): pass
