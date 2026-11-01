# Performance report

- machine: Apple M1, 8 cores, 8 GiB, macOS 27.0
- engines: rust_native, rust_api, lean_api

| scenario | rust_native ms | rust_api ms | lean_api ms | lean/rust_api | lean vs baseline |
|---|---|---|---|---|---|
| layered_small | 0.446 | 0.548 | 0.447 | 0.82x | -0.4% |
| layered_medium | 3.216 | 3.718 | 3.464 | 0.93x | -0.7% |
| layered_large | 15.779 | 18.224 | 17.604 | 0.97x | +0.0% |
| layered_xlarge | 265.762 | 282.535 | 278.667 | 0.99x | +0.1% |
| force_medium | 2.984 | 3.326 | 2.779 | 0.84x | -0.3% |
| force_large | 12.936 | 14.594 | 11.579 | 0.79x | -0.5% |
| force_xlarge | 144.773 | 147.599 | 124.165 | 0.84x | +0.1% |
| stress_medium | 3.672 | 4.001 | 3.877 | 0.97x | -0.0% |
| stress_large | 15.404 | 16.939 | 15.875 | 0.94x | -0.5% |
| stress_xlarge | 175.188 | 180.621 | 186.153 | 1.03x | +0.2% |
| mrtree_medium | 0.222 | 0.464 | 0.300 | 0.65x | -2.3% |
| mrtree_large | 0.864 | 1.743 | 1.186 | 0.68x | -2.4% |
| mrtree_xlarge | 4.622 | 9.370 | 6.178 | 0.66x | -0.9% |
| radial_medium | 1.425 | 1.581 | 0.229 | 0.14x | -2.6% |
| radial_large | 3.033 | 3.935 | 1.205 | 0.31x | -2.3% |
| radial_xlarge | 13.038 | 17.720 | 12.353 | 0.70x | +0.7% |
| rectpacking_medium | 0.169 | 0.254 | 0.157 | 0.62x | -1.3% |
| rectpacking_large | 0.698 | 1.013 | 0.645 | 0.64x | -1.3% |
| rectpacking_xlarge | 4.922 | 6.584 | 3.685 | 0.56x | -1.5% |
| routing_polyline | 2.915 | 3.255 | 3.122 | 0.96x | +1.0% |
| routing_orthogonal | 3.181 | 3.709 | 3.493 | 0.94x | +0.3% |
| routing_splines | 3.771 | 4.236 | 3.718 | 0.88x | +2.4% |
| crossmin_layer_sweep | 3.240 | 3.654 | 3.488 | 0.95x | +0.1% |
| crossmin_none | 1.762 | 2.324 | 2.066 | 0.89x | +0.7% |
| hierarchy_flat | 1.592 | 1.850 | 1.768 | 0.96x | +0.8% |
| hierarchy_nested | 0.888 | 1.076 | 0.914 | 0.85x | -1.1% |

- geometric mean lean/rust_api: 0.74x over 26 scenarios
- regression gate (5%): pass
