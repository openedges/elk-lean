# Performance report

- machine: Apple M1, 8 cores, 8 GiB, macOS 27.0
- engines: rust_native, rust_api, lean_api

| scenario | rust_native ms | rust_api ms | lean_api ms | lean/rust_api | lean vs baseline |
|---|---|---|---|---|---|
| layered_small | 0.463 | 0.574 | 0.495 | 0.86x | +1.0% |
| layered_medium | 3.347 | 3.889 | 3.662 | 0.94x | -0.7% |
| layered_large | 16.542 | 19.023 | 18.740 | 0.99x | +1.5% |
| layered_xlarge | 281.270 | 297.885 | 293.825 | 0.99x | +4.3% |
| force_medium | 3.115 | 3.424 | 2.931 | 0.86x | +2.3% |
| force_large | 13.593 | 15.147 | 12.288 | 0.81x | +1.4% |
| force_xlarge | 150.621 | 154.171 | 130.293 | 0.85x | +4.1% |
| stress_medium | 3.777 | 4.125 | 4.070 | 0.99x | +2.4% |
| stress_large | 15.925 | 17.496 | 16.769 | 0.96x | +2.7% |
| stress_xlarge | 183.903 | 186.285 | 195.070 | 1.05x | +4.3% |
| mrtree_medium | 0.234 | 0.457 | 0.334 | 0.73x | -12.5% |
| mrtree_large | 0.916 | 1.808 | 1.320 | 0.73x | -13.6% |
| mrtree_xlarge | 4.932 | 9.991 | 6.791 | 0.68x | -13.0% |
| radial_medium | 1.416 | 1.695 | 0.263 | 0.16x | -12.6% |
| radial_large | 3.199 | 4.213 | 1.369 | 0.32x | -9.1% |
| radial_xlarge | 13.742 | 18.919 | 13.124 | 0.69x | -4.8% |
| rectpacking_medium | 0.175 | 0.281 | 0.185 | 0.66x | -6.3% |
| rectpacking_large | 0.718 | 1.095 | 0.755 | 0.69x | -4.6% |
| rectpacking_xlarge | 5.094 | 7.296 | 4.309 | 0.59x | -3.0% |
| routing_polyline | 2.955 | 3.476 | 3.303 | 0.95x | +1.3% |
| routing_orthogonal | 3.250 | 3.806 | 3.730 | 0.98x | +1.9% |
| routing_splines | 3.895 | 4.420 | 3.859 | 0.87x | +1.5% |
| crossmin_layer_sweep | 3.254 | 3.822 | 3.806 | 1.00x | +4.0% |
| crossmin_none | 1.842 | 2.405 | 2.171 | 0.90x | +0.8% |
| hierarchy_flat | 1.666 | 1.917 | 1.976 | 1.03x | +2.9% |
| hierarchy_nested | 0.946 | 1.127 | 1.012 | 0.90x | -0.6% |

- geometric mean lean/rust_api: 0.77x over 26 scenarios
- regression gate (5%): pass
