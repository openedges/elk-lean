# Performance report

- machine: Apple M1, 8 cores, 8 GiB, macOS 27.0
- engines: rust_native, rust_api, lean_api

| scenario | rust_native ms | rust_api ms | lean_api ms | lean/rust_api | lean vs baseline |
|---|---|---|---|---|---|
| layered_small | 0.478 | 0.579 | 0.416 | 0.72x | +0.5% |
| layered_medium | 3.317 | 3.693 | 3.399 | 0.92x | +1.2% |
| layered_large | 15.972 | 18.342 | 17.418 | 0.95x | +1.2% |
| layered_xlarge | 266.797 | 282.396 | 290.671 | 1.03x | +4.4% |
| force_medium | 2.972 | 3.307 | 2.859 | 0.86x | +2.9% |
| force_large | 12.966 | 14.462 | 11.724 | 0.81x | +1.3% |
| force_xlarge | 143.275 | 147.973 | 124.576 | 0.84x | +0.5% |
| stress_medium | 3.646 | 3.954 | 3.948 | 1.00x | +1.8% |
| stress_large | 15.244 | 18.202 | 15.933 | 0.88x | +0.4% |
| stress_xlarge | 175.861 | 180.132 | 187.184 | 1.04x | +0.7% |
| mrtree_medium | 0.224 | 0.445 | 0.296 | 0.66x | -0.3% |
| mrtree_large | 0.899 | 1.751 | 1.174 | 0.67x | +0.0% |
| mrtree_xlarge | 4.606 | 9.448 | 6.050 | 0.64x | -0.0% |
| radial_medium | 1.342 | 1.630 | 0.228 | 0.14x | +0.4% |
| radial_large | 3.208 | 3.951 | 1.222 | 0.31x | +1.6% |
| radial_xlarge | 13.176 | 17.961 | 12.194 | 0.68x | +0.5% |
| rectpacking_medium | 0.167 | 0.255 | 0.161 | 0.63x | +4.6% |
| rectpacking_large | 0.724 | 1.025 | 0.654 | 0.64x | +3.7% |
| rectpacking_xlarge | 4.913 | 6.624 | 3.722 | 0.56x | +1.3% |
| routing_polyline | 2.865 | 3.283 | 3.040 | 0.93x | +1.4% |
| routing_orthogonal | 3.113 | 3.811 | 3.383 | 0.89x | +0.3% |
| routing_splines | 3.723 | 4.323 | 3.514 | 0.81x | +0.0% |
| crossmin_layer_sweep | 3.112 | 3.673 | 3.370 | 0.92x | -0.9% |
| crossmin_none | 1.749 | 2.309 | 2.020 | 0.87x | +1.3% |
| hierarchy_flat | 1.582 | 1.852 | 1.671 | 0.90x | -0.3% |
| hierarchy_nested | 0.886 | 1.090 | 0.852 | 0.78x | -0.6% |

- geometric mean lean/rust_api: 0.73x over 26 scenarios
- regression gate (5%): pass
