# Performance report

- machine: Apple M1, 8 cores, 8 GiB, macOS 27.0
- engines: rust_native, rust_api, lean_api

| scenario | rust_native ms | rust_api ms | lean_api ms | lean/rust_api | lean vs baseline |
|---|---|---|---|---|---|
| layered_small | 0.446 | 0.555 | 0.416 | 0.75x | +0.5% |
| layered_medium | 3.242 | 3.704 | 3.369 | 0.91x | +0.3% |
| layered_large | 15.838 | 18.256 | 17.272 | 0.95x | +0.3% |
| layered_xlarge | 266.890 | 284.779 | 290.422 | 1.02x | +4.3% |
| force_medium | 2.966 | 3.294 | 2.799 | 0.85x | +0.7% |
| force_large | 12.873 | 14.499 | 11.663 | 0.80x | +0.8% |
| force_xlarge | 143.169 | 148.002 | 124.692 | 0.84x | +0.5% |
| stress_medium | 3.617 | 3.991 | 3.882 | 0.97x | +0.1% |
| stress_large | 15.306 | 16.807 | 15.952 | 0.95x | +0.5% |
| stress_xlarge | 175.976 | 179.901 | 187.070 | 1.04x | +0.6% |
| mrtree_medium | 0.221 | 0.443 | 0.296 | 0.67x | -0.4% |
| mrtree_large | 0.859 | 1.773 | 1.178 | 0.66x | +0.3% |
| mrtree_xlarge | 4.702 | 9.623 | 6.105 | 0.63x | +0.8% |
| radial_medium | 1.363 | 1.635 | 0.228 | 0.14x | +0.2% |
| radial_large | 3.037 | 3.947 | 1.208 | 0.31x | +0.2% |
| radial_xlarge | 13.107 | 17.807 | 12.133 | 0.68x | -1.1% |
| rectpacking_medium | 0.168 | 0.255 | 0.154 | 0.61x | -0.8% |
| rectpacking_large | 0.690 | 1.055 | 0.631 | 0.60x | -0.9% |
| rectpacking_xlarge | 4.871 | 6.637 | 3.688 | 0.56x | +0.1% |
| routing_polyline | 2.820 | 3.278 | 3.074 | 0.94x | +2.1% |
| routing_orthogonal | 3.169 | 3.640 | 3.383 | 0.93x | +0.4% |
| routing_splines | 3.790 | 4.298 | 3.546 | 0.83x | +0.9% |
| crossmin_layer_sweep | 3.123 | 3.664 | 3.477 | 0.95x | +2.2% |
| crossmin_none | 1.765 | 2.312 | 1.995 | 0.86x | -2.8% |
| hierarchy_flat | 1.604 | 1.848 | 1.723 | 0.93x | +2.1% |
| hierarchy_nested | 0.880 | 1.073 | 0.861 | 0.80x | +0.4% |

- geometric mean lean/rust_api: 0.73x over 26 scenarios
- regression gate (5%): pass
