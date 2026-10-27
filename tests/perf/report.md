# Performance report

- machine: Apple M1, 8 cores, 8 GiB, macOS 27.0
- engines: rust_native, rust_api, lean_api

| scenario | rust_native ms | rust_api ms | lean_api ms | lean/rust_api |
|---|---|---|---|---|
| layered_small | 0.443 | 1.342 | 2.459 | 1.83x |
| layered_medium | 3.231 | 3.914 | 22.455 | 5.74x |
| layered_large | 15.808 | 18.219 | 119.538 | 6.56x |
| layered_xlarge | 265.835 | 280.843 | 2243.660 | 7.99x |
| force_medium | 2.972 | 3.292 | 92.409 | 28.07x |
| force_large | 12.897 | 14.361 | 392.035 | 27.30x |
| force_xlarge | 142.591 | 147.278 | 4670.016 | 31.71x |
| stress_medium | 3.610 | 3.934 | 105.885 | 26.92x |
| stress_large | 15.202 | 16.662 | 428.381 | 25.71x |
| stress_xlarge | 175.168 | 179.467 | 5429.057 | 30.25x |
| mrtree_medium | 0.218 | 0.441 | 1.825 | 4.14x |
| mrtree_large | 0.861 | 1.788 | 7.570 | 4.23x |
| mrtree_xlarge | 4.607 | 9.378 | 37.302 | 3.98x |
| radial_medium | 1.399 | 1.580 | 2.026 | 1.28x |
| radial_large | 3.037 | 3.930 | 8.153 | 2.07x |
| radial_xlarge | 13.040 | 17.731 | 41.435 | 2.34x |
| rectpacking_medium | 0.167 | 0.254 | 1.248 | 4.92x |
| rectpacking_large | 0.684 | 1.023 | 5.259 | 5.14x |
| rectpacking_xlarge | 4.888 | 6.598 | 31.716 | 4.81x |
| routing_polyline | 2.818 | 3.300 | 19.474 | 5.90x |
| routing_orthogonal | 3.105 | 3.634 | 22.398 | 6.16x |
| routing_splines | 3.723 | 4.257 | 22.463 | 5.28x |
| crossmin_layer_sweep | 3.109 | 3.668 | 22.615 | 6.17x |
| crossmin_none | 1.755 | 2.303 | 8.361 | 3.63x |
| hierarchy_flat | 1.580 | 1.847 | 8.975 | 4.86x |
| hierarchy_nested | 0.872 | 1.077 | 3.288 | 3.05x |

- geometric mean lean/rust_api: 6.41x over 26 scenarios
