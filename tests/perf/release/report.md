# Performance report

- machine: Apple M1, 8 cores, 8 GiB, macOS 27.0
- engines: rust_native, rust_api, lean_api

| scenario | rust_native ms | rust_api ms | lean_api ms | lean/rust_api |
|---|---|---|---|---|
| layered_small | 0.489 | 0.585 | 0.316 | 0.54x |
| layered_medium | 3.369 | 3.972 | 2.910 | 0.73x |
| layered_large | 16.741 | 19.393 | 15.059 | 0.78x |
| layered_xlarge | 283.459 | 300.060 | 258.987 | 0.86x |
| force_medium | 3.125 | 3.521 | 2.777 | 0.79x |
| force_large | 13.542 | 15.257 | 11.420 | 0.75x |
| force_xlarge | 154.389 | 155.521 | 129.303 | 0.83x |
| stress_medium | 3.893 | 4.196 | 3.837 | 0.91x |
| stress_large | 16.027 | 17.586 | 15.875 | 0.90x |
| stress_xlarge | 184.161 | 188.777 | 191.905 | 1.02x |
| mrtree_medium | 0.254 | 0.463 | 0.254 | 0.55x |
| mrtree_large | 0.947 | 1.884 | 1.032 | 0.55x |
| mrtree_xlarge | 5.405 | 10.069 | 5.429 | 0.54x |
| radial_medium | 1.517 | 1.643 | 0.196 | 0.12x |
| radial_large | 3.261 | 4.137 | 1.074 | 0.26x |
| radial_xlarge | 13.740 | 18.885 | 11.997 | 0.64x |
| rectpacking_medium | 0.177 | 0.272 | 0.126 | 0.46x |
| rectpacking_large | 0.715 | 1.087 | 0.533 | 0.49x |
| rectpacking_xlarge | 5.115 | 6.962 | 3.358 | 0.48x |
| routing_polyline | 2.939 | 3.494 | 2.531 | 0.72x |
| routing_orthogonal | 3.227 | 3.847 | 3.005 | 0.78x |
| routing_splines | 3.903 | 4.558 | 3.078 | 0.68x |
| crossmin_layer_sweep | 3.324 | 3.883 | 2.910 | 0.75x |
| crossmin_none | 1.846 | 2.546 | 1.661 | 0.65x |
| hierarchy_flat | 1.662 | 1.951 | 1.385 | 0.71x |
| hierarchy_nested | 0.926 | 1.142 | 0.657 | 0.58x |

- geometric mean lean/rust_api: 0.61x over 26 scenarios
