# Performance report

- machine: Apple M1, 8 cores, 8 GiB, macOS 27.0
- engines: rust_native, rust_api, lean_api

| scenario | rust_native ms | rust_api ms | lean_api ms | lean/rust_api | lean vs baseline |
|---|---|---|---|---|---|
| layered_small | 0.448 | 0.569 | 0.492 | 0.86x | -3.8% |
| layered_medium | 3.257 | 3.721 | 3.610 | 0.97x | -3.3% |
| layered_large | 15.850 | 18.169 | 18.651 | 1.03x | -0.6% |
| layered_xlarge | 266.398 | 282.266 | 287.682 | 1.02x | -1.2% |
| force_medium | 3.008 | 3.301 | 2.830 | 0.86x | -0.1% |
| force_large | 13.092 | 14.479 | 12.129 | 0.84x | -0.2% |
| force_xlarge | 143.299 | 149.499 | 125.666 | 0.84x | +0.0% |
| stress_medium | 3.617 | 4.086 | 3.935 | 0.96x | -1.2% |
| stress_large | 15.200 | 16.701 | 16.523 | 0.99x | -0.3% |
| stress_xlarge | 176.434 | 181.498 | 188.062 | 1.04x | -0.3% |
| mrtree_medium | 0.219 | 0.443 | 0.489 | 1.10x | +26.5% ⚠ |
| mrtree_large | 0.879 | 1.755 | 2.259 | 1.29x | +44.9% ⚠ |
| mrtree_xlarge | 4.649 | 9.415 | 14.135 | 1.50x | +70.5% ⚠ |
| radial_medium | 1.344 | 1.632 | 0.375 | 0.23x | +31.4% ⚠ |
| radial_large | 3.061 | 3.952 | 2.751 | 0.70x | +143.7% ⚠ |
| radial_xlarge | 13.118 | 17.834 | 39.227 | 2.20x | +587.2% ⚠ |
| rectpacking_medium | 0.167 | 0.259 | 0.202 | 0.78x | -16.7% |
| rectpacking_large | 0.684 | 1.025 | 0.826 | 0.81x | -15.8% |
| rectpacking_xlarge | 4.880 | 6.666 | 4.629 | 0.69x | -10.5% |
| routing_polyline | 2.822 | 3.333 | 3.229 | 0.97x | -3.8% |
| routing_orthogonal | 3.112 | 3.762 | 3.639 | 0.97x | -4.5% |
| routing_splines | 3.725 | 4.339 | 3.783 | 0.87x | -2.8% |
| crossmin_layer_sweep | 3.114 | 3.707 | 3.647 | 0.98x | -2.8% |
| crossmin_none | 1.756 | 2.310 | 2.210 | 0.96x | -1.0% |
| hierarchy_flat | 1.596 | 1.960 | 1.924 | 0.98x | -2.6% |
| hierarchy_nested | 0.900 | 1.129 | 1.010 | 0.89x | +0.4% |

- geometric mean lean/rust_api: 0.92x over 26 scenarios
- regression gate (5%): FAIL — mrtree_medium +26.5%, mrtree_large +44.9%, mrtree_xlarge +70.5%, radial_medium +31.4%, radial_large +143.7%, radial_xlarge +587.2%
