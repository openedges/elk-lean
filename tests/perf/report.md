# Performance report

- machine: Apple M1, 8 cores, 8 GiB, macOS 27.0
- engines: rust_native, rust_api, lean_api

| scenario | rust_native ms | rust_api ms | lean_api ms | lean/rust_api | lean vs baseline |
|---|---|---|---|---|---|
| layered_small | 0.455 | 0.591 | 0.430 | 0.73x | +4.1% |
| layered_medium | 3.278 | 3.719 | 3.403 | 0.92x | +1.3% |
| layered_large | 15.872 | 18.504 | 17.346 | 0.94x | +0.8% |
| layered_xlarge | 266.598 | 282.862 | 292.406 | 1.03x | +5.0% |
| force_medium | 3.003 | 3.303 | 2.805 | 0.85x | +1.0% |
| force_large | 12.885 | 14.550 | 11.750 | 0.81x | +1.5% |
| force_xlarge | 143.065 | 148.397 | 124.705 | 0.84x | +0.6% |
| stress_medium | 3.708 | 3.939 | 3.924 | 1.00x | +1.2% |
| stress_large | 15.346 | 16.833 | 16.051 | 0.95x | +1.1% |
| stress_xlarge | 181.009 | 180.589 | 187.319 | 1.04x | +0.8% |
| mrtree_medium | 0.217 | 0.443 | 0.296 | 0.67x | -0.0% |
| mrtree_large | 0.859 | 1.784 | 1.177 | 0.66x | +0.3% |
| mrtree_xlarge | 4.778 | 9.545 | 6.051 | 0.63x | -0.0% |
| radial_medium | 1.385 | 1.567 | 0.227 | 0.14x | -0.1% |
| radial_large | 3.077 | 3.963 | 1.203 | 0.30x | -0.2% |
| radial_xlarge | 13.118 | 18.082 | 12.405 | 0.69x | +2.2% |
| rectpacking_medium | 0.168 | 0.264 | 0.154 | 0.58x | -0.1% |
| rectpacking_large | 0.686 | 1.030 | 0.630 | 0.61x | -0.1% |
| rectpacking_xlarge | 4.902 | 6.602 | 3.674 | 0.56x | -0.3% |
| routing_polyline | 2.824 | 3.294 | 2.998 | 0.91x | -0.4% |
| routing_orthogonal | 3.118 | 3.617 | 3.376 | 0.93x | +0.2% |
| routing_splines | 3.728 | 4.235 | 3.529 | 0.83x | +0.4% |
| crossmin_layer_sweep | 3.116 | 3.648 | 3.402 | 0.93x | +0.0% |
| crossmin_none | 1.758 | 2.401 | 2.001 | 0.83x | +0.3% |
| hierarchy_flat | 1.584 | 1.862 | 1.676 | 0.90x | -0.7% |
| hierarchy_nested | 0.874 | 1.092 | 0.863 | 0.79x | +0.7% |

- geometric mean lean/rust_api: 0.73x over 26 scenarios
- regression gate (5%): pass
