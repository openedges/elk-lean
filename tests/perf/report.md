# Performance report

- machine: Apple M1, 8 cores, 8 GiB, macOS 27.0
- engines: rust_native, rust_api, lean_api

| scenario | rust_native ms | rust_api ms | lean_api ms | lean/rust_api | lean vs baseline |
|---|---|---|---|---|---|
| layered_small | 0.451 | 0.621 | 0.409 | 0.66x | -1.0% |
| layered_medium | 3.211 | 3.727 | 3.280 | 0.88x | -2.3% |
| layered_large | 15.831 | 18.385 | 17.330 | 0.94x | +0.7% |
| layered_xlarge | 265.021 | 280.674 | 277.461 | 0.99x | -0.4% |
| force_medium | 2.964 | 3.300 | 2.776 | 0.84x | -0.1% |
| force_large | 12.977 | 14.410 | 11.510 | 0.80x | -0.5% |
| force_xlarge | 142.807 | 147.404 | 124.292 | 0.84x | +0.2% |
| stress_medium | 3.622 | 3.962 | 3.847 | 0.97x | -0.8% |
| stress_large | 15.302 | 16.697 | 15.900 | 0.95x | +0.2% |
| stress_xlarge | 175.203 | 179.684 | 186.183 | 1.04x | +0.2% |
| mrtree_medium | 0.217 | 0.443 | 0.292 | 0.66x | -1.1% |
| mrtree_large | 0.862 | 1.814 | 1.160 | 0.64x | -1.2% |
| mrtree_xlarge | 4.610 | 9.351 | 5.969 | 0.64x | -1.3% |
| radial_medium | 1.401 | 1.590 | 0.225 | 0.14x | -1.0% |
| radial_large | 3.032 | 3.990 | 1.191 | 0.30x | -1.0% |
| radial_xlarge | 13.020 | 17.737 | 12.033 | 0.68x | -0.8% |
| rectpacking_medium | 0.167 | 0.255 | 0.150 | 0.59x | -2.5% |
| rectpacking_large | 0.684 | 1.016 | 0.616 | 0.61x | -2.3% |
| rectpacking_xlarge | 4.867 | 6.619 | 3.557 | 0.54x | -3.2% |
| routing_polyline | 2.846 | 3.274 | 2.909 | 0.89x | -3.0% |
| routing_orthogonal | 3.135 | 3.626 | 3.337 | 0.92x | -1.0% |
| routing_splines | 3.743 | 4.243 | 3.428 | 0.81x | -2.4% |
| crossmin_layer_sweep | 3.151 | 3.685 | 3.284 | 0.89x | -2.6% |
| crossmin_none | 1.752 | 2.303 | 1.904 | 0.83x | -4.6% |
| hierarchy_flat | 1.589 | 1.853 | 1.661 | 0.90x | -0.6% |
| hierarchy_nested | 0.878 | 1.083 | 0.824 | 0.76x | -3.3% |

- geometric mean lean/rust_api: 0.71x over 26 scenarios
- regression gate (5%): pass
