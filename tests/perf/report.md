# Performance report

- machine: Apple M1, 8 cores, 8 GiB, macOS 27.0
- engines: rust_native, rust_api, lean_api

| scenario | rust_native ms | rust_api ms | lean_api ms | lean/rust_api | lean vs baseline |
|---|---|---|---|---|---|
| layered_small | 0.447 | 0.559 | 0.494 | 0.88x | +0.2% |
| layered_medium | 3.219 | 3.764 | 3.613 | 0.96x | -1.1% |
| layered_large | 15.841 | 18.325 | 18.191 | 0.99x | -0.3% |
| layered_xlarge | 264.946 | 281.718 | 280.238 | 0.99x | +0.1% |
| force_medium | 2.973 | 3.302 | 2.870 | 0.87x | +0.6% |
| force_large | 12.878 | 14.434 | 12.119 | 0.84x | +0.5% |
| force_xlarge | 142.671 | 147.100 | 125.541 | 0.85x | -0.0% |
| stress_medium | 3.612 | 3.939 | 4.007 | 1.02x | +0.4% |
| stress_large | 15.272 | 16.697 | 16.366 | 0.98x | +0.2% |
| stress_xlarge | 174.879 | 180.244 | 187.526 | 1.04x | +0.2% |
| mrtree_medium | 0.222 | 0.485 | 0.384 | 0.79x | +0.8% |
| mrtree_large | 0.860 | 1.774 | 1.536 | 0.87x | +1.4% |
| mrtree_xlarge | 4.594 | 9.460 | 7.830 | 0.83x | +1.9% |
| radial_medium | 1.349 | 1.634 | 0.304 | 0.19x | +2.3% |
| radial_large | 3.040 | 3.982 | 1.513 | 0.38x | +1.5% |
| radial_xlarge | 13.040 | 17.944 | 13.693 | 0.76x | +0.6% |
| rectpacking_medium | 0.167 | 0.260 | 0.202 | 0.78x | +0.3% |
| rectpacking_large | 0.683 | 1.031 | 0.824 | 0.80x | +0.2% |
| rectpacking_xlarge | 4.873 | 6.656 | 4.585 | 0.69x | +0.5% |
| routing_polyline | 2.815 | 3.292 | 3.223 | 0.98x | -0.1% |
| routing_orthogonal | 3.095 | 3.677 | 3.706 | 1.01x | +2.0% |
| routing_splines | 3.706 | 4.292 | 3.762 | 0.88x | -2.9% |
| crossmin_layer_sweep | 3.105 | 3.700 | 3.659 | 0.99x | +0.4% |
| crossmin_none | 1.746 | 2.351 | 2.165 | 0.92x | +0.1% |
| hierarchy_flat | 1.580 | 1.870 | 1.912 | 1.02x | -0.2% |
| hierarchy_nested | 0.882 | 1.086 | 0.989 | 0.91x | -0.3% |

- geometric mean lean/rust_api: 0.82x over 26 scenarios
- regression gate (5%): pass
