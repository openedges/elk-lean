# Performance report

- machine: Apple M1, 8 cores, 8 GiB, macOS 27.0
- engines: rust_native, rust_api, lean_api

| scenario | rust_native ms | rust_api ms | lean_api ms | lean/rust_api | lean vs baseline |
|---|---|---|---|---|---|
| layered_small | 0.444 | 0.558 | 0.484 | 0.87x | -2.0% |
| layered_medium | 3.222 | 3.713 | 3.616 | 0.97x | +0.1% |
| layered_large | 15.961 | 18.122 | 18.264 | 1.01x | +0.4% |
| layered_xlarge | 265.179 | 279.628 | 278.719 | 1.00x | -0.5% |
| force_medium | 2.968 | 3.282 | 2.871 | 0.87x | +0.0% |
| force_large | 12.882 | 14.387 | 12.089 | 0.84x | -0.2% |
| force_xlarge | 142.645 | 147.076 | 125.547 | 0.85x | +0.0% |
| stress_medium | 3.615 | 3.933 | 3.982 | 1.01x | -0.6% |
| stress_large | 15.202 | 16.755 | 16.405 | 0.98x | +0.2% |
| stress_xlarge | 174.985 | 179.543 | 187.693 | 1.05x | +0.1% |
| mrtree_medium | 0.218 | 0.443 | 0.383 | 0.86x | -0.2% |
| mrtree_large | 0.861 | 1.756 | 1.538 | 0.88x | +0.1% |
| mrtree_xlarge | 4.596 | 9.324 | 7.808 | 0.84x | -0.3% |
| radial_medium | 1.364 | 1.573 | 0.303 | 0.19x | -0.5% |
| radial_large | 3.037 | 3.940 | 1.513 | 0.38x | +0.0% |
| radial_xlarge | 13.160 | 17.734 | 13.711 | 0.77x | +0.1% |
| rectpacking_medium | 0.168 | 0.256 | 0.195 | 0.76x | -3.4% |
| rectpacking_large | 0.685 | 1.012 | 0.794 | 0.78x | -3.6% |
| rectpacking_xlarge | 4.869 | 6.575 | 4.462 | 0.68x | -2.7% |
| routing_polyline | 2.876 | 3.276 | 3.218 | 0.98x | -0.2% |
| routing_orthogonal | 3.139 | 3.647 | 3.625 | 0.99x | -2.2% |
| routing_splines | 3.774 | 4.278 | 3.760 | 0.88x | -0.0% |
| crossmin_layer_sweep | 3.161 | 3.742 | 3.655 | 0.98x | -0.1% |
| crossmin_none | 1.758 | 2.307 | 2.160 | 0.94x | -0.2% |
| hierarchy_flat | 1.606 | 1.850 | 1.893 | 1.02x | -1.0% |
| hierarchy_nested | 0.882 | 1.076 | 0.985 | 0.92x | -0.4% |

- geometric mean lean/rust_api: 0.82x over 26 scenarios
- regression gate (5%): pass
