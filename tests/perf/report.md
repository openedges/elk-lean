# Performance report

- machine: Apple M1, 8 cores, 8 GiB, macOS 27.0
- engines: rust_native, rust_api, lean_api

| scenario | rust_native ms | rust_api ms | lean_api ms | lean/rust_api | lean vs baseline |
|---|---|---|---|---|---|
| layered_small | 0.448 | 0.545 | 0.490 | 0.90x | +0.9% |
| layered_medium | 3.213 | 3.880 | 3.686 | 0.95x | +0.9% |
| layered_large | 15.763 | 18.095 | 18.465 | 1.02x | +0.1% |
| layered_xlarge | 264.697 | 280.722 | 281.588 | 1.00x | +0.4% |
| force_medium | 2.968 | 3.295 | 2.865 | 0.87x | +0.0% |
| force_large | 12.880 | 14.384 | 12.112 | 0.84x | -0.1% |
| force_xlarge | 143.696 | 146.959 | 125.191 | 0.85x | -0.2% |
| stress_medium | 3.623 | 3.962 | 3.974 | 1.00x | -0.1% |
| stress_large | 15.343 | 16.828 | 16.331 | 0.97x | -0.0% |
| stress_xlarge | 175.766 | 180.593 | 187.117 | 1.04x | -0.1% |
| mrtree_medium | 0.222 | 0.441 | 0.382 | 0.86x | +0.5% |
| mrtree_large | 0.865 | 1.749 | 1.527 | 0.87x | -0.1% |
| mrtree_xlarge | 4.600 | 9.350 | 7.805 | 0.83x | -0.7% |
| radial_medium | 1.351 | 1.628 | 0.301 | 0.19x | +0.3% |
| radial_large | 3.032 | 3.937 | 1.505 | 0.38x | -0.7% |
| radial_xlarge | 13.033 | 17.915 | 13.783 | 0.77x | +0.5% |
| rectpacking_medium | 0.167 | 0.255 | 0.198 | 0.78x | +1.7% |
| rectpacking_large | 0.684 | 1.017 | 0.792 | 0.78x | +0.1% |
| rectpacking_xlarge | 4.893 | 6.579 | 4.442 | 0.68x | +0.3% |
| routing_polyline | 2.838 | 3.239 | 3.262 | 1.01x | +0.0% |
| routing_orthogonal | 3.114 | 3.600 | 3.659 | 1.02x | +0.0% |
| routing_splines | 3.724 | 4.217 | 3.801 | 0.90x | -0.0% |
| crossmin_layer_sweep | 3.123 | 3.652 | 3.658 | 1.00x | -0.0% |
| crossmin_none | 1.748 | 2.311 | 2.154 | 0.93x | -0.5% |
| hierarchy_flat | 1.574 | 1.849 | 1.920 | 1.04x | +0.8% |
| hierarchy_nested | 0.878 | 1.074 | 1.018 | 0.95x | +2.8% |

- geometric mean lean/rust_api: 0.82x over 26 scenarios
- regression gate (5%): pass
