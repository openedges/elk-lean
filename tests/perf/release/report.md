# Performance report

- machine: Apple M1, 8 cores, 8 GiB, macOS 27.0
- engines: rust_native, rust_api, lean_api

| scenario | rust_native ms | rust_api ms | lean_api ms | lean/rust_api | lean vs baseline |
|---|---|---|---|---|---|
| layered_small | 0.477 | 0.568 | 0.305 | 0.54x | -3.6% |
| layered_medium | 3.280 | 3.753 | 2.760 | 0.74x | -5.1% |
| layered_large | 15.896 | 18.321 | 14.447 | 0.79x | -4.1% |
| layered_xlarge | 267.943 | 282.560 | 242.835 | 0.86x | -6.2% |
| force_medium | 2.997 | 3.305 | 2.643 | 0.80x | -4.8% |
| force_large | 13.030 | 14.512 | 11.037 | 0.76x | -3.4% |
| force_xlarge | 144.331 | 148.114 | 122.927 | 0.83x | -4.9% |
| stress_medium | 3.689 | 3.967 | 3.680 | 0.93x | -4.1% |
| stress_large | 15.207 | 16.743 | 15.036 | 0.90x | -5.3% |
| stress_xlarge | 175.513 | 181.761 | 182.874 | 1.01x | -4.7% |
| mrtree_medium | 0.220 | 0.449 | 0.239 | 0.53x | -5.9% |
| mrtree_large | 0.863 | 1.751 | 0.979 | 0.56x | -5.1% |
| mrtree_xlarge | 4.607 | 9.325 | 5.101 | 0.55x | -6.0% |
| radial_medium | 1.341 | 1.588 | 0.184 | 0.12x | -6.2% |
| radial_large | 3.103 | 3.949 | 1.019 | 0.26x | -5.1% |
| radial_xlarge | 13.087 | 19.287 | 11.343 | 0.59x | -5.5% |
| rectpacking_medium | 0.167 | 0.276 | 0.120 | 0.43x | -4.9% |
| rectpacking_large | 0.687 | 1.091 | 0.503 | 0.46x | -5.7% |
| rectpacking_xlarge | 4.878 | 6.893 | 3.093 | 0.45x | -7.9% |
| routing_polyline | 2.853 | 3.399 | 2.420 | 0.71x | -4.4% |
| routing_orthogonal | 3.149 | 3.706 | 2.761 | 0.75x | -8.1% |
| routing_splines | 3.763 | 4.371 | 2.956 | 0.68x | -4.0% |
| crossmin_layer_sweep | 3.159 | 3.775 | 2.766 | 0.73x | -4.9% |
| crossmin_none | 1.762 | 2.323 | 1.581 | 0.68x | -4.8% |
| hierarchy_flat | 1.584 | 1.861 | 1.324 | 0.71x | -4.4% |
| hierarchy_nested | 0.882 | 1.130 | 0.625 | 0.55x | -4.8% |

- geometric mean lean/rust_api: 0.60x over 26 scenarios
- regression gate (5%): pass
