# Performance report

- machine: Apple M1, 8 cores, 8 GiB, macOS 27.0
- engines: rust_native, rust_api, lean_api

| scenario | rust_native ms | rust_api ms | lean_api ms | lean/rust_api | lean vs baseline |
|---|---|---|---|---|---|
| layered_small | 0.469 | 0.547 | 0.414 | 0.76x | -4.5% |
| layered_medium | 3.208 | 3.715 | 3.359 | 0.90x | -2.0% |
| layered_large | 15.786 | 18.228 | 17.215 | 0.94x | -2.1% |
| layered_xlarge | 265.964 | 282.045 | 290.391 | 1.03x | +4.3% |
| force_medium | 2.981 | 3.290 | 2.799 | 0.85x | +0.7% |
| force_large | 13.101 | 14.429 | 11.571 | 0.80x | -0.1% |
| force_xlarge | 145.390 | 147.926 | 124.089 | 0.84x | +0.1% |
| stress_medium | 3.648 | 3.949 | 3.885 | 0.98x | +0.2% |
| stress_large | 15.221 | 16.725 | 15.940 | 0.95x | +0.4% |
| stress_xlarge | 176.399 | 180.874 | 186.437 | 1.03x | +0.3% |
| mrtree_medium | 0.217 | 0.444 | 0.298 | 0.67x | -0.9% |
| mrtree_large | 0.859 | 1.752 | 1.174 | 0.67x | -1.0% |
| mrtree_xlarge | 4.592 | 9.395 | 6.054 | 0.64x | -1.0% |
| radial_medium | 1.400 | 1.623 | 0.227 | 0.14x | -0.8% |
| radial_large | 3.071 | 3.976 | 1.212 | 0.30x | +0.6% |
| radial_xlarge | 13.088 | 17.847 | 12.403 | 0.69x | +1.1% |
| rectpacking_medium | 0.168 | 0.255 | 0.163 | 0.64x | +4.6% |
| rectpacking_large | 0.693 | 1.038 | 0.640 | 0.62x | +0.4% |
| rectpacking_xlarge | 4.873 | 6.626 | 3.686 | 0.56x | +0.0% |
| routing_polyline | 2.845 | 3.399 | 3.011 | 0.89x | -1.1% |
| routing_orthogonal | 3.119 | 3.704 | 3.371 | 0.91x | -2.6% |
| routing_splines | 3.741 | 4.276 | 3.513 | 0.82x | -1.9% |
| crossmin_layer_sweep | 3.123 | 3.692 | 3.402 | 0.92x | -1.6% |
| crossmin_none | 1.754 | 2.392 | 2.058 | 0.86x | +0.3% |
| hierarchy_flat | 1.581 | 1.846 | 1.688 | 0.91x | -2.3% |
| hierarchy_nested | 0.873 | 1.076 | 0.857 | 0.80x | -4.9% |

- geometric mean lean/rust_api: 0.73x over 26 scenarios
- regression gate (5%): pass
