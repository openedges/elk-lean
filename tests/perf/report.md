# Performance report

- machine: Apple M1, 8 cores, 8 GiB, macOS 27.0
- engines: rust_native, rust_api, lean_api

| scenario | rust_native ms | rust_api ms | lean_api ms | lean/rust_api | lean vs baseline |
|---|---|---|---|---|---|
| layered_small | 0.449 | 0.543 | 0.600 | 1.10x | -22.3% |
| layered_medium | 3.274 | 3.716 | 4.184 | 1.13x | -41.2% |
| layered_large | 15.829 | 18.229 | 20.668 | 1.13x | -43.8% |
| layered_xlarge | 264.489 | 281.751 | 302.006 | 1.07x | -62.0% |
| force_medium | 2.960 | 3.285 | 2.882 | 0.88x | -62.3% |
| force_large | 12.865 | 14.434 | 12.451 | 0.86x | -62.2% |
| force_xlarge | 142.405 | 146.872 | 126.213 | 0.86x | -58.5% |
| stress_medium | 3.656 | 3.934 | 4.033 | 1.03x | -57.5% |
| stress_large | 15.253 | 16.647 | 16.830 | 1.01x | -56.9% |
| stress_xlarge | 175.029 | 179.124 | 189.181 | 1.06x | -56.5% |
| mrtree_medium | 0.216 | 0.441 | 0.435 | 0.99x | -34.4% |
| mrtree_large | 0.859 | 1.749 | 1.768 | 1.01x | -34.7% |
| mrtree_xlarge | 4.600 | 9.301 | 9.328 | 1.00x | -33.0% |
| radial_medium | 1.376 | 1.629 | 0.333 | 0.20x | -39.6% |
| radial_large | 3.042 | 3.953 | 1.343 | 0.34x | -40.0% |
| radial_xlarge | 13.116 | 17.757 | 6.783 | 0.38x | -39.2% |
| rectpacking_medium | 0.169 | 0.254 | 0.259 | 1.02x | -56.2% |
| rectpacking_large | 0.685 | 1.017 | 1.048 | 1.03x | -58.6% |
| rectpacking_xlarge | 4.874 | 6.642 | 5.748 | 0.87x | -59.9% |
| routing_polyline | 2.823 | 3.314 | 3.753 | 1.13x | -35.1% |
| routing_orthogonal | 3.107 | 3.699 | 4.166 | 1.13x | -41.6% |
| routing_splines | 3.733 | 4.296 | 5.358 | 1.25x | -27.0% |
| crossmin_layer_sweep | 3.127 | 3.683 | 4.170 | 1.13x | -41.5% |
| crossmin_none | 1.771 | 2.322 | 2.673 | 1.15x | -42.1% |
| hierarchy_flat | 1.586 | 1.848 | 2.247 | 1.22x | -30.5% |
| hierarchy_nested | 0.876 | 1.076 | 1.261 | 1.17x | -17.7% |

- geometric mean lean/rust_api: 0.91x over 26 scenarios
- regression gate (5%): pass
