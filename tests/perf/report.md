# Performance report

- machine: Apple M1, 8 cores, 8 GiB, macOS 27.0
- engines: rust_native, rust_api, lean_api

| scenario | rust_native ms | rust_api ms | lean_api ms | lean/rust_api | lean vs baseline |
|---|---|---|---|---|---|
| layered_small | 0.460 | 0.612 | 0.449 | 0.73x | -1.7% |
| layered_medium | 3.327 | 3.702 | 3.487 | 0.94x | -0.4% |
| layered_large | 16.401 | 18.279 | 17.600 | 0.96x | -1.1% |
| layered_xlarge | 279.037 | 285.566 | 284.343 | 1.00x | +2.1% |
| force_medium | 3.091 | 3.425 | 2.788 | 0.81x | -2.7% |
| force_large | 13.405 | 14.945 | 11.726 | 0.78x | +0.8% |
| force_xlarge | 148.679 | 152.459 | 124.212 | 0.81x | +0.2% |
| stress_medium | 3.737 | 4.197 | 3.931 | 0.94x | +1.4% |
| stress_large | 15.657 | 17.329 | 16.082 | 0.93x | +0.8% |
| stress_xlarge | 181.209 | 185.825 | 186.942 | 1.01x | +0.6% |
| mrtree_medium | 0.226 | 0.459 | 0.308 | 0.67x | +0.1% |
| mrtree_large | 0.891 | 1.815 | 1.223 | 0.67x | +0.6% |
| mrtree_xlarge | 4.991 | 10.088 | 6.248 | 0.62x | +0.2% |
| radial_medium | 1.467 | 1.687 | 0.236 | 0.14x | +0.1% |
| radial_large | 3.145 | 4.087 | 1.235 | 0.30x | +0.2% |
| radial_xlarge | 13.053 | 18.527 | 12.315 | 0.66x | +0.4% |
| rectpacking_medium | 0.168 | 0.264 | 0.160 | 0.61x | +0.2% |
| rectpacking_large | 0.684 | 1.056 | 0.654 | 0.62x | -0.4% |
| rectpacking_xlarge | 4.872 | 6.867 | 3.766 | 0.55x | +0.7% |
| routing_polyline | 2.906 | 3.405 | 3.093 | 0.91x | -0.7% |
| routing_orthogonal | 3.120 | 3.810 | 3.482 | 0.91x | -0.4% |
| routing_splines | 3.736 | 4.572 | 3.670 | 0.80x | +1.1% |
| crossmin_layer_sweep | 3.121 | 3.842 | 3.485 | 0.91x | -0.2% |
| crossmin_none | 1.748 | 2.391 | 2.052 | 0.86x | -1.9% |
| hierarchy_flat | 1.577 | 1.921 | 1.754 | 0.91x | -1.4% |
| hierarchy_nested | 0.884 | 1.109 | 0.923 | 0.83x | -1.1% |

- geometric mean lean/rust_api: 0.72x over 26 scenarios
- regression gate (5%): pass
