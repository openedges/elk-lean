# Performance report

- machine: Apple M1, 8 cores, 8 GiB, macOS 27.0
- engines: rust_native, rust_api, lean_api

| scenario | rust_native ms | rust_api ms | lean_api ms | lean/rust_api | lean vs baseline |
|---|---|---|---|---|---|
| layered_small | 0.449 | 0.573 | 0.772 | 1.35x | -68.6% |
| layered_medium | 3.215 | 4.054 | 7.113 | 1.75x | -68.3% |
| layered_large | 15.823 | 18.517 | 36.787 | 1.99x | -69.2% |
| layered_xlarge | 263.984 | 279.528 | 793.905 | 2.84x | -64.6% |
| force_medium | 2.962 | 3.282 | 7.636 | 2.33x | -91.7% |
| force_large | 12.878 | 14.466 | 32.899 | 2.27x | -91.6% |
| force_xlarge | 142.380 | 147.456 | 304.041 | 2.06x | -93.5% |
| stress_medium | 3.604 | 4.029 | 9.500 | 2.36x | -91.0% |
| stress_large | 15.164 | 16.709 | 39.050 | 2.34x | -90.9% |
| stress_xlarge | 174.848 | 179.438 | 435.147 | 2.43x | -92.0% |
| mrtree_medium | 0.218 | 0.448 | 0.662 | 1.48x | -63.7% |
| mrtree_large | 0.859 | 1.770 | 2.706 | 1.53x | -64.3% |
| mrtree_xlarge | 4.604 | 9.416 | 13.921 | 1.48x | -62.7% |
| radial_medium | 1.340 | 1.639 | 0.550 | 0.34x | -72.8% |
| radial_large | 3.042 | 3.936 | 2.238 | 0.57x | -72.6% |
| radial_xlarge | 13.038 | 17.677 | 11.155 | 0.63x | -73.1% |
| rectpacking_medium | 0.168 | 0.254 | 0.592 | 2.33x | -52.5% |
| rectpacking_large | 0.686 | 1.027 | 2.533 | 2.47x | -51.8% |
| rectpacking_xlarge | 4.885 | 6.671 | 14.331 | 2.15x | -54.8% |
| routing_polyline | 2.815 | 3.265 | 5.781 | 1.77x | -70.3% |
| routing_orthogonal | 3.120 | 3.622 | 7.135 | 1.97x | -68.1% |
| routing_splines | 3.714 | 4.241 | 7.345 | 1.73x | -67.3% |
| crossmin_layer_sweep | 3.113 | 3.670 | 7.126 | 1.94x | -68.5% |
| crossmin_none | 1.754 | 2.306 | 4.614 | 2.00x | -44.8% |
| hierarchy_flat | 1.583 | 1.847 | 3.234 | 1.75x | -64.0% |
| hierarchy_nested | 0.883 | 1.072 | 1.533 | 1.43x | -53.4% |

- geometric mean lean/rust_api: 1.66x over 26 scenarios
- regression gate (5%): pass (baseline refreshed from this run)
