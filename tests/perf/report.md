# Performance report

- machine: Apple M1, 8 cores, 8 GiB, macOS 27.0
- engines: rust_native, rust_api, lean_api

| scenario | rust_native ms | rust_api ms | lean_api ms | lean/rust_api | lean vs baseline |
|---|---|---|---|---|---|
| layered_small | 0.442 | 0.548 | 0.485 | 0.89x | +0.3% |
| layered_medium | 3.230 | 3.694 | 3.655 | 0.99x | +1.1% |
| layered_large | 15.756 | 18.105 | 18.441 | 1.02x | +1.0% |
| layered_xlarge | 265.259 | 280.588 | 280.358 | 1.00x | +0.6% |
| force_medium | 2.972 | 3.282 | 2.865 | 0.87x | -0.2% |
| force_large | 12.889 | 14.387 | 12.127 | 0.84x | +0.3% |
| force_xlarge | 142.996 | 147.189 | 125.406 | 0.85x | -0.1% |
| stress_medium | 3.613 | 3.940 | 3.977 | 1.01x | -0.1% |
| stress_large | 15.148 | 16.667 | 16.335 | 0.98x | -0.4% |
| stress_xlarge | 174.925 | 179.435 | 187.331 | 1.04x | -0.2% |
| mrtree_medium | 0.216 | 0.444 | 0.380 | 0.85x | -0.8% |
| mrtree_large | 0.859 | 1.748 | 1.529 | 0.87x | -0.6% |
| mrtree_xlarge | 4.598 | 9.321 | 7.863 | 0.84x | +0.7% |
| radial_medium | 1.409 | 1.578 | 0.300 | 0.19x | -0.7% |
| radial_large | 3.058 | 3.961 | 1.516 | 0.38x | +0.2% |
| radial_xlarge | 13.064 | 17.735 | 13.718 | 0.77x | +0.0% |
| rectpacking_medium | 0.168 | 0.255 | 0.195 | 0.76x | -0.4% |
| rectpacking_large | 0.684 | 1.017 | 0.791 | 0.78x | -0.4% |
| rectpacking_xlarge | 4.856 | 6.605 | 4.431 | 0.67x | -0.7% |
| routing_polyline | 2.837 | 3.247 | 3.261 | 1.00x | +1.3% |
| routing_orthogonal | 3.126 | 3.613 | 3.658 | 1.01x | +0.9% |
| routing_splines | 3.735 | 4.248 | 3.802 | 0.90x | +1.1% |
| crossmin_layer_sweep | 3.127 | 3.674 | 3.659 | 1.00x | +0.1% |
| crossmin_none | 1.763 | 2.292 | 2.164 | 0.94x | +0.2% |
| hierarchy_flat | 1.581 | 1.849 | 1.906 | 1.03x | +0.7% |
| hierarchy_nested | 0.870 | 1.081 | 0.990 | 0.92x | +0.5% |

- geometric mean lean/rust_api: 0.82x over 26 scenarios
- regression gate (5%): pass
