# tests

- `lean/` — Lean test driver (`lake test`, executable `elktest`). Suites are
  added per plugin as they are ported.
- `model_parity/` — whole-corpus parity reports (inputs/outputs git-ignored;
  `report.md` and `diff_details.tsv` are committed).
- `tmp/` — scratch space for ad-hoc parity runs (git-ignored).
