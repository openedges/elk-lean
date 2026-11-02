#!/bin/sh
# Gate on a parity report of scripts/compare_model_parity_layouts.py: the "matched rows" count
# must reach a minimum. Writes the report head to the job summary.
# usage: sh .github/scripts/parity_gate.sh <report.md> <minimum matched> <title>
set -eu
report=$1; min=$2; title=$3
[ -f "$report" ] || { echo "$title: no report at $report" >&2; exit 1; }
matched=$(sed -n 's/^- matched rows: \([0-9]*\)$/\1/p' "$report" | head -1)
drift=$(sed -n 's/^- drift rows: \([0-9]*\)$/\1/p' "$report" | head -1)
{ echo "## $title"; echo; sed -n '3,12p' "$report"; echo; } >> "${GITHUB_STEP_SUMMARY:-/dev/null}"
echo "$title: matched ${matched:-?}, drift ${drift:-?}, minimum $min"
[ -n "$matched" ] || { echo "$title: no matched-rows line in $report" >&2; exit 1; }
[ "$matched" -ge "$min" ] || { echo "$title: matched $matched < $min" >&2; exit 1; }
