#!/usr/bin/env bash
# The segment probe (research/records/2026-10-01_THE_SEGMENT_PROBE_PINNED_BEFORE_ITS_RUN.md): one
# read-only run of `executed segment` on gate A's batch, under the pin's fixed deadline (`timeout 320`)
# and its early stop (any constitution's read above 45,592 ms stops the run, reported incomplete).
#
#   bash research/notebook/hnn_design/segment_probe.sh <out dir>
#
# Exit 0 complete; 3 stopped early by the per-unit bound; 124 the deadline; otherwise the harness's.
set -euo pipefail
root=$(git rev-parse --show-toplevel)
cd "$root"
out=${1:?an output directory}
mkdir -p "$out"
records=research/records
refit=$records/2026-09-30_THE_MODULUS_FOUNDED_OFF_ONE_receipts/refit_on_lattice.txt
best=$records/2026-09-30_STEP_1B_GATE_A_receipts/witness_best.state
bin=${CARGO_TARGET_DIR:-target}/release/examples/hnn_prediction
unit=45592
{ git rev-parse HEAD; sha256sum "$bin" | cut -d' ' -f1; sha256sum "$refit" "$best"; } > "$out/identities.txt"
start=$(date +%s%3N)
RAYON_NUM_THREADS=19 setsid /usr/bin/time -v -o "$out/segment.time" timeout 320 "$bin" \
  executed segment order2 2026093061 8 \
  "refit=$refit" \
  "refit-founded=$refit@102837/131072" \
  "gateA-best=$best" \
  "chord-3/4=opening+$refit:3/4" \
  "chord-1/2=opening+$refit:1/2" \
  "chord-1/4=opening+$refit:1/4" \
  "opening=opening" \
  > "$out/segment.txt" 2> "$out/segment.err" &
pid=$!
stopped=0
# One line per constitution (`  <label> (<source>): solved … ; <ms> ms`); a line above the unit stops it.
while kill -0 "$pid" 2>/dev/null; do
  if awk -v unit="$unit" '/^  [^ ].*: solved .* ms$/ { if ($(NF-1) + 0 > unit) bad = 1 } END { exit !bad }' "$out/segment.txt"; then
    kill -- "-$pid" 2>/dev/null || true
    stopped=1
    break
  fi
  sleep 1
done
status=0
wait "$pid" || status=$?
echo "wall $(( $(date +%s%3N) - start )) ms; exit $status; early stop $stopped" >> "$out/identities.txt"
if (( stopped )); then
  echo "segment probe: INCOMPLETE, a constitution's read passed ${unit} ms" >&2
  exit 3
fi
exit "$status"
