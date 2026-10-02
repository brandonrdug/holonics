#!/usr/bin/env bash
# One read-only probe of `hnn_prediction` under its pin's fixed deadline and per-unit early stop (the
# waiting standard): the harness's per-constitution lines (`  <label>…; <ms> ms`) are watched, and a
# line above the unit stops the run, reported incomplete. Used by the segment probe and the modulus's
# slope (research/records/2026-10-01_THE_SEGMENT_PROBE_PINNED_BEFORE_ITS_RUN.md,
# research/records/2026-10-01_THE_MODULUS_SLOPE_PINNED_BEFORE_ITS_RUN.md).
#
#   [PROBE_THREADS=<n>] bash research/notebook/hnn_design/read_probe.sh <out dir> <unit ms> <deadline s> <harness args>…
#
# The thread budget is 19 (the PC beside its other workers) unless PROBE_THREADS declares another.
#
# Exit 0 complete; 3 stopped early by the per-unit bound; 124 the deadline; otherwise the harness's.
set -euo pipefail
root=$(git rev-parse --show-toplevel)
cd "$root"
out=${1:?an output directory}
unit=${2:?the unit bound in ms}
deadline=${3:?the deadline in s}
shift 3
mkdir -p "$out"
bin=${CARGO_TARGET_DIR:-target}/release/examples/hnn_prediction
{ git rev-parse HEAD; sha256sum "$bin" | cut -d' ' -f1; echo "args $*"; } > "$out/identities.txt"
start=$(date +%s%3N)
RAYON_NUM_THREADS=${PROBE_THREADS:-19} setsid timeout "$deadline" "$bin" "$@" > "$out/listing.txt" 2> "$out/stderr.txt" &
pid=$!
stopped=0
# One line per constitution (`  <label>…; <ms> ms`). The run stops when the read in progress has
# taken longer than the unit since the last such line (or since launch), not only once a slow line
# has been printed.
lines=0
mark=$(date +%s%3N)
while kill -0 "$pid" 2>/dev/null; do
  now=$(date +%s%3N)
  count=$(grep -cE '^  [^ ].*; [0-9]+ ms$' "$out/listing.txt" || true)
  if (( count > lines )); then
    lines=$count
    mark=$now
  elif (( now - mark > unit )); then
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
  echo "read probe: INCOMPLETE, a constitution's read passed ${unit} ms" >&2
  exit 3
fi
exit "$status"
