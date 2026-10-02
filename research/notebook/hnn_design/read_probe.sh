#!/usr/bin/env bash
# One read-only probe of `hnn_prediction` under its pin's fixed deadline and per-unit early stop (the
# waiting standard): the harness's per-constitution lines (`  <label>…; <ms> ms`) are watched, and a
# line above the unit stops the run, reported incomplete. Used by the segment probe and the modulus's
# slope (research/records/2026-10-01_THE_SEGMENT_PROBE_PINNED_BEFORE_ITS_RUN.md,
# research/records/2026-10-01_THE_MODULUS_SLOPE_PINNED_BEFORE_ITS_RUN.md).
#
#   bash research/notebook/hnn_design/read_probe.sh <out dir> <unit ms> <deadline s> <harness args>…
#
# Exit 0 complete; 3 stopped early by the per-unit bound; 124 the deadline; otherwise the harness's.
#
# An executed move's units each take their own bound in ms, chosen by the last unit line on stderr
# (the unit running is the one after it); unset, a kind takes <unit ms>:
#   UNIT_INCUMBENT_MS    before any line: the move's incumbent read
#   UNIT_PERSISTENCE_MS  after "the move's incumbent read": the proposal and persistence read
#   UNIT_SLOPE_MS        after "the move's proposal and persistence read": returns, slope, first step
#   UNIT_REREAD_MS       after "the move's returns, slope and first step" or any "a trial's …" line:
#                        the next trial's deposit and first-order bound (or its refusal before
#                        them), the trial's reread, or the move's end
# Every trial prints a line after its deposit and first-order bound or its refusal before them, and
# another after its reread, so one reread-kind gap holds one such unit. A move refused before its
# first step (the certificate's refusal or an early return before the ladder) ends under the slope
# kind, and a projection of that kind covers it. The incumbent kind also holds process start, the
# terrain and the requests. Under move-once with several metrics, the next metric's incumbent read
# follows the last trial's line and runs under the reread kind; no current run uses that. Any other
# per-constitution line takes <unit ms>. The four effective bounds are written to identities.txt.
set -euo pipefail
root=$(git rev-parse --show-toplevel)
cd "$root"
out=${1:?an output directory}
unit=${2:?the unit bound in ms}
deadline=${3:?the deadline in s}
shift 3
mkdir -p "$out"
bin=${CARGO_TARGET_DIR:-target}/release/examples/hnn_prediction
{ git rev-parse HEAD; sha256sum "$bin" | cut -d' ' -f1; echo "args $*"
  echo "unit bounds ms: incumbent ${UNIT_INCUMBENT_MS:-$unit} persistence ${UNIT_PERSISTENCE_MS:-$unit} slope ${UNIT_SLOPE_MS:-$unit} reread ${UNIT_REREAD_MS:-$unit}"
} > "$out/identities.txt"
start=$(date +%s%3N)
RAYON_NUM_THREADS=${RAYON_NUM_THREADS:-19} setsid timeout "$deadline" "$bin" "$@" > "$out/listing.txt" 2> "$out/stderr.txt" &
pid=$!
stopped=0
# One line per constitution or unit of work (`  <label>…; <ms> ms`, on stdout or stderr: an executed
# move prints its incumbent read, its persistence read, its returns and slope, each trial's deposit
# and first-order bound, and each trial's reread). The run stops when the read in progress has taken longer than the unit since the last
# such line (or since launch), not only once a slow line has been printed.
lines=0
mark=$(date +%s%3N)
bound=${UNIT_INCUMBENT_MS:-$unit}
kind=incumbent
while kill -0 "$pid" 2>/dev/null; do
  now=$(date +%s%3N)
  count=$(cat "$out/listing.txt" "$out/stderr.txt" | grep -cE '^  [^ ].*; [0-9]+ ms$' || true)
  if (( count > lines )); then
    lines=$count
    mark=$now
    last=$(grep -E '^  [^ ].*; [0-9]+ ms$' "$out/stderr.txt" | tail -1 || true)
    case "$last" in
      "  the move's incumbent read;"*) kind=persistence; bound=${UNIT_PERSISTENCE_MS:-$unit} ;;
      "  the move's proposal and persistence read;"*) kind=slope; bound=${UNIT_SLOPE_MS:-$unit} ;;
      "  the move's returns, slope and first step;"*|"  a trial's "*)
        kind=reread; bound=${UNIT_REREAD_MS:-$unit} ;;
      *) kind=line; bound=$unit ;;
    esac
  elif (( now - mark > bound )); then
    kill -- "-$pid" 2>/dev/null || true
    stopped=1
    break
  fi
  sleep 1
done
status=0
wait "$pid" || status=$?
if (( stopped )); then
  echo "early stop in the unit after the last line: $kind, bound $bound ms" >> "$out/identities.txt"
fi
echo "wall $(( $(date +%s%3N) - start )) ms; exit $status; early stop $stopped" >> "$out/identities.txt"
if (( stopped )); then
  echo "read probe: INCOMPLETE, a unit ($kind) passed its ${bound} ms" >&2
  exit 3
fi
exit "$status"
