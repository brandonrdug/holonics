#!/usr/bin/env bash
# The minimal replay of the September 30 baseline (THE_REBUILD U6, the order's C.1; the record
# research/records/2026-09-30_THE_BASELINE_BEFORE_THE_SEPTEMBER_30_RETIREMENTS.md, which fixes the
# baseline commit d4596102 and states what this script masks).
#
# One development read of step 1's harness: `hnn_prediction -- executed evaluate` on the order-2
# terrain at development seed 41, 8 requests, over the four controls: the lossless opening, the
# founded opening, the native trained constitution and the station-framed refit (both read from the
# modulus record's receipts). The read's listing (the harness's stdout, then its section listing) is
# diffed byte for byte against the reference committed beside the record. Masked: the wall time in
# milliseconds and the two resident-set byte counts of the harness's last line, nothing else.
#
# Every retirement batch reruns it after its change; a mismatch means the batch changed behaviour.
#
#   bash research/notebook/hnn_design/replay_baseline.sh
#
# Exit 0 when the listing matches; 1 with the unified diff when it does not; 2 when the read reaches
# its guard. With REPLAY_OUT set to a directory, the unmasked stdout, the section listing and the
# masked listing are kept there.
set -euo pipefail

root=$(git rev-parse --show-toplevel)
cd "$root"

receipts=research/records/2026-09-30_THE_MODULUS_FOUNDED_OFF_ONE_receipts
reference=research/records/2026-09-30_THE_BASELINE_receipts/replay_reference.txt

if [[ -n "${REPLAY_OUT:-}" ]]; then
  out=$REPLAY_OUT
  mkdir -p "$out"
else
  out=$(mktemp -d)
  trap 'rm -rf "$out"' EXIT
fi

# The read's guard: 600 s against the recorded 93 s at the baseline (the record, §5); a read that
# reaches it stops, and the replay reports incomplete (exit 2), never a match.
cargo build --release -q -p holonics --example hnn_prediction
status=0
timeout 600 cargo run --release -q -p holonics --example hnn_prediction -- \
  executed evaluate order2 41 8 "$out/sections.txt" \
  lossless opening \
  "executed-open=$receipts/E_trained_order2.txt" \
  "refit=$receipts/refit_on_lattice.txt" \
  > "$out/stdout.txt" || status=$?
if (( status == 124 )); then
  echo "replay: INCOMPLETE, the read reached its 600 s guard" >&2
  exit 2
elif (( status != 0 )); then
  echo "replay: the read failed (exit $status)" >&2
  exit "$status"
fi

# The harness's last stdout line is `executed evaluate: <ms> ms; resident <now> now, <peak> peak`
# (or `resident unread`), and since step 1a each constitution's summary line ends in its own wall
# time `; <ms> ms`; only those numbers are masked.
{
  sed -E \
    -e 's/(first lock right [0-9]+); [0-9]+ ms$/\1; <ms> ms/' \
    -e 's/^executed evaluate: [0-9]+ ms; resident [0-9]+ now, [0-9]+ peak$/executed evaluate: <ms> ms; resident <now> now, <peak> peak/' \
    -e 's/^executed evaluate: [0-9]+ ms; resident unread$/executed evaluate: <ms> ms; resident <now> now, <peak> peak/' \
    "$out/stdout.txt"
  cat "$out/sections.txt"
} > "$out/listing.txt"

tail -n 1 "$out/stdout.txt" >&2
if diff -u "$reference" "$out/listing.txt"; then
  echo "replay: the listing matches the baseline reference ($(wc -l < "$reference") lines)"
else
  echo "replay: MISMATCH against $reference" >&2
  exit 1
fi
