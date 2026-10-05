#!/usr/bin/env bash
# The development reads of the located-transport record (§0.6), from the worktree root.
set -u -o pipefail
d=research/records/2026-10-05_THE_LOCATED_TRANSPORT_receipts/development
b=$PWD/target/release/examples/hnn_prediction
systemd-run --user --wait --collect --pipe -p MemoryAccounting=yes --unit=transport-dev-901b \
  timeout 1200 "$b" executed transport 2026100901 48 120 "$PWD/.local/transport/development/s901" \
  > "$d/s901_log.txt" 2> "$d/s901_scope.txt"
for keys in 48 60; do for s in $(seq 2026100941 2026100956); do
  echo "== seed $s, $keys keys x 120"
  timeout 120 "$b" executed transport "$s" "$keys" 120 .local/transport/explore/x locate
done; done > "$d/exploration_location_only.txt" 2>&1
timeout 600 "$b" executed transport 2026100941 60 120 .local/transport/explore/s941_60x120 \
  > "$d/exploration_s941_60x120_log.txt" 2>&1
