#!/usr/bin/env bash
# The read of the located-transport record (§0.6): four draws together, one thread each, each in its
# own systemd scope under the outer deadline of 1,000 s. Run from the worktree root after
# `cargo build --release -p holonics --example hnn_prediction`.
set -u -o pipefail
receipts=research/records/2026-10-05_THE_LOCATED_TRANSPORT_receipts
binary=$PWD/target/release/examples/hnn_prediction
for seed in 2026100911 2026100912 2026100913 2026100914; do
  (
    start=$(date +%s%3N)
    systemd-run --user --wait --collect --pipe -p MemoryAccounting=yes --unit="transport-read-$seed" \
      timeout 1000 "$binary" executed transport "$seed" 48 120 "$PWD/$receipts/s$seed" \
      > "$receipts/s${seed}_log.txt" 2> "$receipts/s${seed}_scope.txt"
    echo "exit $? wall $(( $(date +%s%3N) - start )) ms" >> "$receipts/s${seed}_log.txt"
    gzip -f "$receipts/s$seed.curve"
  ) &
done
wait
