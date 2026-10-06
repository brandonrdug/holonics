#!/usr/bin/env bash
# The physical repair's runs (record §0), each under its committed pin (guard 22) and an outer
# timeout at the pin's deadline. Run from the repository root of the commit that pins them, with the
# worktree's own CARGO_TARGET_DIR. Receipts land beside this script.
set -u -o pipefail
here=research/records/2026-10-05_THE_PHYSICAL_REPAIR_receipts
cargo build --release -p holonics --example hnn_prediction
bin=${CARGO_TARGET_DIR:-target}/release/examples/hnn_prediction
case "${1:-}" in
  dev)
    # The development read: seed 2_026_100_701 on every terrain, 8 passages, aperture 12.
    timeout 300 "$bin" executed physical-repair A 8 12 "$here/development/dev" \
      research/runs/physical-repair/dev.pin \
      order2=2026100701 line=2026100701 alternation=2026100701 \
      | tee "$here/development/dev_log.txt"
    ;;
  read)
    # The read, once: the repair record's seeds, 64 passages a terrain, aperture 48.
    timeout 6881 "$bin" executed physical-repair A 64 48 "$here/read" \
      research/runs/physical-repair/read.pin \
      order2=2026100711 line=2026100712 alternation=2026100713 \
      | tee "$here/read_log.txt"
    ;;
  *) echo "runs.sh dev | read"; exit 2 ;;
esac
