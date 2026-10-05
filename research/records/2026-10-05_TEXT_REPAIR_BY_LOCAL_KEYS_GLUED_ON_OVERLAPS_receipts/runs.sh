#!/usr/bin/env bash
# The runs of research/records/2026-10-05_TEXT_REPAIR_BY_LOCAL_KEYS_GLUED_ON_OVERLAPS.md, from the
# worktree's root. Every byte of text is written to .local/text_repair/ (private); the logs and the
# copy lengths kept here are counts only.
set -euo pipefail
CUT=../../../.local/cuts/curated-u6-choosing-flat-cut.bin   # the main checkout's private cuts
BIN=target/release/examples/hnn_prediction
RECEIPTS=research/records/2026-10-05_TEXT_REPAIR_BY_LOCAL_KEYS_GLUED_ON_OVERLAPS_receipts
cargo build --release -p holonics --example hnn_prediction
# Development (timing and checks): four reads, each under its guard.
for k in 1 2 3; do
  timeout 300 systemd-run --user --wait --collect --pipe -p MemoryAccounting=yes \
    --working-directory="$PWD" -E RAYON_NUM_THREADS=1 "$PWD/$BIN" executed text-repair "$CUT" \
    "$PWD/.local/text_repair/dev" dev > "$RECEIPTS/dev_log_$k.txt" 2> "$RECEIPTS/dev_scope_$k.txt"
done
# The read, once: projection 5,504 ms, deadline 6,880 ms.
timeout 7 systemd-run --user --wait --collect --pipe -p MemoryAccounting=yes \
  --working-directory="$PWD" -E RAYON_NUM_THREADS=1 "$PWD/$BIN" executed text-repair "$CUT" \
  "$PWD/.local/text_repair/run" run > "$RECEIPTS/run_log.txt" 2> "$RECEIPTS/run_scope.txt"
# The copy length of each released span against the training text (the cut's bytes [0, 6144)).
for span in .local/text_repair/run/spans/*.bin; do
  [ -e "$span" ] || continue
  printf '%s ' "$(basename "$span" .bin)"
  python3 tools/copy_length.py --release "$span" --passage .local/text_repair/run/training.bin
done > "$RECEIPTS/copy_lengths.txt"
