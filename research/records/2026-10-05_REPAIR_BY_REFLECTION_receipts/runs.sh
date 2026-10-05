#!/usr/bin/env bash
# The runs of research/records/2026-10-05_REPAIR_BY_REFLECTION_THE_LOCATED_PAIR_RESTRICTS_THE_ERASED_CELLS_FROM_BOTH_SIDES.md,
# at that record's commit. Each run is one process under systemd-run (peak memory) and an outer timeout
# at the projection's upper end (§ "Time and memory"); one thread each (the harness is serial).
set -euo pipefail
cd "$(git rev-parse --show-toplevel)"
export CARGO_TARGET_DIR="${CARGO_TARGET_DIR:-$PWD/target}"
cargo build --release -p holonics --example hnn_prediction
bin="$CARGO_TARGET_DIR/release/examples/hnn_prediction"
receipts=research/records/2026-10-05_REPAIR_BY_REFLECTION_receipts
run() { # <deadline s> <out> <args…>
  local deadline=$1 out=$2; shift 2
  systemd-run --user --wait --collect --pipe -p MemoryAccounting=yes \
    --working-directory="$PWD" -E RAYON_NUM_THREADS=1 \
    timeout "$deadline" "$bin" executed repair "$@" "$out" > "${out}_log.txt" 2>&1 || echo "exit $? for $out" >> "${out}_log.txt"
}
# Development (2_026_100_701, readable): timing and checks, every terrain and damage.
for terrain in order2 line alternation; do
  for damage in A B; do
    run 120 "$receipts/development/${terrain}_${damage}" "$terrain" "$damage" 2026100701 64
  done
done
# The read, once each (the record's §0 seeds), 64 passages. Each deadline is 5/4 of the run's largest
# development service time over five measurements (development/*.log, development/timing_remeasured.txt).
run 0.058 "$receipts/order2_A" order2 A 2026100711 64
run 0.058 "$receipts/line_A" line A 2026100712 64
run 0.079 "$receipts/alternation_A" alternation A 2026100713 64
run 1.834 "$receipts/order2_B" order2 B 2026100721 64
run 0.063 "$receipts/line_B" line B 2026100722 64
run 5.890 "$receipts/alternation_B" alternation B 2026100723 64
