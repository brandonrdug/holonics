#!/usr/bin/env bash
# The keys states written again at main (9914bc5a), after #367 (the regressions record, §12): each run
# once, from the worktree root, at the build of 9914bc5a's source (`cargo build --release -p holonics
# --example hnn_prediction`). Every limit is a committed pin's (research/runs/states-written-again/,
# THE_MACHINE guard 22), read here and refused when untracked, edited or committed more than once;
# no deadline or thread count is written on a command line below. The final confirmation seeds
# (2_026_093_033, 036, 039) are spent: no run reads them.
#   bash runs.sh passages     the training passages and the probe (keys.pin, keys-probe.pin)
#   bash runs.sh development  the development reads on 2_026_093_042 (evaluate-dev.pin)
#   bash runs.sh validation   the validation reads, 64 requests each (evaluate-validation.pin)
set -u
bin=./target/release/examples/hnn_prediction
out=research/records/2026-10-05_THE_REGRESSIONS_LOCATE_THE_LEAST_WINDING_AND_ARE_READ_BY_THE_PAIR_RELEASE_receipts/written_again
pins=research/runs/states-written-again
gain=research/records/2026-10-05_THE_PAIR_GAIN_IS_THE_JOINED_BANKS_LOG_DETERMINANT_receipts
pin() { # pin <file> <key>: the committed pin's field
  local f=$pins/$1
  git ls-files --error-unmatch -- "$f" > /dev/null 2>&1 || { echo "refused: $f is not committed" >&2; exit 3; }
  git diff --quiet HEAD -- "$f" || { echo "refused: $f differs from its commit" >&2; exit 3; }
  [ "$(git log --format=%H -- "$f" | wc -l)" = 1 ] || { echo "refused: $f was committed more than once" >&2; exit 3; }
  sed -n "s/^$2 = //p" "$f"
}
limits() { # limits <pin>: the outer timeout's seconds and the thread budget
  local ms; ms=$(pin "$1" deadline_ms)
  [ $(( ms % 1000 )) = 0 ] || { echo "refused: $1's deadline is not whole seconds" >&2; exit 3; }
  deadline=$(( ms / 1000 )); threads=$(pin "$1" threads)
}
measured() { # measured <log> <command...>: the transient scope's cgroup memory.peak (exact bytes) and wall ms
  local log=$1; shift
  local start; start=$(date +%s%3N)
  systemd-run --user --wait --collect -p MemoryAccounting=yes --working-directory="$PWD" \
    -E RAYON_NUM_THREADS="$threads" \
    -p StandardOutput=truncate:"$PWD/$log" -p StandardError=append:"$PWD/$log" -- \
    bash -c '"$@"; s=$?; echo "--- scope: exit $s; memory.peak $(cat /sys/fs/cgroup$(grep "^0::" /proc/self/cgroup | cut -d: -f3)/memory.peak) bytes"; exit $s' _ "$@" 2>&1 \
    | grep -E "terminated|runtime|CPU" >> "$log"
  echo "wall $(( $(date +%s%3N) - start )) ms" >> "$log"
}
states() { # states <terrain>: the keys states written again
  echo "keys-founded=$out/state_$1_keys_founded.txt keys-lossless=$out/state_$1_keys_lossless.txt"
}
mkdir -p .local/runs "$out/development"
case "${1:-}" in
passages)
  # Lane B's (order-2) and the regressions' (the alternation, the line) training passages: the
  # readings to lock and the deposit at the passage's end, on the lossless and the founded opening.
  limits keys.pin
  for t in "order2 2026093031" "alternation 2026093034" "line 2026093037"; do
    set -- $t
    measured $out/keys_$1_log.txt timeout $deadline $bin executed keys $1 $2 128 .local/runs/keys_$1
    cp .local/runs/keys_$1.founded $out/state_$1_keys_founded.txt
    cp .local/runs/keys_$1.lossless $out/state_$1_keys_lossless.txt
  done
  # Lane B's probe at the scale 4 (its founded state, as lane B committed it).
  limits keys-probe.pin
  measured $out/keys_probe_order2_log.txt timeout $deadline $bin executed keys-probe order2 2026093031 128 4 .local/runs/probe_4
  cp .local/runs/probe_4.founded $out/state_probe_order2_founded.txt
  ;;
development)
  # #365's development reads (8 requests, both keys states), their sections compared with its receipts;
  # then the probe's state mounted on order-2.
  limits evaluate-dev.pin
  for t in order2 alternation line; do
    measured $out/development/eval_dev_${t}_log.txt timeout $deadline $bin executed evaluate $t 2026093042 8 \
      $out/development/eval_dev_${t}_sections.txt $(states $t)
    cmp -s $out/development/eval_dev_${t}_sections.txt $gain/development/eval_dev_${t}_sections.txt \
      && echo "$t: sections identical to #365's development receipt" \
      || echo "$t: sections DIFFER from #365's development receipt"
  done >> $out/development/compare.txt
  measured $out/development/eval_dev_probe_log.txt timeout $deadline $bin executed evaluate order2 2026093042 8 \
    $out/development/eval_dev_probe_sections.txt probe-founded=$out/state_probe_order2_founded.txt
  ;;
validation)
  # #365's validation reads (64 requests, the keys states only), each read once, one after the other.
  limits evaluate-validation.pin
  for t in "order2 2026093032" "alternation 2026093035" "line 2026093038"; do
    set -- $t
    measured $out/validation_$1_log.txt timeout $deadline $bin executed evaluate $1 $2 64 \
      $out/validation_$1_sections.txt $(states $1)
  done
  ;;
*) echo "usage: runs.sh passages|development|validation" >&2; exit 2 ;;
esac
