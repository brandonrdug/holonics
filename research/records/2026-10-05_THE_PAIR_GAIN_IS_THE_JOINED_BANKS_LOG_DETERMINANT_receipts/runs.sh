#!/usr/bin/env bash
# The joint gain's runs (research/records/2026-10-05_THE_PAIR_GAIN_IS_THE_JOINED_BANKS_LOG_DETERMINANT.md),
# each run once, from the worktree root. Thread budget 12 on every release read; the terrains' reads
# run one after the other (one read holds the budget). The states are lane B's and the regressions',
# unchanged. The final confirmation seeds (2_026_093_033, 036, 039) are spent: no run reads them.
set -u
bin=./target/release/examples/hnn_prediction
keys=research/records/2026-10-05_LOCATED_KEYS_receipts
reg=research/records/2026-10-05_THE_REGRESSIONS_LOCATE_THE_LEAST_WINDING_AND_ARE_READ_BY_THE_PAIR_RELEASE_receipts
out=research/records/2026-10-05_THE_PAIR_GAIN_IS_THE_JOINED_BANKS_LOG_DETERMINANT_receipts
states() { # states <terrain>: the keys states' arguments
  if [ "$1" = order2 ]; then
    echo "keys-founded=$keys/state_keys_founded.txt keys-lossless=$keys/state_keys_lossless.txt"
  else
    echo "keys-founded=$reg/state_$1_keys_founded.txt keys-lossless=$reg/state_$1_keys_lossless.txt"
  fi
}
measured() { # measured <log> <command...>: the transient scope's cgroup memory.peak, exact bytes
  local log=$1; shift
  local start; start=$(date +%s%3N)
  systemd-run --user --wait --collect -p MemoryAccounting=yes --working-directory="$PWD" \
    -E RAYON_NUM_THREADS="${RAYON_NUM_THREADS:-}" \
    -p StandardOutput=truncate:"$PWD/$log" -p StandardError=append:"$PWD/$log" -- \
    bash -c '"$@"; s=$?; echo "--- scope: exit $s; memory.peak $(cat /sys/fs/cgroup$(grep "^0::" /proc/self/cgroup | cut -d: -f3)/memory.peak) bytes"; exit $s' _ "$@" 2>&1 \
    | grep -E "terminated|runtime|CPU" >> "$log"
  echo "wall $(( $(date +%s%3N) - start )) ms" >> "$log"
}
# Development 1: the members along the target's trajectory (8 requests, the keys on the founded
# opening; at the build of e237c941, whose member readings this loop's law does not change), and
# every joint reading evaluated on their cells. First read, deadline 120 s each; measured 7,169 to
# 7,398 ms.
for s in 2026093042 2026093043; do
  for t in order2 alternation line; do
    f=$(states $t | cut -d' ' -f1 | cut -d= -f2)
    timeout 120 $bin executed pair-members $t $s 8 $f > $out/development/members_${t}_$s.txt 2>&1
  done
done
(cd $out/development && python3 laws.py members_*.txt > laws.txt && python3 margins.py members_*.txt > margins.txt)
# Development 2: the release with the joint gain (8 requests, both keys states). Deadline 120 s each.
for t in order2 alternation line; do
  RAYON_NUM_THREADS=12 timeout 120 $bin executed evaluate $t 2026093042 8 $out/development/eval_dev_${t}_sections.txt \
    $(states $t) > $out/development/eval_dev_${t}_log.txt 2>&1
  RAYON_NUM_THREADS=12 timeout 120 $bin executed evaluate $t 2026093043 8 $out/development/eval_dev43_${t}_sections.txt \
    $(states $t) > $out/development/eval_dev43_${t}_log.txt 2>&1
done
# Validation, read once after the claim's commit (64 requests, the keys states only; the openings
# read the span's law, untouched). Projections (each state's largest measured time a request before
# launch, times 64; the deadline the upper end, 5/4 of it): order-2 83,952 ms, deadline 105 s; the
# alternation 95,982 ms, deadline 120 s; the line 96,552 ms, deadline 121 s.
RAYON_NUM_THREADS=12 measured $out/validation_order2_log.txt timeout 105 $bin executed evaluate order2 2026093032 64 \
  $out/validation_order2_sections.txt $(states order2)
RAYON_NUM_THREADS=12 measured $out/validation_alternation_log.txt timeout 120 $bin executed evaluate alternation 2026093035 64 \
  $out/validation_alternation_sections.txt $(states alternation)
RAYON_NUM_THREADS=12 measured $out/validation_line_log.txt timeout 121 $bin executed evaluate line 2026093038 64 \
  $out/validation_line_sections.txt $(states line)
# The tallies (nonconstant and constant apart; x_t = x_(t-δ) for the regressions):
#   python3 $reg/tally.py $out/validation_alternation_sections.txt 2
#   python3 $reg/tally.py $out/validation_line_sections.txt 4
