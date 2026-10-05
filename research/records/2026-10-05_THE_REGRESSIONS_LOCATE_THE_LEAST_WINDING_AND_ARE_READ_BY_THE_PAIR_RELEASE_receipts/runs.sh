#!/usr/bin/env bash
# The regressions' runs (research/records/2026-10-05_THE_REGRESSIONS_LOCATE_THE_LEAST_WINDING_AND_ARE_READ_BY_THE_PAIR_RELEASE.md),
# each run once, from the worktree root, at the build of the record's commit. Thread budget 12 on
# every release read; the two terrains' reads run one after the other (one read holds the budget).
# Each measured run goes through a transient systemd scope with memory accounting: the scope's own
# cgroup memory.peak is read inside the unit as the command exits (exact bytes) and appended to its
# log with the unit's runtime and the wall time; /usr/bin/time is absent on this host.
set -u
bin=./target/release/examples/hnn_prediction
out=research/records/2026-10-05_THE_REGRESSIONS_LOCATE_THE_LEAST_WINDING_AND_ARE_READ_BY_THE_PAIR_RELEASE_receipts
measured() { # measured <log> <command...>
  local log=$1; shift
  local start; start=$(date +%s%3N)
  systemd-run --user --wait --collect -p MemoryAccounting=yes --working-directory="$PWD" \
    -E RAYON_NUM_THREADS="${RAYON_NUM_THREADS:-}" \
    -p StandardOutput=truncate:"$PWD/$log" -p StandardError=append:"$PWD/$log" -- \
    bash -c '"$@"; s=$?; echo "--- scope: exit $s; memory.peak $(cat /sys/fs/cgroup$(grep "^0::" /proc/self/cgroup | cut -d: -f3)/memory.peak) bytes"; exit $s' _ "$@" 2>&1 \
    | grep -E "terminated|runtime|CPU" >> "$log"
  echo "wall $(( $(date +%s%3N) - start )) ms" >> "$log"
}
# Loop 1, the unchanged law (lane B's location, at 8f89f8bd): the training passages lock nothing.
#   timeout 120 $bin executed keys alternation 2026093034 128 .local/runs/keys_unchanged_alternation
#   timeout 120 $bin executed keys line 2026093037 128 .local/runs/keys_unchanged_line
#   (logs in unchanged_law/)
# Loop 2, the windings law. Order-2's location and deposit, re-read: its states are byte-identical
# to lane B's (research/records/2026-10-05_LOCATED_KEYS_receipts/state_keys_{founded,lossless}.txt).
timeout 120 $bin executed keys order2 2026093031 128 .local/runs/keys_order2 > $out/keys_order2_log.txt 2>&1
# Development (seeds 2_026_093_041 for the keys, 042 for the release, 8 requests): first reads, deadline 120 s each.
for t in alternation line; do
  timeout 120 $bin executed keys $t 2026093041 16 .local/dev/keys_dev_$t > $out/development/keys_dev_${t}_log.txt 2>&1
  RAYON_NUM_THREADS=12 measured $out/development/eval_dev_${t}_log.txt timeout 120 $bin executed evaluate $t 2026093042 8 \
    $out/development/eval_dev_${t}_sections.txt lossless opening \
    keys-lossless=.local/dev/keys_dev_$t.lossless keys-founded=.local/dev/keys_dev_$t.founded
done
timeout 120 $bin executed pair-members alternation 2026093042 2 .local/dev/keys_dev_alternation.founded \
  > $out/development/pair_members_dev_alternation.txt 2>&1
# The machine's training passages (the two counts' seeds): the readings to lock, and the deposit at
# the passage's end. Deadline 120 s each (development read: 473 ms).
measured $out/keys_alternation_log.txt timeout 120 $bin executed keys alternation 2026093034 128 .local/runs/keys_alternation
measured $out/keys_line_log.txt timeout 120 $bin executed keys line 2026093037 128 .local/runs/keys_line
# (the states .local/runs/keys_<terrain>.{founded,lossless} are committed as state_<terrain>_keys_{founded,lossless}.txt)
# The validation reads (64 requests): alternation 2_026_093_035, projection 363,032 ms, deadline 454 s;
# line 2_026_093_038, projection 254,184 ms, deadline 318 s.
RAYON_NUM_THREADS=12 measured $out/validation_alternation_log.txt timeout 454 $bin executed evaluate alternation 2026093035 64 \
  $out/validation_alternation_sections.txt keys-founded=$out/state_alternation_keys_founded.txt \
  keys-lossless=$out/state_alternation_keys_lossless.txt lossless opening
RAYON_NUM_THREADS=12 measured $out/validation_line_log.txt timeout 318 $bin executed evaluate line 2026093038 64 \
  $out/validation_line_sections.txt keys-founded=$out/state_line_keys_founded.txt \
  keys-lossless=$out/state_line_keys_lossless.txt lossless opening
