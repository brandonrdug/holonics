#!/usr/bin/env bash
# The two counts' pinned runs (research/records/2026-09-30_THE_TWO_COUNTS_PINNED_BEFORE_ITS_RUNS.md
# §3, §6), each run once. Per terrain, one pipeline: its counts, its training (16 moves of 8 from the
# founded opening), then its validation reads (both openings and the five checkpoints on the 64
# validation requests). The three pipelines run at once, each process on a pool of 8 threads.
# The final confirmation seeds (2_026_093_033, 036, 039) are not named here: no run reads them.
set -u
cd "$(git rev-parse --show-toplevel)"
bin=./target/release/examples/hnn_prediction
out=research/records/2026-09-30_THE_TWO_COUNTS_receipts
mkdir -p "$out"

pipeline() {
  local terrain=$1 training=$2 validation=$3
  local t0 t1
  t0=$(date +%s%3N)
  timeout 660 "$bin" executed counts "$terrain" "$training" 128 "$validation" 64 \
    "$out/counts_${terrain}_curve.txt" > "$out/counts_${terrain}_log.txt" 2>&1
  echo "counts exit $? after $(( $(date +%s%3N) - t0 )) ms" >> "$out/runs_${terrain}.txt"
  t1=$(date +%s%3N)
  RAYON_NUM_THREADS=8 timeout 9900 "$bin" executed train executed-open "$terrain" "$training" 8 16 9000000 \
    "$out/E_${terrain}.txt" > "$out/train_${terrain}_log.txt" 2>&1
  echo "train exit $? after $(( $(date +%s%3N) - t1 )) ms" >> "$out/runs_${terrain}.txt"
  local labels=(lossless opening)
  for k in 1 2 4 8 16; do
    if [ -f "$out/E_${terrain}.txt.m$k" ]; then
      labels+=("m$k=$out/E_${terrain}.txt.m$k")
    fi
  done
  t1=$(date +%s%3N)
  RAYON_NUM_THREADS=8 timeout 2760 "$bin" executed evaluate "$terrain" "$validation" 64 \
    "$out/validation_${terrain}_sections.txt" "${labels[@]}" > "$out/validation_${terrain}_log.txt" 2>&1
  echo "evaluate exit $? after $(( $(date +%s%3N) - t1 )) ms" >> "$out/runs_${terrain}.txt"
}

pipeline order2 2026093031 2026093032 &
pipeline alternation 2026093034 2026093035 &
pipeline line 2026093037 2026093038 &
wait
echo "all pipelines done" >> "$out/runs_done.txt"
