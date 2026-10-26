#!/bin/bash
# The card's rate by stream count: one pass of the docs passage at each count, serially (each a
# throughput read of the whole card), under the GPU lock. Deadline 90 s each.
set -u
cd "$(git rev-parse --show-toplevel)"
P=.local/runs/passage/v1
TAG=${1:-v1}
sha() { sha256sum "$1" | cut -d' ' -f1; }
for S in ${STREAMS:-48 96 160 240 320 480}; do
  OUT=.local/runs/scale_${TAG}_s$S
  rm -rf "$OUT"
  PATH=/opt/cuda/bin:$PATH flock .local/gpu.lock python3 .local/runs/measure.py timeout 90 target/release/examples/tower_pass train complete-language train-two-ladder-tower-classes 257 \
    $P/TRAIN.classes $(sha $P/TRAIN.classes) $P/DEV.classes $(sha $P/DEV.classes) $P/DEV.roles $(sha $P/DEV.roles) \
    $P/KEYS $(sha $P/KEYS) 64 128 256 2 $S 128 1 7 $OUT > $OUT.txt 2>&1
  echo "streams=$S $(grep -v SWELL $OUT.txt | grep TOWER_SECTION | tail -1) $(grep -E 'TOWER_CARD|MEASURED' $OUT.txt | tr '\n' ' ')"
done
