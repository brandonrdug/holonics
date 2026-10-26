#!/bin/bash
# The host pass baseline on the 7900X: one pass of the docs passage at 8 and 24 streams, run
# serially (each a throughput read that needs the cores alone). Deadline 300 s each.
set -u
cd "$(git rev-parse --show-toplevel)"
P=.local/runs/passage/v1
sha() { sha256sum "$1" | cut -d' ' -f1; }
for S in 8 24; do
  OUT=.local/runs/host_s$S
  rm -rf "$OUT"
  python3 .local/runs/measure.py timeout 300 target/release/examples/solenoidal_alpha complete-language train-two-ladder-tower-classes 257 \
    $P/TRAIN.classes $(sha $P/TRAIN.classes) $P/DEV.classes $(sha $P/DEV.classes) $P/DEV.roles $(sha $P/DEV.roles) \
    $P/KEYS $(sha $P/KEYS) 64 128 256 2 $S 128 1 7 $OUT > .local/runs/host_s$S.txt 2> .local/runs/host_s$S.time
  echo "streams=$S exit=$?" >> .local/runs/host_s$S.txt
done
