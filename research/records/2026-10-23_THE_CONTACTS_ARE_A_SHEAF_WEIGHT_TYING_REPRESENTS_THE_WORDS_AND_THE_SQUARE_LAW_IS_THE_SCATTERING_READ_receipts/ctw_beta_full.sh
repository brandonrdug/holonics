#!/bin/bash
# The whole training partition (6,726 problems, 14,112,672 cells), depth 24, released at 2^12 and unreleased.
# Projection: 5.38 us/cell (largest plain-tree read on 1,000 problems) to 1.5x that for the 6.8x larger table,
# 76 s to 114 s a run; deadline 120 s a run. Memory: about 4.5 GB a run (29M nodes); two together on four cores.
cd "$(dirname "$0")"
M=$(cat ../full/marks.txt)
run() { timeout 120 ./ctw_beta "$@" ../full/train_all.txt "$M" > full_$2.txt 2>&1 || echo "$* exit $?" >> full_$2.txt; }
run 24 12 0 0 & run 24 0 0 0 & wait
cat full_12.txt full_0.txt
