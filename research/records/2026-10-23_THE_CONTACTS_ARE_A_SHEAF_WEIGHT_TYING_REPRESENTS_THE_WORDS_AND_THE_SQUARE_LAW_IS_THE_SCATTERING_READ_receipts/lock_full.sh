#!/bin/bash
# The located-equality read on the whole partition (14,112,672 cells), with and without its run evidence.
# usage: lock_full.sh RENDERED_PARTITION  (the text render_partition.py writes for all 6,726 problems)
# Projection: 4.50 us/cell (largest read on 1,000 problems) to 1.5x that for the larger table: 64 s to 95 s a run;
# deadline 120 s a run; about 1.1 GB a run (1,020 MiB measured for the tree alone); two together on four cores.
cd "$(dirname "$0")"
timeout 120 ./lock 24 12 13 64 "$1" > full_run.txt 2>&1 || echo "exit $?" >> full_run.txt &
LOCK_NO_RUN=1 timeout 120 ./lock 24 12 13 64 "$1" > full_norun.txt 2>&1 || echo "exit $?" >> full_norun.txt &
wait
cat full_run.txt full_norun.txt
