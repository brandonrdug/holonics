#!/bin/bash
# The junction located from the covector alone on many places (the lead, November 17; guess G-L5 fixed first): read-tension on 60,000
# plain sums at the word problems' lengths at lap 78's mean, then ten products located a tick with 128-wide legs. On the host's threads
# beside lap 79: no card, no state written. Projection: the read about 13 minutes on 8 threads, the location about 25 on 12; deadlines
# 2,400 s and 3,600 s.
set -u
ROOT=ROOT; R=$ROOT/.local/wt/lead/.local/run/tension; Q=$ROOT/.local/wt/depth-sweep/.local/run/mark/lane/line
U0=$ROOT/.local/wt/section-edge/.local/run/gsm8k/UNITS0; K=$ROOT/.local/wt/field-card/.local/run/KEYS8
C=$ROOT/.local/wt/store-trainer/.local/run/p48/g115r1/CODEC; B=$R/bin/athena_tension10; M=$Q/lap78/MEAN.3000; T=$R/sums78.tsv
sha() { sha256sum "$1" | cut -c1-64; }
env -i HOME=$HOME PATH=$PATH RAYON_NUM_THREADS=8 timeout 2400 $B host complete-language read-tension $U0 $(sha $U0) $K $(sha $K) $C $(sha $C) $T $(sha $T) $M $(sha $M) $R/sums78 | grep -E 'TENSION_(LAW|DONE)|rror'
echo "# sums78 read exit $? $(date -u +%H:%M:%S)"
cd $ROOT/.local/wt/lead && timeout 3600 python3 -I tools/tension_ruler.py located $R/sums78 10 > $R/located_sums78.txt 2>&1
echo "# located exit $? $(date -u +%H:%M:%S)"
grep -E '^TENSION_LOCATED met [0-3] 10 |^TENSION_LOCATED_PART met [0-3] units' $R/located_sums78.txt | cut -c1-120
echo "LOCATE78 done $(date -u +%H:%M:%S)"
