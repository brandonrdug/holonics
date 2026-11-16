#!/bin/bash
# A record among eight others of its draw, read on the host (the lead, November 16; guess G-R1 fixed first): 500 met sums and differences,
# the last two value digits opened alone, lap 76's mean, then the held passage with the carried lock (100 places a slice, fresh and carried).
# Readings on the host's threads beside the lap: no card, no state. Projection: about 1,000 regions of about 200 sites, a few minutes on 8
# threads; the held reads about 3 minutes a slice; deadlines 900 s and 1,800 s a read.
set -u
ROOT=ROOT; R=$ROOT/.local/wt/lead/.local/run/tension; Q=$ROOT/.local/wt/depth-sweep/.local/run/mark/lane/line
S=$ROOT/.local/corpus/store-2026-11-16; U0=$ROOT/.local/wt/section-edge/.local/run/gsm8k/UNITS0; K=$ROOT/.local/wt/field-card/.local/run/KEYS8
C=$ROOT/.local/wt/store-trainer/.local/run/p48/g115r1/CODEC; M=$Q/lap76/MEAN.3000; B=$R/bin/athena_tension8
sha() { sha256sum "$1" | cut -c1-64; }
host() { env -i HOME=$HOME PATH=$PATH RAYON_NUM_THREADS=8 timeout "$@"; }
T=$R/crowd76s.tsv
host 900 $B host complete-language read-tension $U0 $(sha $U0) $K $(sha $K) $C $(sha $C) $T $(sha $T) $M $(sha $M) $R/crowd76s | grep -E 'TENSION_(LAW|DONE)|rror'
echo "CROWD76 exit $? $(date -u +%H:%M:%S)"
for g in 0 1000; do
  host 1800 $B host complete-language read-cavity $U0 $(sha $U0) $S $(sha $S/STORE.tsv) $K $(sha $K) $C $(sha $C) 100 $M $(sha $M) $R/cavs76_$g carry=$g > $R/cavs76_$g.log 2>&1
  echo "CAVS76 carry=$g exit $? $(date -u +%H:%M:%S) $(grep -c CAVITY_SLICE $R/cavs76_$g.log) slices"
done
