#!/bin/bash
# The tension at the strand's return over the sections lap 76 meets after its first thousand (the lead's founding read, November 16): the
# store's prefix role cut from lap 76's MEAN.1000 as train-store cuts it, 4 sections, every open site and one written site in 4, by tick.
# A reading on the host's threads beside the card's lap: it opens no card and writes no state. Projection: unmeasured; the first section's
# line gives the rate, and the deadline is 1,500 s (a section's host forward and reverse were about 240 s a thread on November 11).
set -u
ROOT=ROOT; R=$ROOT/.local/wt/lead/.local/run/tension; Q=$ROOT/.local/wt/depth-sweep/.local/run/mark/lane/line
S=$ROOT/.local/corpus/store-2026-11-16; U0=$ROOT/.local/wt/section-edge/.local/run/gsm8k/UNITS0; K=$ROOT/.local/wt/field-card/.local/run/KEYS8
C=$ROOT/.local/wt/store-trainer/.local/run/p48/g115r2/CODEC; M=$Q/lap76/MEAN.1000
sha() { sha256sum "$1" | cut -c1-64; }
env -i HOME=$HOME PATH=$PATH RAYON_NUM_THREADS=10 timeout 1500 $R/bin/athena_tension2 host complete-language read-tension-store $U0 $(sha $U0) $S $(sha $S/STORE.tsv) prefix $K $(sha $K) $C $(sha $C) 4 $M $(sha $M) $R/store76 4
echo "STORE76 exit $? $(date -u +%H:%M:%S)"
