#!/bin/bash
# The tension at the crossing on lap 75's mean (the lead's read of November 16; guesses fixed 21:44 UTC in
# research/records/receipts/2026-11-16_tension/guesses.txt). A reading on the host's threads beside the card's lap: it opens no card and
# writes no state. Projection: the dev read gave 357 places in 4.05 s on 8 threads (88 places a second); 52,000 places about 600 s; the
# deadline 1,200 s.
set -u
ROOT=ROOT; R=$ROOT/.local/wt/lead/.local/run/tension; Q=$ROOT/.local/wt/depth-sweep/.local/run/mark/lane/line
U0=$ROOT/.local/wt/section-edge/.local/run/gsm8k/UNITS0; K=$ROOT/.local/wt/field-card/.local/run/KEYS8
C=$ROOT/.local/wt/store-trainer/.local/run/p48/g115r1/CODEC; T=$R/tension75.tsv; M=$Q/lap75/MEAN.3000
sha() { sha256sum "$1" | cut -c1-64; }
env -i HOME=$HOME PATH=$PATH RAYON_NUM_THREADS=8 timeout 1200 $R/bin/athena_tension host complete-language read-tension $U0 $(sha $U0) $K $(sha $K) $C $(sha $C) $T $(sha $T) $M $(sha $M) $R/out75
echo "READ75 exit $? $(date -u +%H:%M:%S)"
